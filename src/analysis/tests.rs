use std::fmt::Debug;
use std::fs::File;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::Command;

use hashbrown::{HashMap, HashSet};
use llvm_ir::Module;
use serde::{Deserialize, Serialize};
#[cfg(test)]
use test_generator::test_resources;

use crate::analysis::PointsToAnalysis;
use crate::solver::{
    BasicBetterBitVecSolver, BasicBitVecSolver, BasicHashSolver, BasicRoaringSolver,
    BasicSharedBitVecSolver, BetterBitVecWavePropagationSolver, GenericSolver,
    HashWavePropagationSolver, RoaringWavePropagationSolver, SharedBitVecWavePropagationSolver,
    Solver,
};

use super::Cell;

#[derive(Serialize, Deserialize, Debug)]
struct TestConfig {
    c_path: Option<String>,
    llvm_path: Option<String>,
    points_to: HashMap<String, Vec<String>>,
}

fn compile_c(config_dir: &Path, c_path: &String) -> PathBuf {
    let full_c_path = config_dir.join(c_path);
    let bc_path = full_c_path.with_extension("bc");

    let output = Command::new("./ctobc.sh")
        .args([&full_c_path, &bc_path])
        .output()
        .expect("Could not compile c source to bytecode");

    if !output.status.success() {
        io::stdout()
            .write_all(&output.stdout)
            .expect("Failed to write output");
        io::stderr()
            .write_all(&output.stderr)
            .expect("Failed to write output");
        panic!("Could not compile c source to bytecode");
    }

    bc_path
}

fn compile_llvm(config_dir: &Path, llvm_path: &String) -> PathBuf {
    let full_llvm_path = config_dir.join(llvm_path);
    let bc_path = full_llvm_path.with_extension("bc");

    let output = Command::new("./lltobc.sh")
        .args([&full_llvm_path, &bc_path])
        .output()
        .expect("Could not compile ll to bytecode");

    if !output.status.success() {
        io::stdout()
            .write_all(&output.stdout)
            .expect("Failed to write output");
        io::stderr()
            .write_all(&output.stderr)
            .expect("Failed to write output");
        panic!("Could not compile ll to bytecode");
    }

    bc_path
}

fn parse_points_to<'a>(
    points_to: HashMap<String, Vec<String>>,
) -> HashMap<Cell<'a>, HashSet<Cell<'a>>> {
    points_to
        .iter()
        .map(|(cell, pointees)| {
            (
                cell.parse().unwrap_or_else(|err| panic!("{err}")),
                pointees
                    .iter()
                    .map(|cell| cell.parse().unwrap_or_else(|err| panic!("{err}")))
                    .collect(),
            )
        })
        .collect()
}

fn run_test_template<S>(resource: &str)
where
    S: Solver,
    S::Term: TryInto<usize> + TryFrom<usize> + Copy + Debug,
{
    dbg!(resource);
    let config_file = File::open(resource).expect("Could not open file");
    let config: TestConfig =
        serde_json::from_reader(config_file).expect("Could not read config file");

    let config_dir = Path::new(resource)
        .parent()
        .expect("Could not find directory of config file");

    let bc_path = if let Some(c_path) = &config.c_path {
        compile_c(config_dir, c_path)
    } else if let Some(llvm_path) = &config.llvm_path {
        compile_llvm(config_dir, llvm_path)
    } else {
        panic!("Test should provide either 'c_path' or 'llvm_path'")
    };

    let module = Module::from_bc_path(bc_path).expect("Error parsing bc file");

    let expected_points_to = parse_points_to(config.points_to);

    dbg!(&expected_points_to);

    let result = PointsToAnalysis::run::<GenericSolver<_, S, _>>(&module);

    let actual_points_to: HashMap<Cell, HashSet<Cell>> =
        result.get_all_entries().iter_solutions().collect();

    dbg!(&actual_points_to);

    for (cell, pointees) in expected_points_to {
        match actual_points_to.get(&cell) {
            Some(actual_pointees) => assert_eq!(
                &pointees, actual_pointees,
                "Expect cell {cell} to have the correct points-to set"
            ),
            None => panic!("The cell {cell} is not in the solution"),
        }
    }
}

#[test_resources("res/**/test_config.json")]
fn hash(resource: &str) {
    run_test_template::<BasicHashSolver>(resource)
}

#[test_resources("res/**/test_config.json")]
fn bit_vec(resource: &str) {
    run_test_template::<BasicBitVecSolver>(resource)
}

#[test_resources("res/**/test_config.json")]
fn better_bit_vec(resource: &str) {
    run_test_template::<BasicBetterBitVecSolver>(resource)
}

#[test_resources("res/**/test_config.json")]
fn roaring(resource: &str) {
    run_test_template::<BasicRoaringSolver>(resource)
}

#[test_resources("res/**/test_config.json")]
fn shared_bit_vec(resource: &str) {
    run_test_template::<BasicSharedBitVecSolver>(resource)
}

#[test_resources("res/**/test_config.json")]
fn wave_prop(resource: &str) {
    run_test_template::<HashWavePropagationSolver>(resource)
}

#[test_resources("res/**/test_config.json")]
fn roaring_wave_prop(resource: &str) {
    run_test_template::<RoaringWavePropagationSolver>(resource)
}

#[test_resources("res/**/test_config.json")]
fn shared_bit_vec_wave_prop(resource: &str) {
    run_test_template::<SharedBitVecWavePropagationSolver>(resource)
}

#[test_resources("res/**/test_config.json")]
fn better_bitvec_wave_prop(resource: &str) {
    run_test_template::<BetterBitVecWavePropagationSolver>(resource)
}
