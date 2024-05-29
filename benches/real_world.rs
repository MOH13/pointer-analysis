use llvm_ir::Module;
use pointer_analysis::analysis::{Cell, Config, PointsToAnalysis};
use pointer_analysis::solver::{
    BasicDemandSolver, BasicHashSolver, ContextInsensitiveSelector, ContextInsensitiveSolver,
    ContextSelector, DemandContextSensitiveInput, Demands, RoaringContextWavePropagationSolver,
    RoaringTidalPropagationSolver, SharedBitVecContextWavePropagationSolver,
    SharedBitVecTidalPropagationSolver, Solver, SolverExt,
};

use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_template<S, C>(
    name: &str,
    solver: S,
    context_selector: C,
    demands: Demands<Cell>,
    c: &mut Criterion,
) where
    S: Solver<DemandContextSensitiveInput<Cell, C>>,
    C: ContextSelector + Clone,
{
    for entry in glob::glob("benchmarks/*/bench.bc").unwrap() {
        let entry = entry.expect("Error in path");
        let bench_name = format!(
            "{} {name}",
            entry
                .parent()
                .and_then(|f| f.file_name())
                .unwrap()
                .to_string_lossy()
        );
        c.bench_function(&bench_name, |b| {
            let module = Module::from_bc_path(&entry).expect("Error parsing bc file");

            b.iter(|| {
                black_box(PointsToAnalysis::run(
                    &solver,
                    &module,
                    context_selector.clone(),
                    demands.clone(),
                    &Config::default(),
                ))
            });
        });
    }
}

fn basic(c: &mut Criterion) {
    let solver = BasicHashSolver::new()
        .as_context_sensitive()
        .as_generic()
        .as_demand_driven();
    bench_template(
        "HashWorklist",
        solver,
        ContextInsensitiveSelector,
        Demands::All,
        c,
    );
}

fn roaring_wave_prop(c: &mut Criterion) {
    let solver = RoaringContextWavePropagationSolver::new().as_demand_driven();
    bench_template(
        "RoaringWaveProp",
        solver,
        ContextInsensitiveSelector,
        Demands::All,
        c,
    );
}

fn shared_bitvec_wave_prop(c: &mut Criterion) {
    let solver = SharedBitVecContextWavePropagationSolver::new().as_demand_driven();
    bench_template(
        "SharedBitVecWaveProp",
        solver,
        ContextInsensitiveSelector,
        Demands::All,
        c,
    );
}

fn basic_demand(c: &mut Criterion) {
    let solver = BasicDemandSolver::new();
    bench_template(
        "BasicDemand",
        solver,
        ContextInsensitiveSelector,
        Demands::All,
        c,
    );
}

fn basic_demand_call_graph_pointed_by(c: &mut Criterion) {
    let solver = BasicDemandSolver::new();
    bench_template(
        "BasicDemandCallGraphPointedBy",
        solver,
        ContextInsensitiveSelector,
        Demands::CallGraphPointedBy,
        c,
    );
}

fn basic_demand_call_graph_points_to(c: &mut Criterion) {
    let solver = BasicDemandSolver::new();
    bench_template(
        "BasicDemandCallGraphPointsTo",
        solver,
        ContextInsensitiveSelector,
        Demands::CallGraphPointsTo,
        c,
    );
}

fn roaring_tidal_prop(c: &mut Criterion) {
    let solver = RoaringTidalPropagationSolver::new();
    bench_template(
        "RoaringTidalProp",
        solver,
        ContextInsensitiveSelector,
        Demands::All,
        c,
    );
}

fn shared_bitvec_tidal_prop(c: &mut Criterion) {
    let solver = SharedBitVecTidalPropagationSolver::new();
    bench_template(
        "SharedBitVecTidalProp",
        solver,
        ContextInsensitiveSelector,
        Demands::All,
        c,
    );
}

fn roaring_tidal_prop_call_graph_pointed_by(c: &mut Criterion) {
    let solver = RoaringTidalPropagationSolver::new();
    bench_template(
        "RoaringTidalPropCallGraphPointedBy",
        solver,
        ContextInsensitiveSelector,
        Demands::CallGraphPointedBy,
        c,
    );
}

fn shared_bitvec_tidal_prop_call_graph_pointed_by(c: &mut Criterion) {
    let solver = SharedBitVecTidalPropagationSolver::new();
    bench_template(
        "SharedBitVecTidalPropCallGraphPointedBy",
        solver,
        ContextInsensitiveSelector,
        Demands::CallGraphPointedBy,
        c,
    );
}

fn roaring_tidal_prop_call_graph_points_to(c: &mut Criterion) {
    let solver = RoaringTidalPropagationSolver::new();
    bench_template(
        "RoaringTidalPropCallGraphPointsTo",
        solver,
        ContextInsensitiveSelector,
        Demands::CallGraphPointsTo,
        c,
    );
}

fn shared_bitvec_tidal_prop_call_graph_points_to(c: &mut Criterion) {
    let solver = SharedBitVecTidalPropagationSolver::new();
    bench_template(
        "SharedBitVecTidalPropCallGraphPointsTo",
        solver,
        ContextInsensitiveSelector,
        Demands::CallGraphPointsTo,
        c,
    );
}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(10);
    targets =
    basic,
    roaring_wave_prop,
    shared_bitvec_wave_prop,
    basic_demand,
    basic_demand_call_graph_pointed_by,
    basic_demand_call_graph_points_to,
    roaring_tidal_prop,
    shared_bitvec_tidal_prop,
    roaring_tidal_prop_call_graph_pointed_by,
    shared_bitvec_tidal_prop_call_graph_pointed_by,
    roaring_tidal_prop_call_graph_points_to,
    shared_bitvec_tidal_prop_call_graph_points_to,
}
criterion_main!(benches);
