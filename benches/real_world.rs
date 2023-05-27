use llvm_ir::Module;
use pointer_analysis::analysis::PointsToAnalysis;
use pointer_analysis::solver::{
    BasicBetterBitVecSolver, BasicBitVecSolver, BasicHashSolver, BasicRoaringSolver,
    BetterBitVecWavePropagationSolver, GenericSolver, HashWavePropagationSolver,
    RoaringWavePropagationSolver, Solver,
};

use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_template<S>(name: &str, c: &mut Criterion)
where
    S: Solver,
    S::Term: TryInto<usize> + TryFrom<usize> + Copy,
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
            b.iter(|| black_box(PointsToAnalysis::run::<GenericSolver<_, S, _>>(&module)));
        });
    }
}

fn hash(c: &mut Criterion) {
    bench_template::<BasicHashSolver>("BasicHash", c);
}

fn bit_vec(c: &mut Criterion) {
    bench_template::<BasicBitVecSolver>("BitVec", c);
}

fn better_bit_vec(c: &mut Criterion) {
    bench_template::<BasicBetterBitVecSolver>("BetterBitVec", c);
}

fn roaring(c: &mut Criterion) {
    bench_template::<BasicRoaringSolver>("BasicRoaring", c);
}

fn hash_wave_prop(c: &mut Criterion) {
    bench_template::<HashWavePropagationSolver>("HashWaveProp", c);
}

fn roaring_wave_prop(c: &mut Criterion) {
    bench_template::<RoaringWavePropagationSolver>("RoaringWaveProp", c);
}

fn better_bitvec_wave_prop(c: &mut Criterion) {
    bench_template::<BetterBitVecWavePropagationSolver>("BetterBitVecWaveProp", c);
}

criterion_group!(
    benches,
    hash,
    bit_vec,
    better_bit_vec,
    roaring,
    hash_wave_prop,
    roaring_wave_prop,
    better_bitvec_wave_prop
);
criterion_main!(benches);
