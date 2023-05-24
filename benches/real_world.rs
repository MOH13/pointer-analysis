use llvm_ir::Module;
use pointer_analysis::analysis::PointsToAnalysis;
use pointer_analysis::solver::{
    BasicBitVecSolver, BasicHashSolver, BasicRoaringSolver, GenericSolver,
    HashWavePropagationSolver, RoaringWavePropagationSolver, Solver,
};

use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_template<S>(name: &str, c: &mut Criterion)
where
    S: Solver,
    S::Term: TryInto<usize> + TryFrom<usize> + Copy,
{
    for entry in glob::glob("benchmarks/*/bench.bc").unwrap() {
        let entry = entry.expect("Error in path");
        let module = Module::from_bc_path(&entry).expect("Error parsing bc file");
        let bench_name = format!("{} {name}", entry.display());
        c.bench_function(&bench_name, |b| {
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

fn roaring(c: &mut Criterion) {
    bench_template::<BasicRoaringSolver>("BasicRoaring", c);
}

fn hash_wave_prop(c: &mut Criterion) {
    bench_template::<HashWavePropagationSolver>("HashWaveProp", c);
}

fn roaring_wave_prop(c: &mut Criterion) {
    bench_template::<RoaringWavePropagationSolver>("RoaringWaveProp", c);
}

criterion_group!(
    benches,
    hash,
    bit_vec,
    roaring,
    hash_wave_prop,
    roaring_wave_prop
);
criterion_main!(benches);
