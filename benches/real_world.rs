use llvm_ir::Module;
use pointer_analysis::analysis::PointsToAnalysis;
use pointer_analysis::solver::{
    BasicBetterBitVecSolver, BasicHashSolver, BasicRoaringSolver, BasicSharedBitVecSolver,
    BetterBitVecWavePropagationSolver, GenericSolver, HashWavePropagationSolver,
    RoaringWavePropagationSolver, SharedBitVecWavePropagationSolver, Solver,
};
use std::fmt::Debug;

use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_template<S>(name: &str, c: &mut Criterion)
where
    S: Solver,
    S::Term: TryInto<usize> + TryFrom<usize> + Copy + Debug,
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
    bench_template::<BasicHashSolver>("HashWorklist", c);
}

fn better_bit_vec(c: &mut Criterion) {
    bench_template::<BasicBetterBitVecSolver>("BetterBitVecWorklist", c);
}

fn roaring(c: &mut Criterion) {
    bench_template::<BasicRoaringSolver>("RoaringWorklist", c);
}

fn shared_bitvec(c: &mut Criterion) {
    bench_template::<BasicSharedBitVecSolver>("SharedBitVecWorklist", c);
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

fn shared_bitvec_wave_prop(c: &mut Criterion) {
    bench_template::<SharedBitVecWavePropagationSolver>("SharedBitVecWaveProp", c);
}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(10);
    targets = hash,
    better_bit_vec,
    roaring,
    shared_bitvec,
    hash_wave_prop,
    roaring_wave_prop,
    better_bitvec_wave_prop,
    shared_bitvec_wave_prop,
}
criterion_main!(benches);
