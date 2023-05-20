use llvm_ir::Module;
use pointer_analysis::analysis::PointsToAnalysis;
use pointer_analysis::solver::{
    BasicBitVecSolver, BasicHashSolver, GenericSolver, IterableTermSet, RoaringSolver, Solver,
    WavePropagationSolver,
};

use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_template<S>(name: &str, c: &mut Criterion)
where
    S: Solver<Term = usize>,
    S::TermSet: IterableTermSet<usize>,
{
    for entry in glob::glob("benchmarks/*/bench.bc").unwrap() {
        let entry = entry.expect("Error in path");
        let module = Module::from_bc_path(&entry).expect("Error parsing bc file");
        let bench_name = format!("{} {name}", entry.display());
        c.bench_function(&bench_name, |b| {
            b.iter(|| black_box(PointsToAnalysis::run::<GenericSolver<_, S>>(&module)));
        });
    }
}

fn hash(c: &mut Criterion) {
    bench_template::<BasicHashSolver>("Hash", c);
}

fn bit_vec(c: &mut Criterion) {
    bench_template::<BasicBitVecSolver>("BitVec", c);
}

fn wave_prop(c: &mut Criterion) {
    bench_template::<WavePropagationSolver>("WaveProp", c);
}

fn roaring(c: &mut Criterion) {
    bench_template::<RoaringSolver>("Roaring", c);
}

criterion_group!(benches, hash, bit_vec, wave_prop, roaring);
criterion_main!(benches);
