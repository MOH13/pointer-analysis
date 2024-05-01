use llvm_ir::Module;
use pointer_analysis::analysis::{Cell, Config, PointsToAnalysis};
use pointer_analysis::solver::{
    BasicHashSolver, BasicRoaringSolver, BasicSharedBitVecSolver, CallStringSelector,
    ContextInsensitiveSelector, ContextInsensitiveSolver, ContextSelector, ContextSensitiveSolver,
    HashContextWavePropagationSolver, RoaringContextWavePropagationSolver,
    SharedBitVecContextWavePropagationSolver, Solver,
};

use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_template<S, C>(name: &str, solver: S, context_selector: C, c: &mut Criterion)
where
    for<'a> S: ContextSensitiveSolver<Cell<'a>, C>,
    C: ContextSelector + Clone,
{
    let solver = solver.as_demand_driven();
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
                    vec![],
                    &Config::default(),
                ))
            });
        });
    }
}

fn hash(c: &mut Criterion) {
    let solver = BasicHashSolver::new().as_context_sensitive().as_generic();
    bench_template("HashWorklist", solver, ContextInsensitiveSelector, c);
}

fn roaring(c: &mut Criterion) {
    let solver = BasicRoaringSolver::new()
        .as_context_sensitive()
        .as_generic();
    bench_template("RoaringWorklist", solver, ContextInsensitiveSelector, c);
}

fn shared_bitvec(c: &mut Criterion) {
    let solver = BasicSharedBitVecSolver::new()
        .as_context_sensitive()
        .as_generic();
    bench_template(
        "SharedBitVecWorklist",
        solver,
        ContextInsensitiveSelector,
        c,
    );
}

fn hash_wave_prop(c: &mut Criterion) {
    let solver = HashContextWavePropagationSolver::new();
    bench_template("HashWaveProp", solver, ContextInsensitiveSelector, c);
}

fn roaring_wave_prop(c: &mut Criterion) {
    let solver = RoaringContextWavePropagationSolver::new();
    bench_template("RoaringWaveProp", solver, ContextInsensitiveSelector, c);
}

fn shared_bitvec_wave_prop(c: &mut Criterion) {
    let solver = SharedBitVecContextWavePropagationSolver::new();
    bench_template(
        "SharedBitVecWaveProp",
        solver,
        ContextInsensitiveSelector,
        c,
    );
}

fn context(c: &mut Criterion) {
    let solver = SharedBitVecContextWavePropagationSolver::new();
    bench_template("ContextTest", solver, CallStringSelector::<1>::new(), c);
}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(10);
    targets = hash,
    roaring,
    shared_bitvec,
    hash_wave_prop,
    roaring_wave_prop,
    shared_bitvec_wave_prop,
    context,
}
criterion_main!(benches);
