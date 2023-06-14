# pointer-analysis

Authors: Lasse Overgaard Møldrup and Mads Overgård Henningsen

## Usage

This tool analyses LLVM `.bc` files:

```
pointer-analysis <path/to/bc_file.bc>
```

Use `--help` for more options.

We recommend using the VS Code Dev Container included in the project, since it has the required dependencies and configurations.

### Analyze C-files

A shell-script `analyze.sh` can help you analyze C code. It first compiles and links the code using Clang and LLVM before running the analysis on the resulting bytecode.

Run:
```
./analyze.sh <path/to/c_file1.c> <path/to/c_file2.c>...
```

Your shell might allow you to use a glob-expression instead of writing individual files:

```
./analyze.sh <path/to/cfiles/*.c>
```

### Configure Makefiles to generate .bc files

See [WLLVM documentation](https://github.com/travitch/whole-program-llvm#building-a-bitcode-archive-then-extracting-the-bitcode). When a `.bc` file is obtained, analyze as usual.

### Benchmarking

This tool provides several algorithms for pointer analysis. In order to benchmark the different algorithms, place the programs to be analyzed in the `benchmarks` folder (or create it, if it doesn't exist). The program must be compiled to llvm bytecode and have the name `bench.bc` in the root of the program directory.
As an example one could create `benchmarks/vim/bench.bc`.

To run the benchmarks, simply run
```
cargo bench
```
Or if you only want to test certain programs/solvers, you can specify with e.g.
```
cargo bench Hash
```
which will run only the basic hash solver.