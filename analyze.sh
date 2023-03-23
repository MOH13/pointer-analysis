#!/bin/bash
cd llvmtemp
rm ./*
for file in "$@"; do
    clang -c -fno-discard-value-names -emit-llvm "../$file"
done

llvm-link-14 ./*.bc -o linked.ll -S
llvm-link-14 ./*.bc -o linked.bc

cd ..

cargo run --release ./llvmtemp/linked.bc