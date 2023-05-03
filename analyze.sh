#!/bin/bash
mkdir llvmtemp 1>/dev/null 2>&1
rm llvmtemp/* 1>/dev/null 2>&1
for file in "$@"; do
    ./ctobc.sh $file "llvmtemp/$(basename -s .c $file).bc"
done
llvm-link-14 llvmtemp/*.bc -o llvmtemp/linked.ll -S
llvm-link-14 llvmtemp/*.bc -o llvmtemp/linked.bc

cargo run --release -- --solver hash ./llvmtemp/linked.bc