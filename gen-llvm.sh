#!/bin/bash
mkdir llvmtemp 1>/dev/null 2>&1
rm llvmtemp/* 1>/dev/null 2>&1
for file in "$@"; do
    clang -c -fno-discard-value-names -emit-llvm $file -S -o "llvmtemp/$(basename -s .c $file).ll"
done