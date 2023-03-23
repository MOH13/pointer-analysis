#!/bin/bash
cd llvmtemp
rm ./*
for file in "$@"; do
    clang -c -fno-discard-value-names -emit-llvm "../$file" -S
done