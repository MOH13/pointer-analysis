#!/bin/bash
mkdir llvmtemp 1>/dev/null 2>&1
cd llvmtemp && rm ./*
for file in "$@"; do
    clang -c -fno-discard-value-names -emit-llvm "../$file" -S
done