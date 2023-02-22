#!/bin/bash

clang -S -fno-discard-value-names -emit-llvm $1 -o source.ll
