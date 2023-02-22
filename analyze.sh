#!/bin/bash

clang -c -fno-discard-value-names -emit-llvm $1 -o /tmp/source.bc
cargo run --release /tmp/source.bc
