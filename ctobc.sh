#!/bin/bash
if [ "$2" = "" ]
then
    echo "Please provide two arguments: Input file and output file"
    exit 1
fi

clang -c -fno-discard-value-names -emit-llvm $1 -o $2