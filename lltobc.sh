#!/bin/bash
if [ "$2" = "" ]
then
    echo "Please provide two arguments: Input file and output file"
    exit 1
fi

llvm-as-14 $1 -o $2