#!/usr/bin/env bash

file=""
arg=""

if [[ $1 == "" ]]; then
    echo "File expected"; exit 1;
elif [[ $2 == "" ]] && [[ "${1:0:2}" == "--" ]]; then
    echo "File expected"; exit 1;
elif [[ $2 == "" ]]; then
    file=$1
elif [[ "${1:0:2}" == "--" ]]; then
    arg=$1;
    file=$2;
else
    file=$1;
    arg=$2;
fi

if [[ "${file: -2}" != ".c" ]]; then
    echo "File must be .c"; exit 1;
fi

fileName="${file:0: -2}"

gcc -E -P $file -o "$fileName.i"

result="$?"
if [[ $result != "0" ]]; then
    exit $result
fi

~/dev/noraCompilerC/compiler/_build/default/bin/main.exe "$fileName.i" "$arg"
result="$?"

rm "$fileName.i"

if [[ $arg != "" ]]; then
    exit $result
fi

if [[ $result != "0" ]]; then
    exit $result
fi

gcc "$fileName.s" -o $fileName

rm "$fileName.s"
