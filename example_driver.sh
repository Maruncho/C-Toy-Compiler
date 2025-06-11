#!/usr/bin/env bash

files=()
gcc_args=""
o_arg=""
long_flag=""

# Manual command-line parsing
while [[ $# -gt 0 ]]; do
    case "$1" in
        -c)
            gcc_args="-c"
            shift
            ;;
        -o)
            if [[ -z "$2" || "$2" == -* ]]; then
                echo "Error: -o requires an argument." >&2
                exit 1
            fi
            o_arg="$2"
            shift 2
            ;;
        --*)
            if [[ -n "$long_flag" ]]; then
                echo "Error: Only one long flag allowed, but got multiple: '$long_flag' and '$1'" >&2
                exit 1
            fi
            long_flag="$1"
            shift
            ;;
        -*)
            echo "Error: Unknown option: $1" >&2
            exit 1
            ;;
        *)
            if [[ "${1: -2}" != ".c" ]]; then
                echo "File must be .c, but got ${1}" >&2
                exit 1
            fi
            files+=("$1")
            shift
            ;;
    esac
done

# Validation
if [[ ${#files[@]} -lt 1 ]]; then
    echo "File expected" >&2
    exit 1
fi

if [[ -n "$gcc_args" && -n "$o_arg" ]]; then
    echo "Error: -o cannot be used when -c is present." >&2
    exit 1
fi

# If -c not present, no -o provided, and exactly one file => set o_arg to filename without .c
if [[ -z "$gcc_args" && -z "$o_arg" && ${#files[@]} -eq 1 ]]; then
    o_arg="${files[0]%.c}"
fi

# Preprocessing
for file in "${files[@]}"; do
    gcc -E -P "$file" -o "${file%.c}.i"
    if [[ $? -ne 0 ]]; then
        exit 1
    fi
done

# Compile with your custom compiler
result=0
for file in "${files[@]}"; do
    ir_file="${file%.c}.i"
    ./_build/default/bin/main.exe "$ir_file" $long_flag
    result=$(( $? + result ))
    rm "$ir_file"
done

# If a long flag was present, stop here
if [[ -n "$long_flag" ]]; then
    exit $result
fi

# Early exit if compiler failed
if [[ $result -ne 0 ]]; then
    exit $result
fi

# Assembly output
s_files=()
for file in "${files[@]}"; do
    s_files+=("${file%.c}.s")
done

# Compile assembly with gcc
if [[ -n "$o_arg" ]]; then
    gcc "${s_files[@]}" -o "$o_arg"
else
    gcc "$gcc_args" "${s_files[@]}"
fi

# Clean up .s files
rm -f "${s_files[@]}"
