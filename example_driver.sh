#!/usr/bin/env bash

files=()
c_arg=""
lib_args=""
o_arg=""
o_arg_default=""
long_flag=""

# Manual command-line parsing
while [[ $# -gt 0 ]]; do
    case "$1" in
        -c)
            c_arg="-c"
            shift
            ;;
        -l*)
            lib_args="${lib_args} $1"
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

if [[ -n "$c_arg" && -n "$o_arg" && ${#files[@]} -gt 1 ]]; then
    echo "Error: -o cannot be used with multiple files when -c is present." >&2
    exit 1
fi

# If no -o provided, and exactly one file => set o_arg_default
if [[ -z "$o_arg" && ${#files[@]} -eq 1 ]]; then
    if [[ $c_arg = "-c" ]]; then
        o_arg_default="${files[0]%.*}.o"
    else
        o_arg_default="${files[0]%.*}"
    fi
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
    gcc $c_arg "${s_files[@]}" -o "$o_arg" $lib_args
else
    gcc $c_arg "${s_files[@]}" -o "$o_arg_default" $lib_args
fi

# Clean up .s files
rm -f "${s_files[@]}"
