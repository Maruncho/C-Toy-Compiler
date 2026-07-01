# Nora C Compiler

A **pedagogical C compiler** targeting x86-64 Linux, written in OCaml. Implements a substantial subset of C99 (~80%) by following Nora Sandler's *Writing a C Compiler*. Designed for clarity over optimization — each pipeline stage is independently inspectable.

## Quick Start

```bash
opam install . --deps-only
dune build --profile release
./example_driver.sh example.c -o example && ./example
```

### Prerequisites

- [OCaml](https://ocaml.org/) (with `opam`)
- GCC (for preprocessing, assembling, linking)
- Linux x86-64

### Usage

```
./driver.sh file1.c [file2.c ...] -o output
```

Flags: `-c` (compile only to `.o`), `-l<lib>` (link libraries), `--lex|--parse|--tacky|--codegen` (debug).

## Supported C Features

| Category | Features |
|---|---|
| **Types** | `char`, `signed char`, `unsigned char`, `int`, `unsigned int`, `long`, `unsigned long`, `double`, pointers, arrays, structs, unions, functions, `void` |
| **Statements** | `if`/`else`, `while`, `do`/`while`, `for`, `switch`/`case`/`default`, `break`, `continue`, `goto`, labeled statements, `return` |
| **Operators** | All arithmetic (`+` `-` `*` `/` `%`), bitwise (`&` `|` `^` `~` `<<` `>>`), logical (`&&` `||` `!`), comparison (`==` `!=` `<` `>` `<=` `>=`), assignment (`=` `+=` `-=` etc.), increment/decrement (prefix/postfix), `&` `*` `.` `->`, `[]`, `sizeof`, ternary (`?:`) |
| **Storage** | `static`, `extern`, `typedef` |
| **Literals** | Decimal, hex, octal, unsigned/U/L suffixes, floating-point, char, string |
| **Constants** | Full constant expression folding (in `const.ml`) |
| **Struct/Union** | Nested, recursive, member alignment/padding per System V ABI |

### Notable Omissions

| Category | Missing |
|---|---|
| **Types** | `_Bool`, `float`, `short`, `long long`, `long double`, `enum`, `_Complex`, `_Atomic` |
| **Qualifiers** | `const`, `volatile`, `restrict` |
| **Storage** | `register`, `auto`, `_Thread_local` |
| **Features** | VLAs, flexible array members, compound literals `(type){...}`, designated initializers `{.x=v}`/`[i]=v`, union initializers, comma operator, `_Alignof`, `inline` |
| **Functions** | Variadic function *definitions* (declarations and calls work) |

## Notable Capabilities

| Category | Details |
|---|---|
| **NaN handling** | All floating comparisons correct for unordered operands — `==` returns false for NaN, `!=` returns true; `JumpIfZero`/`JumpIfNotZero` handle NaN via `PF` flag |
| **IEEE 754 edge cases** | Infinity, negative zero, and subnormal numbers compare and compute correctly through arithmetic, logical, and comparison operators |
| **Short-circuit semantics** | Side effects in `&&`/`||` conditions only execute when specified; `0 && (1 / 0)` does not trap; ternary condition short-circuits the non-selected branch |
| **ABI compliance** | Full System V AMD64 classification: structs passed/returned via SINT, SXMM, SINTnINT, SXMMnXMM, hybrid (SINTnXMM, SXMMnINT), and by-memory (SMEM ≥16 bytes); stack alignment correct for even/odd argument counts; `%rdx`/`%rcx` preserved across `div`/`idiv`/shifts; page-boundary struct reads don't segfault |
| **Scratch registers** | Fixup uses `%r10`, `%r11`, `%xmm14`, `%xmm15` as temporaries — all caller-saved, no prologue/epilogue overhead |
| **Pointer arithmetic** | `ptr ± int` with automatic scaling, `ptr - ptr` producing element count, multi-dimensional pointer diff, array-of-pointers-to-arrays subscripting |
| **Multi-level indirection** | Read/write `***ptr` chains through arbitrary pointer depths, including through struct members and across re-assignment |
| **Recursion** | Self-calling functions with branching (fibonacci) — stack frame correctly grows per call |
| **Static locals** | Retain state across calls with proper block-scoping (same name in different scopes resolve independently) |
| **Scope & shadowing** | Variables shadowed in inner blocks restore outer values on exit; parameters shadow functions; functions shadow variables |
| **Goto** | Forward references, shared label names across functions, labels in compound/if/loop/switch bodies |
| **sizeof** | Works on types, expressions, arrays (including incomplete), derived types, structs/unions; operand never evaluated |
| **char/string initialization** | `char a[] = "hello"` unpacks char-by-char with length checking; null-termination preserved |
| **Tentative definitions** | `int x;` at file scope treated as a definition, not just a declaration |
| **Compound assignment** | All `op=` forms including `<<=`, `>>=`, `&=`, `|=`, `^=` on integral types |
| **Function pointers** | Direct `call name` and indirect `call *operand` through pointers-to-functions |

## Pipeline

```
Source ──► Lexer ──► Parser ──► Semantics ──► Tacky IR ──► Assembly ──► Register Alloc ──► Fixup ──► .s
            .i        AST       goto/bc/switch   3-addr       pseudo-asm    stack→rbp       x86-64      file
```

### Debug Flags

Pass any flag to stop the pipeline at a specific stage:

| Flag | Stage | Output |
|---|---|---|
| `--lex` | After lexing | (exits cleanly) |
| `--parse` | After parsing | AST pretty-print |
| `--tacky` | After IR gen | Tacky IR dump |
| `--codegen` | After assembly | Assembly text |

## Project Structure

| File | Role | Lines |
|---|---|---|
| `bin/lexer.ml` | Tokenizer (regex-based) | 409 |
| `bin/parser.ml` | Recursive descent parser + type checker | 1698 |
| `bin/parserDeclarator.ml` | C declarator parsing (pointer/array/function) | 272 |
| `bin/ast.ml` | AST types + type utilities (size, alignment, string ops) | 694 |
| `bin/const.ml` | Constant expression evaluator | 282 |
| `bin/environment.ml` | Symbol table (scoped env + global env) | 275 |
| `bin/semantGoto.ml` | Goto label validation + resolution | 118 |
| `bin/semantBreakContinue.ml` | Break/continue binding to loop/switch | 56 |
| `bin/semantSwitch.ml` | Switch case uniqueness validation | 87 |
| `bin/tacky.ml` | Tacky IR types + pretty-printing | 240 |
| `bin/tackify.ml` | AST → Tacky IR lowering | 1019 |
| `bin/assemble.ml` | Tacky → assembly + register alloc + fixup | 1392 |
| `bin/asmt.ml` | Assembly IR types + text emission | 356 |
| `bin/label.ml` | Label generation (code, strings, floats) | 34 |
| `bin/temp.ml` | Temporary variable generation | 6 |
| `bin/log.ml` | Warning logger | 3 |
| `bin/main.ml` | Pipeline orchestrator | 44 |
| `driver.sh` / `example_driver.sh` | Compiler driver scripts | 113 each |

## Testing

Tests are from Nora Sandler's official test suite. Clone it separately and run:

```bash
git clone https://github.com/nlsandler/writing-a-c-compiler-tests.git
cd writing-a-c-compiler-tests
./test_compiler --chapter 1-20 [options]
```

## Acknowledgements

- **[Nora Sandler](https://norasandler.com/)** — author of *Writing a C Compiler*, the book that guided this entire project
- The book's [test suite](https://github.com/nlsandler/writing-a-c-compiler-tests)

## License

MIT — see LICENSE file.
