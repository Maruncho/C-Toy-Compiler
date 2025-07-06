# C-Compiler
Hobby project, guided by the book "Writing a C Compiler" by Nora Sandler.
Compiles C source code to x86-64 assembly on Linux. Other compilation targets are currently not considered, because that's extra work that goes outside of the scope of what I wanna do.

## Compiler Pipeline:
Lexer(lexer.ml) -> Parser(parser.ml) -> Other Semantic Analysis(semant*.ml) -> IR named Tacky(tackify.ml) -> High-level Assembly(assemble.ml) -> Do some clean-up and optimization passes(assemble.ml) -> to_string()

## Compiler Driver Pipeline:
C Source code => Run gcc preprocessor (.c -> .i) => Run this compiler (.i -> .s) => Run gcc assembler and linker (.s -> \<ELF Executable\>)

## How to run:
1. Install opam and ocaml if you haven't already.
2. ```
   git clone https://github.com/Maruncho/C-Toy-Compiler.git # check out the repo
   cd C-Toy-Compiler
   opam install . --deps-only # install dependencies through opam
   dune build [--profile release] # build it
   ```

## Usage:
./example_driver.sh (.c files)... -o (executable name)

## Misc:
- The driver accepts --* arguments, but that's for debugging and running the tests provided by the book.
- The driver accepts the -c flag, which behaves exactly like gcc.
