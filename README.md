# C-Compiler
Hobby project, guided by the book "Writing a C Compiler" by Nora Sandler.
Compiler C code to x86-64 assembly on Linux. Other compilation targets are currently not considered, because that's extra work that is not compiler study related really.

## Pipeline:
Lexer(lexer.ml) -> Parser(parser.ml) -> Other Semantic Analysis(semant*.ml) -> IR named Tacky(tackify.ml) -> High-level Assembly(assemble.ml) -> Do some clean-up and optimization passes(assemble.ml) -> to_string()

## Usage:
./driver.sh (.c files)... -o (executable name)
