# Architecture

## Pipeline Walkthrough

The compiler transforms C source to x86-64 assembly through 8 stages. Here's what happens at each stage for a tiny C program:

```c
int main(void) {
    int x = 2 + 3;
    return x;
}
```

```
Source ──► Lexer ──► Parser ──► 3x Semant ──► Tacky ──► Assembly ──► RegAlloc ──► Fixup ──► .s
  .i       tokens     AST      goto/bc/switch   3-addr    pseudo-asm   stack→%rbp  x86-64     file
```

### Stage 1: Lexer (`lexer.ml`)

Regex-based tokenizer. Produces a token stream:

```
INT ID("main") LPAREN VOID RPAREN LBRACE INT ID("x") ASSIGN INT32_LIT(2) PLUS INT32_LIT(3) SEMICOLON RETURN ID("x") SEMICOLON RBRACE EOF
```

Token types: keywords (`INT`, `VOID`, `RETURN`, `IF`, ...), operators (`PLUS`, `MINUS`, `ASTERISK`, `ARROW`, `LSHIFT`, ...), literals (`INT32_LIT`, `INT64_LIT`, `DOUBLE_LIT`, `STRING_LIT`, `CHAR_LIT`), and structural (`LPAREN`, `LBRACE`, `SEMICOLON`, ...).

### Stage 2: Parser (`parser.ml`)

Recursive descent parser with **precedence climbing** for expressions. Produces a typed AST:

```
Program
  FunDecl("main" -> int) {
    VarDecl("x", int)
    Return(Var("x"))
  }
```

Key responsibilities:
- **Expression parsing**: Uses binding power table (`get_bp`) for Pratt-style precedence climbing. Handles all C precedence levels from comma (lowest) through postfix (highest).
- **Type checking**: Every expression node is annotated with its resolved `data_type`. Ensures operand compatibility, performs implicit integer promotions, and inserts cast nodes where needed.
- **Declarator parsing**: Delegated to `parserDeclarator.ml`.

### Stage 3a: Goto Semantics (`semantGoto.ml`)

Two-pass over each function body:
1. **Label scanning**: Collects all `Label` statements, assigns unique internal labels, and builds a label→label mapping.
2. **Goto resolution**: Replaces each `Goto` with the resolved label. Reports error for undeclared labels.

Labels within compound statements, `if`/`else` branches, and loop bodies are all scanned recursively. Duplicate labels are rejected.

### Stage 3b: Break/Continue Semantics (`semantBreakContinue.ml`)

Threads `(continue_label, break_label)` pairs through compound statements. Each `While`/`DoWhile`/`For`/`Switch` generates fresh labels and binds `Break`/`Continue` statements within their body to those labels. Reports error for orphaned `break`/`continue`.

### Stage 3c: Switch Semantics (`semantSwitch.ml`)

Validates switch statements:
- Checks that `case` and `default` appear only inside a `switch`
- Rejects duplicate `case` values and duplicate `default` labels
- Uses a `Set` of `Const.result` for O(n log n) duplicate detection

### Stage 4: Tacky IR Generation (`tackify.ml`)

Lowers typed AST to **three-address code** in Tacky IR. The `x = 2 + 3` example becomes:

```
Copy($int32 2, %tmp.0)
Copy($int32 3, %tmp.1)
Binary(ADD, %tmp.0, %tmp.1, %tmp.2)
Copy(%tmp.2, %x)
```

Key design decisions:

- **Lvalue conversion**: `parseExpr` returns an `lval` type — either `PlainOperand`, `DereferencedPointer`, or `SubObject`. The caller decides whether to load the value or take the address.
- **Postfix scheduling**: The `typed_expr_sp` type pairs an expression with a "postfix" list of statements. Expressions like `a++ + b` decompose the side-effect (`a++`) into a postfix statement, evaluated after the condition but before the then/else branch.
- **Struct member access**: `Dot` and `Arrow` use pre-computed byte offsets (from `struct_data`), producing `SubObject(oper, offset, type)` lvals or `CopyFromOffset`/`CopyToOffset` instructions.
- **Short-circuit evaluation**: `&&` and `||` are lowered to explicit `JumpIfZero`/`JumpIfNotZero` with labels, matching C's short-circuit semantics.
- **Ternary**: Lowered to `JumpIfZero`/`Jump` with copy-to-result.
- **String constants**: Deduplicated via `label.ml`'s `Label.String` map, stored as `.rodata` entries.
- **Float constants**: Same deduplication pattern — NaN-correct comparisons with `JumpIfZero` use special handling for `unordered` results.
- **Compound initialisation**: Structs and arrays use `DeclCompound` metadata + `CopyToOffset` sequences.
- **Static variables**: Collected during tackification, emitted as `StaticVariable` toplevels. Tentative definitions get `ZeroInit`.

### Stage 5: Assembly Generation (`assemble.ml`)

Translates Tacky IR into a **pseudo-assembly** IR using virtual registers (`Pseudo`):

```
Mov(l $2, %tmp.0)
Mov(l $3, %tmp.1)
Mov(l %tmp.1, %tmp.0)    // after constant folding of Mov + Binary(Add)
Add(l %tmp.1, %tmp.0)
```

Major subsystems within this stage:

#### System V AMD64 ABI Classification

Handles parameter passing and return values for all types including **structs larger than 16 bytes** (`SMEM` — passed in memory with hidden pointer). The `parseStructClass` function in `tackify.ml` implements the classification algorithm:

- Flattens nested structs and arrays, classifies each eightbyte individually
- Each eightbyte: `INTEGER` (general-purpose), `SSE` (XMM), `MEMORY` (stack), or `NO_CLASS`
- The eightbyte pair is combined into one of 7 final classes: `SINT`, `SXMM`, `SMEM`, `SINTnINT`, `SINTnXMM`, `SXMMnINT`, `SXMMnXMM`
- Parameters exceeding 6 integer / 8 XMM registers spill to stack

`classify_parameters` in `assemble.ml` maps each classified Tacky type to actual registers (`RDI`, `RSI`, ... for integer; `XMM0`–`XMM7` for SSE) or `%rbp`-relative stack locations.

`classify_return` handles return values:
- SMEM: hidden pointer in `%rdi`, return via `%rax` + memcpy
- SINT (≤8 bytes): return in `%rax`
- SXMM (≤8 bytes): return in `%xmm0`
- SINTnINT (>8 bytes): return in `%rax` + `%rdx`
- SXMMnXMM (>8 bytes): return in `%xmm0` + `%xmm1`
- SINTnXMM (first eightbyte integer, second SSE): return in `%rax` + `%xmm0`
- SXMMnINT (first eightbyte SSE, second integer): return in `%xmm0` + `%rax`

#### Call Instruction Lowering

`Tac.Call` expands to:
1. **Parameter setup**: Move int args into `%rdi`–`%r9`, float args into `%xmm0`–`%xmm7`, spill rest to stack. Uses `Push` for stack args (with `AllocateStack` for structs). Adds 16-byte alignment padding as needed.
2. **Variadic protocol**: Set `%al` = number of XMM registers used.
3. **Call**: Direct (`call <name>`) or indirect (`call *<operand>`).
4. **Return value**: Copies from `%rax`/`%rdx`/`%xmm0`/`%xmm1` back to virtual register. For SMEM returns, the hidden pointer was passed in `%rdi`.

#### Float NaN Handling

All floating-point comparisons are NaN-correct:
- `JumpIfZero` on float: compares value against itself; if `PF` (parity, meaning NaN), skips the jump.
- `JumpIfNotZero` on float: jumps if `PF` (NaN) or value ≠ 0.
- Conditional `SetCC`/`Cmov` for float `==` uses `cmovnp` to handle unordered == false.
- `!=` on float: sets `PF` first, then `cmovnp` for the actual comparands.

```
// float == comparison
xorq    %r11, %r11
xorq    %r10, %r10
comisd  %src1, %src2
setnp   %r10b
cmove   %r10, %r11
movq    %r11, %dst
```

The NaN-correct approach also handles all IEEE 754 special values correctly: infinity, negative zero, and subnormals compare and compute as the standard requires. Negative zero is false in controlling expressions and short-circuits `&&`; `1.0 / (-0.0)` produces negative infinity; subnormal numbers are not flushed to zero.

#### Additional Edge Cases

- **Page-boundary safety**: Return value copies and struct/array moves never read past the end of the source object. This is verified by tests that place objects at page boundaries where the next page is unmapped.
- **Stack clobber protection**: Return value stores do not overwrite other live stack slots. Verified by placing sentinel bytes on the stack, calling a struct-returning function, and validating the sentinels afterward — across all 7 classification classes.
- **Scratch register discipline**: Fixup uses `%r10`, `%r11`, `%xmm14`, `%xmm15` as temporaries. All are caller-saved — no prologue/epilogue modifications needed. The compiler avoids `%rdx`/`%rcx` for scratch usage so `div`/`idiv`/`shl`/`shr`/`sal`/`sar` operations don't clobber argument registers.

#### Byte Array (Struct/Array) Copies

Structs ≤8 bytes are moved as `QuadWord`. Larger structs use `generateByteArrayCopy` which issues aligned `movq`/`movl`/`movw`/`movb` sequences. `generateByteArrayCopyToReg` / `generateByteArrayCopyFromReg` handle register transfers with proper endianness via shifts.

### Stage 5b: Register Allocation (`replacePseudos`)

A **stack-based allocator** — every virtual register (`Pseudo`) becomes an `%rbp`-relative stack slot. No register coalescing, no graph coloring:

1. **Count pass**: Scans all instructions to count distinct `Pseudo` IDs per alignment class (16-byte, 8-byte, 4-byte, 2-byte, 1-byte).
2. **Offset assignment**: Starting from `%rbp`-0 (or `%rbp`-8 for SMEM return), allocates descending offsets. Each pseudo gets a unique `Memory(RBP, -offset, None, None)`.
3. **Replacement**: Rewrites every `Pseudo(id)` → `Memory(RBP, -offset, None, None)`. `PseudoMem(id, sub_off)` → `Memory(RBP, -offset+sub_off, None, None)`.

`DeclCompound` meta-instructions (for struct/array locals) are translated to stack slots and then removed (replaced with `Nop true` which the fixup stage eliminates).

### Stage 5c: Instruction Fixup (`fixUp`)

Resolves x86-64 instruction encoding constraints. Two passes:

**Pass 1 (`fixErroneous`)**:
- Removes dead `Jmp lbl; Label lbl:` sequences and `Nop true`
- Converts `xor mem,mem` to `mov $0, mem` (faster)
- SSE binary ops can't have memory destination ⇒ spill to `%xmm15`
- `imul` can't have memory destination ⇒ spill to `%r11`
- Shift count must be imm or `%cl` ⇒ move non-imm counts to `%rcx`
- `cmp` with float memory ⇒ load `%xmm15`
- `cvttsx2si`/`cvtsi2sx` can't write to memory ⇒ spill to `%r11`/`%xmm15`
- Double `mov` can't be mem→mem ⇒ route through `%xmm14`
- General `mov` can't be mem→mem ⇒ route through `%r10`
- General `Binary`/`Cmp` can't be mem→mem ⇒ route through `%r10`
- `Lea` can't write to memory ⇒ route through `%r11`
- `Push` can't take XMM ⇒ sub `%rsp` + mov
- `Movsx`/`Movzx` can't take imm source ⇒ route through `%r10`
- `Cmov` can't take imm source ⇒ route through `%r10`
- `Cmp` can't have imm destination ⇒ route through `%r11`
- `[I]div` can't take imm ⇒ route through `%r10`

**Pass 2 (`fixErroneousAgain`)**:
- `Movsx`/`Movzx` can't write to memory ⇒ route through `%r11`
- `movzlq` doesn't exist (uses `movl` to zero-extend)
- `xorpd` with memory source ⇒ load `%xmm14` first
- 64-bit immediates in `Binary`/`Cmp`/`Push`/`Mov` exceeding 32 bits ⇒ load to `%r10`
- `Mov` into `%eax` zero-extends (mov imm32 to mem uses signed 32-bit move)
- `Cvtsi2sx` can't take imm ⇒ route through `%r10`

**Peephole optimizations** (`combineSequentialMoves`):
- Adjacent byte stores to aligned offsets → single word store
- Adjacent word stores to aligned offsets → single longword store
- Adjacent longword stores to aligned offsets → single quadword store

### Stage 6: Assembly Text Emission (`asmt.ml`)

The assembly IR is written to a `.s` file. `string_of_asmt` produces:
- `.section .rodata` (read-only data: float constants, string literals)
- `.bss` (zero-initialized static variables)
- `.data` (initialized static variables)
- `.text` (function code with push/mov %rbp prologue, ret epilogue)
- `.section .note.GNU-stack` (non-executable stack marker)

### Final Stage: Driver (`driver.sh`)

GCC wrapper: `gcc -E -P` (preprocess) → `main.exe` (compile) → `gcc` (assemble + link).

## AST Design

### Typed Expressions (`typed_expr`)

Every expression carries its `data_type` as a tag:

```ocaml
type typed_expr = data_type * expr
```

This means type information is always available without a separate symbol table lookup — the parser embeds it directly into the tree. The type checking and implicit conversion logic is fused with parsing.

### Lvalues (`lval` in `tackify.ml`)

Rather than load every expression to a value immediately, `parseExpr` returns an `lval`:

```ocaml
type lval =
  | PlainOperand of operand          (* already a value / address *)
  | DereferencedPointer of operand   (* *expr — holds pointer *)
  | SubObject of operand * int64 * typ  (* struct.field — holds base + offset *)
```

The caller chooses the conversion:
- `parseExpr_lval_convert` — always produces a value (loads from memory via `Load` or `CopyFromOffset`)
- Expression operands that need addresses (like `AddressOf`) can pattern-match on the lval to emit `GetAddress` or `AddPtr` without loading

### Postfix Scheduling

C's side-effect sequencing (e.g., `i++` in `a[i++] = b`) is handled via the `postfix` type:

```ocaml
type postfix = stmt list          (* deferred side-effect statements *)
type typed_expr_sp = typed_expr * postfix
```

When parsing `a++` inside a larger expression, the increment is decomposed into a statement appended to a postfix list. The postfix is emitted at the next sequencing point (end of condition, before else branch, etc.).

## Parsing C Declarators (`parserDeclarator.ml`)

C declarators are parsed as a chain of pointer/array/function modifiers applied to a base type:

```
int *f(int)[] → base=int, chain=[Pointer, Function([int]), Array([])]
```

The parsing algorithm:
1. Parse optional `*` pointers (left-to-right)
2. Parse the "core" declarator (identifier or nested `(...)`)
3. Parse postfix modifiers: `[...]` (array), `(...)` (function)
4. Apply the chain to the base type, wrapping inside-out

**Abstract declarators** (in parameters, casts) follow the same rules but omit the identifier.

### Storage Class Specifiers

Handled in `parseDeclaration`. `static`, `extern`, and `typedef` are parsed and annotated on `var_decl`/`fun_decl` nodes. `typedef` entries are stored in the environment for subsequent parsing.

## Struct/Union Layout (`parser.ml`)

Layout computation in `fixOffsets` follows the System V AMD64 ABI:

```
offset = 0
for each member:
    member_align = alignment(member_type)
    offset = round_up(offset, member_align)
    member.offset = offset
    offset += member.size
struct.align = max(member_alignments)
struct.size = round_up(offset, struct.align)
```

- `alignment` respects the ABI: scalars align to their size, arrays to their element alignment, structs to their largest member alignment.
- `aligned_size` for arrays rounds up to alignment (handles over-aligned types).
- Unions: `size = max(member sizes)`, `align = max(member alignments)`, all offsets are 0.

## Tacky IR

Tacky is the compiler's **three-address code** intermediate representation. Operands are:

```ocaml
type operand =
  | Constant of constant        (* immediate values, strings, float labels *)
  | Var of string * typ         (* local virtual variables *)
  | StaticVar of string * typ   (* global/static variables *)
```

### Tacky Types

```ocaml
type typ =
  | Int8 of bool   | Int32 of bool   | Int64 of bool   (* bool = signed *)
  | Float64
  | Ptr of typ
  | ArrObj of typ * int64 * int64    (* element type, length, alignment *)
  | Struct of int64 * int64 * struct_class  (* size, align, ABI class *)
  | Function of string
  | Void
```

### Instruction Set

| Instruction | Meaning |
|---|---|
| `Copy(src, dst)` | `dst = src` |
| `Load(src, dst)` | `dst = *src` (pointer dereference) |
| `Store(src, dst)` | `*dst = src` |
| `GetAddress(src, dst)` | `dst = &src` |
| `AddPtr(ptr, idx, scale, dst)` | `dst = ptr + idx * scale` |
| `Unary(op, src, dst)` | `dst = op src` (negate, complement, not, incr, decr) |
| `Binary(op, s1, s2, dst)` | `dst = s1 op s2` |
| `SignExtend(s, d)` / `ZeroExtend(s, d)` | Integer type widening |
| `Truncate(s, d)` | Integer type narrowing |
| `FloatToInt(s, d)` / `IntToFloat(s, d)` | Float-integer conversion |
| `CopyToOffset(src, base, off)` | `*(base + off) = src` (struct member write) |
| `CopyFromOffset(base, off, dst)` | `dst = *(base + off)` (struct member read) |
| `DeclCompound(id, align, count)` | Stack allocation metadata |
| `Call(callee, args, dst, variadic)` | Function call |
| `Return(op)` | Return from function |
| `Jump(lbl)` | Unconditional branch |
| `JumpIfZero(val, lbl)` | Branch if val == 0 |
| `JumpIfNotZero(val, lbl)` | Branch if val != 0 |
| `Label(lbl)` | Label target |

### Memory Model

All virtual variables live in the Tacky IR's infinite register file. The stack-based allocator in `assemble.ml` maps them to `%rbp`-relative memory. There is no spilling — every variable has a dedicated slot for its lifetime.

## Control Flow Lowering

| C Construct | Tacky Pattern |
|---|---|
| `if (c) t` | `JumpIfZero c, end; t; Label end` |
| `if (c) t else e` | `JumpIfZero c, else; t; Jump end; Label else; e; Label end` |
| `while (c) b` | `Label cont; JumpIfZero c, brk; b; Jump cont; Label brk` |
| `do b while (c)` | `Label start; b; Label cont; JumpIfNotZero c, start; Label brk` |
| `for (i; c; p) b` | `i; Label start; JumpIfZero c, brk; b; Label cont; p; Jump start; Label brk` |
| `switch(c) { case v: ... }` | Linear `==` chain with `JumpIfNotZero` per case + `Jump default` |
| `a && b` | `JumpIfZero a, false; JumpIfZero b, false; result=1; Jump end; Label false; result=0; Label end` |
| `a \|\| b` | `JumpIfNotZero a, true; JumpIfNotZero b, true; result=0; Jump end; Label true; result=1; Label end` |
| `c ? t : e` | `JumpIfZero c, else; t->result; Jump end; Label else; e->result; Label end` |
| `goto lbl` | `Jump lbl` |
| `break` | `Jump break_label` |
| `continue` | `Jump continue_label` |

## Known Limitations

- **No VLAs**: Arrays must have compile-time constant sizes
- **No `_Bool`**: No boolean type; uses `int` for logical results
- **No `float`**: Only `double` for floating point
- **No `short`**: The `short` type specifier is not tokenized
- **No `long long`**: Only a single `long` modifier is supported
- **No `long double`**: 80-bit extended precision not supported
- **No `enum`**: Enumerations not implemented
- **No `complex`**: No complex number support
- **No `inline`**: The `inline` keyword is not parsed
- **No `const`/`volatile`/`restrict`**: Type qualifiers are not tokenized
- **No `register`/`auto`/`_Thread_local`**: Storage class specifiers not implemented
- **No flexible array members**: Structs with trailing flexible arrays
- **No variadic function definitions**: Only declarations and calls work; definitions raise an error
- **No compound literals**: The `(type){init}` syntax is not supported
- **No designated initializers**: The `.member=val` and `[idx]=val` syntax is not supported
- **No `_Alignof`**: Alignment query operator not implemented
- **No union initializers**: Compound initializers for unions not supported
- **Register allocator**: Stack-only, no register promotion — every variable lives on the stack
- **No SSA**: Tacky IR uses a flat variable namespace, not SSA form
- **Single compilation unit**: No separate compilation; all source files are concatenated
- **Memory model**: No aliasing analysis; all loads/stores go through memory
- **Floats as function parameters in variadic functions**: Default argument promotions for variadic calls are incomplete for floating-point types
- **Comma operator**: Not implemented in expression parsing (the `Comma` case raises `"TODO: Add Comma"`)
- **No TACKY optimizations**: Constant folding, copy propagation, dead store elimination, and unreachable code elimination (chapters 19–20 of the book) are not implemented
