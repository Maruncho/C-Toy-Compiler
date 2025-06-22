
let debug = ref false;

type identifier = string
type translationUnitIdentifiersDict = unit Environment.Env.t

type assembly_type = Byte | Word | LongWord | QuadWord

type cond_code = E | NE | G | GE | L | LE

type register = RAX | RCX |
                RDX | RDI |
                RSI |
                R8  | R9  |
                R10 | R11

type unop = Neg | Not
type binop = Add | Sub | Mul |
             And | Or | Xor | Sal | Sar

type operand = Imm of Int32.t
             | Reg of register
             | Pseudo of identifier
             | Data of identifier
             | Stack of Int64.t

type instruction = Mov of (operand * operand)
                 | Unary of (unop * operand)
                 | Incr of operand
                 | Decr of operand
                 | Binary of (binop * operand * operand)
                 | Cmp of operand * operand
                 | Idiv of operand
                 | Cdq 
                 | Jmp of identifier
                 | JmpCC of cond_code * identifier
                 | SetCC of cond_code * operand
                 | Label of identifier
                 | AllocateStack of Int64.t
                 | DeallocateStack of Int64.t
                 | Push of operand
                 | Call of identifier
                 | Ret

type func = string * instruction list * bool
type bss = string * bool
type data = string * Int32.t * bool

type program = func list * bss list * data list

let cond_code_str = function
    | E -> "e"
    | NE -> "ne"
    | G -> "g"
    | GE -> "ge"
    | L -> "l"
    | LE -> "le"

let register_str reg = function
     | Byte -> (match reg with
        | RAX -> "%al"
        | RCX -> "%cl"
        | RDX -> "%dl"
        | RDI -> "%dil"
        | RSI -> "%sil"
        | R8  -> "%r8b"
        | R9  -> "%r9b"
        | R10 -> "%r10b"
        | R11 -> "%r11b"
    )| Word -> (match reg with
        | RAX -> "%ax"
        | RCX -> "%cx"
        | RDX -> "%dx"
        | RDI -> "%di"
        | RSI -> "%si"
        | R8  -> "%r8w"
        | R9  -> "%r9w"
        | R10 -> "%r10w"
        | R11 -> "%r11w"
    )| LongWord -> (match reg with
        | RAX -> "%eax"
        | RCX -> "%ecx"
        | RDX -> "%edx"
        | RDI -> "%edi"
        | RSI -> "%esi"
        | R8  -> "%r8d"
        | R9  -> "%r9d"
        | R10 -> "%r10d"
        | R11 -> "%r11d"
    )| QuadWord -> (match reg with
        | RAX -> "%rax"
        | RCX -> "%rcx"
        | RDX -> "%rdx"
        | RDI -> "%rdi"
        | RSI -> "%rsi"
        | R8  -> "%r8"
        | R9  -> "%r9"
        | R10 -> "%r10"
        | R11 -> "%r11"
    )

let unop_str = function
    | Neg -> "negl\t"
    | Not -> "notl\t"

let binop_str = function
    | Add -> "addl\t"
    | Sub -> "subl\t"
    | Mul -> "imull\t"
    | And -> "andl\t"
    | Or  -> "orl\t"
    | Xor -> "xorl\t"
    | Sal -> "sall\t"
    | Sar -> "sarl\t"


let operand_str ?(asm_type=LongWord) oper externalNames =
    match oper with
        | Imm num -> "$" ^ (Int32.to_string num)
        | Reg reg -> register_str reg asm_type
        | Pseudo id -> if not !debug then failwith "PseudoRegister in prod" else "%" ^ id
        | Data id -> (if Environment.setMem id externalNames then id^"@PLT" else id) ^ "(%rip)"
        | Stack num -> (Int64.to_string num)^"(%rbp)"

let instruction_str inst externalNames =
    let en = externalNames in
    (match inst with Label _ -> "" | _ -> "\t") ^ (*ugly, but outliers do exist in simpler models*)
    (match inst with
        | Mov (s, d) -> "movl\t" ^ (operand_str s en) ^ ", " ^ (operand_str d en)
        | Unary (unop, d) -> (unop_str unop) ^ (operand_str d en)

        | Decr d -> "decl\t" ^ (operand_str d en)
        | Incr d -> "incl\t" ^ (operand_str d en)

        | Binary (Sal as binop, s, d)
        | Binary (Sar as binop, s, d) -> (binop_str binop) ^ (operand_str ~asm_type:Byte s en) ^ ", " ^ (operand_str d en)
        | Binary (binop, s, d) -> (binop_str binop) ^ (operand_str s en) ^ ", " ^ (operand_str d en)

        | Cmp (s, d) -> "cmpl\t" ^ (operand_str s en) ^ ", " ^ (operand_str d en)
        | Idiv s -> "idivl\t" ^ (operand_str s en)
        | Cdq -> "cdq"
        | Jmp lbl -> "jmp\t" ^ lbl
        | JmpCC (cc, lbl) -> "j"^(cond_code_str cc)^"\t" ^ lbl
        | SetCC (cc, d) -> "set"^(cond_code_str cc)^"\t" ^ (operand_str ~asm_type:Byte d en)
        | Label lbl -> lbl^":"
        | AllocateStack bytes -> "subq\t$" ^ (Int64.to_string bytes) ^ ", %rsp"
        | DeallocateStack bytes -> "addq\t$" ^ (Int64.to_string bytes) ^ ", %rsp"
        | Push s -> "pushq\t" ^ (operand_str ~asm_type:QuadWord s en)
        | Call lbl -> "call\t" ^ (if Environment.setMem lbl externalNames then lbl^"@PLT" else lbl)
        | Ret -> "movq\t%rbp, %rsp\n\tpopq\t%rbp\n\tret"
    ) ^ "\n"

let func_str (name, instructions, is_global) externalNames =
    (if is_global then "\t.globl " ^ name ^ "\n" else "")  ^
    name ^ ":\n" ^
    "\tpushq\t%rbp\n" ^
    "\tmovq\t%rsp, %rbp\n" ^
    (List.fold_left (fun acc inst -> acc ^ (instruction_str inst externalNames)) "" instructions) ^
    "\n"

let bss_str (name, is_global) =
    (if is_global then "\t.globl " ^ name ^ "\n" else "")  ^
    name ^ ":\n" ^
    "\t.zero 4\n"

let data_str (name, init, is_global) =
    (if is_global then "\t.globl " ^ name ^ "\n" else "")  ^
    name ^ ":\n" ^
    "\t.long "^(Int32.to_string init)^"\n"


let string_of_asmt (fns, bsses, datas) externalNames =
    (if not (List.is_empty bsses) then
        "\t.bss\n\t.align 4\n" ^
        List.fold_left (fun acc x -> acc ^ (bss_str x)) "" bsses
    else "") ^ 
    (if not (List.is_empty datas) then
        "\n\t.data\n\t.align 4\n" ^
        List.fold_left (fun acc x -> acc ^ (data_str x)) "" datas
    else "") ^
    (if not (List.is_empty fns) then
        "\n\t.text\n" ^
        List.fold_left (fun acc x -> acc ^ (func_str x externalNames)) "" fns
    else "") ^

    "\t.section .note.GNU-stack,\"\",@progbits\n"

let string_of_asmt_debug asmt externalNames = 
    (*Thread safety is not my expertise*)
    let () = debug := true in
    let str = string_of_asmt asmt externalNames in
    let () = debug := false in
    str

