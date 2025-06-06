
let debug = ref false;

type identifier = string

type assembly_type = Byte | Word | LongWord | QuadWord

type cond_code = E | NE | G | GE | L | LE

type register = RAX |
                RCX |
                RDX |
                R10 |
                R11

type unop = Neg | Not
type binop = Add | Sub | Mul |
             And | Or | Xor | Sal | Sar

type operand = Imm of Int32.t
             | Reg of register
             | Pseudo of identifier
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
                 | Ret

type toplevel = Function of string * instruction list

type program = Program of toplevel

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
        | R10 -> "%r10b"
        | R11 -> "%r11b"
    )| Word -> (match reg with
        | RAX -> "%ax"
        | RCX -> "%cx"
        | RDX -> "%dx"
        | R10 -> "%r10w"
        | R11 -> "%r11w"
    )| LongWord -> (match reg with
        | RAX -> "%eax"
        | RCX -> "%ecx"
        | RDX -> "%edx"
        | R10 -> "%r10d"
        | R11 -> "%r11d"
    )| QuadWord -> (match reg with
        | RAX -> "%rax"
        | RCX -> "%rcx"
        | RDX -> "%rdx"
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


let operand_str ?(asm_type=LongWord) oper =
    match oper with
        | Imm num -> "$" ^ (Int32.to_string num)
        | Reg reg -> register_str reg asm_type
        | Pseudo id -> if not !debug then failwith "PseudoRegister in prod" else "%" ^ id
        | Stack num -> "-"^(Int64.to_string num)^"(%rbp)"

let instruction_str inst =
    (match inst with Label _ -> "" | _ -> "\t") ^ (*ugly, but outliers do exist in simpler models*)
    (match inst with
        | Mov (s, d) -> "movl\t" ^ (operand_str s) ^ ", " ^ (operand_str d)
        | Unary (unop, d) -> (unop_str unop) ^ (operand_str d)

        | Decr d -> "decl\t" ^ (operand_str d)
        | Incr d -> "incl\t" ^ (operand_str d)

        | Binary (Sal as binop, s, d)
        | Binary (Sar as binop, s, d) -> (binop_str binop) ^ (operand_str ~asm_type:Byte s) ^ ", " ^ (operand_str d)
        | Binary (binop, s, d) -> (binop_str binop) ^ (operand_str s) ^ ", " ^ (operand_str d)

        | Cmp (s, d) -> "cmpl\t" ^ (operand_str s) ^ ", " ^ (operand_str d)
        | Idiv s -> "idivl\t" ^ (operand_str s)
        | Cdq -> "cdq"
        | Jmp lbl -> "jmp\t" ^ lbl
        | JmpCC (cc, lbl) -> "j"^(cond_code_str cc)^"\t" ^ lbl
        | SetCC (cc, d) -> "set"^(cond_code_str cc)^"\t" ^ (operand_str ~asm_type:Byte d)
        | Label lbl -> lbl^":"
        | AllocateStack bytes -> "subq\t$" ^ (Int64.to_string bytes) ^ ", %rsp"
        | Ret -> "movq\t%rbp, %rsp\n\tpopq\t%rbp\n\tret"
    ) ^ "\n"

let toplevel_str tl =
    match tl with
        | Function (name, instructions) ->
            "\t.globl " ^ name ^ "\n" ^
            name ^ ":\n" ^
            "\tpushq\t%rbp\n" ^
            "\tmovq\t%rsp, %rbp\n" ^
            List.fold_left (fun acc inst -> acc ^ (instruction_str inst)) "" instructions



let string_of_asmt asmt = 
    match asmt with
        | Program tl ->
            toplevel_str tl ^
            "\t.section .note.GNU-stack,\"\",@progbits\n"

let string_of_asmt_debug asmt = 
    (*Thread safety is not my expertise*)
    let () = debug := true in
    let str = string_of_asmt asmt in
    let () = debug := false in
    str

