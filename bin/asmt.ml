
let debug = ref false;

type identifier = string

type register = RAX |
                RCX | CL |(*temporary*)
                RDX |
                R10 |
                R11

type unop = Neg | Not
type binop = Add | Sub | Mul |
             And | Or | Xor | Sal | Sar

type operand = Imm of Int64.t
             | Reg of register
             | Pseudo of identifier
             | Stack of Int64.t

type instruction = Mov of (operand * operand)
                 | Unary of (unop * operand)
                 | Binary of (binop * operand * operand)
                 | Idiv of operand
                 | Cdq 
                 | AllocateStack of Int64.t
                 | Ret

type toplevel = Function of string * instruction list

type program = Program of toplevel

let register_str = function
    | RAX -> "%eax"
    | RDX -> "%edx"
    | RCX -> "%ecx"
    | CL -> "%cl"
    | R10 -> "%r10d"
    | R11 -> "%r11d"

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


let operand_str oper =
    match oper with
        | Imm num -> "$" ^ (Int64.to_string num)
        | Reg reg -> register_str reg
        | Pseudo id -> if not !debug then failwith "PseudoRegister in prod" else "%" ^ id
        | Stack num -> "-"^(Int64.to_string num)^"(%rbp)"

let instruction_str inst =
    "\t" ^
    (match inst with
        | Mov (s, d) -> "movl\t" ^ (operand_str s) ^ ", " ^ (operand_str d)
        | Unary (unop, d) -> (unop_str unop) ^ (operand_str d)
        | Binary (binop, s, d) -> (binop_str binop) ^ (operand_str s) ^ ", " ^ (operand_str d)
        | Idiv s -> "idivl\t" ^ (operand_str s)
        | Cdq -> "cdq"
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

