
let debug = ref false;

type identifier = string

type register = RAX | R10

type unop = Neg | Not

type operand = Imm of Int64.t
             | Reg of register
             | Pseudo of identifier
             | Stack of Int64.t

type instruction = Mov of (operand * operand)
                 | Unary of (unop * operand)
                 | AllocateStack of Int64.t
                 | Ret

type toplevel = Function of string * instruction list

type program = Program of toplevel

let register_str = function
    | RAX -> "%eax"
    | R10 -> "%r10d"

let unop_str = function
    | Neg -> "negl\t"
    | Not -> "notl\t"


let operand_str oper =
    match oper with
        | Imm num -> "$" ^ (Int64.to_string num)
        | Reg reg -> register_str reg
        | Pseudo id -> if not !debug then failwith "PseudoRegister in prod" else "%" ^ id
        | Stack num -> "-"^(Int64.to_string num)^"(%rbp)"

let instruction_str inst =
    "\t" ^
    match inst with
        | Mov (s, d) -> "movl\t" ^ (operand_str s) ^ ", " ^ (operand_str d) ^ "\n"
        | Unary (unop, d) -> (unop_str unop) ^ (operand_str d) ^ "\n"
        | AllocateStack bytes -> "subq\t$" ^ (Int64.to_string bytes) ^ ", %rsp\n"
        | Ret -> "movq\t%rbp, %rsp\n\tpopq\t%rbp\n\tret\n"

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

