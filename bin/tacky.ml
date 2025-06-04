
type identifier = string

type unary_op = Complement | Negate | Not | Incr | Decr
type binary_op = Add | Subtract | Multiply | Divide | Remainder |
                 And | Or | Xor | LShift | RShift |
                 Equal | NotEqual | LessThan | LessOrEqual | GreaterThan | GreaterOrEqual

type operand = Constant of Int32.t
             | Var of identifier

type instruction = Return of operand
                 | Unary of unary_op * operand * operand
                 | Binary of binary_op * operand * operand * operand
                 | Copy of operand * operand
                 | Jump of identifier
                 | JumpIfZero of operand * identifier
                 | JumpIfNotZero of operand * identifier
                 | Label of identifier

type toplevel = Function of string * instruction list

type program = Program of toplevel

let unary_op_str = function
    | Complement -> "NOT"
    | Negate -> "NEG"
    | Not -> "LNOT"
    | Incr -> "INCR"
    | Decr -> "DECR"

let binary_op_str = function
    | Add -> "ADD"
    | Subtract -> "SUB"
    | Multiply -> "MUL"
    | Divide -> "DIV"
    | Remainder -> "MOD"
    | And -> "AND"
    | Or -> "OR"
    | Xor -> "XOR"
    | LShift -> "LSHIFT"
    | RShift -> "RSHIFT"
    | Equal -> "EQ"
    | NotEqual -> "NEQ"
    | LessThan -> "LT"
    | LessOrEqual -> "LE"
    | GreaterThan -> "GT"
    | GreaterOrEqual -> "GE"

let operand_str oper =
    match oper with
        | Constant num -> "$" ^ (Int32.to_string num)
        | Var id -> "%" ^ id

let instruction_str inst =
    "\t" ^
    match inst with
        | Return opr -> "Return("^(operand_str opr)^")\n"
        | Unary (op, s, d) -> "Unary("^(unary_op_str op)^", "^(operand_str s)^", "^(operand_str d)^")\n"
        | Binary (op, s1, s2, d) -> "Binary("^(binary_op_str op)^", "^(operand_str s1)^", "^(operand_str s2)^", "^(operand_str d)^")\n"
        | Copy (s, d) -> "Copy("^(operand_str s)^", "^(operand_str d)^")\n"
        | Jump lbl -> "Jump("^lbl^")\n"
        | JumpIfZero (s, lbl) -> "JumpIfZero("^(operand_str s)^", "^lbl^")\n"
        | JumpIfNotZero (s, lbl) -> "JumpIfNotZero("^(operand_str s)^", "^lbl^")\n"
        | Label lbl -> "Label("^lbl^")\n"

let toplevel_str tl =
    match tl with
        | Function (name, instructions) ->
            name ^ ":\n" ^
            List.fold_left (fun acc inst -> acc ^ (instruction_str inst)) "" instructions



let string_of_tacky tacky = 
    match tacky with
        | Program tl ->
            toplevel_str tl ^
            "\n"

