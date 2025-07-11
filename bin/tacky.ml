
type identifier = string

type unary_op = Complement | Negate | Not | Incr | Decr
type binary_op = Add | Subtract | Multiply | Divide | Remainder |
                 And | Or | Xor | LShift | RShift |
                 Equal | NotEqual | LessThan | LessOrEqual | GreaterThan | GreaterOrEqual

type typ = Int32 of bool | Int64 of bool (*is_signed*)

type operand = Constant of Z.t * typ
             | Var of identifier * typ
             | StaticVar of identifier * typ

type instruction = Return of operand
                 | SignExtend of operand * operand
                 | ZeroExtend of operand * operand
                 | Truncate of operand * operand
                 | Unary of unary_op * operand * operand
                 | Binary of binary_op * operand * operand * operand
                 | Copy of operand * operand
                 | Jump of identifier
                 | JumpIfZero of operand * identifier
                 | JumpIfNotZero of operand * identifier
                 | Label of identifier
                 | Call of identifier * operand list * operand

type toplevel = Function of string * bool(*global*) * (identifier * typ) list * instruction list 
              | StaticVariable of string * bool(*global*) * Z.t * typ

type program = Program of toplevel list

let type_signed = function
    | Int32 s -> s
    | Int64 s -> s

let operand_type = function
    | Constant (_, t)
    | Var (_, t)
    | StaticVar (_, t) -> t

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
        | Constant (num, _) -> "$" ^ (Z.to_string num)
        | Var (id, _) -> "%" ^ id
        | StaticVar (lbl, _) -> "("^lbl^")"

let instruction_str inst =
    "\t" ^
    match inst with
        | Return opr -> "Return("^(operand_str opr)^")\n"
        | SignExtend (s, d) -> "SignExtend("^(operand_str s)^", "^(operand_str d)^")\n"
        | ZeroExtend (s, d) -> "ZeroExtend("^(operand_str s)^", "^(operand_str d)^")\n"
        | Truncate (s, d) -> "Truncate("^(operand_str s)^", "^(operand_str d)^")\n"
        | Unary (op, s, d) -> "Unary("^(unary_op_str op)^", "^(operand_str s)^", "^(operand_str d)^")\n"
        | Binary (op, s1, s2, d) -> "Binary("^(binary_op_str op)^", "^(operand_str s1)^", "^(operand_str s2)^", "^(operand_str d)^")\n"
        | Copy (s, d) -> "Copy("^(operand_str s)^", "^(operand_str d)^")\n"
        | Jump lbl -> "Jump("^lbl^")\n"
        | JumpIfZero (s, lbl) -> "JumpIfZero("^(operand_str s)^", "^lbl^")\n"
        | JumpIfNotZero (s, lbl) -> "JumpIfNotZero("^(operand_str s)^", "^lbl^")\n"
        | Label lbl -> "Label("^lbl^")\n"
        | Call (name, params, dst) -> "Call<"^name^">("^(List.map (fun x -> operand_str x) params |> (String.concat ", "))^") -> " ^ (operand_str dst) ^ "\n"

let toplevel_str tl =
    match tl with
        | Function (name, is_global, params, instructions) ->
            (if is_global then "global " else "") ^ name ^ "("^(String.concat ", " (List.split params |> fst))^"):\n" ^
            List.fold_left (fun acc inst -> acc ^ (instruction_str inst)) "" instructions
        | StaticVariable (name, is_global, init, _) ->
            (if is_global then "global " else "") ^ name ^ " = " ^ (Z.to_string init)



let string_of_tacky tacky =
    match tacky with
        | Program tls ->
            List.fold_left (fun acc x -> acc ^ (toplevel_str x) ^ "\n") "" tls

