
type identifier = string

type unary_op = Complement | Negate | Not | Incr | Decr
type binary_op = Add | Subtract | Multiply | Divide | Remainder |
                 And | Or | Xor | LShift | RShift |
                 Equal | NotEqual | LessThan | LessOrEqual | GreaterThan | GreaterOrEqual

type struct_class =
    | SINT | SXMM | SMEM
    | SINTnINT | SINTnXMM | SXMMnINT | SXMMnXMM

type typ = Int8 of bool | Int32 of bool | Int64 of bool (*is_signed*)
         | Float64
         | Ptr of typ
         | ArrObj of typ * Int64.t * Int64.t (*size * align*)
         | Struct of Int64.t * Int64.t (*size * align*) * struct_class
         | Void

type constant = I of Z.t * typ
              | D of float
              | S of string
              | SLab of string
              | ZeroInit of Int64.t

type operand = Constant of constant
             | Var of identifier * typ
             | StaticVar of identifier * typ

type instruction = Return of operand option
                 | SignExtend of operand * operand
                 | ZeroExtend of operand * operand
                 | FloatToInt of operand * operand
                 | FloatToUInt of operand * operand
                 | IntToFloat of operand * operand
                 | UIntToFloat of operand * operand
                 | Truncate of operand * operand
                 | Unary of unary_op * operand * operand
                 | Binary of binary_op * operand * operand * operand
                 | Copy of operand * operand
                 | GetAddress of operand * operand
                 | Load of operand * operand
                 | Store of operand * operand
                 | DeclCompound of identifier * Int64.t * Int64.t(*align and count*)
                 | AddPtr of operand * operand * Int64.t * operand
                 | CopyToOffset of operand * operand * Int64.t
                 | CopyFromOffset of operand * Int64.t * operand
                 | Jump of identifier
                 | JumpIfZero of operand * identifier
                 | JumpIfNotZero of operand * identifier
                 | Label of identifier
                 | Call of identifier * operand list * operand option * bool(*is_variadic*)

type toplevel = Function of string * bool(*global*) * (identifier * typ) list * typ * instruction list
              | StaticVariable of string * bool(*global*) * constant list * Int64.t(*size bytes*) * Int64.t(*alignment*)
              | StaticConst of string * constant list

type program = Program of toplevel list

let type_signed = function
    | Int8 s -> s
    | Int32 s -> s
    | Int64 s -> s
    | Float64 -> failwith "Make the code so that type_signed is not used with floats"
    | Ptr _ -> failwith "Make the code so that type_signed is not used with pointers"
    | ArrObj _ -> failwith "Make the code so that type_signed is not used with array objects"
    | Void -> failwith "Make the code so that type_signed is not used with voids"
    | Struct _ -> failwith "Make the code so that type_signed is not used with structs"

let rec to_ast_type = function
    | Int8 true -> Ast.SChar
    | Int32 true -> Ast.Int
    | Int64 true -> Ast.Long
    | Int8 false -> Ast.UChar
    | Int32 false -> Ast.UInt
    | Int64 false -> Ast.ULong
    | Float64 -> Ast.Double
    | Ptr x -> Ast.Ptr (to_ast_type x)
    | ArrObj (x, s, _) -> Ast.Array (to_ast_type x, s)
    | Void -> Ast.Void
    | Struct _ -> failwith "Cannot convert tacky struct back to Ast struct"

let rec typ_size = function
    | Int8 _ -> 1L
    | Int32 _ -> 4L
    | Int64 _ -> 8L
    | Float64 -> 8L
    | Ptr _ -> 8L
    | ArrObj (typ, size, _) -> Int64.mul (typ_size typ) size
    | Struct (size, _, _) -> size
    | Void -> failwith "Nuh-uh"

(*let type_float = function*)
(*    | Float64 -> true*)
(*    | Int32 _ | Int64 _ -> false*)

let number_zero typ = match typ with
    | Int8 _ -> I (Z.zero, typ)
    | Int32 _ -> I (Z.zero, typ)
    | Int64 _ -> I (Z.zero, typ)
    | Float64 -> D Float.zero
    | Ptr _ -> I (Z.zero, Int64 false)
    | ArrObj _ -> failwith "Cannot number_zero an ArrObj"
    | Void -> failwith "Cannot number_zero a void"
    | Struct _ -> failwith "Cannot number_zero a struct"

let number_zero_operand typ = match typ with
    | Int8 _ -> Constant (I (Z.zero, typ))
    | Int32 _ -> Constant (I (Z.zero, typ))
    | Int64 _ -> Constant (I (Z.zero, typ))
    | Float64 -> StaticVar (Label.getLabelDouble Float.zero, Float64)
    | Ptr _ -> Constant (I (Z.zero, Int64 false))
    | ArrObj _ -> failwith "Cannot number_zero_operand an ArrObj"
    | Void -> Constant (I (Z.zero, typ))
    | Struct _ -> Constant (I (Z.zero, typ))

let operand_type = function
    | Constant D _ -> Float64
    | Constant S _ -> Ptr (Int8 true)
    | Constant SLab _ -> Ptr (Int8 true)
    | Constant I (_, t)
    | Var (_, t)
    | StaticVar (_, t) -> t
    | Constant ZeroInit _ -> failwith "Cannot use operand_type with ZeroInit Const"

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

let rec typ_str = function
    | Int8 false -> "int8"
    | Int8 true -> "uint8"
    | Int32 false -> "uint32"
    | Int32 true -> "int32"
    | Int64 false -> "uint64"
    | Int64 true -> "int64"
    | Float64 -> "float64"
    | Ptr x -> (typ_str x)^"_ptr"
    | ArrObj (x, s, _) -> (typ_str x)^"_arr["^(Int64.to_string s)^"]"
    | Void -> "void"
    | Struct _ -> "struct"

let struct_class_str = function
    | SMEM -> "MEMORY"
    | SINT -> "INTEGER"
    | SXMM -> "SSE"
    | SINTnINT -> "INTEGER_INTEGER"
    | SINTnXMM -> "INTEGER_SSE"
    | SXMMnINT -> "SSE_INTEGER"
    | SXMMnXMM -> "SSE_SSE"

let constant_str = function
    | I (n, typ) -> (typ_str typ) ^ " " ^ Z.to_string n
    | D n -> (typ_str Float64) ^ " " ^ Float.to_string n
    | S str -> "StringLiteral " ^ str
    | SLab str -> "StringLabel " ^ str
    | ZeroInit s -> "ZeroInit " ^ (Int64.to_string s)

let operand_str oper =
    match oper with
        | Constant num -> "$" ^ (constant_str num)
        | Var (id, typ) -> "%(" ^ (typ_str typ) ^ " " ^ id ^ ")"
        | StaticVar (lbl, typ) -> "%%("^ (typ_str typ) ^ " " ^ lbl^")"

let instruction_str inst =
    "\t" ^
    match inst with
        | Return None -> "Return(void)\n"
        | Return (Some opr) -> "Return("^(operand_str opr)^")\n"
        | SignExtend (s, d) -> "SignExtend("^(operand_str s)^", "^(operand_str d)^")\n"
        | ZeroExtend (s, d) -> "ZeroExtend("^(operand_str s)^", "^(operand_str d)^")\n"
        | FloatToInt (s, d) -> "DoubleToInt("^(operand_str s)^", "^(operand_str d)^")\n"
        | FloatToUInt (s, d) -> "DoubleToUInt("^(operand_str s)^", "^(operand_str d)^")\n"
        | IntToFloat (s, d) -> "IntToDouble("^(operand_str s)^", "^(operand_str d)^")\n"
        | UIntToFloat (s, d) -> "UIntToDouble("^(operand_str s)^", "^(operand_str d)^")\n"
        | Truncate (s, d) -> "Truncate("^(operand_str s)^", "^(operand_str d)^")\n"
        | Unary (op, s, d) -> "Unary("^(unary_op_str op)^", "^(operand_str s)^", "^(operand_str d)^")\n"
        | Binary (op, s1, s2, d) -> "Binary("^(binary_op_str op)^", "^(operand_str s1)^", "^(operand_str s2)^", "^(operand_str d)^")\n"
        | Copy (s, d) -> "Copy("^(operand_str s)^", "^(operand_str d)^")\n"
        | GetAddress (s, d) -> "GetAddress("^(operand_str s)^", "^(operand_str d)^")\n"
        | Load (s, d) -> "Load("^(operand_str s)^", "^(operand_str d)^")\n"
        | Store (s, d) -> "Store("^(operand_str s)^", "^(operand_str d)^")\n"
        | DeclCompound (opr, aln, cnt) -> "DeclCompound("^(opr)^", "^(Int64.to_string aln)^" * "^(Int64.to_string cnt)^")\n"
        | AddPtr (s, i, sc, d) -> "AddPtr("^(operand_str s)^", "^(operand_str i)^" * "^(Int64.to_string sc)^", "^(operand_str d)^")\n"
        | CopyToOffset (s, d, o) -> "CopyToOffset("^(operand_str s)^", "^(operand_str d)^", "^(Int64.to_string o)^")\n"
        | CopyFromOffset (s, o, d) -> "CopyFromOffset("^(operand_str s)^", "^(Int64.to_string o)^", "^(operand_str d)^")\n"
        | Jump lbl -> "Jump("^lbl^")\n"
        | JumpIfZero (s, lbl) -> "JumpIfZero("^(operand_str s)^", "^lbl^")\n"
        | JumpIfNotZero (s, lbl) -> "JumpIfNotZero("^(operand_str s)^", "^lbl^")\n"
        | Label lbl -> "Label("^lbl^")\n"
        | Call (name, params, Some dst, _) -> "Call<"^name^">("^(List.map (fun x -> operand_str x) params |> (String.concat ", "))^") -> " ^ (operand_str dst) ^ "\n"
        | Call (name, params, None, _) -> "Call<"^name^">("^(List.map (fun x -> operand_str x) params |> (String.concat ", "))^") -> void\n"

let toplevel_str tl =
    match tl with
        | Function (name, is_global, params, _, instructions) ->
            (if is_global then "global " else "") ^ name ^ "("^(String.concat ", " (List.map (fun (n, t) -> n^":"^(typ_str t)) params))^"):\n" ^
            List.fold_left (fun acc inst -> acc ^ (instruction_str inst)) "" instructions
        | StaticVariable (name, is_global, init, _, _) ->
            (if is_global then "global " else "") ^ name ^ " = " ^ String.concat ", " (List.map constant_str init)
        | StaticConst (name, init) ->
            name ^ " = " ^ String.concat ", " (List.map constant_str init)



let string_of_tacky tacky =
    match tacky with
        | Program tls ->
            List.fold_left (fun acc x -> acc ^ (toplevel_str x) ^ "\n") "" tls

