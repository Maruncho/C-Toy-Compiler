
type identifier = string

type unary_op = Complement | Negate | LogNot
type binary_op = Add | Sub | Mul | Div | Mod | And | Or | Xor | Lshift | Rshift |
                 LogAnd | LogOr | Eq | Neq | Lt | Le | Gt | Ge

type expr = Int32 of Int32.t
          (*| Identifier of identifier*)
          | Unary of unary_op * expr
          | Binary of binary_op * expr * expr

type stmt = Return of expr
          (*| If of expr * stmt * (stmt option)*)

type toplevel = Function of string * stmt

type program = Program of toplevel

let string_unary_op = function
    | Complement -> "~"
    | Negate -> "-"
    | LogNot -> "!"

let string_binary_op = function
    | Add -> "+"
    | Sub -> "-"
    | Mul -> "*"
    | Div -> "/"
    | Mod -> "%"
    | And -> "&"
    | Or -> "|"
    | Xor -> "^"
    | Lshift -> "<<"
    | Rshift -> ">>"
    | LogAnd -> "&&"
    | LogOr -> "||"
    | Eq -> "=="
    | Neq -> "!="
    | Lt -> "<"
    | Le -> "<="
    | Gt -> ">"
    | Ge -> ">="

let rec print_expr tabs expr =
    print_string (String.make (tabs*2) ' ');
    match expr with
        | Int32 num -> print_string ("Int32(" ^ (Int32.to_string num) ^ ")")
        (*| Identifier id -> print_string ("var " ^ id)*)
        | Unary (op, expr) -> print_string ("Unary(" ^ string_unary_op op ^ ",\n");
                              print_expr (tabs+1) expr;
                              print_string (")")
        | Binary (op, left, right) -> print_string ("Binary(" ^ string_binary_op op ^ ",\n");
                                      print_expr (tabs+1) left; print_string ",\n";
                                      print_expr (tabs+1) right;
                                      print_string (")")

and print_stmt tabs stmt =
    print_string (String.make (tabs*2) ' ');
    match stmt with
        | Return expr -> print_string "Return(\n"; (print_expr (tabs+1) expr); print_string ")\n"

let print_top_level ?(tabs=1) tl =
    print_string (String.make (tabs*2) ' ');
    match tl with
        | Function (name, stmt) -> print_string ("fn<" ^ name ^ ">{\n");
                                   print_stmt (tabs+1) stmt;
                                   print_string (String.make (tabs*2) ' ');
                                   print_string "}\n"


let printProgram ast = 
    match ast with
        | Program tl ->
            print_string "Program(\n";
            print_top_level tl;
            print_string ")\n"

