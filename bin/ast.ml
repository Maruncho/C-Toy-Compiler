
type identifier = string

type unary_op = Complement | Negate | LogNot
type binary_op = Add | Sub | Mul | Div | Mod | And | Or | Xor | Lshift | Rshift |
                 LogAnd | LogOr | Eq | Neq | Lt | Le | Gt | Ge |
                 Assign

type expr = Int32 of Int32.t
          | Var of identifier
          | Unary of unary_op * expr
          | Binary of binary_op * expr * expr
          | Assignment of expr * expr

type stmt = Return of expr
          | Expression of expr
          | Null
          (*| If of expr * stmt * (stmt option)*)

type decl = Declaration of identifier * expr option

type block_item = S of stmt | D of decl

type toplevel = Function of string * block_item list

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
    | Assign -> "="

let rec print_expr tabs expr =
    print_string (String.make (tabs*2) ' ');
    match expr with
        | Int32 num -> print_string ("Int32(" ^ (Int32.to_string num) ^ ")")

        | Var id -> print_string ("Var("^id^")")

        | Unary (op, expr) -> print_string ("Unary(" ^ string_unary_op op ^ ",\n");
                              print_expr (tabs+1) expr;
                              print_string (")")
        | Binary (op, left, right) -> print_string ("Binary(" ^ string_binary_op op ^ ",\n");
                                      print_expr (tabs+1) left; print_string ",\n";
                                      print_expr (tabs+1) right;
                                      print_string (")")

        | Assignment (left, right) -> print_string "Assign(\n";
                                      print_expr (tabs+1) left; print_string ",\n";
                                      print_expr (tabs+1) right;
                                      print_string (")")

let print_stmt tabs stmt =
    print_string (String.make (tabs*2) ' ');
    match stmt with
        | Return expr -> print_string "Return(\n"; (print_expr (tabs+1) expr); print_string ")\n"
        | Expression expr -> print_string "Expression(\n"; (print_expr (tabs+1) expr); print_string ")\n"
        | Null -> print_string "<Empty Statement>\n"

let print_decl tabs decl =
    print_string (String.make (tabs*2) ' ');
    match decl with
        Declaration (id, expr_opt) ->
            print_string ("Decl("^id);
            begin match expr_opt with
                | None -> print_string ")\n"
                | Some e -> print_string ",\n";
                            print_expr (tabs+1) e;
                            print_string ")\n"
            end

let print_block_item tabs b = 
    print_string (String.make (tabs*2) ' ');
    match b with
        | S stmt -> print_stmt tabs stmt
        | D decl -> print_decl tabs decl

let print_top_level ?(tabs=1) tl =
    print_string (String.make (tabs*2) ' ');
    match tl with
        | Function (name, block_items) ->
            print_string ("fn<" ^ name ^ ">{\n");
            List.iter (fun x -> print_block_item (tabs+1) x) block_items;
            print_string (String.make (tabs*2) ' ');
            print_string "}\n"


let printProgram ast = 
    match ast with
        | Program tl ->
            print_string "Program(\n";
            print_top_level tl;
            print_string ")\n"

