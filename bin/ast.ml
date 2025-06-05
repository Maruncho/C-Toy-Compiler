
type identifier = string

type unary_op = Complement | Negate | LogNot | Increment | Decrement | Rvalue(*unary plus*)
type binary_op = Add | Sub | Mul | Div | Mod | And | Or | Xor | Lshift | Rshift |
                 Eq | Neq | Lt | Le | Gt | Ge |
                 Assign
type binary_op_sp = LogAnd | LogOr | Comma

type expr = Int32 of Int32.t
          | Var of identifier
          | Unary of unary_op * expr
          | Binary of binary_op * expr * expr
          | BinarySp of binary_op_sp * expr * expr * stmt list
          | BinaryAssign of binary_op * expr * expr
          | Assignment of expr * expr
          | Ternary of expr * expr * expr * stmt list

and stmt = Return of expr
          | Expression of expr
          | If of expr * stmt * (stmt option)
          | Null

type decl = Declaration of identifier * expr option

type block_item = S of stmt | D of decl

type toplevel = Function of string * block_item list

type program = Program of toplevel

let string_unary_op = function
    | Complement -> "~"
    | Negate -> "-"
    | LogNot -> "!"
    | Increment -> "++"
    | Decrement -> "--"
    | Rvalue -> "+"

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
    | Eq -> "=="
    | Neq -> "!="
    | Lt -> "<"
    | Le -> "<="
    | Gt -> ">"
    | Ge -> ">="
    | Assign -> "="

let string_binary_op_sp = function
    | LogAnd -> "&&"
    | LogOr -> "||"
    | Comma -> ","


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

        | BinarySp (op, left, right, between) ->
            print_string ("BinarySp(" ^ string_binary_op_sp op ^ ",\n");
            print_expr (tabs+1) left; print_string ",\n";
            if not (List.is_empty between) then
                List.iter (fun x -> print_stmt (tabs+1) x) between;
            print_expr (tabs+1) right;

        | BinaryAssign (op, dst, src) -> print_string ("BinaryAssign(" ^ string_binary_op op ^ ",\n");
                                          print_expr (tabs+1) dst; print_string ",\n";
                                          print_expr (tabs+1) src;
                                          print_string (")")

        | Assignment (left, right) -> print_string "Assign(\n";
                                      print_expr (tabs+1) left; print_string ",\n";
                                      print_expr (tabs+1) right;
                                      print_string (")")

        | Ternary (cond, th, el, postfix) ->
            print_string "Ternary(\n";
            print_expr (tabs+1) cond; print_string ",\n";
            if not (List.is_empty postfix) then
                List.iter (fun x -> print_stmt (tabs+1) x) postfix;
            print_expr (tabs+1) th; print_string ",\n";
            print_expr (tabs+1) el;
            print_string (")")


and print_stmt tabs stmt =
    print_string (String.make (tabs*2) ' ');
    match stmt with
        | Return expr -> print_string "Return(\n"; (print_expr (tabs+1) expr); print_string ")\n"
        | Expression expr -> print_string "Expression(\n"; (print_expr (tabs+1) expr); print_string ")\n"
        | If (cond, th, Some el) -> print_string "If(\n"; (print_expr (tabs+1) cond); print_string ",\n";  print_stmt (tabs+1) th; print_stmt (tabs+1) el
        | If (cond, th, None) -> print_string "If(\n"; (print_expr (tabs+1) cond); print_string ",\n"; (print_stmt (tabs+1) th);
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

