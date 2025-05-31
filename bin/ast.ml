
type identifier = string

type unary_op = Complement | Negate

type expr = Int32 of Int32.t
          (*| Identifier of identifier*)
          | Unary of unary_op * expr

type stmt = Return of expr
          (*| If of expr * stmt * (stmt option)*)

type toplevel = Function of string * stmt

type program = Program of toplevel

let string_unary_op = function
    | Complement -> "~"
    | Negate -> "-"

let rec print_expr tabs expr =
    print_string (String.make (tabs*2) ' ');
    match expr with
        | Int32 num -> print_string ("Int32(" ^ (Int32.to_string num) ^ ")")
        (*| Identifier id -> print_string ("var " ^ id)*)
        | Unary (op, expr) -> print_string ("Unary(" ^ string_unary_op op ^ ", ");
                              print_expr 0 expr;
                              print_string (")")

and print_stmt tabs stmt =
    print_string (String.make (tabs*2) ' ');
    match stmt with
        | Return expr -> print_string "Return("; (print_expr 0 expr); print_string ")\n"

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

