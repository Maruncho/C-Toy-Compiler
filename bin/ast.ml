
type identifier = string

type var_type = Variable | Function of int

type unary_op = Complement | Negate | LogNot | Increment | Decrement | Rvalue(*unary plus*)
type binary_op = Add | Sub | Mul | Div | Mod | And | Or | Xor | Lshift | Rshift |
                 Eq | Neq | Lt | Le | Gt | Ge |
                 Assign
type binary_op_sp = LogAnd | LogOr | Comma

type expr = Int32 of Int32.t
          | Var of identifier * var_type
          | Unary of unary_op * expr
          | Binary of binary_op * expr * expr
          | BinarySp of binary_op_sp * expr_sp * expr
          | BinaryAssign of binary_op * expr * expr
          | Assignment of expr * expr
          | Ternary of expr_sp * expr * expr
          | Call of identifier * expr list

and postfix = stmt list
and expr_sp = expr * postfix
and decl_sp = decl * postfix

and block_item = S of stmt | D of decl
and block = block_item list

and for_init = InitDecl of var_decl_sp | InitExpr of expr_sp

and case = Int32.t * identifier (*case <expr>: -> <label> *)

and stmt = Return of expr
         | Expression of expr
         | If of expr_sp * stmt * stmt option
         | Compound of block
         | Break of identifier
         | Continue of identifier
         | While of expr_sp * stmt * (identifier * identifier)
         | DoWhile of stmt * expr_sp * (identifier * identifier)
         | For of for_init option * expr_sp option * expr_sp option * stmt * (identifier * identifier)
         | Null
         | Label of string
         | Goto of string
         | Switch of expr_sp * case list * stmt * identifier(*break*) * identifier(*default*)
         | Case of case | Default of string

and var_decl = identifier * expr option
and var_decl_sp = var_decl * postfix

and fun_decl = identifier * identifier list * block option

and decl = VarDecl of var_decl
         | FunDecl of fun_decl

type toplevel = Function of fun_decl

type program = Program of toplevel list

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

        | Var (id, _) -> print_string ("Var("^id^")")

        | Unary (op, expr) -> print_string ("Unary(" ^ string_unary_op op ^ ",\n");
                              print_expr (tabs+1) expr;
                              print_string (")")
        | Binary (op, left, right) -> print_string ("Binary(" ^ string_binary_op op ^ ",\n");
                                      print_expr (tabs+1) left; print_string ",\n";
                                      print_expr (tabs+1) right;
                                      print_string (")")

        | BinarySp (op, (left, between), right) ->
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

        | Ternary ((cond, postfix), th, el) ->
            print_string "Ternary(\n";
            print_expr (tabs+1) cond; print_string ",\n";
            if not (List.is_empty postfix) then
                List.iter (fun x -> print_stmt (tabs+1) x) postfix;
            print_expr (tabs+1) th; print_string ",\n";
            print_expr (tabs+1) el;
            print_string (")")

        | Call (name, args) ->
            print_string ("Call("^name^",\n");
            List.iter (fun x -> print_expr (tabs+1) x; print_string "\n") args;
            print_string (")")



and print_stmt tabs stmt =
    print_string (String.make (tabs*2) ' ');
    match stmt with
        | Return expr -> print_string "Return(\n"; (print_expr (tabs+1) expr); print_string ")\n"
        | Expression expr -> print_string "Expression(\n"; (print_expr (tabs+1) expr); print_string ")\n"
        | If ((cond, postfix), th, Some el) ->
            print_string "If(\n";
            print_expr (tabs+1) cond; print_string ",\n";
            print_postfix (tabs+1) postfix;
            print_stmt (tabs+1) th;
            print_stmt (tabs+1) el
        | If ((cond, postfix), th, None) ->
            print_string "If(\n";
            print_expr (tabs+1) cond;print_string ",\n";
            print_postfix (tabs+1) postfix;
            print_stmt (tabs+1) th;
        | Compound item_list ->
            print_string ("Block{\n");
            List.iter (fun x -> print_block_item (tabs+1) x) item_list;
            print_string (String.make (tabs*2) ' ');
            print_string "}\n"
        | Null -> print_string "<Empty Statement>\n"
        | Label lbl -> print_string ("Label("^lbl^")\n")
        | Case (i32, lbl) -> print_string ("Case "^(Int32.to_string i32)^":>("^lbl^")\n")
        | Default lbl -> print_string ("Default("^lbl^")\n")
        | Goto lbl -> print_string ("Goto("^lbl^")\n")
        | Break _ -> print_string ("Break\n")
        | Continue _ -> print_string ("Continue\n")
        | While ((cond, postfix), body, _) ->
            print_string "While(\n";
            (print_expr (tabs+1) cond); print_string ",\n";
            (print_postfix (tabs+1) postfix);
            (print_stmt (tabs+1) body)
        | DoWhile (body, (cond, postfix), _) ->
            print_string "DoWhile(\n";
            (print_expr (tabs+1) cond); print_string ",\n";
            (print_postfix (tabs+1) postfix);
            (print_stmt (tabs+1) body)
        | For (init, cond, post, body, _) ->
            print_string "For(\n";
            (match init with None -> print_string "<no init>,\n"
                           | Some init -> print_for_init (tabs+1) init);
            (match cond with None -> print_string "<no condition>,\n"
                           | Some (cond, postfix) -> print_expr (tabs+1) cond; print_string ",\n";
                                                     print_postfix (tabs+1) postfix);
            (match post with None -> print_string "<no post>,\n"
                           | Some (post, postfix) -> print_expr (tabs+1) post; print_string ",\n";
                                                     print_postfix (tabs+1) postfix);
            print_stmt (tabs+1) body;
        | Switch ((cond, postfix), cases, body, br, de) ->
            print_string "Switch(\n";
            print_expr (tabs+1) cond;print_string ",\n";
            print_postfix (tabs+1) postfix;
            print_string (String.make (tabs*2+2) ' ');
            print_string ("Cases: " ^ List.fold_left (fun acc (x, _) -> acc ^ (Int32.to_string x) ^ ", ") "" cases);
            if br <> de then print_string "default,\n" else print_string "\n";
            print_stmt (tabs+1) body

and print_decl tabs decl =
    print_string (String.make (tabs*2) ' ');
    match decl with
        | VarDecl (id, expr_opt) ->
            print_string ("VarDecl("^id);
            begin match expr_opt with
                | None -> print_string ")\n"
                | Some e -> print_string ",\n";
                            print_expr (tabs+1) e;
                            print_string ")\n"
            end
        | FunDecl (id, params, body) ->
            print_string ("<fn "^id^">(");
            List.iter (fun x -> print_string (", "^x)) params;
            match body with
                | None -> print_string ")\n"
                | Some body ->
                    print_string ") {\n";
                    List.iter (fun x -> print_block_item (tabs+2) x) body;
                    print_string (String.make (tabs*2) ' ');
                    print_string "}\n"


and print_block_item tabs b = 
    match b with
        | S stmt -> print_stmt tabs stmt
        | D decl -> print_decl tabs decl

and print_postfix tabs postfix = 
    if not (List.is_empty postfix) then (
        print_string ("Postfix{\n");
        List.iter (fun x -> print_stmt (tabs+1) x) postfix;
        print_string (String.make (tabs*2) ' ');
        print_string "}\n"
    )

and print_for_init tabs i =
    match i with
        | InitDecl (decl, postfix) ->
            print_decl tabs (VarDecl decl);
            print_postfix tabs postfix
        | InitExpr (expr, postfix) -> 
            print_expr tabs expr; print_newline();
            print_postfix tabs postfix

let print_top_level ?(tabs=1) tl =
    print_string (String.make (tabs*2) ' ');
    match tl with
        | Function funDecl -> print_decl tabs (FunDecl funDecl)


let printProgram ast = 
    match ast with
        | Program tl ->
            print_string "Program(\n";
            List.iter (fun x -> print_top_level x) tl;
            print_string ")\n"

