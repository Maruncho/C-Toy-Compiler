
type identifier = string

type data_type = Int | Long | UInt | ULong | Double
               | Ptr of data_type
               | FunType of data_type list * data_type (*used in declaration parsing*)

type var_type = AutoVariable of data_type
              | StaticVariable of data_type
              | Function of data_type list * data_type

type unary_op = Complement | Negate | LogNot | Increment | Decrement | Rvalue(*unary plus*)
type binary_op = Add | Sub | Mul | Div | Mod | And | Or | Xor | Lshift | Rshift |
                 Eq | Neq | Lt | Le | Gt | Ge |
                 Assign
type binary_op_sp = LogAnd | LogOr | Comma

type typed_expr = data_type * expr
and expr = Literal of lit
         | Var of identifier * var_type
         | Cast of data_type * typed_expr
         | Unary of unary_op * typed_expr
         | Dereference of typed_expr
         | AddressOf of typed_expr
         | Binary of binary_op * typed_expr * typed_expr
         | BinarySp of binary_op_sp * typed_expr_sp * typed_expr
         | BinaryAssign of binary_op * typed_expr * typed_expr * (data_type option) (*cast to rhs type if necessary*)
         | Assignment of typed_expr * typed_expr
         | Ternary of typed_expr_sp * typed_expr * typed_expr
         | Call of identifier * typed_expr list

and lit = Int32 of Int32.t | Int64 of Int64.t | UInt32 of Int32.t | UInt64 of Int64.t 
        | Float64 of float

and postfix = stmt list
and typed_expr_sp = typed_expr * postfix
and expr_sp = expr * postfix
and decl_sp = decl * postfix

and block_item = S of stmt | D of decl
and block = block_item list

and for_init = InitDecl of var_decl_sp | InitExpr of typed_expr_sp

and case = lit * identifier (*case <expr>: -> <label> *)

and stmt = Return of typed_expr
         | Expression of typed_expr
         | If of typed_expr_sp * stmt * stmt option
         | Compound of block
         | Break of identifier
         | Continue of identifier
         | While of typed_expr_sp * stmt * (identifier * identifier)
         | DoWhile of stmt * typed_expr_sp * (identifier * identifier)
         | For of for_init option * typed_expr_sp option * typed_expr_sp option * stmt * (identifier * identifier)
         | Null
         | Label of string
         | Goto of string
         | Switch of typed_expr_sp * case list * stmt * identifier(*break*) * identifier(*default*)
         | Case of case | Default of string

and storage_class = Static | Extern

and var_decl = identifier * expr option * data_type * storage_class option
and var_decl_sp = var_decl * postfix

and fun_decl = identifier * (data_type * identifier) list * block option * data_type * storage_class

and decl = VarDecl of var_decl
         | FunDecl of fun_decl

type toplevel = decl

type program = Program of toplevel list

let size = function
    | Int -> 4
    | UInt -> 4
    | Long -> 8
    | ULong -> 8
    | Double -> 100_8
    | Ptr _ -> failwith "Don't use size() with ptr"
    | FunType _ -> failwith "Don't use size() with func"

let signed = function
    | Int | Long -> true
    | UInt | ULong -> false
    | _ -> failwith "Cannot use with non-integral types."

let isIntegral = function
    | Int | UInt | Long | ULong -> true
    | Double -> false
    | Ptr _ -> false
    | FunType _ -> failwith "Don't use isFloatingPoint() with func"

let isFloatingPoint = function
    | Double -> true
    | Int | UInt | Long | ULong | Ptr _ -> false
    | FunType _ -> failwith "Don't use isFloatingPoint() with func"

let isPointer = function
    | Ptr _ -> true
    | Int | UInt | Long | ULong | Double -> false
    | FunType _ -> failwith "Don't use isFloatingPoint() with func"

let getPointerType = function
    | Ptr t -> t
    | _ -> failwith "Don't use getPointerType() with non-pointer"


let flipSigned = function
    | Int -> UInt
    | Long -> ULong
    | UInt -> Int
    | ULong -> Long
    | _ -> failwith "Cannot use with non-integral types."

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

let string_storage_specifier = function
    | Static -> "static "
    | Extern -> "extern "

let string_storage_specifier_opt = function
    | None -> ""
    | Some x -> string_storage_specifier x

let rec string_data_type = function
    | Int -> "int"
    | Long -> "long"
    | UInt -> "unsigned int"
    | ULong -> "unsigned long"
    | Double -> "double"
    | Ptr r -> (string_data_type r) ^ "*"
    | FunType (ps, r) -> (List.fold_left (fun acc p -> acc ^ (string_data_type p) ^ " -> ") "" ps) ^ (string_data_type r)

let string_literal = function
    | Int32 num -> ("Int32(" ^ (Int32.to_string num) ^ ")")
    | Int64 num -> ("Int64(" ^ (Int64.to_string num) ^ ")")
    | UInt32 num -> ("UInt32(" ^ (Int32.to_string num) ^ ")")
    | UInt64 num -> ("UInt64(" ^ (Int64.to_string num) ^ ")")
    | Float64 num -> ("Float64("^ (Float.to_string num) ^")")


let rec print_expr tabs expr =
    print_string (String.make (tabs*2) ' ');
    match expr with
        | Literal lit -> print_string (string_literal lit)

        | Var (id, _) -> print_string ("Var("^id^")")

        | Cast (typ, expr) -> print_string ("Cast("^(string_data_type typ)^",\n");
                              print_typed_expr (tabs+1) expr;
                              print_string (")")

        | Unary (op, expr) -> print_string ("Unary(" ^ string_unary_op op ^ ",\n");
                              print_typed_expr (tabs+1) expr;
                              print_string (")")

        | Dereference expr -> print_string ("Dereference(\n");
                              print_typed_expr (tabs+1) expr;
                              print_string (")")
        | AddressOf expr -> print_string ("AddressOf(\n");
                              print_typed_expr (tabs+1) expr;
                              print_string (")")

        | Binary (op, left, right) -> print_string ("Binary(" ^ string_binary_op op ^ ",\n");
                                      print_typed_expr (tabs+1) left; print_string ",\n";
                                      print_typed_expr (tabs+1) right;
                                      print_string (")")

        | BinarySp (op, (left, between), right) ->
            print_string ("BinarySp(" ^ string_binary_op_sp op ^ ",\n");
            print_typed_expr (tabs+1) left; print_string ",\n";
            if not (List.is_empty between) then
                List.iter (fun x -> print_stmt (tabs+1) x) between;
            print_typed_expr (tabs+1) right;

        | BinaryAssign (op, dst, src, original_type_opt) ->
            print_string ("BinaryAssign(" ^ string_binary_op op ^ ",\n");
            print_typed_expr (tabs+1) dst; print_string ",\n";
            print_typed_expr (tabs+1) src;
            (match original_type_opt with None ->() | Some t -> print_string (",\n"^string_data_type t));
            print_string (")")

        | Assignment (left, right) -> print_string "Assign(\n";
                                      print_typed_expr (tabs+1) left; print_string ",\n";
                                      print_typed_expr (tabs+1) right;
                                      print_string (")")

        | Ternary ((cond, postfix), th, el) ->
            print_string "Ternary(\n";
            print_typed_expr (tabs+1) cond; print_string ",\n";
            if not (List.is_empty postfix) then
                List.iter (fun x -> print_stmt (tabs+1) x) postfix;
            print_typed_expr (tabs+1) th; print_string ",\n";
            print_typed_expr (tabs+1) el;
            print_string (")")

        | Call (name, args) ->
            print_string ("Call("^name^",\n");
            List.iter (fun x -> print_typed_expr (tabs+1) x; print_string "\n") args;
            print_string (")")

and print_typed_expr tabs (typ, expr) =
    print_string (String.make (tabs*2) ' ');
    print_string ((string_data_type typ)^" ");
    print_expr 0 expr


and print_stmt tabs stmt =
    print_string (String.make (tabs*2) ' ');
    match stmt with
        | Return expr -> print_string "Return(\n"; (print_typed_expr (tabs+1) expr); print_string ")\n"
        | Expression typed_expr -> print_string "Expression(\n"; (print_typed_expr (tabs+1) typed_expr); print_string ")\n"
        | If ((cond, postfix), th, Some el) ->
            print_string "If(\n";
            print_typed_expr (tabs+1) cond; print_string ",\n";
            print_postfix (tabs+1) postfix;
            print_stmt (tabs+1) th;
            print_stmt (tabs+1) el
        | If ((cond, postfix), th, None) ->
            print_string "If(\n";
            print_typed_expr (tabs+1) cond;print_string ",\n";
            print_postfix (tabs+1) postfix;
            print_stmt (tabs+1) th;
        | Compound item_list ->
            print_string ("Block{\n");
            List.iter (fun x -> print_block_item (tabs+1) x) item_list;
            print_string (String.make (tabs*2) ' ');
            print_string "}\n"
        | Null -> print_string "<Empty Statement>\n"
        | Label lbl -> print_string ("Label("^lbl^")\n")
        | Case (lit, lbl) -> print_string ("Case "^(string_literal lit)^":>("^lbl^")\n")
        | Default lbl -> print_string ("Default("^lbl^")\n")
        | Goto lbl -> print_string ("Goto("^lbl^")\n")
        | Break _ -> print_string ("Break\n")
        | Continue _ -> print_string ("Continue\n")
        | While ((cond, postfix), body, _) ->
            print_string "While(\n";
            (print_typed_expr (tabs+1) cond); print_string ",\n";
            (print_postfix (tabs+1) postfix);
            (print_stmt (tabs+1) body)
        | DoWhile (body, (cond, postfix), _) ->
            print_string "DoWhile(\n";
            (print_typed_expr (tabs+1) cond); print_string ",\n";
            (print_postfix (tabs+1) postfix);
            (print_stmt (tabs+1) body)
        | For (init, cond, post, body, _) ->
            print_string "For(\n";
            (match init with None -> print_string "<no init>,\n"
                           | Some init -> print_for_init (tabs+1) init);
            (match cond with None -> print_string "<no condition>,\n"
                           | Some (cond, postfix) -> print_typed_expr (tabs+1) cond; print_string ",\n";
                                                     print_postfix (tabs+1) postfix);
            (match post with None -> print_string "<no post>,\n"
                           | Some (post, postfix) -> print_typed_expr (tabs+1) post; print_string ",\n";
                                                     print_postfix (tabs+1) postfix);
            print_stmt (tabs+1) body;
        | Switch ((cond, postfix), cases, body, br, de) ->
            print_string "Switch(\n";
            print_typed_expr (tabs+1) cond;print_string ",\n";
            print_postfix (tabs+1) postfix;
            print_string (String.make (tabs*2+2) ' ');
            print_string ("Cases: " ^ List.fold_left (fun acc (x, _) -> acc ^ (string_literal x) ^ ", ") "" cases);
            if br <> de then print_string "default,\n" else print_string "\n";
            print_stmt (tabs+1) body

and print_decl tabs decl =
    print_string (String.make (tabs*2) ' ');
    match decl with
        | VarDecl (id, expr_opt, typ, storage) ->
            print_string ((string_storage_specifier_opt storage)^(string_data_type typ)^" VarDecl("^id);
            begin match expr_opt with
                | None -> print_string ")\n"
                | Some e -> print_string ",\n";
                            print_expr (tabs+1) e;
                            print_string ")\n"
            end
        | FunDecl (id, params, body, ret_typ, storage) ->
            print_string ((string_storage_specifier storage)^"<fn "^id^"> -> "^(string_data_type ret_typ)^" (");
            print_string (String.concat ", " (List.map (fun (typ, name) -> (string_data_type typ)^" "^name) params));
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
            print_typed_expr tabs expr; print_newline();
            print_postfix tabs postfix

let print_top_level ?(tabs=1) = print_decl tabs


let printProgram ast = 
    match ast with
        | Program tl ->
            print_string "Program(\n";
            List.iter (fun x -> print_top_level x) tl;
            print_string ")\n"

