
type identifier = string

type data_type = Char | SChar | UChar | Int | Long | UInt | ULong | Double
               | Ptr of data_type
               | Array of data_type * Int64.t
               | FunType of data_type list * data_type (*used in declaration parsing*)

type var_type = AutoVariable of data_type
              | StaticVariable of data_type
              | Function of data_type list * data_type

type unary_op = Complement | Negate | LogNot | Increment | Decrement | Rvalue(*unary plus*)
              | PtrIncrement | PtrDecrement
type binary_op = Add | Sub | Mul | Div | Mod | And | Or | Xor | Lshift | Rshift |
                 Eq | Neq | Lt | Le | Gt | Ge |
                 Assign |
                 PtrAdd | PtrSub | PtrPtrSub

type binary_op_sp = LogAnd | LogOr | Comma

type typed_expr = data_type * expr
and expr = Literal of lit
         | String of string
         | Var of identifier * var_type
         | Cast of data_type * typed_expr
         | Unary of unary_op * typed_expr
         | Dereference of typed_expr
         | AddressOf of typed_expr
         | Subscript of typed_expr * typed_expr
         | Binary of binary_op * typed_expr * typed_expr
         | BinarySp of binary_op_sp * typed_expr_sp * typed_expr
         | BinaryAssign of binary_op * typed_expr * typed_expr * (data_type option) (*cast to rhs type if necessary*)
         | Assignment of typed_expr * typed_expr
         | Ternary of typed_expr_sp * typed_expr * typed_expr
         | Call of identifier * typed_expr list

and lit = Int8 of int | Int32 of Int32.t | Int64 of Int64.t
        | UInt8 of int | UInt32 of Int32.t | UInt64 of Int64.t
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

and initialiser = SingleInit of typed_expr | CompoundInit of initialiser list

and var_decl = identifier * initialiser option * data_type * storage_class option
and var_decl_sp = var_decl * postfix

and fun_decl = identifier * (data_type * identifier) list * block option * data_type * storage_class

and decl = VarDecl of var_decl
         | FunDecl of fun_decl

type toplevel = decl

type program = Program of toplevel list

let init_zero = function
    | Char -> Int8 0
    | SChar -> Int8 0
    | UChar -> UInt8 0
    | Int -> Int32 0l
    | UInt -> UInt32 0l
    | Long -> Int64 0L
    | ULong -> UInt64 0L
    | Double -> Float64 0.0
    | Ptr _ -> failwith "Cannot use int_zero with ptr."
    | Array _ -> failwith "Cannot use int_zero with arr."
    | FunType _ -> failwith "Cannot use int_zero with funType."

let size = function
    | Char -> 1
    | SChar -> 1
    | UChar -> 1
    | Int -> 4
    | UInt -> 4
    | Long -> 8
    | ULong -> 8
    | Double -> 100_8
    | Ptr _ -> failwith "Don't use size() with ptr"
    | Array _ -> failwith "Don't use size() with array"
    | FunType _ -> failwith "Don't use size() with func"

let rec indexing_size = function
    | Char -> 1L
    | SChar -> 1L
    | UChar -> 1L
    | Int -> 4L
    | UInt -> 4L
    | Long -> 8L
    | ULong -> 8L
    | Double -> 8L
    | Ptr _ -> 8L
    | Array (typ, size) -> Int64.mul (indexing_size typ) size
    | FunType _ -> failwith "Don't use indexing_size() with func"

let array_scale = function
    | Array (typ, _) -> indexing_size typ
    | Ptr typ -> indexing_size typ
    | _ -> failwith "Cannot use array_scale with non-array or non-ptr"

let rec alignment = function
    | Char -> 1L
    | SChar -> 1L
    | UChar -> 1L
    | Int -> 4L
    | UInt -> 4L
    | Long -> 8L
    | ULong -> 8L
    | Double -> 8L
    | Ptr _ -> 8L
    | Array (typ, _) as x -> if Int64.compare (indexing_size x) 16L >= 0
                             then 16L
                             else alignment typ
    | FunType _ -> failwith "Don't use alignment() with func"

let aligned_size = function
    | Char -> 1L
    | SChar -> 1L
    | UChar -> 1L
    | Int -> 4L
    | UInt -> 4L
    | Long -> 8L
    | ULong -> 8L
    | Double -> 8L
    | Ptr _ -> 8L
    | Array _ as x -> 
        let size = indexing_size x in
        let align = alignment x in
        let modulo = Int64.rem size align in
        if Int64.equal modulo 0L then size else Int64.add size (Int64.sub align modulo)
    | FunType _ -> failwith "Don't use indexing_size() with func"


let signed = function
    | Char | SChar | Int | Long -> true
    | UChar| UInt | ULong -> false
    | _ -> failwith "Cannot use with non-integral types."

let isIntegral = function
    | Char | SChar | UChar | Int | UInt | Long | ULong -> true
    | Double -> false
    | Ptr _ -> false
    | Array _ -> false
    | FunType _ -> failwith "Don't use isIntegral() with func"

let isChar = function
    | Char | SChar | UChar -> true
    | Int | UInt | Long | ULong -> false
    | Double -> false
    | Ptr _ -> false
    | Array _ -> false
    | FunType _ -> failwith "Don't use isIntegral() with func"

let isStringLiteral = function
    | Ptr Char, String _ -> true
    | Ptr (Array (Char, _)), String _ -> true
    | _, String _ -> failwith "isStringLiteral -> found a string literal which is not a char ptr"
    | _ -> false

let isFloatingPoint = function
    | Double -> true
    | Char | SChar | UChar | Int | UInt | Long | ULong | Ptr _ | Array _ -> false
    | FunType _ -> failwith "Don't use isFloatingPoint() with func"

let isScalar = function
    | Char | SChar | UChar | Int | UInt | Long | ULong | Double -> true
    | Ptr _ -> false
    | Array _ -> false
    | FunType _ -> failwith "Don't use isScalar() with func"

let isPointer = function
    | Ptr _ -> true
    | Array _ -> false (*Sadly, not quite at the parsing-typechecking stage*)
    | Char | SChar | UChar | Int | UInt | Long | ULong | Double -> false
    | FunType _ -> failwith "Don't use isPointer() with func"

let isArray = function
    | Array _ -> true
    | Char | SChar | UChar | Int | UInt | Long | ULong | Double | Ptr _ -> false
    | FunType _ -> failwith "Don't use isArray() with func"

let isCompound = function
    | Array _ -> true
    | Char | SChar | UChar | Int | UInt | Long | ULong | Double | Ptr _ -> false
    | FunType _ -> failwith "Don't use isCompound() with func"

let isCharArray = function
    | Array (Char, _)
    | Array (SChar, _)
    | Array (UChar, _) -> true
    | Char | SChar | UChar | Int | UInt | Long | ULong | Double | Ptr _ | Array _ -> false
    | FunType _ -> failwith "Don't use isCompound() with func"

let isCharPtr ?(forStringDecay=false) = function
    | Ptr Char -> true
    | Ptr SChar -> true && (not forStringDecay)
    | Ptr UChar -> true && (not forStringDecay)
    | Char | SChar | UChar | Int | UInt | Long | ULong | Double | Ptr _ | Array _ -> false
    | FunType _ -> failwith "Don't use isCompound() with func"

let isCharArrayPtr length = function
    | Ptr (Array (Char, here_length)) -> length = here_length
    | Char | SChar | UChar | Int | UInt | Long | ULong | Double | Ptr _ | Array _ -> false
    | FunType _ -> failwith "Don't use isCompound() with func"

let getPointerType = function
    | Ptr t -> t
    | Array (t, _) -> t
    | _ -> failwith "Don't use getPointerType() with non-pointer"


let getArrayData = function
    | Array (t, s) -> (t, s)
    | _ -> failwith "Don't use getArrayData() with non-array"

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
    | PtrIncrement -> "++"
    | Decrement -> "--"
    | PtrDecrement -> "--"
    | Rvalue -> "+"

let string_binary_op = function
    | Add | PtrAdd -> "+"
    | Sub | PtrSub | PtrPtrSub -> "-"
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
    | Char -> "char"
    | SChar -> "signed char"
    | UChar -> "unsigned char"
    | Int -> "int"
    | Long -> "long"
    | UInt -> "unsigned int"
    | ULong -> "unsigned long"
    | Double -> "double"
    | Ptr r -> (string_data_type r) ^ "*"
    | Array (r, s) -> (string_data_type r) ^ "[" ^ (Int64.to_string s) ^ "]"
    | FunType (ps, r) -> (List.fold_left (fun acc p -> acc ^ (string_data_type p) ^ " -> ") "" ps) ^ (string_data_type r)

let string_literal = function
    | Int8 num -> ("Int8(" ^ (string_of_int num) ^ ")")
    | UInt8 num -> ("UInt8(" ^ (string_of_int num) ^ ")")
    | Int32 num -> ("Int32(" ^ (Int32.to_string num) ^ ")")
    | Int64 num -> ("Int64(" ^ (Int64.to_string num) ^ ")")
    | UInt32 num -> ("UInt32(" ^ (Int32.to_string num) ^ ")")
    | UInt64 num -> ("UInt64(" ^ (Int64.to_string num) ^ ")")
    | Float64 num -> ("Float64("^ (Float.to_string num) ^")")


let rec print_expr tabs expr =
    print_string (String.make (tabs*2) ' ');
    match expr with
        | Literal lit -> print_string (string_literal lit)
        | String str -> print_string ("String("^str^")")

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

        | Subscript (left, right) -> print_string "Subscript(\n";
                                     print_typed_expr (tabs+1) left; print_string ",\n";
                                     print_typed_expr (tabs+1) right;
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

and print_initialiser tabs init =
    match init with
        | SingleInit e -> print_typed_expr tabs e
        | CompoundInit init_lst ->
            print_string "{";
            List.iter (fun init -> print_initialiser (tabs+1) init; print_string ",\n") init_lst;
            print_string "}"


and print_decl tabs decl =
    print_string (String.make (tabs*2) ' ');
    match decl with
        | VarDecl (id, expr_opt, typ, storage) ->
            print_string ((string_storage_specifier_opt storage)^(string_data_type typ)^" VarDecl("^id);
            begin match expr_opt with
                | None -> print_string ")\n"
                | Some init -> print_string ",\n";
                            print_initialiser (tabs+1) init;
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

