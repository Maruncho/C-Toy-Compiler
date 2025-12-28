
type identifier = string

type data_type = Char | SChar | UChar | Int | Long | UInt | ULong | Double
               | Ptr of data_type
               | Array of data_type * Int64.t
               | Void
               | FunType of data_type list * data_type (*used in declaration parsing*)
               | Struct of struct_data ref
               | Union of union_data ref

and struct_member_data = identifier * data_type * Int64.t(*offset*)
and struct_data = {name: identifier; mems : struct_member_data list; size: Int64.t; align: Int64.t}

and union_member_data = identifier * data_type
and union_data = {name: identifier; mems: union_member_data list; size: Int64.t; align: Int64.t}

type var_type = AutoVariable of data_type
              | StaticVariable of data_type
              | Function of data_type list * data_type * bool(*is_variadic*)

type unary_op = Complement | Negate | LogNot | Increment | Decrement | Rvalue(*unary plus*)
              | PtrIncrement | PtrDecrement
type binary_op = Add | Sub | Mul | Div | Mod | And | Or | Xor | Lshift | Rshift |
                 Eq | Neq | Lt | Le | Gt | Ge |
                 Assign |
                 PtrAdd | PtrSub | PtrPtrSub of data_type

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
         | Call of identifier * typed_expr list * bool(*is_variadic*)
         | Dot of typed_expr * identifier * Int64.t
         | Arrow of typed_expr * identifier * Int64.t
         | SizeOf of typed_expr
         | SizeOfT of data_type

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

and stmt = Return of typed_expr option
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

and initialiser = SingleInit of typed_expr | CompoundInit of initialiser list | ZeroesInit of Int64.t

and var_decl = identifier * initialiser option * data_type * storage_class option
and var_decl_sp = var_decl * postfix

and fun_decl = identifier * (data_type * identifier) list * block option * data_type * storage_class * bool(*is_variadic*)

and struct_decl = identifier * (identifier * data_type) list
and union_decl = struct_decl

and decl = VarDecl of var_decl
         | FunDecl of fun_decl
         | StructDecl of struct_decl
         | UnionDecl of union_decl

type toplevel = decl

type program = Program of toplevel list

(*Sometimes structs are infinitely recursive, that's why we check references when comparing structs*)
let rec compare_types t1 t2 = match t1, t2 with
    | Ptr t1, Ptr t2 -> compare_types t1 t2
    | Array (t1, s1), Array (t2, s2) -> s1 = s2 && compare_types t1 t2
    | FunType (ps1, r1), FunType (ps2, r2) ->
        List.length ps1 = List.length ps2 &&
        not (List.exists (fun (p1, p2) -> not (compare_types p1 p2)) (List.combine ps1 ps2)) &&
        compare_types r1 r2
    | Struct s1, Struct s2 -> s1 == s2
    | Union s1, Union s2 -> s1 == s2
    | _ -> t1 = t2


let init_zero = function
    | Char -> Int8 0
    | SChar -> Int8 0
    | UChar -> UInt8 0
    | Int -> Int32 0l
    | UInt -> UInt32 0l
    | Long -> Int64 0L
    | ULong -> UInt64 0L
    | Double -> Float64 0.0
    | Ptr _ -> failwith "Cannot use init_zero with ptr."
    | Array _ -> failwith "Cannot use init_zero with arr."
    | Void -> failwith "Cannot use init_zero with void."
    | FunType _ -> failwith "Cannot use init_zero with funType."
    | Struct _ -> failwith "Cannot use init_zero with struct."
    | Union _ -> failwith "Cannot use init_zero with union."

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
    | Void -> failwith "Don't use size() with void"
    | FunType _ -> failwith "Don't use size() with func"
    | Struct _ -> failwith "Cannot use size() with struct."
    | Union _ -> failwith "Cannot use init_zero with union."

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
    | Struct data -> !data.size
    | Union data -> !data.size
    | FunType _ -> failwith "Don't use indexing_indexing_size() with func"
    | Void -> failwith "Don't use indexing_indexing_size() with void"

let array_scale = function
    | Array (typ, _) -> indexing_size typ
    | Ptr typ -> indexing_size typ
    | _ -> failwith "Cannot use array_scale with non-array or non-ptr"

let rec alignment ?(in_struct=false) = function
    | Char -> 1L
    | SChar -> 1L
    | UChar -> 1L
    | Int -> 4L
    | UInt -> 4L
    | Long -> 8L
    | ULong -> 8L
    | Double -> 8L
    | Ptr _ -> 8L
    | Array (typ, _) when in_struct -> alignment ~in_struct:in_struct typ
    | Array (typ, _) as x -> if Int64.compare (indexing_size x) 16L >= 0
                             then 16L
                             else alignment typ
    | Struct data -> !data.align
    | Union data -> !data.align
    | FunType _ -> failwith "Don't use alignment() with func"
    | Void -> failwith "Don't use alignment() with void"

let aligned_size ?(in_struct=false) = function
    | Char -> 1L
    | SChar -> 1L
    | UChar -> 1L
    | Int -> 4L
    | UInt -> 4L
    | Long -> 8L
    | ULong -> 8L
    | Double -> 8L
    | Ptr _ -> 8L
    | Array _ as x when in_struct -> indexing_size x
    | Array _ as x -> 
        let size = indexing_size x in
        let align = alignment x in
        let modulo = Int64.rem size align in
        if Int64.equal modulo 0L then size else Int64.add size (Int64.sub align modulo)
    | Struct data -> !data.size (*its size is multiple of the alignment by the System V ABI requirements*)
    | Union data -> !data.size (*its size is multiple of the alignment by the System V ABI requirements*)
    | FunType _ -> failwith "Don't use alignment_size() with func"
    | Void -> failwith "Don't use aligned_size() with void"

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
    | Void -> false
    | Struct _ -> false
    | Union _ -> false

let isChar = function
    | Char | SChar | UChar -> true
    | Int | UInt | Long | ULong -> false
    | Double -> false
    | Ptr _ -> false
    | Array _ -> false
    | FunType _ -> failwith "Don't use isIntegral() with func"
    | Void -> false
    | Struct _ -> false
    | Union _ -> false

let isStringLiteral = function
    | Ptr Char, String _ -> true
    | Ptr (Array (Char, _)), String _ -> true
    | _, String _ -> failwith "isStringLiteral -> found a string literal which is not a char ptr"
    | _ -> false

let isFloatingPoint = function
    | Double -> true
    | Char | SChar | UChar | Int | UInt | Long | ULong | Ptr _ | Array _ -> false
    | FunType _ -> failwith "Don't use isFloatingPoint() with func"
    | Void -> false
    | Struct _ -> false
    | Union _ -> false

let isScalar = function
    | Char | SChar | UChar | Int | UInt | Long | ULong | Double -> true
    | Ptr _ -> true
    | Array _ -> false
    | Void -> false
    | Struct _ -> false
    | Union _ -> false
    | FunType _ -> failwith "Don't use isScalar() with func"

let isPointer = function
    | Ptr _ -> true
    | Array _ -> false (*Sadly, not quite at the parsing-typechecking stage*)
    | Char | SChar | UChar | Int | UInt | Long | ULong | Double -> false
    | FunType _ -> failwith "Don't use isPointer() with func"
    | Void -> false
    | Struct _ -> false
    | Union _ -> false

let isArray = function
    | Array _ -> true
    | Char | SChar | UChar | Int | UInt | Long | ULong | Double | Ptr _ -> false
    | FunType _ -> failwith "Don't use isArray() with func"
    | Void -> false
    | Struct _ -> false
    | Union _ -> false

let isCompound = function
    | Array _ -> true
    | Struct _ -> true
    | Union _ -> true
    | Char | SChar | UChar | Int | UInt | Long | ULong | Double | Ptr _ -> false
    | FunType _ -> failwith "Don't use isCompound() with func"
    | Void -> false

let isStruct = function
    | Array _ -> false
    | Struct _ -> true
    | Union _ -> false
    | Char | SChar | UChar | Int | UInt | Long | ULong | Double | Ptr _ -> false
    | FunType _ -> failwith "Don't use isCompound() with func"
    | Void -> false

let isUnion = function
    | Array _ -> false
    | Struct _ -> false
    | Union _ -> true
    | Char | SChar | UChar | Int | UInt | Long | ULong | Double | Ptr _ -> false
    | FunType _ -> failwith "Don't use isCompound() with func"
    | Void -> false

let typIsInUnion union typ = match union with
    | Union {contents={mems;_}} -> List.exists (fun (_, t) -> compare_types t typ) mems
    | _ -> failwith "Can't use typIsInUnion() with non-union"

let isStructOrUnion = function
    | Array _ -> false
    | Struct _ -> true
    | Union _ -> true
    | Char | SChar | UChar | Int | UInt | Long | ULong | Double | Ptr _ -> false
    | FunType _ -> failwith "Don't use isCompound() with func"
    | Void -> false

let rec isComplete = function
    | Char | SChar | UChar | Int | UInt | Long | ULong | Double | Ptr _-> true
    | Void -> false
    | Array (x, _) -> isComplete x
    | Struct data -> !data.size > 0L
    | Union data -> !data.size > 0L
    | FunType _ -> failwith "Don't use isComplete() with func"

let isPtrToComplete = function
    | Ptr x -> isComplete x
    | _ -> failwith "Don't use isPtrToComplete() with non-pointer"

let isCharArray = function
    | Array (Char, _)
    | Array (SChar, _)
    | Array (UChar, _) -> true
    | Char | SChar | UChar | Int | UInt | Long | ULong | Double | Ptr _ | Array _ -> false
    | FunType _ -> failwith "Don't use isCharArray() with func"
    | Void -> false
    | Struct _ -> false
    | Union _ -> false

let isCharPtr ?(forStringDecay=false) = function
    | Ptr Char -> true
    | Ptr SChar -> true && (not forStringDecay)
    | Ptr UChar -> true && (not forStringDecay)
    | Char | SChar | UChar | Int | UInt | Long | ULong | Double | Ptr _ | Array _ -> false
    | FunType _ -> failwith "Don't use isCharPtr() with func"
    | Void -> false
    | Struct _ -> false
    | Union _ -> false

let isCharArrayPtr length = function
    | Ptr (Array (Char, here_length)) -> length = here_length
    | Char | SChar | UChar | Int | UInt | Long | ULong | Double | Ptr _ | Array _ -> false
    | FunType _ -> failwith "Don't use isCharArrayPtr() with func"
    | Void -> false
    | Struct _ -> false
    | Union _ -> false

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
    | Sub | PtrSub | PtrPtrSub _ -> "-"
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
    | Void -> "void"
    | FunType (ps, r) -> (List.fold_left (fun acc p -> acc ^ (string_data_type p) ^ " -> ") "" ps) ^ (string_data_type r)
    | Struct data -> "struct "^(!data.name)
    | Union data -> "union "^(!data.name)

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

        | Call (name, args, _) ->
            print_string ("Call("^name^",\n");
            List.iter (fun x -> print_typed_expr (tabs+1) x; print_string "\n") args;
            print_string (")")

        | Dot (strct, id,_) ->
            print_string "Dot(\n";
            print_typed_expr (tabs+1) strct; print_string ",\n";
            print_string (id^",\n");
            print_string (")")

        | Arrow (strct, id,_) ->
            print_string "Arrow(\n";
            print_typed_expr (tabs+1) strct; print_string ",\n";
            print_string (id^",\n");
            print_string (")")

        | SizeOf expr ->
            print_string ("SizeOf(\n");
            print_typed_expr (tabs+1) expr; print_string "\n";
            print_string (")")

        | SizeOfT typ ->
            print_string ("SizeOfT(\n");
            print_string ((string_data_type typ)^"\n");
            print_string (")")

and print_typed_expr tabs (typ, expr) =
    print_string (String.make (tabs*2) ' ');
    print_string ((string_data_type typ)^" ");
    print_expr 0 expr


and print_stmt tabs stmt =
    print_string (String.make (tabs*2) ' ');
    match stmt with
        | Return expr_opt ->
            print_string "Return(\n";
            if Option.is_some expr_opt then print_typed_expr (tabs+1) (Option.get expr_opt);
            print_string ")\n"
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
        | ZeroesInit count -> print_string ("ZeroesInit("^(Int64.to_string count)^")")
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
        | FunDecl (id, params, body, ret_typ, storage, is_variadic) ->
            print_string ((string_storage_specifier storage)^"<fn "^id^"> -> "^(string_data_type ret_typ)^" (");
            print_string (String.concat ", " (List.map (fun (typ, name) -> (string_data_type typ)^" "^name) params));
            if is_variadic then (print_string ", ...");
            begin match body with
                | None -> print_string ")\n"
                | Some body ->
                    print_string ") {\n";
                    List.iter (fun x -> print_block_item (tabs+2) x) body;
                    print_string (String.make (tabs*2) ' ');
                    print_string "}\n"
            end
        | StructDecl (id, mems) ->
            print_string ("<struct "^id^">{\n");
            List.iter (fun (id, typ) ->
                print_string (String.make ((tabs+1)*2) ' ');
                print_string ((string_data_type typ) ^ id)
            ) mems;
            print_string "}\n"
        | UnionDecl (id, mems) ->
            print_string ("<union "^id^">{\n");
            List.iter (fun (id, typ) ->
                print_string (String.make ((tabs+1)*2) ' ');
                print_string ((string_data_type typ) ^ id)
            ) mems;
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

