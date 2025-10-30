
module L = Lexer

exception ParserError of string

let globalEnv = ref Environment.emptyGlobal

let parse tokens =
    let tokens = ref tokens
    in let nextToken() = match !tokens with
            | [] -> failwith "Went beyond EOF"
            | t :: _ -> t
    in let nextNextToken() = match !tokens with
            | _ :: t :: _ -> t
            | _ -> failwith "Went beyond EOF"
    in let eatToken() = match !tokens with
            | [] -> failwith "Trying to eat beyond EOF"
            | h :: t -> let () = tokens := t in h
    in let expect expected = let t = eatToken() in if t <> expected then
                             raise (ParserError ("Expected " ^ (L.string_of_token expected) ^ ", but got " ^ (L.string_of_token t)))

    in let dummyLabel = ("?dummyLabelContinue?", "?dummyLabelBreak?")
    in let dummyCase = "?dummyCase?"

    in let tmpVar = ref 0
    in let newVar id = (let t = id ^ "." ^ (string_of_int (!tmpVar)) in let () = tmpVar := !tmpVar + 1 in t)

    in let tmpLabel = ref 0
    in let newLabel() = let t = ".LS" ^ (string_of_int (!tmpLabel)) in let () = tmpLabel := !tmpLabel + 1 in t

    in let expectIdentifier() = match eatToken() with
        | L.ID id -> id
        | _ as t -> raise (ParserError ("Expected identifier, but got " ^ (L.string_of_token t)))

    in let arrayToPtrParam = function
        | Ast.Array (t, _) -> Ast.Ptr t
        | x -> x

    in let decay_arr t_expr = match t_expr with
        | (Ast.Array(t,_), _) -> (Ast.Ptr t, Ast.AddressOf t_expr)
        | _ -> t_expr

    in let undecay_arr t_expr = match t_expr with
        | (Ast.Ptr t, Ast.AddressOf ((Ast.Array _, _) as arr)) -> arr
        | _ -> t_expr

    in let typ (t_expr : Ast.typed_expr) : Ast.data_type = t_expr |> fst

    in let postfix : Ast.stmt list ref = ref []
    in let schedulePostfixIncr var =
        let typ_var = typ var in
        let op = if Ast.isPointer typ_var then Ast.PtrIncrement else Ast.Increment in
        postfix := (Ast.Expression (typ_var, Ast.Unary (op, var))) :: !postfix
    in let schedulePostfixDecr var =
        let typ_var = typ var in
        let op = if Ast.isPointer typ_var then Ast.PtrDecrement else Ast.Decrement in
        postfix := (Ast.Expression (typ_var, Ast.Unary (op, var))) :: !postfix
    in let flushPostfix() =
        let lst = !postfix in
        let () = postfix := [] in
        lst

    in let list_to_stmt = function
        | [] -> Ast.Null
        | [stmt] -> stmt
        | stmts -> Ast.Compound (List.map (fun x -> Ast.S x) stmts)

    in let parseOp = function
        | L.PLUS
        | L.PLUSASSIGN -> Ast.Add
        | L.MINUS
        | L.MINUSASSIGN -> Ast.Sub
        | L.ASTERISK
        | L.ASTERISKASSIGN -> Ast.Mul
        | L.SLASH
        | L.SLASHASSIGN -> Ast.Div
        | L.PERCENT
        | L.PERCENTASSIGN -> Ast.Mod
        | L.ASSIGN -> Ast.Assign
        | L.PIPE
        | L.PIPEASSIGN -> Ast.Or
        | L.AMPERSAND
        | L.AMPERSANDASSIGN -> Ast.And
        | L.CARET
        | L.CARETASSIGN -> Ast.Xor
        | L.LSHIFT
        | L.LSHIFTASSIGN -> Ast.Lshift
        | L.RSHIFT
        | L.RSHIFTASSIGN -> Ast.Rshift
        | L.EQUAL -> Ast.Eq
        | L.NOTEQUAL -> Ast.Neq
        | L.LESS -> Ast.Lt
        | L.LESSEQ -> Ast.Le
        | L.GREATER -> Ast.Gt
        | L.GREATEREQ -> Ast.Ge
        | token -> raise (ParserError ("Invalid operator " ^ (Lexer.string_of_token token)))

    in let parseOpSp = function
        | L.LOGAND -> Ast.LogAnd
        | L.LOGOR -> Ast.LogOr
        | token -> raise (ParserError ("Invalid operator sp " ^ (Lexer.string_of_token token)))

    in let isNotFloatable = function
        | Ast.Mod
        | Ast.And
        | Ast.Or
        | Ast.Xor
        | Ast.Lshift
        | Ast.Rshift -> true
        | _ -> false

    in let isNotPointerable = function
        | Ast.Mul
        | Ast.Div
        | Ast.Mod
        | Ast.And
        | Ast.Or
        | Ast.Xor
        | Ast.Lshift
        | Ast.Rshift -> true
        | _ -> false

    in let isAssign = function
        | 2 -> true
        | _ -> false

    in let isBoolean = function
        | 9 | 10 -> true
        | _ -> false

    in let isShift = function
        | 11 -> true
        | _ -> false

    in let isLvalue ?(imAddressOfOperator=false) = function
        | (_, Ast.Var (_, Ast.StaticVariable Ast.Array _)) -> imAddressOfOperator || false
        | (_, Ast.Var (_, Ast.AutoVariable Ast.Array _)) -> imAddressOfOperator || false
        | (_, Ast.Var (_, Ast.StaticVariable _)) -> true
        | (_, Ast.Var (_, Ast.AutoVariable _)) -> true
        | (_, Ast.Dereference _) -> true
        | (_, Ast.Subscript _) -> true
        | (_, Ast.String _) -> imAddressOfOperator || false
        | _ -> false

    in let isTernary = function
        | 3 -> true
        | _ -> false

    in let isLogicalAndOr = function
        | 5 | 4 -> true
        | _ -> false

    in let prec = function
        | L.ASSIGN | L.PLUSASSIGN | L.MINUSASSIGN | L.ASTERISKASSIGN | L.SLASHASSIGN | L.PERCENTASSIGN | L.AMPERSANDASSIGN | L.PIPEASSIGN | L.CARETASSIGN | LSHIFTASSIGN | RSHIFTASSIGN -> 2
        | L.QUESTION -> 3
        | L.LOGOR -> 4
        | L.LOGAND -> 5
        | L.PIPE -> 6
        | L.CARET -> 7
        | L.AMPERSAND -> 8
        | L.EQUAL | L.NOTEQUAL -> 9
        | L.LESS | L.GREATER | L.LESSEQ | L.GREATEREQ -> 10
        | L.LSHIFT | L.RSHIFT -> 11
        | L.PLUS | L.MINUS -> 12
        | L.ASTERISK | L.SLASH | L.PERCENT -> 13
        | _ -> -1

    in let isTypeSpec = function
        | L.DOUBLE
        | L.CHAR
        | L.INT
        | L.UNSIGNED
        | L.SIGNED
        | L.LONG -> true
        | _ -> false

    in let isDecl = function
        | L.STATIC
        | L.EXTERN -> true
        | x -> isTypeSpec x

    in let isDeclForInit = function
        | L.STATIC
        | L.EXTERN -> failwith "Cannot use storage class specifiers in for loop initializer declaration"
        | x -> isTypeSpec x

    in let parseLiteral tok =
        let lit = match tok with
            | L.INT32_LIT lit -> lit
            | L.UINT32_LIT lit -> lit
            | L.INT64_LIT lit -> lit
            | L.UINT64_LIT lit -> lit
            | _ -> failwith "Invalid usage of parseLiteral"
        in if not (Z.fits_int64_unsigned lit) then raise (ParserError "Literal is too large to represent in a 64bit integer.")
        else match tok with
            | L.INT32_LIT _ when Z.fits_int32 lit -> (Ast.Int, Ast.Literal (Ast.Int32 (Z.to_int32 lit)))
            | L.UINT32_LIT _ when Z.fits_int32_unsigned lit -> (Ast.UInt, Ast.Literal (Ast.UInt32 (Z.to_int32_unsigned lit)))
            | L.INT32_LIT _ | L.INT64_LIT _ -> (Ast.Long, Ast.Literal (Ast.Int64 (Z.to_int64 lit)))
            | L.UINT32_LIT _ | L.UINT64_LIT _ -> (Ast.ULong, Ast.Literal (Ast.UInt64 (Z.to_int64_unsigned lit)))
            | _ -> failwith "Invalid usage of parseLiteral"

    in let expectConstExpr() = match eatToken() with
        | L.INT32_LIT _ as tok -> parseLiteral tok
        | L.UINT32_LIT _ as tok -> parseLiteral tok
        | L.INT64_LIT _ as tok -> parseLiteral tok
        | L.UINT64_LIT _ as tok -> parseLiteral tok
        | L.DOUBLE_LIT num -> Ast.Double, Ast.Literal (Ast.Float64 num)
        | L.CHAR_LIT num_str -> Ast.Int, Ast.Literal (Ast.Int32 ((String.get num_str 0) |> Char.code |> Int32.of_int))
        | _ as t -> raise (ParserError ("Expected constant expression, but got " ^ (L.string_of_token t)))

    in let is_nullptr_constant expr =
        try (Const.parseConstExpr expr) |> Const.isZero
        with _ -> false

    in let get_common_type t1 t2 =
        (*chars are promoted to int*)
        let t1 = if Ast.isChar t1 then Ast.Int else t1 in
        let t2 = if Ast.isChar t2 then Ast.Int else t2 in

        if t1 = t2 then
            t1
        else if (Ast.size t1) = (Ast.size t2) then (
            if (Ast.signed t1) then
                t2
            else
                t1
        ) else if (Ast.size t1) > (Ast.size t2) then
            t1
        else
            t2

    in let get_common_ptr_type ?(can_convert_to_nullptr=true) e1 e2 = 
    let t1, t2 = typ e1, typ e2 in
    (*let () = print_string (Ast.string_data_type t1 ^ "->" ^ (Ast.string_data_type t2) ^ "\n") in*)
    if t1 = t2 then
        t2
    else if Ast.isIntegral t1 && is_nullptr_constant e1 && can_convert_to_nullptr then
        t2
    else if Ast.isIntegral t2 && is_nullptr_constant e2 && can_convert_to_nullptr then
        t1
    else
        raise (ParserError "Expressions have incompatible types.")

    in let explicit_convert_to ((old_type, _) as typed_expr) new_type =
        if old_type = new_type then typed_expr
        else if (Ast.isArray old_type) && (Ast.isPointer new_type) && (Ast.getPointerType old_type) = (Ast.getPointerType new_type) then
            failwith "explicit_convert_to array to pointer should've been handled by the decay"
            (*(decayArray old_type, old_expr)*)
        else if (Ast.isFloatingPoint old_type) && (Ast.isPointer new_type) then
            raise (ParserError "Cannot convert a double to a pointer.")
        else if (Ast.isPointer old_type) && (Ast.isFloatingPoint new_type) then
            raise (ParserError "Cannot convert a pointer to a double.")
        else (new_type, Ast.Cast (new_type, typed_expr))

    in let implicit_convert_to ((old_type, _) as typed_expr) new_type =
        if (Ast.isPointer old_type) && (Ast.isPointer new_type) && new_type <> old_type then
            raise (ParserError "Cannot implicitly convert from one pointer type to another.")
        else if (Ast.isArray old_type) && (Ast.isPointer new_type) && (Ast.getPointerType old_type) <> (Ast.getPointerType new_type) then
            raise (ParserError "Cannot implicitly convert from one pointer type to another.")
        else if (Ast.isPointer old_type) && (Ast.isArray new_type) then
            raise (ParserError "Cannot implicitly convert a pointer to an array.")
        else if (Ast.isPointer old_type) && (not (Ast.isPointer new_type)) then
            raise (ParserError "Cannot implicitly convert a pointer to a non-pointer.")
        else if (not (Ast.isPointer old_type)) && (Ast.isPointer new_type) then(
            if (Ast.isIntegral old_type) then(
                if (is_nullptr_constant typed_expr) then
                    explicit_convert_to typed_expr new_type
                else
                    raise (ParserError "Cannot implicitly convert an integer to a pointer."))
            else
                raise (ParserError "Cannot implicitly convert a non-pointer to a pointer."))
        else
            explicit_convert_to typed_expr new_type

    (*in let convert_lit_to lit new_type = match lit, new_type with*)
    (*    | Ast.Int32 _, Ast.Int -> lit*)
    (*    | Ast.Int64 _, Ast.Long -> lit*)
    (*    | Ast.Int32 num, Ast.Long -> Ast.Int64 (Int64.of_int32 num)*)
    (*    | Ast.Int64 num, Ast.Int -> Ast.Int32 ((Z.signed_extract (Z.of_int64 num) 0 32) |> Z.to_int32)*)
 
    in let rec parse_block_items env lvl fn_return_type = match nextToken() with
        | L.EOF -> raise (ParserError "Unmatched left brace")
        | L.RBRACE -> let _ = eatToken() in []
        | _ -> let (items, env') = (parse_block_item env lvl fn_return_type) in
               items @ parse_block_items env' lvl fn_return_type

    and parse_block_item env lvl fn_return_type = match nextToken() with
        | t when isDecl t ->
            let (item, env') = parse_decl env lvl in
            (Ast.D item :: (List.map (fun x -> Ast.S x) (flushPostfix())), env')

        | _ -> try (List.map (fun x -> Ast.S x) (parse_stmt env lvl fn_return_type), env)
        with ParserError e -> raise (ParserError ("Expected statement/declaration\n"^e))

    and parse_for_init env lvl = match nextToken() with
        | L.SEMICOLON -> let _ = eatToken() in None, env
        | t when isDeclForInit t ->
            let [@warning "-8"] (Ast.VarDecl item, env') = parse_decl ~forInit:true env lvl in (*suppress FunDecl unmatched warning*)
            (Some (Ast.InitDecl (item, flushPostfix())), env')

        | _ -> try (
            let r = parse_expr env lvl in
            let r = Some (Ast.InitExpr (r, flushPostfix())) in let () = expect L.SEMICOLON in r, env
        )
        with ParserError e -> raise (ParserError ("Expected statement/declaration\n"^e))

    and parse_switch_body body cond_type =
        let default = ref None in
        let rec parseBlock block = match block with
            | [] -> ([], [])
            | (Ast.S h) :: t -> 
                let (cases, item) = parseStmt h in
                let (cases', items) = parseBlock t in
                (cases @ cases', (Ast.S item) :: items)
            | h :: t ->
                let (cases', items) = parseBlock t in
                (cases', h :: items)

        and parseStmt stmt = match stmt with
            | Ast.Compound block ->
                let (cases, block) = parseBlock block
                in (cases, Ast.Compound block)

            | Ast.Default _ -> 
                let lbl = newLabel() in
                let () = default := Some lbl in ([], Ast.Default lbl)
            | Ast.Case (lit, _) ->
                let lbl = newLabel() in
                let num, isFloat = begin match lit with
                    | Ast.Int8 num -> Const.trunc (Z.of_int num) Ast.Int, false
                    | Ast.UInt8 num -> Const.trunc (Z.of_int num) Ast.Int, false
                    | Ast.Int32 num -> Const.trunc (Z.of_int32 num) cond_type, false
                    | Ast.UInt32 num -> Const.trunc (Z.of_int32_unsigned num) cond_type, false
                    | Ast.Int64 num -> Const.trunc (Z.of_int64 num) cond_type, false
                    | Ast.UInt64 num -> Const.trunc (Z.of_int64_unsigned num) cond_type, false
                    | Ast.Float64 _ -> Z.zero, true
                end in
                let numFloat = begin match lit with
                    (*Don't forget to add other float types, be aware that _ hides warnings*)
                    | Ast.Float64 num -> num
                    | _ -> 0.0
                end in

                (*Quick fix. Too lazy to refactor and this code is probably not gotta be touched again in any logic-changing way*)
                let () = if (Ast.isFloatingPoint cond_type && isFloat) || (Ast.isIntegral cond_type && (not isFloat)) then ()
                         else raise (ParserError "Type mismatch in switch condition and a case") in

                let lit = begin match cond_type with
                    | Ast.Char -> Ast.Int32 (Z.to_int32 num)
                    | Ast.SChar -> Ast.Int8 (Z.to_int num)
                    | Ast.UChar -> Ast.Int8 (Z.to_int num)
                    | Ast.Int -> Ast.Int32 (Z.to_int32 num)
                    | Ast.UInt -> Ast.UInt32 (Z.to_int32_unsigned num)
                    | Ast.Long -> Ast.Int64 (Z.to_int64 num)
                    | Ast.ULong -> Ast.UInt64 (Z.to_int64_unsigned num)
                    | Ast.Double -> Ast.Float64 numFloat
                    | Ast.Ptr _ -> raise (ParserError "Cannot use pointer types in cases.")
                    | Ast.Array _ -> raise (ParserError "Cannot use array types in cases.")
                    | Ast.FunType _ -> raise (ParserError "Cannot use functions in cases.")
                end in
                ([(lit, lbl)], Ast.Case (lit, lbl))

            | Ast.If (cond, th, Some el) ->
                let (cases, th) = parseStmt th in
                let (cases', el) = parseStmt el in
                (cases @ cases', Ast.If (cond, th, Some el))

            | Ast.If (cond, th, None) ->
                let (cases, th) = parseStmt th in
                (cases, Ast.If (cond, th, None))

            | Ast.While (cond, body, lbl) ->
                let (cases, body) = parseStmt body in
                (cases, Ast.While (cond, body, lbl))

            | Ast.DoWhile (body, cond, lbl) ->
                let (cases, body) = parseStmt body in
                (cases, Ast.DoWhile (body, cond, lbl))

            | Ast.For (init, cond, post, body, lbl) ->
                let (cases, body) = parseStmt body in
                (cases, Ast.For (init, cond, post, body, lbl))

            | stmt -> [], stmt

        in let (cases,stmt) = parseStmt body in (cases, stmt, !default)

    and parse_type_spec list_opt =
        let rec iter() = match nextToken() with
            | L.CHAR
            | L.INT
            | L.LONG
            | L.SIGNED
            | L.UNSIGNED
            | L.DOUBLE -> let t = eatToken() in t :: iter()
            | _ -> []

        in let lst = match list_opt with | None -> iter() | Some lst -> lst
        in if List.is_empty lst then raise (ParserError "No type specifier.") else

        if lst = [L.CHAR] then Ast.Char else
        if lst = [L.SIGNED; L.CHAR] || lst = [L.CHAR; L.SIGNED] then Ast.SChar else
        if lst = [L.UNSIGNED; L.CHAR] || lst = [L.CHAR; L.UNSIGNED] then Ast.UChar else
        if List.mem L.CHAR lst then raise (ParserError "Can't combine 'char' with other type specifiers") else

        if lst = [L.DOUBLE] then Ast.Double else
        if List.mem L.DOUBLE lst then raise (ParserError "Can't combine 'double' with other type specifiers") else

        let _ = List.fold_left (fun seen x -> (
            if List.mem x seen then raise (ParserError "Invalid type specifier.") else
            if x = L.SIGNED && List.mem L.UNSIGNED seen then raise (ParserError "Type specifier cannot be both signed and unsigned") else
            if x = L.UNSIGNED && List.mem L.SIGNED seen then raise (ParserError "Type specifier cannot be both signed and unsigned")
            else (x::seen)

        )) [] lst in
        let isUnsigned = List.mem L.UNSIGNED lst in
        let isLong = List.mem L.LONG lst in
        match (isUnsigned, isLong) with
            | (true, true) -> Ast.ULong
            | (true, false) -> Ast.UInt
            | (false, true) -> Ast.Long
            | (false, false) -> Ast.Int


    and parse_specifiers() =
        let rec iter typ storage = match nextToken() with
            | L.EXTERN -> let _ = eatToken() in
                          if Option.is_some storage then raise (ParserError "Invalid storage class")
                          else iter typ (Some Ast.Extern)
            | L.STATIC -> let _ = eatToken() in
                          if Option.is_some storage then raise (ParserError "Invalid storage class")
                          else iter typ (Some Ast.Static)

            | x when isTypeSpec x -> 
                iter (eatToken() :: typ) storage

            | _ -> (typ, storage)
        in let (typ, storage) = iter [] None in
        (parse_type_spec (Some typ), storage)

    and parse_initialiser typ is_static env lvl =
        let rec fill_array typ len = match len with
            | 0L -> []
            | _ -> (zeroInit typ) :: fill_array typ (Int64.sub len 1L)
        and zeroInit typ = match typ with
            | _ when Ast.isScalar typ ->
                Ast.SingleInit (typ, Ast.Literal (Ast.init_zero typ))
            | Ast.Ptr _ ->
                Ast.SingleInit (Ast.Long, Ast.Literal (Ast.init_zero Ast.Long))
            | Ast.Array (typ, length) ->
                Ast.CompoundInit (fill_array typ length)
            | Ast.FunType _ -> failwith "Impossible."
            | Ast.Char | Ast.SChar | Ast.UChar | Ast.Int | Ast.Double | Ast.UInt | Ast.Long | Ast.ULong -> failwith "For OCaml to stop complaining"

        in let str_to_compound typ t_expr = match (typ, t_expr) with
            | (Ast.Array (arr_of_typ, length), (x, Ast.String str)) ->
                let str_length = String.length str in
                if (Int64.of_int (str_length - 1)) > length then
                    raise (ParserError "String initializer exceeds array length.")

                else if is_static then
                    let str, zeroes = if (Int64.of_int (str_length - 1) = length)
                        then String.sub str 0 (str_length - 1), 0L
                        else str, (Int64.sub length (Int64.of_int str_length))
                    in Ast.CompoundInit ((Ast.SingleInit (x, Ast.String str)) :: (fill_array arr_of_typ zeroes))

                else
                    let init = (String.sub str 0 (str_length - 1)) |> String.to_seq |> List.of_seq |>
                    List.map Char.code |>
                    List.map (fun n -> Ast.SingleInit (arr_of_typ, Ast.Literal (if Ast.signed arr_of_typ then Ast.Int8 n else Ast.UInt8 n))) in
                    Ast.CompoundInit (init @ (fill_array arr_of_typ (Int64.sub length (Int64.of_int (str_length - 1)))))

            | _ -> failwith "Incorrect usage of str_to_compound in parser"

        in let rec parseRestOfArray typ arr_length = match nextToken() with
            | L.COMMA ->
                let _ = eatToken() in
                if nextToken() = L.RBRACE then
                    let _ = eatToken() in
                    fill_array typ arr_length
                else
                    if arr_length <= 0L then
                        raise (ParserError "Array Compound Initializer exceeds array length.")
                    else
                        let init = parse_initialiser typ is_static env lvl in
                        init :: (parseRestOfArray typ (Int64.sub arr_length 1L))
            | L.RBRACE ->
                let _ = eatToken() in
                fill_array typ arr_length
            | _ -> raise (ParserError "Invalid compound initializer.")
        in
        match nextToken() with
        | L.LBRACE ->
            let _ = eatToken() in
                if Ast.isArray typ then
                    let (typ, length) = Ast.getArrayData typ in
                    let first_init = parse_initialiser typ is_static env lvl in
                    Ast.CompoundInit (first_init :: (parseRestOfArray typ (Int64.sub length 1L)))
                else
                    raise (ParserError ("Cannot use compound initializer with " ^ Ast.string_data_type typ))
        | _ ->
            let t_expr = parse_expr env lvl in

            if Ast.isStringLiteral t_expr then
                let str_length = match t_expr with (_, Ast.String str) -> String.length str | _ -> failwith "Impossible." in
                if Ast.isCharArray typ then
                    str_to_compound typ t_expr
                else if Ast.isCharPtr ~forStringDecay:true typ then
                    Ast.SingleInit t_expr
                else if Ast.isCharArrayPtr (Int64.of_int str_length) typ then
                    Ast.SingleInit t_expr
                else
                    raise (ParserError ("Cannot initialize a " ^ (Ast.string_data_type typ) ^ " with a string literal."))

            else if not (Ast.isCompound typ) then
                Ast.SingleInit (implicit_convert_to t_expr typ)
            else
                raise (ParserError ("Cannot use scalar initializer with " ^ Ast.string_data_type typ))

    and parse_var_decl (typ, storage, id) env lvl =

        let newId = newVar id in

        (*Because C Standard allows self-reference in midst of definition.........*)
        let initEnv = Environment.add id (Environment.Var (newId, typ), lvl) env in

        (*let (typed_expr, _) = match nextToken() with*)
        (*    | L.ASSIGN -> let _ = eatToken() in*)
        (*                  let (_, expr) as typed_expr = implicit_convert_to (parse_expr initEnv lvl) typ in*)
        (*                  (Some typed_expr, Some expr)*)
        (*    | _ -> (None, None)*)

        let initialiser = match nextToken() with
            | L.ASSIGN -> let _ = eatToken() in
                          let is_static = storage = Some Ast.Static || lvl = 0 in
                          Some (parse_initialiser typ is_static initEnv lvl)
            | _ -> None

        in let (newEnv, gEnv) = try Environment.tryAddVariable env !globalEnv lvl storage id newId initialiser typ
            with Environment.EnvironmentError s -> raise (ParserError s)
        in let () = globalEnv := gEnv

        in let () = expect L.SEMICOLON
        in (Ast.VarDecl (newId, initialiser, typ, storage), newEnv)

    and parse_fun_decl (ret_type, (param_names, param_types), storage, id) env lvl =

        let storage = match storage with None -> Ast.Extern | Some s -> s in

        (* Parse parameters *)
        let tempEnv = Environment.add id
            (Environment.Func (id, [], ret_type, false), (*dummy function so we can know later whether it was shadowed by a paramter*)
             lvl)
            env in

        let param_types = List.map arrayToPtrParam param_types in

        let paramsEnv, param_names = List.fold_left (fun (env, newNames) (id, typ) -> (
            if Environment.isInScope id (lvl+1) env then raise (ParserError (id ^ " is already a parameter"))
            else

            let newId = newVar id in
            (Environment.add id (Environment.Var (newId, typ), lvl+1) env, newNames @ [newId])
        )) (tempEnv, []) (List.combine param_names param_types) in
        (*-------------------*)

        (* Parse body*)
        let bodyEnv = match Option.get (Environment.find_opt id paramsEnv) with
            | (Environment.Func _, _) -> 
                Environment.add id
                ((Environment.Func (id, param_types, ret_type, true(*doesn't matter. Definitions are not allowed in body.*))),
                 lvl)
                paramsEnv
            | _ -> paramsEnv (* A parameter shadowed the function declaration *)

        in let body = match nextToken() with
            | L.LBRACE -> let _ = eatToken() in Some (parse_block_items bodyEnv (lvl+1) ret_type)
            | _ -> let () = expect L.SEMICOLON in None
        in
        (*-----------------------*)


        let (newEnv, gEnv) = try Environment.tryAddFunction env !globalEnv lvl storage id param_types ret_type body
            with Environment.EnvironmentError s -> raise (ParserError s)
        in let () = globalEnv := gEnv

        in (Ast.FunDecl (id, List.combine param_types param_names, body, ret_type, storage), newEnv)

    and parse_decl ?(forInit=false) env lvl = 
        let (typ, storage) = parse_specifiers() in
        let (id, typ, maybe_params) = try
                ParserDeclarator.process_declarator tokens typ
                    (fun () -> parse_type_spec None)
                    (fun () -> parse_expr env lvl)
            with ParserDeclarator.ParserDeclaratorError e -> raise (ParserError e) in
        match typ with
            | Ast.FunType (param_types, ret_type) ->
                if forInit then raise (ParserError "Cannot declare function in a for initilalization clause") else
                if Ast.isArray ret_type then raise (ParserError "Cannot return an array type.") else
                parse_fun_decl (ret_type, (maybe_params, param_types), storage, id) env lvl
            | _ ->
                parse_var_decl (typ, storage, id) env lvl

    and parse_stmt env lvl fn_return_type =
        let result = match nextToken() with
        | L.RETURN -> let _ = eatToken() in
                      let typed_expr = parse_expr env lvl in
                      let r = implicit_convert_to typed_expr fn_return_type in
                      let () = expect L.SEMICOLON in [Ast.Return r]
        | L.SEMICOLON -> let () = expect L.SEMICOLON in [Ast.Null]
        | L.IF ->
            let _ = eatToken() in
            let () = expect L.LPAREN in
            let cond = parse_expr env lvl in
            let () = expect L.RPAREN in
            let postfixAfterCond = flushPostfix() in
            let true_branch = (parse_stmt env lvl fn_return_type) |> list_to_stmt  in
            let else_branch =
                if nextToken() = L.ELSE then
                    let _ = eatToken() in
                    Some ((parse_stmt env lvl fn_return_type) |> list_to_stmt)
                else None
            in [Ast.If ((cond, postfixAfterCond), true_branch, else_branch)]

        | L.CASE -> let _ = eatToken() in
                    let (_, expr) = expectConstExpr() in
                    let lit = (match expr with Ast.Literal lit -> lit | _ -> failwith "Impossible.") in
                    let _ = expect L.COLON in
                    (Ast.Case (lit, dummyCase)) :: parse_stmt env lvl fn_return_type (*C17 labelled statements*)
        | L.DEFAULT -> let _ = eatToken() in let _ = expect L.COLON in
                (Ast.Default dummyCase) :: parse_stmt env lvl fn_return_type (*C17 labelled statements*)
        | L.SWITCH ->
            let _ = eatToken() in
            let () = expect L.LPAREN in
            let cond = parse_expr env lvl in
            if not (Ast.isScalar (typ cond)) then raise (ParserError "Cannot switch on a non-integral expression.") else
            let () = expect L.RPAREN in
            let postfixAfterCond = flushPostfix() in
            let stmt = list_to_stmt (parse_stmt env lvl fn_return_type) in
            let promoted_cond_typ = if Ast.isChar (typ cond) then Ast.Int else (typ cond) in
            let promoted_cond = explicit_convert_to cond promoted_cond_typ in
            let (cases, body, default_opt) = parse_switch_body stmt promoted_cond_typ in
            let break = newLabel() in
            let default = (match default_opt with None -> break | Some d -> d) in
            [Ast.Switch ((promoted_cond, postfixAfterCond), List.rev cases, body, break, default)]

        | L.WHILE ->
            let _ = eatToken() in
            let () = expect L.LPAREN in
            let cond = parse_expr env lvl in
            let () = expect L.RPAREN in
            let postfixAfterCond = flushPostfix() in
            let body = (parse_stmt env lvl fn_return_type) |> list_to_stmt
            in [Ast.While ((cond, postfixAfterCond), body, dummyLabel)]

        | L.DO ->
            let _ = eatToken() in
            let body = (parse_stmt env lvl fn_return_type) |> list_to_stmt in
            let () = expect L.WHILE in
            let () = expect L.LPAREN in
            let cond = parse_expr env lvl in
            let () = expect L.RPAREN in
            let () = expect L.SEMICOLON in
            let postfixAfterCond = flushPostfix()
            in [Ast.DoWhile (body, (cond, postfixAfterCond), dummyLabel)]

        | L.FOR ->
            let _ = eatToken() in
            let () = expect L.LPAREN in
            let (init, newEnv) = parse_for_init env (lvl+1) in
            let cond = begin match nextToken() with
                | L.SEMICOLON -> let _ = eatToken() in None
                | _ -> let r = parse_expr newEnv (lvl+1) in let () = expect L.SEMICOLON in
                       let postfixAfterCond = flushPostfix() in Some (r, postfixAfterCond)
            end in
            let post = begin match nextToken() with
                | L.RPAREN -> let _ = eatToken() in None
                | _ -> let r = parse_expr newEnv (lvl+1) in let () = expect L.RPAREN in
                       let postfixAfterPost =  flushPostfix() in Some (r, postfixAfterPost)
            end in
            let body = (parse_stmt newEnv (lvl+1) fn_return_type) |> list_to_stmt
            in [Ast.For (init, cond, post, body, dummyLabel)]


        | L.LBRACE -> let _ = eatToken() in [Ast.Compound (parse_block_items env (lvl+1) fn_return_type)]
        | L.GOTO -> let _ = eatToken() in let id = expectIdentifier() in let () = expect L.SEMICOLON in [Ast.Goto id]
        | L.BREAK -> let _ = eatToken() in let _ = expect L.SEMICOLON in [Ast.Break (snd dummyLabel)]
        | L.CONTINUE -> let _ = eatToken() in let _ = expect L.SEMICOLON in [Ast.Continue (fst dummyLabel)]

        (*Label. They are kind of not statements, but no one uses goto so it doesn't deserve its own type.*)
        | L.ID lbl when nextNextToken() = L.COLON ->
(* C23 *)(* let _ = eatToken() in let _ = eatToken() in [Ast.Label lbl] *)
            let _ = eatToken() in let _ = eatToken() in (Ast.Label lbl) :: (parse_stmt env lvl fn_return_type)

        | _ -> try let r = Ast.Expression (parse_expr env lvl) in let () = expect L.SEMICOLON in [r]
            with ParserError e -> raise (ParserError ("Expected statement\n" ^ e))
        in result @ flushPostfix()

    and parse_args env lvl paramTypes =
        let originalCount = List.length paramTypes in
        let original = string_of_int originalCount in
        let rec iter paramTypes count no_comma =
            match nextToken() with
            | L.RPAREN when no_comma ->
                if count > 0 then raise (ParserError ("Argument count is more than " ^ original))
                else let _ = eatToken() in []
            | _ ->
                if count <= 0 then raise (ParserError ("Argument count is less than " ^ original)) else
                let [@warning "-8"] param_typ :: rest = paramTypes in
                let arg = parse_expr env lvl in
                let arg = implicit_convert_to arg param_typ in
                begin match nextToken() with
                    | L.COMMA -> let _ = eatToken() in arg :: (iter rest (count-1) false)
                    | _ -> arg :: (iter rest (count-1) true)
                end
        in iter paramTypes originalCount true

    and parse_primary ?(arr_decay=true) env lvl =
        let t = eatToken() in
        match t with
            | L.INT32_LIT _ as tok -> parseLiteral tok
            | L.UINT32_LIT _ as tok -> parseLiteral tok
            | L.INT64_LIT _ as tok -> parseLiteral tok
            | L.UINT64_LIT _ as tok -> parseLiteral tok
            | L.DOUBLE_LIT num -> Ast.Double, Ast.Literal (Ast.Float64 num)
            | L.CHAR_LIT num_str -> Ast.Int, Ast.Literal (Ast.Int32 ((String.get num_str 0) |> Char.code |> Int32.of_int))
            | L.STRING_LIT str ->
                let rec iter acc = match nextToken() with
                    | L.STRING_LIT str -> let _ = eatToken() in iter (acc ^ str)
                    | _ -> acc ^ "\x00"
                in let str = iter str in
                (Ast.Ptr Ast.Char), Ast.String str
            | L.LPAREN -> let expr = parse_expr ~arr_decay:arr_decay env lvl in
                          let () = expect L.RPAREN in
                          expr
            | L.ID id -> begin
                match Environment.find_opt id env with
                    | None -> raise (ParserError (id ^ " is not declared."))
                    | Some (decl, _) -> begin match decl with
                        | Environment.Var (realId, (Ast.Array _ as typ)) when arr_decay ->
                            decay_arr (typ, (Ast.Var (realId, Ast.AutoVariable typ)))
                        | Environment.Var (realId, typ) ->
                            typ, (Ast.Var (realId, Ast.AutoVariable typ))
                        | Environment.StaticVar (realId, typ) when arr_decay ->
                            decay_arr (typ, (Ast.Var (realId, Ast.StaticVariable typ)))
                        | Environment.StaticVar (realId, typ) ->
                            typ, (Ast.Var (realId, Ast.StaticVariable typ))
                        | Environment.Func (id, paramTypes, retType, _) -> retType, (Ast.Var (id, Ast.Function (paramTypes, retType)))
                    end
            end
            | _ -> raise (ParserError ("Expected primary, but got " ^ L.string_of_token t))

    and parse_postfix ?(arr_decay=true) env lvl =
        let primary = parse_primary env lvl in
        let rec iter peekToken left = match peekToken with
            | L.INCREMENT ->
                if not (isLvalue left) then raise (ParserError "Suffix Increment operator rhs is not an lvalue") else
                let _ = eatToken() in
                let () = schedulePostfixIncr left in
                iter (nextToken()) (typ left, Ast.Unary (Ast.Rvalue, left))
            | L.DECREMENT ->
                if not (isLvalue left) then raise (ParserError "Suffix Increment operator rhs is not an lvalue") else
                let _ = eatToken() in
                let () = schedulePostfixDecr left in
                iter (nextToken()) (typ left, Ast.Unary (Ast.Rvalue, left))
            | L.LPAREN ->
                let id, paramsTypes, retType = begin match left with (_, Ast.Var (id, Ast.Function (paramsTypes, retType))) -> id, paramsTypes, retType
                                                     | _ -> raise (ParserError "Cannot call a variable.") end in
                let _ = eatToken() in
                let args = parse_args env lvl paramsTypes in
                iter (nextToken()) (retType, Ast.Call (id, args))

            | L.LBRACK ->
                let _ = eatToken() in
                let right = parse_expr env lvl in
                let () = expect L.RBRACK in

                let typ1 = typ left in
                let typ2 = typ right in

                if (Ast.isPointer typ1 && Ast.isIntegral typ2) then
                    let deref_type = Ast.getPointerType typ1 in
                    let longed = explicit_convert_to right Ast.Long in
                    iter (nextToken()) (decay_arr (deref_type, Ast.Subscript (left, longed)))
                else if (Ast.isPointer typ2 && Ast.isIntegral typ1) then
                    let deref_type = Ast.getPointerType typ2 in
                    let longed = explicit_convert_to left Ast.Long in
                    iter (nextToken()) (decay_arr (deref_type, Ast.Subscript (right, longed)))
                else
                    raise (ParserError "Cannot use subscript operator with nothing other than a pointer and an integral expression.")


            | _ -> (*functions cannot be an expression past this point*)
                begin match left with
                    | (_, Ast.Var (_, Ast.Function _)) -> raise (ParserError "Cannot use function as a variable.")
                    | _ -> if arr_decay then left else undecay_arr left
                end

        in iter (nextToken()) primary

    and parse_unary ?(arr_decay=true) env lvl = match nextToken() with
        | L.PLUS -> let _ = eatToken() in
                    let typed_expr = parse_unary env lvl in
                    let typed_expr = if Ast.isChar (typ typed_expr) then explicit_convert_to typed_expr Ast.Int else typed_expr in
                    if Ast.isPointer (typ typed_expr) then raise (ParserError "Can't unary plus a pointer") else
                    (typ typed_expr, Ast.Unary (Ast.Rvalue, typed_expr))
        | L.MINUS -> let _ = eatToken() in
                     let typed_expr = parse_unary env lvl in
                    let typed_expr = if Ast.isChar (typ typed_expr) then explicit_convert_to typed_expr Ast.Int else typed_expr in
                     if Ast.isPointer (typ typed_expr) then raise (ParserError "Can't negate a pointer") else
                     (typ typed_expr, Ast.Unary (Ast.Negate, typed_expr))
        | L.COMPLEMENT -> let _ = eatToken() in
                          let typed_expr = parse_unary env lvl in
                          let typed_expr = if Ast.isChar (typ typed_expr) then explicit_convert_to typed_expr Ast.Int else typed_expr in
                          if Ast.isFloatingPoint (typ typed_expr) then raise (ParserError "Can't take the bitwise complement of a floating point expression") else
                          if Ast.isPointer (typ typed_expr) then raise (ParserError "Can't take the bitwise complement of a pointer") else
                          (typ typed_expr, Ast.Unary (Ast.Complement, typed_expr))
        | L.BANG -> let _ = eatToken() in
                    let typed_expr = parse_unary env lvl in
                    (Ast.Int, Ast.Unary (Ast.LogNot, typed_expr))
        | L.ASTERISK -> let _ = eatToken() in
                        let typed_expr = parse_unary env lvl in
                        if (Ast.isPointer (typ typed_expr)) then
                            decay_arr (Ast.getPointerType (typ typed_expr), Ast.Dereference typed_expr)
                        else
                            raise (ParserError "Cannot dereference a non-pointer.")
        | L.AMPERSAND -> let _ = eatToken() in
                        let typed_expr = parse_unary ~arr_decay:false env lvl in
                        begin match typed_expr with
                            | (_, Ast.Dereference t_expr) ->
                                (typ t_expr, Ast.Unary (Ast.Rvalue, t_expr))
                            | (_, Ast.Subscript (ptr, index)) ->
                                (typ ptr, Ast.Binary (Ast.PtrAdd, ptr, index))
                            | (typ, _) ->
                                if (isLvalue ~imAddressOfOperator:true typed_expr) then
                                    if Ast.isStringLiteral typed_expr then
                                        let str = (match typed_expr with (_, Ast.String str) -> str | _ -> failwith "Impossible.") in
                                        (Ast.Ptr (Ast.Array (Ast.Char, Int64.of_int (String.length str))), snd typed_expr)
                                    else
                                        (Ast.Ptr typ, Ast.AddressOf typed_expr)
                                else
                                    raise (ParserError "Cannot addressOf a non-lvalue.")
                        end
        | L.INCREMENT ->
            let _ = eatToken() in
            let right = parse_unary env lvl in
            if not (isLvalue right) then raise (ParserError "Expected an lvalue") else
            let typ_right = typ right in
            if Ast.isPointer typ_right then
                (typ_right, Ast.Unary (Ast.PtrIncrement, right))
            else
                (typ_right, Ast.Unary (Ast.Increment, right))
        | L.DECREMENT -> 
            let _ = eatToken() in
            let right = parse_unary env lvl in
            if not (isLvalue right) then raise (ParserError "Expected an lvalue") else
            let typ_right = typ right in
            if Ast.isPointer typ_right then
                (typ_right, Ast.Unary (Ast.PtrDecrement, right))
            else
                (typ_right, Ast.Unary (Ast.Decrement, right))
        | L.LPAREN when isTypeSpec (nextNextToken()) ->
            let _ = eatToken() in
            let typ = parse_type_spec None in
            let typ = ParserDeclarator.process_abstract_declarator tokens typ (fun () -> parse_expr env lvl) in
            if Ast.isArray typ then raise (ParserError "Cannot use cast to an array type.") else
            let () = expect L.RPAREN in
            let src = parse_unary env lvl in
            explicit_convert_to src typ
            (*(typ, Ast.Cast (typ, src))*)

        | _ -> try parse_postfix ~arr_decay:arr_decay env lvl
               with ParserError e -> raise (ParserError ("Expected unary\n"^e))

    and parse_expr ?(arr_decay=true) ?(min_prec=0) env lvl : (Ast.typed_expr) =
        let left = parse_unary ~arr_decay:arr_decay env lvl in
        let peek = nextToken() in
        let rec iter peekToken left = let p = prec(peekToken) in
            if p >= min_prec then(
                if isAssign p then
                    let op = eatToken() |> parseOp in

                    if not (isLvalue left) then raise (ParserError "Expected an lvalue") else
                    let right = parse_expr ~min_prec:p env lvl in
                    let left_type = typ left in
                    let right_type = typ right in

                    if (op = Ast.Add && Ast.isPointer left_type && Ast.isIntegral right_type) ||
                       (op = Ast.Sub && Ast.isPointer left_type && Ast.isIntegral right_type)
                    then
                        let op = if op = Ast.Add then Ast.PtrAdd else Ast.PtrSub in
                        let longed = explicit_convert_to right Ast.Long in
                        iter (nextToken()) (left_type, Ast.BinaryAssign (op, left, longed, None))

                    else if (op = Ast.Add && Ast.isPointer left_type && Ast.isPointer right_type) then
                        raise (ParserError "Cannot add two pointers together.")
                    else if (op = Ast.Sub && Ast.isPointer left_type && Ast.isPointer right_type) then
                        raise (ParserError "Cannot compound assign subtract two pointers together.")
                    else

                    let cmn_type = if Ast.isPointer (typ left) || Ast.isPointer (typ right)
                        then get_common_ptr_type left right
                        else get_common_type (typ left) (typ right) in
                    (*let new_left = explicit_convert_to left cmn_type in*)
                    let l_type_right = explicit_convert_to right left_type in
                    let cmn_type_right = explicit_convert_to right cmn_type in
                    match op with
                        | Ast.Assign -> iter (nextToken()) (left_type, (Ast.Assignment (left, l_type_right)))
                        | Ast.Lshift | Ast.Rshift ->
                            if (Ast.isFloatingPoint cmn_type) then raise (ParserError "Can't take the shift of a floating point expression") else
                            if (Ast.isPointer cmn_type) then raise (ParserError "Can't shift pointers") else
                            iter (nextToken()) (left_type, Ast.BinaryAssign (op, left, l_type_right, None))
                        | _ ->
                            if (Ast.isFloatingPoint cmn_type && isNotFloatable op) then raise (ParserError "Can't take modulo or logic operator of a floating point expression") else
                            if (Ast.isPointer cmn_type && isNotPointerable op) then raise (ParserError "Can't multiply/divide/modulo/logical operators on pointers.") else
                            if left_type <> cmn_type then
                                iter (nextToken()) (left_type, Ast.BinaryAssign (op, left, cmn_type_right, Some cmn_type))
                            else
                                iter (nextToken()) (left_type, Ast.BinaryAssign (op, left, l_type_right, None))


                else if isTernary p then
                    let _ = eatToken() in
                    (*let th = Ast.Unary(Ast.Rvalue, parse_expr ~min_prec:0 env lvl) in*)
                    let th = parse_expr ~min_prec:0 env lvl in
                    let () = expect L.COLON in
                    let el = parse_expr ~min_prec:p env lvl in

                    let cmn_type = if Ast.isPointer (typ th) || Ast.isPointer (typ el)
                        then get_common_ptr_type th el
                        else get_common_type (typ th) (typ el) in
                    let new_th = (cmn_type, Ast.Unary (Ast.Rvalue, explicit_convert_to th cmn_type)) in
                    let new_el = (cmn_type, Ast.Unary (Ast.Rvalue, explicit_convert_to el cmn_type)) in

                    let postfix = flushPostfix() in
                    iter (nextToken()) (cmn_type, (Ast.Ternary ((left, postfix), new_th, new_el)))

                else if isLogicalAndOr p then
                    let op = eatToken() |> parseOpSp in
                    let between = flushPostfix() in
                    let right = parse_expr ~min_prec:(p+1) env lvl in
                    iter (nextToken()) (Ast.Int, (Ast.BinarySp (op, (left, between), right)))

                else if isShift p then
                    let op = eatToken() |> parseOp in
                    let typ_left = (typ left) in
                    let typ_left = if Ast.isChar typ_left then Ast.Int else typ_left in
                    let right = parse_expr ~min_prec:(p+1) env lvl in
                    if (typ right) = Ast.Double || typ_left = Ast.Double then raise (ParserError "Can't use double as rhs of a shift operator.") else
                    if (Ast.isPointer (typ right) || Ast.isPointer typ_left) then raise (ParserError "Can't multiply/divide/modulo/logical operators on pointers.") else
                    let new_left = explicit_convert_to left typ_left in
                    let new_right = explicit_convert_to right typ_left

                    in iter (nextToken()) (typ_left, Ast.Binary (op, new_left, new_right))

                else
                    let op = eatToken() |> parseOp in

                    let right = parse_expr ~min_prec:(p+1) env lvl in
                    let left_type = typ left in
                    let right_type = typ right in

                    if (op = Ast.Add && Ast.isPointer left_type && Ast.isIntegral right_type) ||
                       (op = Ast.Add && Ast.isIntegral left_type && Ast.isPointer right_type) ||
                       (op = Ast.Sub && Ast.isPointer left_type && Ast.isIntegral right_type)
                    then
                        let typ, ptr, longed = if Ast.isPointer left_type
                            then left_type, left, explicit_convert_to right Ast.Long
                            else right_type, right, explicit_convert_to left Ast.Long in
                        let op = if op = Ast.Add then Ast.PtrAdd else Ast.PtrSub in
                        iter (nextToken()) (typ, Ast.Binary (op, ptr, longed))

                    else if (op = Ast.Sub && Ast.isIntegral left_type && Ast.isPointer right_type) then
                        raise (ParserError "Cannot subtract a pointer from an integral type.")

                    else if (op = Ast.Add && Ast.isPointer left_type && Ast.isPointer right_type) then
                        raise (ParserError "Cannot add two pointers together.")
                    else if (op = Ast.Sub && Ast.isPointer left_type && Ast.isPointer right_type && left_type = right_type) then
                        iter (nextToken()) (Ast.Long, Ast.Binary (Ast.PtrPtrSub, left, right))
                    else

                    (*simple and quick bugfix. Pretty sure it's not 100% correct, though.*)
                    let can_implicit_cast_nullptr = match op with Ast.Lt | Ast.Le | Ast.Gt | Ast.Ge -> false | _ -> true in

                    let cmn_type = if Ast.isPointer left_type || Ast.isPointer right_type
                        then get_common_ptr_type ~can_convert_to_nullptr:can_implicit_cast_nullptr left right
                        else get_common_type left_type right_type in
                    if (Ast.isFloatingPoint cmn_type && isNotFloatable op) then raise (ParserError "Can't take modulo or logic operator of a floating point expression") else
                    if (Ast.isPointer cmn_type && isNotPointerable op) then raise (ParserError "Can't multiply/divide/modulo/logical operators on pointers.") else
                    let new_left = explicit_convert_to left cmn_type in
                    let new_right = explicit_convert_to right cmn_type in
                    let return = if isBoolean p then
                        (Ast.Int, Ast.Binary (op, new_left, new_right))
                    else
                        (cmn_type, Ast.Binary (op, new_left, new_right))

                    in iter (nextToken()) return 
            )else
                left
        in iter peek left

    and parse_toplevel env lvl = match nextToken() with
        | L.EOF -> []
        | _ -> let (decl, newEnv) = parse_decl env lvl in
               decl :: (parse_toplevel newEnv lvl)

    and parse_program() =
        let env = Environment.empty in
        let toplevel = parse_toplevel env 0 in
        let result = Ast.Program(toplevel) in
        let () = expect EOF in
        result

    in try let p = parse_program() |> SemantGoto.parse |> SemantBreakContinue.parse
           in let () = SemantSwitch.parse p in p,!globalEnv with
        | SemantGoto.ParserError e -> raise (ParserError e)
        | SemantBreakContinue.ParserError e -> raise (ParserError e)
        | SemantSwitch.ParserError e -> raise (ParserError e)

