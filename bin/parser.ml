
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

    in let typ : (Ast.typed_expr -> Ast.data_type) = fst

    in let postfix : Ast.stmt list ref = ref []
    in let schedulePostfixIncr var = postfix := (Ast.Expression (typ var, Ast.Unary (Ast.Increment, var))) :: !postfix
    in let schedulePostfixDecr var = postfix := (Ast.Expression (typ var, Ast.Unary (Ast.Decrement, var))) :: !postfix
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

    in let isAssign = function
        | 2 -> true
        | _ -> false

    in let isBoolean = function
        | 9 | 10 -> true
        | _ -> false

    in let isShift = function
        | 11 -> true
        | _ -> false

    in let isVar = function
        | (_, Ast.Var (_, Ast.StaticVariable _)) -> true
        | (_, Ast.Var (_, Ast.AutoVariable _)) -> true
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
        | _ as t -> raise (ParserError ("Expected constant expression, but got " ^ (L.string_of_token t)))

    in let get_common_type t1 t2 =
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

    in let convert_to ((old_type, _) as typed_expr) new_type =
        if old_type = new_type then typed_expr
        else (new_type, Ast.Cast (new_type, typed_expr))

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
            let [@warning "-8"] (Ast.VarDecl item, env') = parse_var_decl env lvl in (*suppress FunDecl unmatched warning*)
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
                let num = begin match lit with
                    | Ast.Int32 num -> Const.trunc (Z.of_int32 num) cond_type
                    | Ast.UInt32 num -> Const.trunc (Z.of_int32_unsigned num) cond_type
                    | Ast.Int64 num -> Const.trunc (Z.of_int64 num) cond_type
                    | Ast.UInt64 num -> Const.trunc (Z.of_int64_unsigned num) cond_type
                end in
                let lit = begin match cond_type with
                    | Ast.Int -> Ast.Int32 (Z.to_int32 num)
                    | Ast.UInt -> Ast.UInt32 (Z.to_int32_unsigned num)
                    | Ast.Long -> Ast.Int64 (Z.to_int64 num)
                    | Ast.ULong -> Ast.UInt64 (Z.to_int64_unsigned num)
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

    and parse_params env lvl =
        let rec inner params env = match nextToken() with
            | x when isDecl x ->
                let typ = parse_type_spec None in
                let id = expectIdentifier() in

                if Environment.isInScope id lvl env then raise (ParserError (id ^ " is already a parameter"))
                else

                let newId = newVar id in
                let newEnv = Environment.add id (Environment.Var (newId, typ), lvl) env in

                if nextToken() = L.COMMA
                then let _ = eatToken() in inner ((typ, newId) :: params) newEnv
                else (List.rev ((typ, newId) :: params), newEnv)
            | t -> raise (ParserError ("Expected parameter, but got " ^ (L.string_of_token t)))
        in
        match nextToken() with
            | L.VOID -> let _ = eatToken() in ([], env)
            | _ -> inner [] env

    and parse_type_spec list_opt =
        let rec iter() = match nextToken() with
            | L.INT -> let t = eatToken() in t :: iter()
            | L.LONG -> let t = eatToken() in t :: iter()
            | L.SIGNED -> let t = eatToken() in t :: iter()
            | L.UNSIGNED -> let t = eatToken() in t :: iter()
            | _ -> []

        in let lst = match list_opt with | None -> iter() | Some lst -> lst
        in if List.is_empty lst then raise (ParserError "No type specifier.") else
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

    and parse_var_decl ?(common=None) env lvl =
        let (typ, storage, id) = match common with
        | None ->
            let (typ, storage) = parse_specifiers() in 
            (typ, storage, expectIdentifier())
        | Some common -> common in

        let newId = newVar id in

        (*Because C Standard allows self-reference in midst of definition.........*)
        let initEnv = Environment.add id (Environment.Var (newId, typ), lvl) env in

        let (typed_expr, expr) = match nextToken() with
            | L.ASSIGN -> let _ = eatToken() in
                          let (_, expr) as typed_expr = convert_to (parse_expr initEnv lvl) typ in
                          (Some typed_expr, Some expr)
            | _ -> (None, None)

        in let (newEnv, gEnv) = try Environment.tryAddVariable env !globalEnv lvl storage id newId typed_expr typ
            with Environment.EnvironmentError s -> raise (ParserError s)
        in let () = globalEnv := gEnv

        in let () = expect L.SEMICOLON
        in (Ast.VarDecl (newId, expr, typ, storage), newEnv)

    and parse_fun_decl ?(common=None) env lvl =
        let (return_typ, storage, id) = match common with
        | None ->
            let (typ, storage) = parse_specifiers() in
            (typ, storage, expectIdentifier())
        | Some common -> common in

        let storage = match storage with None -> Ast.Extern | Some s -> s in

        (* Parse parameters *)
        let tempEnv = Environment.add id
            (Environment.Func (id, [], return_typ, false), (*dummy function so we can know later whether it was shadowed by a paramter*)
             lvl)
            env in

        let () = expect L.LPAREN in
        let (params, paramsEnv) = parse_params tempEnv (lvl+1) in
        let paramTypes = fst (List.split params) in
        let () = expect L.RPAREN in
        (*-------------------*)

        (* Parse body*)
        let bodyEnv = match Option.get (Environment.find_opt id paramsEnv) with
            | (Environment.Func _, _) -> 
                Environment.add id
                ((Environment.Func (id, paramTypes, return_typ, true(*doesn't matter. Definitions are not allowed in body.*))),
                 lvl)
                paramsEnv
            | _ -> paramsEnv (* A parameter shadowed the function declaration *)

        in let body = match nextToken() with
            | L.LBRACE -> let _ = eatToken() in Some (parse_block_items bodyEnv (lvl+1) return_typ)
            | _ -> let () = expect L.SEMICOLON in None
        in
        (*-----------------------*)


        let (newEnv, gEnv) = try Environment.tryAddFunction env !globalEnv lvl storage id paramTypes return_typ body
            with Environment.EnvironmentError s -> raise (ParserError s)
        in let () = globalEnv := gEnv

        (*define the name globally*)
        in (Ast.FunDecl (id, params, body, return_typ, storage), newEnv)

    and parse_decl env lvl = 
        let (typ, storage) = parse_specifiers() in
        let id = expectIdentifier() in

        match nextToken() with
            | L.LPAREN -> parse_fun_decl ~common:(Some (typ, storage, id)) env lvl
            | _ -> parse_var_decl ~common:(Some (typ, storage, id)) env lvl


    and parse_stmt env lvl fn_return_type =
        let result = match nextToken() with
        | L.RETURN -> let _ = eatToken() in
                      let typed_expr = parse_expr env lvl in
                      let r = convert_to typed_expr fn_return_type in
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
            let () = expect L.RPAREN in
            let postfixAfterCond = flushPostfix() in
            let stmt = list_to_stmt (parse_stmt env lvl fn_return_type) in
            let (cases, body, default_opt) = parse_switch_body stmt (typ cond) in
            let break = newLabel() in
            let default = (match default_opt with None -> break | Some d -> d) in
            [Ast.Switch ((cond, postfixAfterCond), List.rev cases, body, break, default)]

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
                (*let arg_typ = typ arg in*)
                (*if arg_typ <> param_typ then raise (ParserError ("Argument "^(string_of_int (1+originalCount-count))^": Expected "^(Ast.string_data_type param_typ)^", but got "^(Ast.string_data_type arg_typ)^".")) else*)
                let arg = convert_to arg param_typ in
                begin match nextToken() with
                    | L.COMMA -> let _ = eatToken() in arg :: (iter rest (count-1) false)
                    | _ -> arg :: (iter rest (count-1) true)
                end
        in iter paramTypes originalCount true

    and parse_primary env lvl =
        let t = eatToken() in
        match t with
            | L.INT32_LIT _ as tok -> parseLiteral tok
            | L.UINT32_LIT _ as tok -> parseLiteral tok
            | L.INT64_LIT _ as tok -> parseLiteral tok
            | L.UINT64_LIT _ as tok -> parseLiteral tok
            | L.LPAREN -> let expr = parse_expr env lvl in
                          let () = expect L.RPAREN in
                          expr
            | L.ID id -> begin
                match Environment.find_opt id env with
                    | None -> raise (ParserError (id ^ " is not declared."))
                    | Some (decl, _) -> begin match decl with
                        | Environment.Var (realId, typ) -> typ, (Ast.Var (realId, Ast.AutoVariable typ))
                        | Environment.StaticVar (realId, typ) -> typ, (Ast.Var (realId, Ast.StaticVariable typ))
                        | Environment.Func (id, paramTypes, retType, _) -> retType, (Ast.Var (id, Ast.Function (paramTypes, retType)))
                    end
            end
            | _ -> raise (ParserError ("Expected primary, but got " ^ L.string_of_token t))

    and parse_postfix env lvl =
        let primary = parse_primary env lvl in
        let rec iter peekToken left = match peekToken with
            | L.INCREMENT ->
                if not (isVar left) then raise (ParserError "Suffix Increment operator rhs is not an lvalue") else
                let _ = eatToken() in
                let () = schedulePostfixIncr left in
                iter (nextToken()) (typ left, Ast.Unary (Ast.Rvalue, left))
            | L.DECREMENT ->
                if not (isVar left) then raise (ParserError "Suffix Increment operator rhs is not an lvalue") else
                let _ = eatToken() in
                let () = schedulePostfixDecr left in
                iter (nextToken()) (typ left, Ast.Unary (Ast.Rvalue, left))
            | L.LPAREN ->
                let id, paramsTypes, retType = begin match left with (_, Ast.Var (id, Ast.Function (paramsTypes, retType))) -> id, paramsTypes, retType
                                                     | _ -> raise (ParserError "Cannot call a variable.") end in
                let _ = eatToken() in
                let args = parse_args env lvl paramsTypes in
                iter (nextToken()) (retType, Ast.Call (id, args))

            | _ -> (*functions cannot be an expression past this point*)
                begin match left with
                    | (_, Ast.Var (_, Ast.Function _)) -> raise (ParserError "Cannot use function as a variable.")
                    | _ -> left
                end

        in iter (nextToken()) primary

    and parse_unary env lvl = match nextToken() with
        | L.PLUS -> let _ = eatToken() in
                    let typed_expr = parse_unary env lvl in
                    (typ typed_expr, Ast.Unary (Ast.Rvalue, typed_expr))
        | L.MINUS -> let _ = eatToken() in
                     let typed_expr = parse_unary env lvl in
                     (typ typed_expr, Ast.Unary (Ast.Negate, typed_expr))
        | L.COMPLEMENT -> let _ = eatToken() in
                          let typed_expr = parse_unary env lvl in
                          (typ typed_expr, Ast.Unary (Ast.Complement, typed_expr))
        | L.BANG -> let _ = eatToken() in
                    let typed_expr = parse_unary env lvl in
                    (typ typed_expr, Ast.Unary (Ast.LogNot, typed_expr))
        | L.INCREMENT ->
            let _ = eatToken() in
            let right = parse_unary env lvl in
            let () = begin match right with (_, Ast.Var _) -> () | _ -> raise (ParserError "Prefix Increment operator rhs is not an lvalue") end in
            (typ right, Ast.Unary (Ast.Increment, right))
        | L.DECREMENT -> 
            let _ = eatToken() in
            let right = parse_unary env lvl in
            let () = begin match right with (_, Ast.Var _) -> () | _ -> raise (ParserError "Prefix Decrement operator rhs is not an lvalue") end in
            (typ right, Ast.Unary (Ast.Decrement, right))
        | L.LPAREN when isTypeSpec (nextNextToken()) ->
            let _ = eatToken() in
            let typ = parse_type_spec None in
            let () = expect L.RPAREN in
            let src = parse_unary env lvl in
            (typ, Ast.Cast (typ, src))

        | _ -> try parse_postfix env lvl
               with ParserError e -> raise (ParserError ("Expected unary\n"^e))

    and parse_expr ?(min_prec=0) env lvl : (Ast.typed_expr) =
        let left = parse_unary env lvl in
        let peek = nextToken() in
        let rec iter peekToken left = let p = prec(peekToken) in
            if p >= min_prec then(
                if isAssign p then
                    let op = eatToken() |> parseOp in

                    let () = match left with (_, Ast.Var _) -> () | _ -> raise (ParserError "Expected an lvalue") in
                    let right = parse_expr ~min_prec:p env lvl in
                    let left_type = typ left in
                    let cmn_type = get_common_type (typ left) (typ right) in
                    let new_left = convert_to left cmn_type in
                    let l_type_right = convert_to right left_type in
                    let cmn_type_right = convert_to right cmn_type in
                    match op with
                        | Ast.Assign -> iter (nextToken()) (left_type, (Ast.Assignment (left, l_type_right)))
                        | Ast.Lshift | Ast.Rshift ->
                             iter (nextToken()) (left_type, Ast.BinaryAssign (op, left, l_type_right))
                        | _ when left_type <> cmn_type ->
                            iter (nextToken()) (left_type, Ast.Assignment (left, (left_type, Ast.Cast (left_type, (cmn_type, (Ast.Binary (op, new_left, cmn_type_right)))))))
                        | _ -> iter (nextToken()) (left_type, (Ast.BinaryAssign (op, left, l_type_right)))


                else if isTernary p then
                    let _ = eatToken() in
                    (*let th = Ast.Unary(Ast.Rvalue, parse_expr ~min_prec:0 env lvl) in*)
                    let th = parse_expr ~min_prec:0 env lvl in
                    let () = expect L.COLON in
                    let el = parse_expr ~min_prec:p env lvl in

                    let cmn_type = get_common_type (typ th) (typ el) in
                    let new_th = (cmn_type, Ast.Unary (Ast.Rvalue, convert_to th cmn_type)) in
                    let new_el = (cmn_type, Ast.Unary (Ast.Rvalue, convert_to el cmn_type)) in

                    let postfix = flushPostfix() in
                    iter (nextToken()) (cmn_type, (Ast.Ternary ((left, postfix), new_th, new_el)))

                else if isLogicalAndOr p then
                    let op = eatToken() |> parseOpSp in
                    let between = flushPostfix() in
                    let right = parse_expr ~min_prec:(p+1) env lvl in
                    let cmn_type = get_common_type (typ left) (typ right) in
                    let new_left = convert_to left cmn_type in
                    let new_right = convert_to right cmn_type in
                    iter (nextToken()) (Ast.Int, (Ast.BinarySp (op, (new_left, between), new_right)))

                else if isShift p then
                    let op = eatToken() |> parseOp in
                    let typ_left = (typ left) in
                    let right = parse_expr ~min_prec:(p+1) env lvl in
                    let new_right = convert_to right typ_left

                    in iter (nextToken()) (typ_left, Ast.Binary (op, left, new_right))

                else
                    let op = eatToken() |> parseOp in

                    let right = parse_expr ~min_prec:(p+1) env lvl in
                    let cmn_type = get_common_type (typ left) (typ right) in
                    let new_left = convert_to left cmn_type in
                    let new_right = convert_to right cmn_type in
                    let return = if isBoolean p then
                        (Ast.Int, (Ast.Cast (Ast.Int, (cmn_type, Ast.Binary (op, new_left, new_right)))))
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

