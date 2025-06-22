
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

    in let expectConstExpr() = match eatToken() with
        | L.INT32_LIT i32 -> i32
        | _ as t -> raise (ParserError ("Expected constant expression, but got " ^ (L.string_of_token t)))

    in let postfix : Ast.stmt list ref = ref []
    in let schedulePostfixIncr var = postfix := (Ast.Expression (Ast.Unary (Ast.Increment, var))) :: !postfix
    in let schedulePostfixDecr var = postfix := (Ast.Expression (Ast.Unary (Ast.Decrement, var))) :: !postfix
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

    in let isVar = function
        | Ast.Var (_, Ast.StaticVariable) -> true
        | Ast.Var (_, Ast.AutoVariable) -> true
        | _ -> false

    in let isTernary = function
        | 3 -> true
        | _ -> false

    in let hasSequencePoint = function
        | 5 | 4 | 1 -> true
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

    in let isDecl = function
        | L.INT32
        | L.STATIC
        | L.EXTERN -> true
        | _ -> false

    in let isDeclForInit = function
        | L.INT32 -> true
        | L.STATIC
        | L.EXTERN -> failwith "Cannot use storage class specifiers in for loop initializer declaration"
        | _ -> false

    in let rec parse_block_items env lvl = match nextToken() with
        | L.EOF -> raise (ParserError "Unmatched left brace")
        | L.RBRACE -> let _ = eatToken() in []
        | _ -> let (items, env') = (parse_block_item env lvl) in
               items @ parse_block_items env' lvl

    and parse_block_item env lvl = match nextToken() with
        | t when isDecl t ->
            let (item, env') = parse_decl env lvl in
            (Ast.D item :: (List.map (fun x -> Ast.S x) (flushPostfix())), env')

        | _ -> try (List.map (fun x -> Ast.S x) (parse_stmt env lvl), env)
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

    and parse_switch_body body =
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
            | Ast.Case (i32, _) ->
                let lbl = newLabel() in
                ([(i32, lbl)], Ast.Case (i32, lbl))

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
                let _ = eatToken() in
                let id = expectIdentifier() in

                if Environment.isInScope id lvl env then raise (ParserError (id ^ " is already a parameter"))
                else

                let newId = newVar id in
                let newEnv = Environment.add id (Environment.Var newId, lvl) env in

                if nextToken() = L.COMMA
                then let _ = eatToken() in inner (newId :: params) newEnv
                else (List.rev (newId :: params), newEnv)
            | t -> raise (ParserError ("Expected parameter, but got " ^ (L.string_of_token t)))
        in
        match nextToken() with
            | L.VOID -> let _ = eatToken() in ([], env)
            | _ -> inner [] env

    and parse_specifiers() =
        let rec iter typ storage = match nextToken() with
            | L.INT32 -> let _ = eatToken() in
                         if Option.is_some typ then raise (ParserError "Invalid type specifier")
                         else iter (Some ()) storage (* only int for now, so placeholder *)
            | L.EXTERN -> let _ = eatToken() in
                          if Option.is_some storage then raise (ParserError "Invalid storage class")
                          else iter typ (Some Ast.Extern)
            | L.STATIC -> let _ = eatToken() in
                          if Option.is_some storage then raise (ParserError "Invalid storage class")
                          else iter typ (Some Ast.Static)
            | _ -> (typ, storage)
        in let (typ, storage) = iter None None in
        if Option.is_none typ then raise (ParserError "No type specifier.") else
        (typ, storage)

    and parse_var_decl ?(common=None) env lvl =
        let (_, storage, id) = match common with
        | None ->
            let (typ, storage) = parse_specifiers() in 
            (typ, storage, expectIdentifier())
        | Some common -> common in

        let newId = newVar id in

        (*Because C Standard allows self-reference in midst of definition.........*)
        let initEnv = Environment.add id (Environment.Var newId, lvl) env in

        let expr = match nextToken() with
            | L.ASSIGN -> let _ = eatToken() in Some (parse_expr initEnv lvl)
            | _ -> None


        in let (newEnv, gEnv) = try Environment.tryAddVariable env !globalEnv lvl storage id newId expr
            with Environment.EnvironmentError s -> raise (ParserError s)
        in let () = globalEnv := gEnv

        in let () = expect L.SEMICOLON
        in (Ast.VarDecl (newId, expr, storage), newEnv)

    and parse_fun_decl ?(common=None) env lvl =
        let (_, storage, id) = match common with
        | None ->
            let (typ, storage) = parse_specifiers() in 
            (typ, storage, expectIdentifier())
        | Some common -> common in

        let storage = match storage with None -> Ast.Extern | Some s -> s in

        (* Parse parameters *)
        let tempEnv = Environment.add id
            ((Environment.Func (id, 69, false)),
             lvl)
            env in

        let () = expect L.LPAREN in
        let (params, paramsEnv) = parse_params tempEnv (lvl+1) in
        let () = expect L.RPAREN in
        (*-------------------*)

        (* Parse body*)
        let bodyEnv = match Option.get (Environment.find_opt id paramsEnv) with
            | (Environment.Func _, _) -> 
                Environment.add id
                ((Environment.Func (id, List.length params, true(*doesn't matter. Definitions are not allowed in body.*))),
                 lvl)
                paramsEnv
            | _ -> paramsEnv (* A parameter shadowed the function declaration *)

        in let body = match nextToken() with
            | L.LBRACE -> let _ = eatToken() in Some (parse_block_items bodyEnv (lvl+1))
            | _ -> let () = expect L.SEMICOLON in None
        in
        (*-----------------------*)


        let (newEnv, gEnv) = try Environment.tryAddFunction env !globalEnv lvl storage id (List.length params) body
            with Environment.EnvironmentError s -> raise (ParserError s)
        in let () = globalEnv := gEnv

        (*define the name globally*)
        in (Ast.FunDecl (id, params, body, storage), newEnv)

    and parse_decl env lvl = 
        let (typ, storage) = parse_specifiers() in
        let id = expectIdentifier() in

        match nextToken() with
            | L.LPAREN -> parse_fun_decl ~common:(Some (typ, storage, id)) env lvl
            | _ -> parse_var_decl ~common:(Some (typ, storage, id)) env lvl


    and parse_stmt env lvl =
        let result = match nextToken() with
        | L.RETURN -> let _ = eatToken() in let r = Ast.Return (parse_expr env lvl) in let () = expect L.SEMICOLON in [r]
        | L.SEMICOLON -> let () = expect L.SEMICOLON in [Ast.Null]
        | L.IF ->
            let _ = eatToken() in
            let () = expect L.LPAREN in
            let cond = parse_expr env lvl in
            let () = expect L.RPAREN in
            let postfixAfterCond = flushPostfix() in
            let true_branch = (parse_stmt env lvl) |> list_to_stmt  in
            let else_branch =
                if nextToken() = L.ELSE then
                    let _ = eatToken() in
                    Some ((parse_stmt env lvl) |> list_to_stmt)
                else None
            in [Ast.If ((cond, postfixAfterCond), true_branch, else_branch)]

        | L.CASE -> let _ = eatToken() in
                    let i32 = expectConstExpr() in
                    let _ = expect L.COLON in
                    (Ast.Case (i32, dummyCase)) :: parse_stmt env lvl (*C17 labelled statements*)
        | L.DEFAULT -> let _ = eatToken() in let _ = expect L.COLON in
                (Ast.Default dummyCase) :: parse_stmt env lvl (*C17 labelled statements*)
        | L.SWITCH ->
            let _ = eatToken() in
            let () = expect L.LPAREN in
            let cond = parse_expr env lvl in
            let () = expect L.RPAREN in
            let postfixAfterCond = flushPostfix() in
            let stmt = list_to_stmt (parse_stmt env lvl) in
            let (cases, body, default_opt) = parse_switch_body stmt in
            let break = newLabel() in
            let default = (match default_opt with None -> break | Some d -> d) in
            [Ast.Switch ((cond, postfixAfterCond), List.rev cases, body, break, default)]

        | L.WHILE ->
            let _ = eatToken() in
            let () = expect L.LPAREN in
            let cond = parse_expr env lvl in
            let () = expect L.RPAREN in
            let postfixAfterCond = flushPostfix() in
            let body = (parse_stmt env lvl) |> list_to_stmt
            in [Ast.While ((cond, postfixAfterCond), body, dummyLabel)]

        | L.DO ->
            let _ = eatToken() in
            let body = (parse_stmt env lvl) |> list_to_stmt in
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
            let body = (parse_stmt newEnv (lvl+1)) |> list_to_stmt
            in [Ast.For (init, cond, post, body, dummyLabel)]


        | L.LBRACE -> let _ = eatToken() in [Ast.Compound (parse_block_items env (lvl+1))]
        | L.GOTO -> let _ = eatToken() in let id = expectIdentifier() in let () = expect L.SEMICOLON in [Ast.Goto id]
        | L.BREAK -> let _ = eatToken() in let _ = expect L.SEMICOLON in [Ast.Break (snd dummyLabel)]
        | L.CONTINUE -> let _ = eatToken() in let _ = expect L.SEMICOLON in [Ast.Continue (fst dummyLabel)]

        (*Label. They are kind of not statements, but no one uses goto so it doesn't deserve its own type.*)
        | L.ID lbl when nextNextToken() = L.COLON ->
(* C23 *)(* let _ = eatToken() in let _ = eatToken() in [Ast.Label lbl] *)
            let _ = eatToken() in let _ = eatToken() in (Ast.Label lbl) :: (parse_stmt env lvl)

        | _ -> try let r = Ast.Expression (parse_expr env lvl) in let () = expect L.SEMICOLON in [r]
            with ParserError e -> raise (ParserError ("Expected statement\n" ^ e))
        in result @ flushPostfix()

    and parse_args env lvl count =
        let original = string_of_int count in
        let rec iter count no_comma = match nextToken() with
            | L.RPAREN when no_comma ->
                if count > 0 then raise (ParserError ("Argument count is more than " ^ original))
                else let _ = eatToken() in []
            | _ ->
                if count <= 0 then raise (ParserError ("Argument count is less than " ^ original)) else
                let arg = parse_expr env lvl in
                begin match nextToken() with
                    | L.COMMA -> let _ = eatToken() in arg :: (iter (count-1) false)
                    | _ -> arg :: (iter (count-1) true)
                end
        in iter count true

    and parse_primary env lvl =
        let t = eatToken() in
        match t with
            | L.INT32_LIT num -> Ast.Int32 num
            | L.LPAREN -> let expr = parse_expr env lvl in
                          let () = expect L.RPAREN in
                          expr
            | L.ID id -> begin
                let () = Environment.globalEnvString !globalEnv in
                match Environment.find_opt id env with
                    | None -> raise (ParserError (id ^ " is not declared."))
                    | Some (decl, _) -> begin match decl with
                        | Environment.Var realId -> Ast.Var (realId, Ast.AutoVariable)
                        | Environment.StaticVar realId -> Ast.Var (realId, Ast.StaticVariable)
                        | Environment.Func (id, paramCount, _) -> Ast.Var (id, Ast.Function paramCount)
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
                iter (nextToken()) (Ast.Unary (Ast.Rvalue, left))
            | L.DECREMENT ->
                if not (isVar left) then raise (ParserError "Suffix Increment operator rhs is not an lvalue") else
                let _ = eatToken() in
                let () = schedulePostfixDecr left in
                iter (nextToken()) (Ast.Unary (Ast.Rvalue, left))
            | L.LPAREN ->
                let id, count = begin match left with Ast.Var (id, Ast.Function count) -> id, count | _ -> raise (ParserError "Cannot call a variable.") end in
                let _ = eatToken() in
                let args = parse_args env lvl count in
                iter (nextToken()) (Ast.Call (id, args))

            | _ -> (*functions cannot be an expression past this point*)
                begin match left with
                    | Ast.Var (_, Ast.Function _) -> raise (ParserError "Cannot use function as a variable.")
                    | _ -> left
                end

        in iter (nextToken()) primary

    and parse_unary env lvl = match nextToken() with
        | L.PLUS -> let _ = eatToken() in Ast.Unary (Ast.Rvalue, parse_unary env lvl)
        | L.MINUS -> let _ = eatToken() in Ast.Unary (Ast.Negate, parse_unary env lvl)
        | L.COMPLEMENT -> let _ = eatToken() in Ast.Unary (Ast.Complement, parse_unary env lvl)
        | L.BANG -> let _ = eatToken() in Ast.Unary (Ast.LogNot, parse_unary env lvl)
        | L.INCREMENT ->
            let _ = eatToken() in 
            let right = parse_unary env lvl in
            let () = begin match right with Ast.Var _ -> () | _ -> raise (ParserError "Prefix Increment operator rhs is not an lvalue") end in
            Ast.Unary (Ast.Increment, right)
        | L.DECREMENT -> 
            let _ = eatToken() in 
            let right = parse_unary env lvl in
            let () = begin match right with Ast.Var _ -> () | _ -> raise (ParserError "Prefix Decrement operator rhs is not an lvalue") end in
            Ast.Unary (Ast.Decrement, right)
        | _ -> try parse_postfix env lvl
               with ParserError e -> raise (ParserError ("Expected unary\n"^e))

    and parse_expr ?(min_prec=0) env lvl : (Ast.expr) =
        let left = parse_unary env lvl in
        let peek = nextToken() in
        let rec iter peekToken left = let p = prec(peekToken) in
            if p >= min_prec then(
                if isAssign p then
                    let op = eatToken() |> parseOp in

                    let () = match left with Ast.Var _ -> () | _ -> raise (ParserError "Expected an lvalue") in
                    let right = parse_expr ~min_prec:p env lvl in
                    match op with
                        | Ast.Assign -> iter (nextToken()) (Ast.Assignment (left, right))
                        | _ -> iter (nextToken()) (Ast.BinaryAssign (op, left, right))

                else if isTernary p then
                    let _ = eatToken() in
                    let th = Ast.Unary(Ast.Rvalue, parse_expr ~min_prec:0 env lvl) in
                    let () = expect L.COLON in
                    let el = Ast.Unary(Ast.Rvalue, parse_expr ~min_prec:p env lvl) in
                    let postfix = flushPostfix() in
                    iter (nextToken()) (Ast.Ternary ((left, postfix), th, el))

                else if hasSequencePoint p then
                    let op = eatToken() |> parseOpSp in
                    let between = flushPostfix() in
                    let right = parse_expr ~min_prec:(p+1) env lvl in
                    iter (nextToken()) (Ast.BinarySp (op, (left, between), right))

                else
                    let op = eatToken() |> parseOp in

                    let right = parse_expr ~min_prec:(p+1) env lvl in
                    iter (nextToken()) (Ast.Binary (op, left, right))
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

