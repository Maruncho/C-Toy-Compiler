
module L = Lexer

exception ParserError of string

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

    in let tmpNum = ref 0
    in let newVar id = (let t = id ^ "." ^ (string_of_int (!tmpNum)) in let () = tmpNum := !tmpNum + 1 in t)

    in let expectIdentifier() = match eatToken() with
                    L.ID id -> id
                    | _ as t -> raise (ParserError ("Expected identifier, but got " ^ (L.string_of_token t)))

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

    in let rec parse_block_items env lvl = match nextToken() with
        | L.EOF -> raise (ParserError "Unmatched left brace")
        | L.RBRACE -> let _ = eatToken() in []
        | _ -> let (items, env') = (parse_block_item env lvl) in
               items @ parse_block_items env' lvl

    and parse_block_item env lvl = match nextToken() with
        | L.INT32 -> let (item, env') = parse_decl env lvl in
                     (Ast.D item :: (List.map (fun x -> Ast.S x) (flushPostfix())), env')

        | _ -> try (List.map (fun x -> Ast.S x) (parse_stmt env lvl), env)
        with ParserError e -> raise (ParserError ("Expected statement/declaration\n"^e))

    and parse_for_init env lvl = match nextToken() with
        | L.SEMICOLON -> let _ = eatToken() in None, env
        | L.INT32 -> let (item, env') = parse_decl env lvl in
                     (Some (Ast.InitDecl (item, flushPostfix())), env')

        | _ -> try (
            let r = parse_expr env lvl in
            let r = Some (Ast.InitExpr (r, flushPostfix())) in let () = expect L.SEMICOLON in r, env
        )
        with ParserError e -> raise (ParserError ("Expected statement/declaration\n"^e))

    and parse_decl env lvl =
        let _ = eatToken() in
        let id = expectIdentifier() in

        if Environment.isInScope id lvl env then raise (ParserError (id ^ " is already in scope"))
        else

        let newId = newVar id in
        let newEnv = Environment.add id (newId, lvl) env in

        let expr = match nextToken() with
            | L.ASSIGN -> let _ = eatToken() in Some (parse_expr newEnv lvl)
            | _ -> None

        in let () = expect L.SEMICOLON
        in (Ast.Declaration (newId, expr), newEnv)

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

    and parse_primary env lvl =
        let t = eatToken() in
        match t with
            | L.INT32_LIT num -> Ast.Int32 num
            | L.LPAREN -> let expr = parse_expr env lvl in
                          let () = expect L.RPAREN in
                          expr
            | L.ID id -> begin
                match Environment.find_opt id env with
                    | None -> raise (ParserError (id ^ " is not declared."))
                    | Some (realId, _) -> Ast.Var realId
            end
            | _ -> raise (ParserError ("Expected primary, but got " ^ L.string_of_token t))

    and parse_postfix env lvl =
        let primary = parse_primary env lvl in
        let rec iter peekToken left = match peekToken with
            | L.INCREMENT ->
                let () = begin match left with Ast.Var _ -> () | _ -> raise (ParserError "Suffix Increment operator rhs is not an lvalue") end in
                let _ = eatToken() in
                let () = schedulePostfixIncr left in
                iter (nextToken()) (Ast.Unary (Ast.Rvalue, left))
            | L.DECREMENT ->
                let () = begin match left with Ast.Var _ -> () | _ -> raise (ParserError "Suffix Decrement operator rhs is not an lvalue") end in
                let _ = eatToken() in
                let () = schedulePostfixDecr left in
                iter (nextToken()) (Ast.Unary (Ast.Rvalue, left))
            | _ -> left

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

    and parse_program() =
        let env = Environment.empty in

        let () = expect INT32 in
        let () = expect (ID "main") in
        let () = expect LPAREN in
        let () = expect VOID in
        let () = expect RPAREN in
        let () = expect LBRACE in
        let result = Ast.Program(Ast.Function ("main", parse_block_items env 1)) in
        let () = expect EOF in
        result

    in try parse_program() |> SemantGoto.parse |> SemantBreakContinue.parse with 
        | SemantGoto.ParserError e -> raise (ParserError e)
        | SemantBreakContinue.ParserError e -> raise (ParserError e)

