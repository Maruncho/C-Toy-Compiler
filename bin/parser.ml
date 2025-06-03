
module L = Lexer

exception ParserError of string

let parse tokens =
    let tokens = ref tokens
    in let nextToken() = match !tokens with
            | [] -> failwith "Went beyond EOF"
            | t :: _ -> t
    in let eatToken() = match !tokens with
            | [] -> failwith "Trying to eat beyond EOF"
            | h :: t -> let () = tokens := t in h
    in let expect expected = let t = eatToken() in if t <> expected then
                             raise (ParserError ("Expected " ^ (L.string_of_token expected) ^ ", but got " ^ (L.string_of_token t)))

    in let tmpNum = ref 0
    in let newVar id = (let t = id ^ "." ^ (string_of_int (!tmpNum)) in let () = tmpNum := !tmpNum + 1 in t)

    in let expectIdentifier() = match eatToken() with
                    L.ID id -> id
                    | _ as t -> raise (ParserError ("Expected identifier, but got " ^ (L.string_of_token t)))

    in let parseOp = function
        | L.PLUS -> Ast.Add
        | L.MINUS -> Ast.Sub
        | L.ASTERISK -> Ast.Mul
        | L.SLASH -> Ast.Div
        | L.PERCENT -> Ast.Mod
        | L.ASSIGN -> Ast.Assign
        | L.PIPE -> Ast.Or
        | L.AMPERSAND -> Ast.And
        | L.CARET -> Ast.Xor
        | L.LSHIFT -> Ast.Lshift
        | L.RSHIFT -> Ast.Rshift
        | L.LOGAND -> Ast.LogAnd
        | L.LOGOR -> Ast.LogOr
        | L.EQUAL -> Ast.Eq
        | L.NOTEQUAL -> Ast.Neq
        | L.LESS -> Ast.Lt
        | L.LESSEQ -> Ast.Le
        | L.GREATER -> Ast.Gt
        | L.GREATEREQ -> Ast.Ge
        | token -> raise (ParserError ("Invalid operator " ^ (Lexer.string_of_token token)))

    in let isAssign = function
        | Ast.Assign -> true
        | _ -> false

    in let prec = function
        | L.ASSIGN -> 2
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
        | _ -> let (item, env') = (parse_block_item env lvl) in
               item :: parse_block_items env' lvl

    and parse_block_item env lvl = match nextToken() with
        | L.INT32 -> let (item, env') = parse_decl env lvl in
                     (Ast.D (item), env')

        | _ -> try (S (parse_stmt env lvl), env)
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
        in (Ast.Declaration (newId, expr)), newEnv

    and parse_stmt env lvl =
        let result = match nextToken() with
        | L.RETURN -> let _ = eatToken() in Ast.Return (parse_expr env lvl)
        | L.SEMICOLON -> Ast.Null

        | _ -> try Ast.Expression (parse_expr env lvl)
            with ParserError e ->raise (ParserError ("Expected statement\n" ^ e))
        in let () = expect L.SEMICOLON in result

    and parse_factor env lvl = match eatToken() with
        | L.INT32_LIT num -> Ast.Int32 num

        | L.ID id -> begin
            match Environment.find_opt id env with
                | None -> raise (ParserError (id ^ " is not declared."))
                | Some (realId, _) -> Ast.Var realId
        end

        | L.PLUS -> parse_factor env lvl
        | L.MINUS -> Ast.Unary (Ast.Negate, parse_factor env lvl)
        | L.COMPLEMENT -> Ast.Unary (Ast.Complement, parse_factor env lvl)
        | L.BANG -> Ast.Unary (Ast.LogNot, parse_factor env lvl)

        | L.LPAREN -> let expr = parse_expr env lvl in
                      let () = expect L.RPAREN in
                      expr

        | _ -> raise (ParserError "Expected factor")

    and parse_expr ?(min_prec=0) env lvl =
        let left = parse_factor env lvl in
        let peek = nextToken() in
        let rec iter peekToken left = let p = prec(peekToken) in
            if p >= min_prec then
                let op = eatToken() |> parseOp in

                if isAssign op then
                    let () = match left with Ast.Var _ -> () | _ -> raise (ParserError "Expected an lvalue") in
                    let right = parse_expr ~min_prec:p env lvl in
                    iter (nextToken()) (Ast.Assignment (left, right))

                else
                    let right = parse_expr ~min_prec:(p+1) env lvl in
                    iter (nextToken()) (Ast.Binary (op, left, right))
            else
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

    in parse_program()

