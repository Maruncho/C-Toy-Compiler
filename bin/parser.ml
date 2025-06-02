
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

    in let parseOp = function
        | L.PLUS -> Ast.Add
        | L.MINUS -> Ast.Sub
        | L.ASTERISK -> Ast.Mul
        | L.SLASH -> Ast.Div
        | L.PERCENT -> Ast.Mod
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

    in let prec = function
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

    in let rec parse_stmt() =
        let parse_return() = Ast.Return (parse_expr 0) in
        let result = match eatToken() with
        | L.RETURN -> parse_return()

        | _ -> raise (ParserError "Expected statement")
        in let () = expect L.SEMICOLON in result

    and parse_factor() = match eatToken() with
        | L.INT32_LIT num -> Ast.Int32 num

        | L.PLUS -> parse_factor()
        | L.MINUS -> Ast.Unary (Ast.Negate, parse_factor())
        | L.COMPLEMENT -> Ast.Unary (Ast.Complement, parse_factor())
        | L.BANG -> Ast.Unary (Ast.LogNot, parse_factor())

        | L.LPAREN -> let expr = parse_expr 0 in
                      let () = expect L.RPAREN in
                      expr

        | _ -> raise (ParserError "Expected factor")

    and parse_expr min_prec =
        let left = parse_factor() in
        let peek = nextToken() in
        let rec iter peekToken left = let p = prec(peekToken) in
            if p >= min_prec then
                let op = eatToken() |> parseOp in
                let right = parse_expr (p+1) in
                iter (nextToken()) (Ast.Binary (op, left, right))
            else
                left
        in iter peek left



    and parse_program() =
        let () = expect INT32 in
        let () = expect (ID "main") in
        let () = expect LPAREN in
        let () = expect VOID in
        let () = expect RPAREN in
        let () = expect LBRACE in
        let result = Ast.Program(Ast.Function ("main", parse_stmt())) in
        let () = expect RBRACE in
        let () = expect EOF in
        result

    in parse_program()

