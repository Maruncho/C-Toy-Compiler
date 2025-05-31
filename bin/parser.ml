
module L = Lexer

exception ParserError of string

let parse tokens =
    let tokens = ref tokens
    (*in let nextToken() = match !tokens with*)
    (*        | [] -> failwith "Went beyond EOF"*)
    (*        | t :: _ -> t*)
    in let eatToken() = match !tokens with
            | [] -> failwith "Trying to eat beyond EOF"
            | h :: t -> let () = tokens := t in h
    in let expect expected = let t = eatToken() in if t <> expected then
                             raise (ParserError ("Expected " ^ (L.string_of_token expected) ^ ", but got " ^ (L.string_of_token t)))

    in let rec parse_stmt() =
        let parse_return() = Ast.Return (parse_expr()) in
        let result = match eatToken() with
        | L.RETURN -> parse_return()

        | _ -> raise (ParserError "Expected statement")
        in let () = expect L.SEMICOLON in result

    and parse_expr() = match eatToken() with
        | L.INT32_LIT num -> Ast.Int32 num

        | L.MINUS -> Ast.Unary (Ast.Negate, parse_expr())
        | L.COMPLEMENT -> Ast.Unary (Ast.Complement, parse_expr())

        | L.LPAREN -> let expr = parse_expr() in
                      let () = expect L.RPAREN in
                      expr

        | _ -> raise (ParserError "Expected expression")

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

