
exception NotMatched
exception LexError of string

type token =
    | ID of string
    | INT32_LIT of Int32.t
    | INT32
    | VOID
    | RETURN
    | LPAREN
    | RPAREN
    | LBRACE
    | RBRACE
    | SEMICOLON
    | MINUS
    | COMPLEMENT
    | DECREMENT
    | EOF

let string_of_token = function
    | ID str -> "ID " ^ str
    | INT32_LIT num -> (Int32.to_string num)
    | INT32 -> "int"
    | VOID -> "void"
    | RETURN -> "return"
    | LPAREN -> "("
    | RPAREN -> ")"
    | LBRACE -> "{"
    | RBRACE -> "}"
    | SEMICOLON -> ";"
    | MINUS -> "-"
    | COMPLEMENT -> "~"
    | DECREMENT -> "--"
    | EOF -> "eof"

let re regex = Re.seq [Re.bos; Re.Perl.re regex; Re.Perl.re {|((?:.|\s)*)|}] |> Re.compile

let token_regexes =
[
    (* Identifiers and keywords *)
    (re {|([a-zA-Z_]\w*)\b|},
    (fun str -> match str with
        | "int" -> INT32
        | "void" -> VOID
        | "return" -> RETURN
        | _ -> ID str))
;
    (* Integer32 *)
    (re {|([0-9]+)\b|}, (fun str -> INT32_LIT (Int32.of_string str)))
;
    (* ( *)
    (re {|(\()|}, (fun _ -> LPAREN))
;
    (* ) *)
    (re {|(\))|}, (fun _ -> RPAREN))
;
    (* { *)
    (re {|(\{)|}, (fun _ -> LBRACE))
;
    (* } *)
    (re {|(\})|}, (fun _ -> RBRACE))
;
    (* ; *)
    (re {|(;)|}, (fun _ -> SEMICOLON))
;
    (* -- *)
    (re {|(--)|}, (fun _ -> DECREMENT))
;
    (* - *)
    (re {|(-)|}, (fun _ -> MINUS))
;
    (* ~ *)
    (re {|(~)|}, (fun _ -> COMPLEMENT))
]

let match_opt regex text = match Re.exec_opt regex text with
    | None -> None
    | Some g -> Some (Re.Group.get g 1, (Re.Group.get g 2) |> String.trim)

let rec match_a_regex pairs text = match pairs with
    | [] -> raise NotMatched
    | (regex, tokenize) :: rest -> begin match match_opt regex text with
        | None -> match_a_regex rest text
        | Some (matched, afterText) -> (tokenize matched, afterText)
    end

let rec lex ?(print=false) program = let program = (String.trim program) in
    if program = String.empty then [EOF] else
    match match_a_regex token_regexes program with
        | (token, afterText) -> 
            let () = if print then print_string ((string_of_token token) ^ "\n")
            in token :: (lex ~print:print afterText)
        | exception NotMatched -> raise (LexError "Syntax error")
