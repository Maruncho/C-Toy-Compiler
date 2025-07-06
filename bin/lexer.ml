
exception NotMatched
exception LexError of string

type token =
    | ID of string
    | INT32_LIT of Z.t
    | INT64_LIT of Z.t
    | INT
    | LONG
    | VOID
    | IF
    | ELSE
    | GOTO
    | RETURN
    | DO
    | WHILE
    | FOR
    | BREAK
    | CONTINUE
    | SWITCH
    | CASE
    | DEFAULT
    | STATIC
    | EXTERN
    | LPAREN
    | RPAREN
    | LBRACE
    | RBRACE
    | COLON
    | SEMICOLON
    | QUESTION
    | PLUS
    | MINUS
    | ASTERISK
    | SLASH
    | PERCENT
    | AMPERSAND
    | PIPE
    | CARET
    | LSHIFT
    | RSHIFT
    | COMPLEMENT
    | INCREMENT
    | DECREMENT
    | BANG
    | LOGAND
    | LOGOR
    | EQUAL
    | NOTEQUAL
    | LESS
    | GREATER
    | LESSEQ
    | GREATEREQ
    | ASSIGN
    | PLUSASSIGN
    | MINUSASSIGN
    | ASTERISKASSIGN
    | SLASHASSIGN
    | PERCENTASSIGN
    | AMPERSANDASSIGN
    | PIPEASSIGN
    | CARETASSIGN
    | LSHIFTASSIGN
    | RSHIFTASSIGN
    | COMMA
    | EOF

let string_of_token = function
    | ID str -> "ID " ^ str
    | INT32_LIT num -> (Z.to_string num)
    | INT64_LIT num -> (Z.to_string num)
    | INT -> "int"
    | LONG -> "long"
    | VOID -> "void"
    | IF -> "if"
    | ELSE -> "else"
    | RETURN -> "return"
    | GOTO -> "goto"
    | DO -> "do"
    | WHILE -> "while"
    | FOR -> "for"
    | BREAK -> "break"
    | CONTINUE -> "continue"
    | SWITCH -> "switch"
    | CASE -> "case"
    | DEFAULT -> "default"
    | STATIC -> "static"
    | EXTERN -> "extern"
    | LPAREN -> "("
    | RPAREN -> ")"
    | LBRACE -> "{"
    | RBRACE -> "}"
    | COLON -> ":"
    | SEMICOLON -> ";"
    | QUESTION -> "?"
    | PLUS -> "+"
    | MINUS -> "-"
    | ASTERISK -> "*"
    | SLASH -> "/"
    | PERCENT -> "%"
    | AMPERSAND -> "&"
    | PIPE -> "|"
    | CARET -> "^"
    | LSHIFT -> "<<"
    | RSHIFT -> ">>"
    | COMPLEMENT -> "~"
    | INCREMENT -> "++"
    | DECREMENT -> "--"
    | BANG -> "!"
    | LOGAND -> "&&"
    | LOGOR -> "||"
    | EQUAL -> "=="
    | NOTEQUAL -> "!="
    | LESS -> "<"
    | GREATER -> ">"
    | LESSEQ -> "<="
    | GREATEREQ -> ">="
    | ASSIGN -> "="
    | PLUSASSIGN -> "+="
    | MINUSASSIGN -> "-="
    | ASTERISKASSIGN -> "*="
    | SLASHASSIGN -> "/="
    | PERCENTASSIGN -> "%="
    | AMPERSANDASSIGN -> "&="
    | PIPEASSIGN -> "|="
    | CARETASSIGN -> "^="
    | LSHIFTASSIGN -> "<<="
    | RSHIFTASSIGN -> ">>="
    | COMMA -> ","
    | EOF -> "eof"

let re regex = Re.seq [Re.bos; Re.Perl.re regex; Re.Perl.re {|((?:.|\s)*)|}] |> Re.compile

let token_regexes =
[
    (* Identifiers and keywords *)
    (re {|([a-zA-Z_]\w*)\b|},
    (fun str -> match str with
        | "int" -> INT
        | "long" -> LONG
        | "void" -> VOID
        | "if" -> IF
        | "else" -> ELSE
        | "return" -> RETURN
        | "do" ->  DO
        | "while" -> WHILE
        | "for" -> FOR
        | "break" -> BREAK
        | "continue" -> CONTINUE
        | "goto" -> GOTO
        | "switch" -> SWITCH
        | "case" -> CASE
        | "default" -> DEFAULT
        | "static" -> STATIC
        | "extern" -> EXTERN
        | _ -> ID str))
;
    (* Integer64 *)
    (re {|([0-9]+)[lL]\b|}, (fun str -> INT64_LIT (Z.of_string str)))
;
    (* Integer32 *)
    (re {|([0-9]+)\b|}, (fun str -> INT32_LIT (Z.of_string str)))
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
    (* : *)
    (re {|(:)|}, (fun _ -> COLON))
;
    (* ; *)
    (re {|(;)|}, (fun _ -> SEMICOLON))
;
    (* ? *)
    (re {|(\?)|}, (fun _ -> QUESTION))
;
    (* == *)
    (re {|(==)|}, (fun _ -> EQUAL))
;
    (* != *)
    (re {|(!=)|}, (fun _ -> NOTEQUAL))
;
    (* <= *)
    (re {|(<=)|}, (fun _ -> LESSEQ))
;
    (* >= *)
    (re {|(>=)|}, (fun _ -> GREATEREQ))
;
    (* += *)
    (re {|(\+=)|}, (fun _ -> PLUSASSIGN))
;
    (* -= *)
    (re {|(-=)|}, (fun _ -> MINUSASSIGN))
;
    (* *= *)
    (re {|(\*=)|}, (fun _ -> ASTERISKASSIGN))
;
    (* /= *)
    (re {|(\/=)|}, (fun _ -> SLASHASSIGN))
;
    (* %= *)
    (re {|(%=)|}, (fun _ -> PERCENTASSIGN))
;
    (* &= *)
    (re {|(&=)|}, (fun _ -> AMPERSANDASSIGN))
;
    (* |= *)
    (re {|(\|=)|}, (fun _ -> PIPEASSIGN))
;
    (* ^= *)
    (re {|(\^=)|}, (fun _ -> CARETASSIGN))
;
    (* <<= *)
    (re {|(<<=)|}, (fun _ -> LSHIFTASSIGN))
;
    (* >>= *)
    (re {|(>>=)|}, (fun _ -> RSHIFTASSIGN))
;
    (* = *)
    (re {|(=)|}, (fun _ -> ASSIGN))
;
    (* && *)
    (re {|(&&)|}, (fun _ -> LOGAND))
;
    (* || *)
    (re {|(\|\|)|}, (fun _ -> LOGOR))
;
    (* ++ *)
    (re {|(\+\+)|}, (fun _ -> INCREMENT))
;
    (* -- *)
    (re {|(--)|}, (fun _ -> DECREMENT))
;
    (* - *)
    (re {|(-)|}, (fun _ -> MINUS))
;
    (* + *)
    (re {|(\+)|}, (fun _ -> PLUS))
;
    (* * *)
    (re {|(\*)|}, (fun _ -> ASTERISK))
;
    (* / *)
    (re {|(\/)|}, (fun _ -> SLASH))
;
    (* % *)
    (re {|(%)|}, (fun _ -> PERCENT))
;
    (* & *)
    (re {|(&)|}, (fun _ -> AMPERSAND))
;
    (* | *)
    (re {|(\|)|}, (fun _ -> PIPE))
;
    (* ^ *)
    (re {|(\^)|}, (fun _ -> CARET))
;
    (* << *)
    (re {|(<<)|}, (fun _ -> LSHIFT))
;
    (* >> *)
    (re {|(>>)|}, (fun _ -> RSHIFT))
;
    (* ~ *)
    (re {|(~)|}, (fun _ -> COMPLEMENT))
;
    (* ! *)
    (re {|(!)|}, (fun _ -> BANG))
;
    (* < *)
    (re {|(<)|}, (fun _ -> LESS))
;
    (* > *)
    (re {|(>)|}, (fun _ -> GREATER))
;
    (* , *)
    (re {|(,)|}, (fun _ -> COMMA))
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
        | exception NotMatched -> raise (LexError ("Syntax error. Unknown symbol: " ^ (String.sub program 0 1)))
