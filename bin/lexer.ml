
exception NotMatched
exception LexError of string

type token =
    | ID of string
    | INT32_LIT of Z.t
    | INT64_LIT of Z.t
    | UINT32_LIT of Z.t
    | UINT64_LIT of Z.t
    | DOUBLE_LIT of float
    | CHAR_LIT of string
    | STRING_LIT of string
    | CHAR
    | INT
    | LONG
    | SIGNED
    | UNSIGNED
    | DOUBLE
    | SIZEOF
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
    | LBRACK
    | RBRACK
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
    | UINT32_LIT num -> (Z.to_string num)
    | UINT64_LIT num -> (Z.to_string num)
    | DOUBLE_LIT num -> (Float.to_string num)
    | CHAR_LIT str -> "'" ^ str ^ "'"
    | STRING_LIT str -> "\"" ^ str ^ "\""
    | CHAR -> "char"
    | INT -> "int"
    | LONG -> "long"
    | SIGNED -> "signed"
    | UNSIGNED -> "unsigned"
    | DOUBLE -> "double"
    | SIZEOF -> "sizeof"
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
    | LBRACK -> "["
    | RBRACK -> "]"
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
let reLiteral regex = Re.seq [Re.bos; Re.Perl.re regex; Re.Perl.re {|([^\w.](?:.|\s)*)|}] |> Re.compile

let rec unescape_unOCamlable str =
    if String.length str < 2 then str else
    let ascii_code = match (String.sub str 0 2) with
        | "\\?" -> 63
        | "\\a" -> 7
        | "\\f" -> 12
        | "\\v" -> 11
        | _ -> -1
    in
    if ascii_code < 0 then
        let rest = unescape_unOCamlable (String.sub str 1 ((String.length str) - 1)) in
        (String.sub str 0 1) ^ rest
    else
        let rest = unescape_unOCamlable (String.sub str 2 ((String.length str) - 2)) in
        (String.make 1 (Char.chr ascii_code)) ^ rest

let fixDoubleQuote = function
    | "\"" -> "\\\""
    | x -> x


let token_regexes =
[
    (* Identifiers and keywords *)
    (re {|([a-zA-Z_]\w*)\b|},
    (fun str -> match str with
        | "char" -> CHAR
        | "int" -> INT
        | "long" -> LONG
        | "signed" -> SIGNED
        | "unsigned" -> UNSIGNED
        | "double" -> DOUBLE
        | "sizeof" -> SIZEOF
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
    (* Double *)
    (reLiteral {|((?:[0-9]*\.[0-9]+|[0-9]+\.?)[Ee][+-]?[0-9]+|[0-9]*\.[0-9]+|[0-9]+\.)|}, (fun str -> DOUBLE_LIT (Float.of_string str)))
;
    (* Unsigned Integer64 *)
    (reLiteral {|([0-9]+)(?:[lL][uU]|[uU][lL])\b|}, (fun str -> UINT64_LIT (Z.of_string str)))
;
    (* Integer64 *)
    (reLiteral {|([0-9]+)[lL]\b|}, (fun str -> INT64_LIT (Z.of_string str)))
;
    (* Unsigned Integer32 *)
    (reLiteral {|([0-9]+)[uU]\b|}, (fun str -> UINT32_LIT (Z.of_string str)))
;
    (* Integer32 *)
    (reLiteral {|([0-9]+)\b|}, (fun str -> INT32_LIT (Z.of_string str)))
;
    (* Char *)
    (re {|'([^'\\\n]|\\['"?\\abfnrtv])'|}, (fun str -> CHAR_LIT (str |> fixDoubleQuote |> unescape_unOCamlable |> Scanf.unescaped)))
;
    (* String *)
    (re {|"((?:[^"\\\n]|\\['"\\?abfnrtv])*)"|}, (fun str -> STRING_LIT (str |> unescape_unOCamlable |> Scanf.unescaped)))
;
    (* ( *)
    (re {|(\()|}, (fun _ -> LPAREN))
;
    (* ) *)
    (re {|(\))|}, (fun _ -> RPAREN))
;
    (* [ *)
    (re {|(\[)|}, (fun _ -> LBRACK))
;
    (* ] *)
    (re {|(\])|}, (fun _ -> RBRACK))
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
