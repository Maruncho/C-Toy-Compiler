type mode = Lex | Parse | Codegen | Tacky | Free

let m = if Core.Array.length (Core.Sys.get_argv()) >= 3 then
    (match (Core.Sys.get_argv()).(2) with
    | "--lex" -> Lex
    | "--validate"
    | "--parse" -> Parse
    | "--codegen" -> Codegen
    | "--tacky" -> Tacky
    | _ -> Free)
else Free

let file = if Core.Array.length (Core.Sys.get_argv()) >= 2 then
        (Core.Sys.get_argv()).(1)
else "./example.c"

let print_string_err = Out_channel.output_string (Out_channel.stderr)

let contents = Core.In_channel.read_all file

let () = try
    let lexed = Lexer.lex contents in
    let _ = if m = Lex then (exit 0) in

    let (parsed, globalEnv) = Parser.parse lexed in
    (*let _ = Ast.printProgram parsed in*)
    (*let () = Environment.globalEnvString globalEnv in*)
    let _ = if m = Parse then (exit 0) in

    let (tacky, externalNames) = Tackify.tackify parsed globalEnv in
    let _ = print_string (Tacky.string_of_tacky tacky) in
    let _ = if m = Tacky then (exit 0) in

    let asmt = Assemble.assemble tacky in
    let _ = if m = Codegen then (exit 0) in

    let assembly = Asmt.string_of_asmt_debug asmt externalNames in
    let _ = print_string assembly in
    let outputFile = (String.sub file 0 ((String.length file) - 2)) ^ ".s"
    in Core.Out_channel.output_string (Core.Out_channel.create outputFile) assembly
with
    | Lexer.LexError m -> print_string_err (m ^ "\n"); exit 1;
    | Parser.ParserError m -> print_string_err (m ^ "\n"); exit 1;
    | Tackify.TackyError m -> print_string_err (m ^ "\n"); exit 1;
