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

let print_source_context file line =
    let lines = try
        let ch = open_in file in
        let content = In_channel.input_all ch in
        close_in ch;
        Some (String.split_on_char '\n' content |> Array.of_list)
    with _ -> None in
    match lines with
    | Some lines ->
        let start = max 0 (line - 3) in
        let finish = min (Array.length lines - 1) (line + 1) in
        for i = start to finish do
            let marker = if i + 1 = line then ">" else " " in
            print_string_err (marker ^ " " ^ string_of_int (i + 1) ^ " | " ^ lines.(i) ^ "\n")
        done
    | None -> ()

let contents = Core.In_channel.read_all file

let () = try
    let lexed = Lexer.lex contents in
    let _ = if m = Lex then (exit 0) in

    let (parsed, globalEnv) = Parser.parse lexed in
    let _ = Ast.printProgram parsed in
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
    | Lexer.LexError m ->
        let () = print_source_context !Lexer.currentFile !Lexer.currentLine in
        print_string_err (m ^ "\n"); exit 1;
    | Parser.ParserError m ->
        let () = print_source_context !Parser.currentFile !Parser.currentLine in
        print_string_err (!Parser.currentFile ^ ":" ^ string_of_int (!Parser.currentLine) ^ ": " ^ m ^ "\n"); exit 1;
    | Tackify.TackyError m -> print_string_err (m ^ "\n"); exit 1;
