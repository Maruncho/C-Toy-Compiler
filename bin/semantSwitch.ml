
exception ParserError of string

module Env32 = Set.Make(struct type t = Int32.t let compare = Int32.compare end)

let parse (program:Ast.program) =
    let rec parseStatement stmt switch env default = match stmt with
        | Ast.Case (c, _) -> if not switch then raise (ParserError "Case statement cannot be outside of switch.")
                             else if Env32.mem c env then raise (ParserError ("Duplicate case " ^ (Int32.to_string c)))
                             else default, (Env32.add c env)
        | Ast.Default _ -> if not switch then raise (ParserError "Default statement cannot be outside of switch.")
                           else if default then raise (ParserError "Duplicate default.")
                           else true, env

        | Ast.If (_, th, Some el) ->
            let d1, env = parseStatement th switch env default in
            let d2, env =  parseStatement el switch env d1 in d2, env
        | Ast.If (_, th, None) ->
            let denv = parseStatement th switch env default in denv

        | Ast.Compound block ->
            let denv = parseBlock block switch env default in denv

        | Ast.While (_, body, _) ->
            let denv = parseStatement body switch env default in denv

        | Ast.DoWhile (body, _, _) ->
            let denv = parseStatement body switch env default in denv

        | Ast.For (_, _, _, body, _) ->
            let denv = parseStatement body switch env default in denv

        | Ast.Switch (_, _, stmt, _, _) ->
            let _ = parseStatement stmt true (Env32.empty) false in default, env

        | _ -> default, env


    and parseBlock block switch env default = match block with
        | [] -> default, env
        | (Ast.S h) :: t -> let d, env = parseStatement h switch env default in
                            parseBlock t switch env d
        | _ :: t -> parseBlock t switch env default

    in let parseToplevel = function
        | Ast.FunDecl (_, _, Some body, _) -> let _ = parseBlock body false (Env32.empty) false in ()
        | _ -> ()
    in
    match program with
        | Ast.Program toplevel -> List.iter (fun x -> parseToplevel x) toplevel
