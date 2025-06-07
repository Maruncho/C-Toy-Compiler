
exception ParserError of string

let parse (program:Ast.program) =
    let tmpNum = ref 0
    in let newLabel() = let t = ".LL" ^ (string_of_int (!tmpNum))
                         in let () = tmpNum := !tmpNum + 1 in t

    in let rec parseStatement stmt last = match stmt with
        | Ast.Break _ -> begin match last with
            | None -> raise (ParserError "Cannot place a break statement here.")
            | Some (_, lbl) -> Ast.Break lbl
        end
        | Ast.Continue _ -> begin match last with
            | None -> raise (ParserError "Cannot place a continue statement here.")
            | Some (lbl, _) -> Ast.Continue lbl
        end

        | Ast.If (cond, th, Some el) -> Ast.If (cond, parseStatement th last, Some (parseStatement el last))
        | Ast.If (cond, th, None) -> Ast.If (cond, parseStatement th last, None)

        | Ast.Compound block -> Ast.Compound (parseBlock block last)

        | Ast.While (cond, body, _) ->
            let lbl = (newLabel(), newLabel()) in Ast.While (cond, parseStatement body (Some lbl), lbl)

        | Ast.DoWhile (body, cond, _) ->
            let lbl = (newLabel(), newLabel()) in Ast.DoWhile (parseStatement body (Some lbl), cond, lbl)

        | Ast.For (init, cond, post, body, _) ->
            let lbl = (newLabel(), newLabel()) in Ast.For (init, cond, post, (parseStatement body (Some lbl)), lbl)

        | stmt -> stmt


    and parseBlock block last = match block with
        | [] -> []
        | (Ast.S h) :: t -> let h = parseStatement h last in (Ast.S h) :: parseBlock t last
        | h :: t -> h :: (parseBlock t last)

    in let parseToplevel = function
        | Ast.Function (name, body) -> Ast.Function (name, parseBlock body None)
    in
    match program with
        | Ast.Program toplevel -> Ast.Program (parseToplevel toplevel)
