
exception ParserError of string

let parse (program:Ast.program) =
    let tmpNum = ref 0
    in let newLabel() = let t = ".LL" ^ (string_of_int (!tmpNum))
                         in let () = tmpNum := !tmpNum + 1 in t

    in let rec parseStatement stmt last = match stmt with
        | Ast.Break _ -> begin match last with
            | (_, Some lbl) -> Ast.Break lbl
            | _ -> raise (ParserError "Cannot place a break statement here.")
        end
        | Ast.Continue _ -> begin match last with
            | (Some lbl, _) -> Ast.Continue lbl
            | _ -> raise (ParserError "Cannot place a continue statement here.")
        end

        | Ast.If (cond, th, Some el) -> Ast.If (cond, parseStatement th last, Some (parseStatement el last))
        | Ast.If (cond, th, None) -> Ast.If (cond, parseStatement th last, None)

        | Ast.Compound block -> Ast.Compound (parseBlock block last)

        | Ast.While (cond, body, _) ->
            let lbl = (newLabel(), newLabel()) in
            let lbl_opt = (Some (fst lbl), Some (snd lbl)) in
            Ast.While (cond, parseStatement body lbl_opt, lbl)

        | Ast.DoWhile (body, cond, _) ->
            let lbl = (newLabel(), newLabel()) in
            let lbl_opt = (Some (fst lbl), Some (snd lbl)) in
            Ast.DoWhile (parseStatement body lbl_opt, cond, lbl)

        | Ast.For (init, cond, post, body, _) ->
            let lbl = (newLabel(), newLabel()) in
            let lbl_opt = (Some (fst lbl), Some (snd lbl)) in
            Ast.For (init, cond, post, (parseStatement body lbl_opt), lbl)

        | Ast.Switch (cond, cases, Ast.Compound block, break, default) ->
            let lbl_opt = (fst last, Some break) in
            Ast.Switch (cond, cases, Ast.Compound (parseBlock block lbl_opt), break, default)

        | stmt -> stmt


    and parseBlock block last = match block with
        | [] -> []
        | (Ast.S h) :: t -> let h = parseStatement h last in (Ast.S h) :: parseBlock t last
        | h :: t -> h :: (parseBlock t last)

    in let parseToplevel = function
        | Ast.FunDecl (name, params, Some body, storage) -> Ast.FunDecl (name, params, Some (parseBlock body (None, None)), storage)
        | x -> x
    in
    match program with
        | Ast.Program toplevel -> Ast.Program (List.map (fun x -> parseToplevel x) toplevel)
