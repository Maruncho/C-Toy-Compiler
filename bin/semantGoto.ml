
exception ParserError of string

let parse (program:Ast.program) =
    let tmpNum = ref 0
    in let lastLabel = ref ".CLCRINGE"
    in let newLabel() = let t = ".CL" ^ (string_of_int (!tmpNum))
                         in let () = tmpNum := !tmpNum + 1 in let () = lastLabel := t in t

    in let parseBlock block =
        let rec scanLabels ?(prevIsLabel=false) env block = 
            match block with
                | [] -> ([], env, prevIsLabel)
                | (Ast.S (Ast.Label lbl)) :: rest -> begin match Environment.find_opt lbl env with
                    | None ->
                        let newLbl = if prevIsLabel then !lastLabel else newLabel() in
                        let newEnv = Environment.add lbl newLbl env in
                        let (lst, newEnv, l) = scanLabels ~prevIsLabel:true newEnv rest in
                        if prevIsLabel then (lst, newEnv, l) else ((Ast.S (Ast.Label newLbl))::lst, newEnv, l)
                    | Some _ ->
                        raise (ParserError ("Duplicate label " ^ lbl))
                end

                | (Ast.S (Ast.Null)) as h :: rest ->
                    let (lst, env, l) = scanLabels ~prevIsLabel:prevIsLabel env rest in (*Empty statements are not interesting enough to break the label chain*)
                    (h::lst, env, l)

                | (Ast.S (Ast.Compound comp_block)) :: rest ->
                    let (newCompound, newEnv, prevIsLabel) = scanLabels ~prevIsLabel:prevIsLabel env comp_block in
                    let (lst, newEnv, l) = scanLabels ~prevIsLabel:prevIsLabel newEnv rest in
                    ((Ast.S (Ast.Compound newCompound)) :: lst, newEnv, l)

                | (Ast.S (Ast.If (cond, Ast.Compound th, el_opt))) :: rest ->
                    let (newThen, newEnv, _) = scanLabels env th in
                    let newThenComp = Ast.Compound newThen in
                    let (newElseOpt, newEnv, _) = begin match el_opt with
                        | Some (Ast.Compound el) -> let (x,y,z) = scanLabels newEnv el in (Some (Ast.Compound x), y, z)
                        | _ -> (el_opt, newEnv, false)
                    end in
                    let (lst, newEnv, l) = scanLabels newEnv rest in
                    ((Ast.S (Ast.If (cond, newThenComp, newElseOpt))) :: lst, newEnv, l)

                | (Ast.S (Ast.While (cond, Ast.Compound body, lbl))) :: rest ->
                    let (newBody, newEnv, _) = scanLabels env body in
                    let (lst, newEnv, l) = scanLabels newEnv rest in
                    ((Ast.S (Ast.While (cond, Ast.Compound newBody, lbl))) :: lst, newEnv, l)

                | (Ast.S (Ast.DoWhile (Ast.Compound body, cond, lbl))) :: rest ->
                    let (newBody, newEnv, _) = scanLabels env body in
                    let (lst, newEnv, l) = scanLabels newEnv rest in
                    ((Ast.S (Ast.DoWhile (Ast.Compound newBody, cond, lbl))) :: lst, newEnv, l)

                | (Ast.S (Ast.For (init, cond, post, Ast.Compound body, lbl))) :: rest ->
                    let (newBody, newEnv, _) = scanLabels env body in
                    let (lst, newEnv, l) = scanLabels newEnv rest in
                    ((Ast.S (Ast.For (init, cond, post, Ast.Compound newBody, lbl))) :: lst, newEnv, l)

                | (Ast.S (Ast.Switch (cond, cases, Ast.Compound body, break, default))) :: rest ->
                    let (newBody, newEnv, l) = scanLabels env body in
                    let (lst, newEnv, l) = scanLabels ~prevIsLabel:l newEnv rest in
                    ((Ast.S (Ast.Switch (cond, cases, Ast.Compound newBody, break, default))) :: lst, newEnv, l)

                | h :: rest -> let (lst, env, l) = scanLabels env rest (*nothing to see*) in
                               (h::lst, env, l)

        in let checkGotos env block =
            let rec parseBlock block = match block with
                | [] -> []
                | (Ast.S h) :: t -> let h = parseStatement h in (Ast.S h) :: parseBlock t
                | h :: t -> h :: (parseBlock t)

            and parseStatement (stmt:Ast.stmt) = match stmt with
                | Ast.Goto lbl -> begin match Environment.find_opt lbl env with
                    | Some newLbl -> Ast.Goto newLbl
                    | None ->
                        raise (ParserError ("Goto label " ^ lbl ^ " doesn't exist"))
                end

                | Ast.Compound comp_block -> Ast.Compound (parseBlock comp_block)

                | Ast.If (cond, th, el_opt) ->
                    let newThenComp = parseStatement th in
                    let newElseOpt = begin match el_opt with
                        | Some el -> Some (parseStatement el)
                        | _ -> el_opt
                    end in
                    Ast.If (cond, newThenComp, newElseOpt)

                | Ast.While (cond, body, lbl) ->
                    let newBody = parseStatement body in
                    Ast.While (cond, newBody, lbl)

                | Ast.DoWhile (body, cond, lbl) ->
                    let newBody = parseStatement body in
                    Ast.DoWhile (newBody, cond, lbl)

                | Ast.For (init, cond, post, body, lbl) ->
                    let newBody = parseStatement body in
                    Ast.For (init, cond, post, newBody, lbl)

                | Ast.Switch (cond, cases, body, break, default) ->
                    let newBody = parseStatement body in
                    Ast.Switch (cond, cases, newBody, break, default)

                | stmt -> stmt

            in parseBlock block

        in let (newAst, env, _) = scanLabels (Environment.emptySemantGoto) block
        (*in let () = Environment.printSemantGoto env*)
        in checkGotos env newAst 

    in let parseToplevel = function
        | Ast.Function (name, params, Some body) -> Ast.Function (name, params, Some (parseBlock body))
        | x -> x
    in
    match program with
        | Ast.Program toplevel -> Ast.Program (List.map (fun x -> parseToplevel x) toplevel)
