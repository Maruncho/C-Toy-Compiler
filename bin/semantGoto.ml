
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

                | h :: rest -> let (lst, env, l) = scanLabels env rest (*nothing to see*) in
                               (h::lst, env, l)

        in let rec checkGotos env block =
            match block with
                | [] -> []
                | (Ast.S (Ast.Goto lbl)) :: rest -> begin match Environment.find_opt lbl env with
                    | Some newLbl ->
                        (Ast.S (Ast.Goto newLbl)) :: checkGotos env rest
                    | None ->
                        raise (ParserError ("Goto label " ^ lbl ^ " doesn't exist"))
                end

                | (Ast.S (Ast.Compound comp_block)) :: rest ->
                    let new_block = checkGotos env comp_block in
                    (Ast.S (Ast.Compound new_block)) :: checkGotos env rest

                | (Ast.S (Ast.If (cond, Ast.Compound th, el_opt))) :: rest ->
                    let newThen = checkGotos env th in
                    let newThenComp = Ast.Compound newThen in
                    let newElseOpt = begin match el_opt with
                        | Some (Ast.Compound el) -> let x = checkGotos env el in Some (Ast.Compound x)
                        | _ -> el_opt
                    end in
                    (Ast.S (Ast.If (cond, newThenComp, newElseOpt))) :: checkGotos env rest

                | h :: rest -> h :: checkGotos env rest (*nothing to see*)

        in let (newAst, env, _) = scanLabels (Environment.emptySemantGoto) block
        in let () = Environment.printSemantGoto env
        in checkGotos env newAst 

    in let parseToplevel = function
        | Ast.Function (name, body) -> Ast.Function (name, parseBlock body)
    in
    match program with
        | Ast.Program toplevel -> Ast.Program (parseToplevel toplevel)
