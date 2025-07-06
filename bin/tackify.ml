
module Tac = Tacky

exception TackyError of string

let parseUnaryOp = function
        | Ast.Negate -> Tac.Negate
        | Ast.Complement -> Tac.Complement
        | Ast.LogNot -> Tac.Not
        | Ast.Increment -> Tac.Incr
        | Ast.Decrement -> Tac.Decr
        | Ast.Rvalue -> failwith "Rvalue is a useless unop and should be just unboxed(tackify.ml)"

let parseBinaryOp = function
        | Ast.Add -> Tac.Add
        | Ast.Sub -> Tac.Subtract
        | Ast.Mul -> Tac.Multiply
        | Ast.Div -> Tac.Divide
        | Ast.Mod -> Tac.Remainder
        | Ast.And -> Tac.And
        | Ast.Or -> Tac.Or
        | Ast.Xor -> Tac.Xor
        | Ast.Lshift -> Tac.LShift
        | Ast.Rshift -> Tac.RShift
        | Ast.Eq -> Tac.Equal
        | Ast.Neq -> Tac.NotEqual
        | Ast.Lt -> Tac.LessThan
        | Ast.Le -> Tac.LessOrEqual
        | Ast.Gt -> Tac.GreaterThan
        | Ast.Ge -> Tac.GreaterOrEqual
        | Ast.Assign -> failwith "assignment operator is not handled by parseBinary"

let tackify ast globalEnv = 
    let ( #: ) (h: 'a) (t: 'a list ref) = t := (h :: (!t)) in
    let instrs : Tac.instruction list ref = ref [] in
    let undefinedNames = ref Environment.setEmpty in
    let localStatics = ref [] in

    let tmpNum = ref 0 in
    let newTemp() = (let t = "tmp." ^ (string_of_int (!tmpNum)) in let () = tmpNum := !tmpNum + 1 in t) in

    let lblNum = ref 0 in
    let newLbl() = (let t = ".L" ^ (string_of_int (!lblNum)) in let () = lblNum := !lblNum + 1 in t) in

    let rec helpParseConditionWithPostfix postfix cond =
        let oldToNewTemps, theirType = (List.fold_left (fun lst stmt -> (match stmt with
            | Ast.Expression (typ, Ast.Unary (Ast.Increment, (_, Ast.Var (old, _)))) -> ((old, newTemp()), parseType typ) :: lst
            | Ast.Expression (typ, Ast.Unary (Ast.Decrement, (_, Ast.Var (old, _)))) -> ((old, newTemp()), parseType typ) :: lst
            | _ -> lst
        )) [] postfix) |> List.split
        in let rec walkExpr expr = match expr with
            | typ, Ast.Var (old, t) -> begin match List.assoc_opt old oldToNewTemps with
                | None -> typ, Ast.Var (old, t)
                | Some neww -> typ, Ast.Var (neww, t)
            end
            | typ, Ast.Unary (op, expr) -> typ, Ast.Unary (op, walkExpr expr)
            | typ, Ast.Binary (op, expr1, expr2) -> typ, Ast.Binary (op, walkExpr expr1, walkExpr expr2)
            | typ, Ast.BinarySp (op, expr1_sp, expr2) -> typ, Ast.BinarySp (op, expr1_sp, walkExpr expr2)
            | typ, Ast.BinaryAssign (op, var, expr) -> typ, Ast.BinaryAssign (op, walkExpr var, walkExpr expr)
            | typ, Ast.Assignment (var, expr) -> typ, Ast.Assignment (walkExpr var, walkExpr expr)
            | typ, Ast.Ternary (cond_sp, th, el) -> typ, Ast.Ternary (cond_sp, walkExpr th, walkExpr el)
            | typ, Ast.Cast (new_typ, expr) -> typ, Ast.Cast (new_typ, walkExpr expr)
            | typ, Ast.Call (id, args) -> typ, Ast.Call (id, List.map walkExpr args)
            | typ, Ast.Literal lit -> typ, Ast.Literal lit

        in let () = List.iter (fun ((x,y),typ) -> (Tac.Copy (Tac.Var (x, typ), Tac.Var (y, typ))) #: instrs) (List.combine oldToNewTemps theirType)
        in let () = List.iter (fun x -> parseStmt x) postfix
        in walkExpr cond

    and parseCases cond cases = match cases with
        | [] -> ()
        | (lit, lbl) :: t ->
            let (const, typ) = parseLiteral lit in
            let dst = Tac.Var (newLbl(), typ) in
            let () = (Tac.Binary (Tac.Equal, cond, Tac.Constant (const, typ), dst)) #: instrs in
            let () = (Tac.JumpIfNotZero (dst, lbl)) #: instrs in
            parseCases cond t

    and parseLiteral : Ast.lit -> Z.t * Tac.typ = function
        | Ast.Int32 num -> Z.of_int32 num, Tac.Int32 true(*is_signed*)
        | Ast.Int64 num -> Z.of_int64 num, Tac.Int64 true
        | Ast.UInt32 num -> Z.of_int32 num, Tac.Int32 false
        | Ast.UInt64 num -> Z.of_int64 num, Tac.Int64 false

    and parseType = function
        | Ast.Int -> Tac.Int32 true(*is_signed*)
        | Ast.Long -> Tac.Int64 true
        | Ast.UInt -> Tac.Int32 false
        | Ast.ULong -> Tac.Int64 false

    and flipIsSigned =
        let flipType = function
            | Tac.Int32 s -> Tac.Int32 (not s)
            | Tac.Int64 s -> Tac.Int64 (not s)
        in function
            | Tac.Constant (n, t) -> Tac.Constant (n, flipType t)
            | Tac.Var (n, t) -> Tac.Var (n, flipType t)
            | Tac.StaticVar (n, t) -> Tac.StaticVar (n, flipType t)

    and parseExpr (expr:Ast.typed_expr) =
        match expr with
            | _, Ast.Literal lit -> let a,b = (parseLiteral lit) in Tac.Constant (a, b)
            | typ, Ast.Var (id, Ast.AutoVariable _) -> Tac.Var (id, parseType typ)
            | typ, Ast.Var (id, Ast.StaticVariable _) -> Tac.StaticVar (id, parseType typ)
            | _, Ast.Var (_, Ast.Function _) -> failwith "No support for function variables"

            | _, Ast.Cast (new_type, ((inner_type, _) as inner_expr)) ->
                let result = parseExpr inner_expr in
                (*let () = print_string((Ast.string_data_type inner_type) ^ " " ^ (Ast.string_data_type new_type) ^ " \n") in*)
                if inner_type = new_type then result else

                if (Ast.size new_type) = (Ast.size inner_type) then
                    flipIsSigned result
                else
                    let dst = Tac.Var (newTemp(), parseType new_type) in
                    let () = if (Ast.size new_type) < (Ast.size inner_type) then
                        ((Tac.Truncate (result, dst)) #: instrs)
                    else if (Ast.signed inner_type) then
                        ((Tac.SignExtend (result, dst)) #: instrs)
                    else
                        ((Tac.ZeroExtend (result, dst)) #: instrs)
                    in dst

            | _, Ast.Unary (Ast.Increment, dst) ->
                let dst = parseExpr dst in
                let () = (Tac.Unary (Tac.Incr, dst, dst)) #: instrs in
                dst

            | _, Ast.Unary (Ast.Decrement, dst) ->
                let dst = parseExpr dst in
                let () = (Tac.Unary (Tac.Decr, dst, dst)) #: instrs in
                dst

            | _, Ast.Unary (Ast.Rvalue, src) -> parseExpr src
            | typ, Ast.Unary (op, expr) ->
                let src = parseExpr expr in
                let dst = Tac.Var (newTemp(), parseType typ) in
                let op = parseUnaryOp op in
                let () = (Tac.Unary (op, src, dst)) #: instrs in
                dst

            | _, Ast.BinarySp (Ast.LogAnd, (left, between), right) ->
                let false_lbl = newLbl() in
                let end_lbl = newLbl() in
                let left = parseExpr left in
                let () = (Tac.JumpIfZero (left, false_lbl)) #: instrs in
                let () = List.iter (fun stmt -> parseStmt stmt) between in
                let right = parseExpr right in
                let () = (Tac.JumpIfZero (right, false_lbl)) #: instrs in
                let result = Tac.Var (newTemp(), Tac.Int32 true) in
                let () = (Tac.Copy (Tac.Constant (Z.one, Tac.Int32 true), result)) #: instrs in
                let () = (Tac.Jump end_lbl) #: instrs in
                let () = (Tac.Label false_lbl) #: instrs in
                let () = (Tac.Copy (Tac.Constant (Z.zero, Tac.Int32 true), result)) #: instrs in
                let () = (Tac.Label end_lbl) #: instrs in
                result

            | _, Ast.BinarySp (Ast.LogOr, (left, between), right) ->
                let true_lbl = newLbl() in
                let end_lbl = newLbl() in
                let left = parseExpr left in
                let () = (Tac.JumpIfNotZero (left, true_lbl)) #: instrs in
                let () = List.iter (fun stmt -> parseStmt stmt) between in
                let right = parseExpr right in
                let () = (Tac.JumpIfNotZero (right, true_lbl)) #: instrs in
                let result = Tac.Var (newTemp(), Tac.Int32 true) in
                let () = (Tac.Copy (Tac.Constant (Z.zero, Tac.Int32 true), result)) #: instrs in
                let () = (Tac.Jump end_lbl) #: instrs in
                let () = (Tac.Label true_lbl) #: instrs in
                let () = (Tac.Copy (Tac.Constant (Z.one, Tac.Int32 true), result)) #: instrs in
                let () = (Tac.Label end_lbl) #: instrs in
                result

            | _, Ast.BinarySp (Ast.Comma, _, _) -> failwith "TODO: Add Comma"

            | typ, Ast.Binary (op, left, right) ->
                let src1 = parseExpr left in
                let src2 = parseExpr right in
                let dst = Tac.Var (newTemp(), parseType typ) in
                let op = parseBinaryOp op in
                let () = (Tac.Binary (op, src1, src2, dst)) #: instrs in
                dst

            | _, Ast.BinaryAssign (op, dst, src) ->
                let () = match dst with (_, Ast.Var _) -> () | _ -> failwith "BinaryAssign dst is not a var" in
                let src = parseExpr src in
                let dst = parseExpr dst in
                let op = parseBinaryOp op in
                let () = (Tac.Binary (op, dst, src, dst)) #: instrs in
                dst

            | typ, Ast.Assignment (left, right) ->
                let dst = (match left with (_, Ast.Var (v, Ast.AutoVariable _)) -> Tac.Var (v, parseType typ)
                                         | (_, Ast.Var (v, Ast.StaticVariable _)) -> Tac.StaticVar (v, parseType typ)
                                         | _ -> failwith "lvalue of Assignment is not a variable") in
                let src = parseExpr right in
                let () = (Tac.Copy (src, dst)) #: instrs in
                dst

            | typ, Ast.Ternary ((cond, postfix), th, el) -> 
                let cond = parseExpr cond in
                let else_lbl = newLbl() in
                let end_lbl = newLbl() in
                let result = Tac.Var(newTemp(), parseType typ) in
                let () = (Tac.JumpIfZero (cond, else_lbl)) #: instrs in
                let () = List.iter (fun stmt -> parseStmt stmt) postfix in
                let th = parseExpr th in
                let () = (Tac.Copy (th, result)) #: instrs in
                let () = (Tac.Jump end_lbl) #: instrs in
                let () = (Tac.Label else_lbl) #: instrs in
                let () = List.iter (fun stmt -> parseStmt stmt) postfix in
                let el = parseExpr el in
                let () = (Tac.Copy (el, result)) #: instrs in
                let () = (Tac.Label end_lbl) #: instrs in
                result

            | typ, Ast.Call (name, args) ->
                let args = List.map (fun arg -> parseExpr arg) args in
                let dst = Tac.Var(newTemp(), parseType typ) in
                let () = (Tac.Call (name, args, dst)) #: instrs in
                dst


    and parseStmt stmt =
        match stmt with
            | Ast.Return expr ->
                let src = parseExpr expr in
                (Tac.Return src) #: instrs
            | Ast.Expression expr -> let _ = parseExpr expr in ()

            | Ast.If ((cond, postfix), th, None) ->
                let newCond = helpParseConditionWithPostfix postfix cond in
                let cond = parseExpr newCond in
                let end_lbl = newLbl() in
                let () = (Tac.JumpIfZero (cond, end_lbl)) #: instrs in
                let () = parseStmt th in
                (Tac.Label end_lbl) #: instrs
            | Ast.If ((cond, postfix), th, Some el) ->
                let newCond = helpParseConditionWithPostfix postfix cond in
                let cond = parseExpr newCond in
                let else_lbl = newLbl() in
                let end_lbl = newLbl() in
                let () = (Tac.JumpIfZero (cond, else_lbl)) #: instrs in
                let () = parseStmt th in
                let () = (Tac.Jump end_lbl) #: instrs in
                let () = (Tac.Label else_lbl) #: instrs in
                let () = parseStmt el in
                (Tac.Label end_lbl) #: instrs

            | Ast.Switch ((cond, postfix), cases, stmt, break, default) ->
                let newCond = helpParseConditionWithPostfix postfix cond in
                let cond = parseExpr newCond in
                let () = parseCases cond cases in
                let () = (Tac.Jump default) #: instrs in
                let () = parseStmt stmt in
                (Tac.Label break) #: instrs

            | Ast.DoWhile (body, (cond, postfix), (continue, break)) ->
                let begin_lbl = newLbl() in
                let () = (Tac.Label begin_lbl) #: instrs in
                let () = parseStmt body in
                let () = (Tac.Label continue) #: instrs in
                let newCond = helpParseConditionWithPostfix postfix cond in
                let cond = parseExpr newCond in
                let () = (Tac.JumpIfNotZero (cond, begin_lbl)) #: instrs in
                (Tac.Label break) #: instrs

            | Ast.While ((cond, postfix), body, (continue, break)) ->
                let () = (Tac.Label continue) #: instrs in
                let newCond = helpParseConditionWithPostfix postfix cond in
                let cond = parseExpr newCond in
                let () = (Tac.JumpIfZero (cond, break)) #: instrs in
                let () = parseStmt body in
                let () = (Tac.Jump continue) #: instrs in
                (Tac.Label break) #: instrs

            | Ast.For (init_opt, cond_opt, post_opt, body, (continue, break)) ->
                let () = begin match init_opt with
                    | None -> ()
                    | Some Ast.InitExpr (init, postfix) ->
                        let _ = parseExpr init in
                        List.iter (fun stmt -> parseStmt stmt) postfix
                    | Some Ast.InitDecl (init, postfix) ->
                        let () = parseDecl (Ast.VarDecl init) in
                        List.iter (fun stmt -> parseStmt stmt) postfix
                end in
                let begin_lbl = newLbl() in
                let () = (Tac.Label begin_lbl) #: instrs in
                let cond = begin match cond_opt with
                    | None -> None
                    | Some (cond, postfix) ->
                        let newCond = helpParseConditionWithPostfix postfix cond in
                        Some (parseExpr newCond)
                end in
                let () = (match cond with None -> () | Some cond -> (Tac.JumpIfZero (cond, break)) #: instrs) in
                let () = parseStmt body in
                let () = (Tac.Label continue) #: instrs in
                let () = begin match post_opt with
                    | None -> ()
                    | Some (post, postfix) ->
                        let _ = parseExpr post in
                        List.iter (fun stmt -> parseStmt stmt) postfix
                end in
                let () = (Tac.Jump begin_lbl) #: instrs in 
                (Tac.Label break) #: instrs

            | Ast.Compound items -> parseBlockItems items

            | Ast.Break lbl -> (Tac.Jump lbl) #: instrs
            | Ast.Continue lbl -> (Tac.Jump lbl) #: instrs
            | Ast.Case (_, lbl) -> (Tac.Label lbl) #: instrs
            | Ast.Default lbl -> (Tac.Label lbl) #: instrs
            | Ast.Null -> ()
            | Ast.Label lbl -> (Tac.Label lbl) #: instrs
            | Ast.Goto lbl -> (Tac.Jump lbl) #: instrs

    and parseDecl decl =
        match decl with
            | Ast.VarDecl (_, None, _, None) -> ()
            | Ast.VarDecl (id, Some expr, typ, None) -> 
                let src = parseExpr (typ, expr) in
                (Tac.Copy (src, Tac.Var(id, parseType typ))) #: instrs

            | Ast.VarDecl (id, None, typ, Some Ast.Static) ->
                localStatics := (Tac.StaticVariable (id, false, Z.zero, parseType typ)) :: !localStatics

            | Ast.VarDecl (id, Some expr , typ, Some Ast.Static) ->
                let i = Const.parseConstExpr (typ, expr) (*(Some globalEnv)*) in
                localStatics := (Tac.StaticVariable (id, false, i, parseType typ)) :: !localStatics

            | _ -> ()

    and parseBlockItems block_items = match block_items with
        | [] -> ()
        | (Ast.S stmt) :: rest -> parseStmt stmt; parseBlockItems rest
        | (Ast.D decl) :: rest -> parseDecl decl; parseBlockItems rest

    in let rec parseTopLevel tls = match tls with
        | [] -> []
        | tl :: rest -> begin match tl with
            | Ast.FunDecl (name, params, block_items, _, _) ->
                let is_global = begin match Environment.find_opt name globalEnv with
                    | None -> failwith "DEBUG: Function found in AST, but not in globalEnv"
                    | Some (Environment.VarAttr _) -> failwith "DEBUG: Function found in AST, but var found in globalEnv"
                    | Some (Environment.FunAttr (_, is_global)) -> is_global
                end in
                let has_body = begin match block_items with
                    | None -> false (*no body, no definition, no assembly*)
                    | Some items -> let () = parseBlockItems items in true
                end in
                if not has_body then parseTopLevel rest else
                let () = (Tac.Return (Tac.Constant (Z.zero, Tac.Int64 true))) #: instrs in
                let params = List.map (fun (typ, id) -> (id, parseType typ)) params in
                let lEXECUTE_LHS_FIRST = Tac.Function (name, is_global, params, List.rev !instrs) in
                let () = instrs := []
                in lEXECUTE_LHS_FIRST :: (parseTopLevel rest)

            | Ast.VarDecl _ -> parseTopLevel rest
        end

    in let parseStaticVarsAndNoticeUndefinedExternFunctions() =
        Environment.Env.fold (fun _ v acc -> match v with
        | Environment.VarAttr (id,initial,typ,is_global) ->
            begin match initial with
                | Environment.NoInitializer -> let () = undefinedNames := Environment.setAdd id !undefinedNames in acc
                | Environment.Tentative -> (Tac.StaticVariable (id, is_global, Z.zero, parseType typ)) :: acc
                | Environment.Initial i -> (Tac.StaticVariable (id, is_global, i, parseType typ)) :: acc
            end
        | Environment.FunAttr ((id,_,_,is_defined),is_global) ->
            let () = if (not is_defined) && is_global then undefinedNames := Environment.setAdd id !undefinedNames
            in acc
    ) globalEnv []

    in try match ast with
        | Ast.Program tls -> let p = (parseTopLevel tls) @ (parseStaticVarsAndNoticeUndefinedExternFunctions())
                             in Tac.Program (p @ !localStatics), !undefinedNames
    with Environment.EnvironmentError e -> raise (TackyError e)

