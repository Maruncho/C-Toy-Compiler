
module Tac = Tacky


let tackify ast = 
    let ( #: ) (h: 'a) (t: 'a list ref) = t := (h :: (!t)) in
    let instrs : Tac.instruction list ref = ref [] in

    let tmpNum = ref 0 in
    let newTemp() = (let t = "tmp." ^ (string_of_int (!tmpNum)) in let () = tmpNum := !tmpNum + 1 in t) in

    let lblNum = ref 0 in
    let newLbl() = (let t = ".L" ^ (string_of_int (!lblNum)) in let () = lblNum := !lblNum + 1 in t) in

    let parseUnaryOp = function
        | Ast.Negate -> Tac.Negate
        | Ast.Complement -> Tac.Complement
        | Ast.LogNot -> Tac.Not
        | Ast.Increment -> Tac.Incr
        | Ast.Decrement -> Tac.Decr
        | Ast.Rvalue -> failwith "Rvalue is a useless unop and should be just unboxed(tackify.ml)"

    in let parseBinaryOp = function
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

    in let rec parseExpr expr =
        match expr with
            | Ast.Int32 num -> Tac.Constant num
            | Ast.Var id -> Tac.Var id

            | Ast.Unary (Ast.Increment, dst) ->
                let dst = parseExpr dst in
                let () = (Tac.Unary (Tac.Incr, dst, dst)) #: instrs in
                dst
            | Ast.Unary (Ast.Decrement, dst) ->
                let dst = parseExpr dst in
                let () = (Tac.Unary (Tac.Decr, dst, dst)) #: instrs in
                dst
            | Ast.Unary (Ast.Rvalue, src) -> parseExpr src
            | Ast.Unary (op, expr) ->
                let src = parseExpr expr in
                let dst = Tac.Var (newTemp()) in
                let op = parseUnaryOp op in
                let () = (Tac.Unary (op, src, dst)) #: instrs in
                dst

            | Ast.BinarySp (Ast.LogAnd, left, right, between) ->
                let false_lbl = newLbl() in
                let end_lbl = newLbl() in
                let left = parseExpr left in
                let () = (Tac.JumpIfZero (left, false_lbl)) #: instrs in
                let () = List.iter (fun stmt -> parseStmt stmt) between in
                let right = parseExpr right in
                let () = (Tac.JumpIfZero (right, false_lbl)) #: instrs in
                let result = Tac.Var (newTemp()) in
                let () = (Tac.Copy (Tac.Constant 1l, result)) #: instrs in
                let () = (Tac.Jump end_lbl) #: instrs in
                let () = (Tac.Label false_lbl) #: instrs in
                let () = (Tac.Copy (Tac.Constant 0l, result)) #: instrs in
                let () = (Tac.Label end_lbl) #: instrs in
                result

            | Ast.BinarySp (Ast.LogOr, left, right, between) ->
                let true_lbl = newLbl() in
                let end_lbl = newLbl() in
                let left = parseExpr left in
                let () = (Tac.JumpIfNotZero (left, true_lbl)) #: instrs in
                let () = List.iter (fun stmt -> parseStmt stmt) between in
                let right = parseExpr right in
                let () = (Tac.JumpIfNotZero (right, true_lbl)) #: instrs in
                let result = Tac.Var (newTemp()) in
                let () = (Tac.Copy (Tac.Constant 0l, result)) #: instrs in
                let () = (Tac.Jump end_lbl) #: instrs in
                let () = (Tac.Label true_lbl) #: instrs in
                let () = (Tac.Copy (Tac.Constant 1l, result)) #: instrs in
                let () = (Tac.Label end_lbl) #: instrs in
                result

            | Ast.BinarySp (Ast.Comma, _, _, _) -> failwith "TODO: Add Comma"

            | Ast.Binary (op, left, right) ->
                let src1 = parseExpr left in
                let src2 = parseExpr right in
                let dst = Tac.Var (newTemp()) in
                let op = parseBinaryOp op in
                let () = (Tac.Binary (op, src1, src2, dst)) #: instrs in
                dst

            | Ast.BinaryAssign (op, dst, src) ->
                let () = match dst with Ast.Var _ -> () | _ -> failwith "BinaryAssign dst is not a var" in
                let src = parseExpr src in
                let dst = parseExpr dst in
                let op = parseBinaryOp op in
                let () = (Tac.Binary (op, dst, src, dst)) #: instrs in
                dst

            | Ast.Assignment (left, right) ->
                let dst = Tac.Var (match left with Ast.Var v -> v | _ -> failwith "lvalue of Assignment is not a Ast.Var") in
                let src = parseExpr right in
                let () = (Tac.Copy (src, dst)) #: instrs in
                dst

            | Ast.Ternary (cond, th, el, postfix) -> 
                let cond = parseExpr cond in
                let else_lbl = newLbl() in
                let end_lbl = newLbl() in
                let result = Tac.Var(newTemp()) in
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


    and parseStmt stmt =
        match stmt with
            | Ast.Return expr ->
                let src = parseExpr expr in
                (Tac.Return src) #: instrs
            | Ast.Expression expr -> let _ = parseExpr expr in ()

            | Ast.If (cond, th, None) ->
                let cond = parseExpr cond in
                let end_lbl = newLbl() in
                let () = (Tac.JumpIfZero (cond, end_lbl)) #: instrs in
                let () = parseStmt th in
                (Tac.Label end_lbl) #: instrs
            | Ast.If (cond, th, Some el) ->
                let cond = parseExpr cond in
                let else_lbl = newLbl() in
                let end_lbl = newLbl() in
                let () = (Tac.JumpIfZero (cond, else_lbl)) #: instrs in
                let () = parseStmt th in
                let () = (Tac.Jump end_lbl) #: instrs in
                let () = (Tac.Label else_lbl) #: instrs in
                let () = parseStmt el in
                (Tac.Label end_lbl) #: instrs

            | Ast.Compound items -> parseBlockItems items

            | Ast.Null -> ()
            | Ast.Label lbl -> (Tac.Label lbl) #: instrs
            | Ast.Goto lbl -> (Tac.Jump lbl) #: instrs

    and parseDecl decl =
        match decl with
            | Ast.Declaration (_, None) -> ()
            | Ast.Declaration (id, Some expr) ->
                let src = parseExpr expr in
                (Tac.Copy (src, Tac.Var(id))) #: instrs

    and parseBlockItems block_items = match block_items with
        | [] -> ()
        | (Ast.S stmt) :: rest -> parseStmt stmt; parseBlockItems rest
        | (Ast.D decl) :: rest -> parseDecl decl; parseBlockItems rest

    in let parseTopLevel tl = match tl with
            | Ast.Function (name, block_items) ->
                let () = parseBlockItems block_items in
                let () = (Tac.Return (Tac.Constant 0l)) #: instrs in
                Tac.Function (name, List.rev !instrs)

    in match ast with
        | Ast.Program tl -> Tac.Program (parseTopLevel tl)

