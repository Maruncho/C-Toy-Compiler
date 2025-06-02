
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
        | Ast.LogAnd | Ast.LogOr -> failwith "and and/or or are not really binary ops"

    in let rec parseExpr expr =
        match expr with
            | Ast.Int32 num -> Tac.Constant num

            | Ast.Unary (op, expr) ->
                let src = parseExpr expr in
                let dst = Tac.Var (newTemp()) in
                let op = parseUnaryOp op in
                let () = (Tac.Unary (op, src, dst)) #: instrs in
                dst

            | Ast.Binary (Ast.LogAnd, left, right) ->
                let false_lbl = newLbl() in
                let end_lbl = newLbl() in
                let left = parseExpr left in
                let () = (Tac.JumpIfZero (left, false_lbl)) #: instrs in
                let right = parseExpr right in
                let () = (Tac.JumpIfZero (right, false_lbl)) #: instrs in
                let result = Tac.Var (newTemp()) in
                let () = (Tac.Copy (Tac.Constant 1l, result)) #: instrs in
                let () = (Tac.Jump end_lbl) #: instrs in
                let () = (Tac.Label false_lbl) #: instrs in
                let () = (Tac.Copy (Tac.Constant 0l, result)) #: instrs in
                let () = (Tac.Label end_lbl) #: instrs in
                result

            | Ast.Binary (Ast.LogOr, left, right) ->
                let true_lbl = newLbl() in
                let end_lbl = newLbl() in
                let left = parseExpr left in
                let () = (Tac.JumpIfNotZero (left, true_lbl)) #: instrs in
                let right = parseExpr right in
                let () = (Tac.JumpIfNotZero (right, true_lbl)) #: instrs in
                let result = Tac.Var (newTemp()) in
                let () = (Tac.Copy (Tac.Constant 0l, result)) #: instrs in
                let () = (Tac.Jump end_lbl) #: instrs in
                let () = (Tac.Label true_lbl) #: instrs in
                let () = (Tac.Copy (Tac.Constant 1l, result)) #: instrs in
                let () = (Tac.Label end_lbl) #: instrs in
                result

            | Ast.Binary (op, left, right) ->
                let src1 = parseExpr left in
                let src2 = parseExpr right in
                let dst = Tac.Var (newTemp()) in
                let op = parseBinaryOp op in
                let () = (Tac.Binary (op, src1, src2, dst)) #: instrs in
                dst

    and parseStmt stmt =
        match stmt with
            | Ast.Return expr ->
                let src = parseExpr expr in
                (Tac.Return src) #: instrs

    in let parseTopLevel tl =
        match tl with
            | Ast.Function (name, stmt) -> let _ = parseStmt stmt in
                                           Tac.Function (name, List.rev !instrs)

    in match ast with
        | Ast.Program tl -> Tac.Program (parseTopLevel tl)

