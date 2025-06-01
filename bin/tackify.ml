
module Tac = Tacky


let tackify ast = 
    let ( #: ) (h: 'a) (t: 'a list ref) = t := (h :: (!t)) in
    let instrs : Tac.instruction list ref = ref [] in

    let tmpNum = ref 0 in
    let newTemp() = (let t = "tmp." ^ (string_of_int (!tmpNum)) in let () = tmpNum := !tmpNum + 1 in t) in

    let parseUnaryOp = function
        | Ast.Negate -> Tac.Negate
        | Ast.Complement -> Tac.Complement

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

    in let rec parseExpr expr =
        match expr with
            | Ast.Int32 num -> Tac.Constant(Int64.of_int32 num)

            | Ast.Unary (op, expr) ->
                let src = parseExpr expr in
                let dst = Tac.Var (newTemp()) in
                let op = parseUnaryOp op in
                let () = (Tac.Unary (op, src, dst)) #: instrs in
                dst

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

