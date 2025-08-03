
module Tac = Tacky

exception TackyError of string

type lval = PlainOperand of Tac.operand
          | DereferencedPointer of Tac.operand

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

let const_to_tacky c typ = match c with
    | Const.I n -> Tac.I (n, typ)
    | Const.D n -> Tac.D n

let unpointerOnce = function
    | Tac.Var (i, Tac.Ptr t) -> Tac.Var (i, t)
    | Tac.StaticVar (i, Tac.Ptr t) -> Tac.StaticVar (i, t)
    | _ -> failwith "Don't use unpointerOnce() with non-pointer"

let pointerOnce = function
    | Tac.Var (i, t) -> Tac.Var (i, Tac.Ptr t)
    | Tac.StaticVar (i, t) -> Tac.StaticVar (i, Tac.Ptr t)
    | _ -> failwith "Don't use pointerOnce() with non-pointer"

let makeLongIntoPointer ptr = function
    | Tac.Var (i, Tac.Int64 _) -> Tac.Var (i, ptr)
    | Tac.StaticVar (i, Tac.Int64 _) -> Tac.StaticVar (i, ptr)
    | Tac.Constant (I (n, Tac.Int64 _)) -> Tac.Constant (I (n, ptr))
    | _ -> failwith "Don't use makeLongIntoPointer with non-long integers"

let makePointerIntoLong sign = function
    | Tac.Var (i, Tac.Ptr _) -> Tac.Var (i, Tac.Int64 sign)
    | Tac.StaticVar (i, Tac.Ptr _) -> Tac.StaticVar (i, Tac.Int64 sign)
    | _ -> failwith "Don't use makePointerIntoULong with non-pointers"

let tackify ast globalEnv = 
    let ( #: ) (h: 'a) (t: 'a list ref) = t := (h :: (!t)) in
    let instrs : Tac.instruction list ref = ref [] in
    let undefinedNames = ref Environment.setEmpty in
    let localStatics = ref [] in

    let rec helpParseConditionWithPostfix postfix cond =
        let oldToNewTemps, theirTypeAndStatic = (List.fold_left (fun lst stmt -> (match stmt with
            | Ast.Expression (typ, Ast.Unary (Ast.Increment, (_, Ast.Var (old, StaticVariable _)))) -> ((old, Temp.newTemp()), (parseType typ, true)) :: lst
            | Ast.Expression (typ, Ast.Unary (Ast.Increment, (_, Ast.Var (old, _)))) -> ((old, Temp.newTemp()), (parseType typ, false)) :: lst
            | Ast.Expression (typ, Ast.Unary (Ast.Decrement, (_, Ast.Var (old, StaticVariable _)))) -> ((old, Temp.newTemp()), (parseType typ, true)) :: lst
            | Ast.Expression (typ, Ast.Unary (Ast.Decrement, (_, Ast.Var (old, _)))) -> ((old, Temp.newTemp()), (parseType typ, false)) :: lst
            | _ -> lst
        )) [] postfix) |> List.split
        in let derefsToVars = List.fold_left (fun lst stmt -> (match stmt with
            | Ast.Expression (typ, Ast.Unary (Ast.Increment, (_, Ast.Dereference _ as deref))) ->
                (deref, (typ, Ast.Var (Temp.newTemp(), Ast.AutoVariable typ))) :: lst
            | Ast.Expression (typ, Ast.Unary (Ast.Decrement, (_, Ast.Dereference _ as deref))) ->
                (deref, (typ, Ast.Var (Temp.newTemp(), Ast.AutoVariable typ))) :: lst
            | _ -> lst
        )) [] postfix
        in let rec walkExpr expr = match expr with
            | typ, Ast.Var (old, t) -> begin match List.assoc_opt old oldToNewTemps with
                | None -> typ, Ast.Var (old, t)
                | Some neww -> typ, Ast.Var (neww, Ast.AutoVariable typ)
            end
            | typ, Ast.Unary (op, expr) -> typ, Ast.Unary (op, walkExpr expr)
            | typ, Ast.Dereference sub -> begin match List.assoc_opt expr derefsToVars with
                | None -> typ, Ast.Dereference (walkExpr sub)
                | Some neww -> neww
            end
            | typ, Ast.AddressOf (expr) -> typ, Ast.AddressOf (walkExpr expr)
            | typ, Ast.Binary (op, expr1, expr2) -> typ, Ast.Binary (op, walkExpr expr1, walkExpr expr2)
            | typ, Ast.BinarySp (op, expr1_sp, expr2) -> typ, Ast.BinarySp (op, expr1_sp, walkExpr expr2)
            | typ, Ast.BinaryAssign (op, var, expr, opt) -> typ, Ast.BinaryAssign (op, walkExpr var, walkExpr expr, opt)
            | typ, Ast.Assignment (var, expr) -> typ, Ast.Assignment (walkExpr var, walkExpr expr)
            | typ, Ast.Ternary (cond_sp, th, el) -> typ, Ast.Ternary (cond_sp, walkExpr th, walkExpr el)
            | typ, Ast.Cast (new_typ, expr) -> typ, Ast.Cast (new_typ, walkExpr expr)
            | typ, Ast.Call (id, args) -> typ, Ast.Call (id, List.map walkExpr args)
            | typ, Ast.Literal lit -> typ, Ast.Literal lit

        in let () = List.iter (fun ((old,neww),(typ, static)) ->
            let old = if static then Tac.StaticVar (old, typ) else Tac.Var (old, typ) in
            (Tac.Copy (old, Tac.Var (neww, typ))) #: instrs) (List.combine oldToNewTemps theirTypeAndStatic)

        in let () = List.iter (fun (deref, var) ->
            let var = parseExpr_lval_convert var in
            let deref = parseExpr_lval_convert deref in
            (Tac.Copy (deref, var)) #: instrs
        ) derefsToVars

        in let () = List.iter (fun x -> parseStmt x) postfix
        in walkExpr cond

    and parseCases cond cases = match cases with
        | [] -> ()
        | (lit, lbl) :: t ->
            let const = Tac.Constant (parseLiteral lit) in
            let dst = Tac.Var (Label.newLbl(), Tac.operand_type const) in
            let () = (Tac.Binary (Tac.Equal, cond, const, dst)) #: instrs in
            let () = (Tac.JumpIfNotZero (dst, lbl)) #: instrs in
            parseCases cond t

    and parseLiteral : Ast.lit -> Tac.number = function
        | Ast.Int32 num -> Tac.I (Z.of_int32 num, Tac.Int32 true)
        | Ast.Int64 num -> Tac.I (Z.of_int64 num, Tac.Int64 true)
        | Ast.UInt32 num -> Tac.I (Z.of_int32 num, Tac.Int32 false)
        | Ast.UInt64 num -> Tac.I (Z.of_int64 num, Tac.Int64 false)
        | Ast.Float64 num -> Tac.D num

    and parseType = function
        | Ast.Int -> Tac.Int32 true(*is_signed*)
        | Ast.Long -> Tac.Int64 true
        | Ast.UInt -> Tac.Int32 false
        | Ast.ULong -> Tac.Int64 false
        | Ast.Double -> Tac.Float64
        | Ast.Ptr x -> Tac.Ptr (parseType x)
        | Ast.FunType _ -> failwith "parseType should not handle funtype"

    and flipIsSigned =
        let flipType = function
            | Tac.Int32 s -> Tac.Int32 (not s)
            | Tac.Int64 s -> Tac.Int64 (not s)
            | Tac.Float64 -> failwith "Cannot call flipIsSigned with float"
            | Tac.Ptr _ -> failwith "Cannot call flipIsSigned with ptr"
        in function
            | Tac.Constant Tac.I (n, t) -> Tac.Constant (Tac.I (n, flipType t))
            | Tac.Var (n, t) -> Tac.Var (n, flipType t)
            | Tac.StaticVar (n, t) -> Tac.StaticVar (n, flipType t)
            | Tac.Constant Tac.D _ -> failwith "Cannot call flipIsSigned with float"

    and cast old_type new_type tacExpr =
        let () = print_string((Ast.string_data_type old_type) ^ " " ^ (Ast.string_data_type new_type) ^ " " ^ (Tac.typ_str (Tac.operand_type tacExpr)) ^ " \n") in
        if old_type = new_type then tacExpr else

        if (Ast.isPointer old_type) && (Ast.isPointer new_type) then
            tacExpr
        else if (Ast.isPointer new_type) then
            if Ast.size old_type = 8 then (makeLongIntoPointer (parseType new_type) tacExpr) else
            let dst = Tac.Var (Temp.newTemp(), parseType new_type) in
            let () = ((Tac.ZeroExtend (tacExpr, dst)) #: instrs) in
            dst
        else if (Ast.isPointer old_type) then
            if Ast.size new_type = 8 then (makePointerIntoLong (Ast.signed new_type) tacExpr) else
            let dst = Tac.Var (Temp.newTemp(), parseType new_type) in
            let () = ((Tac.Truncate (tacExpr, dst)) #: instrs) in
            dst

        else if (Ast.size new_type) = (Ast.size old_type) then
            (flipIsSigned tacExpr)

        else
            let dst = Tac.Var (Temp.newTemp(), parseType new_type) in

            if (Ast.isFloatingPoint new_type) && (Ast.isFloatingPoint old_type) then failwith "float32 not implemented" else

            let () = if (Ast.isFloatingPoint new_type) then
            begin match old_type with
                | Ast.Int
                | Ast.Long -> (Tac.IntToFloat (tacExpr, dst)) #: instrs
                | Ast.UInt
                | Ast.ULong -> (Tac.UIntToFloat (tacExpr, dst)) #: instrs
                | Ast.Double -> failwith "Impossible."
                | Ast.FunType _ -> failwith "Impossible."
                | Ast.Ptr _ -> failwith "Impossible."
            end
            else if (Ast.isFloatingPoint old_type) then
            begin match new_type with
                | Ast.Int
                | Ast.Long -> (Tac.FloatToInt (tacExpr, dst)) #: instrs
                | Ast.UInt
                | Ast.ULong -> (Tac.FloatToUInt (tacExpr, dst)) #: instrs
                | Ast.Double -> failwith "Impossible."
                | Ast.FunType _ -> failwith "Impossible."
                | Ast.Ptr _ -> failwith "Impossible."
            end

            else if (Ast.size new_type) < (Ast.size old_type) then
                ((Tac.Truncate (tacExpr, dst)) #: instrs)
            else if (Ast.signed old_type) then
                ((Tac.SignExtend (tacExpr, dst)) #: instrs)
            else
                ((Tac.ZeroExtend (tacExpr, dst)) #: instrs)
            in dst


    and parseExpr_lval_convert (expr:Ast.typed_expr) =
        let r = parseExpr expr in
        match r with
            | PlainOperand oper -> oper
            | DereferencedPointer oper ->
                let dst = Tac.Var (Temp.newTemp(), Tac.operand_type oper) in
                let () = (Tac.Load (oper, dst)) #: instrs in
                dst

    and parseExpr (expr:Ast.typed_expr) =
        match expr with
            | _, Ast.Literal lit -> PlainOperand (Tac.Constant (parseLiteral lit))
            | typ, Ast.Var (id, Ast.AutoVariable _) -> PlainOperand (Tac.Var (id, parseType typ))
            | typ, Ast.Var (id, Ast.StaticVariable _) -> PlainOperand (Tac.StaticVar (id, parseType typ))
            | _, Ast.Var (_, Ast.Function _) -> failwith "No support for function variables"

            | _, Ast.Cast (new_type, ((inner_type, _) as inner_expr)) ->
                let result = parseExpr_lval_convert inner_expr in
                PlainOperand (cast inner_type new_type result)

            | typ, Ast.Unary (Ast.Increment, dst) ->
                let dst = parseExpr dst in
                begin match dst with
                    | PlainOperand oper ->
                        let () = (Tac.Unary (Tac.Incr, oper, oper)) #: instrs in
                        dst
                    | DereferencedPointer oper ->
                        let dst = Tac.Var (Temp.newTemp(), parseType typ) in
                        let () = (Tac.Load (oper, dst)) #: instrs in
                        let () = (Tac.Unary (Tac.Incr, dst, dst)) #: instrs in
                        let () = (Tac.Store (dst, oper)) #: instrs in
                        PlainOperand dst
                end

            | typ, Ast.Unary (Ast.Decrement, dst) ->
                let dst = parseExpr dst in
                begin match dst with
                    | PlainOperand oper ->
                        let () = (Tac.Unary (Tac.Decr, oper, oper)) #: instrs in
                        dst
                    | DereferencedPointer oper ->
                        let dst = Tac.Var (Temp.newTemp(), parseType typ) in
                        let () = (Tac.Load (oper, dst)) #: instrs in
                        let () = (Tac.Unary (Tac.Decr, dst, dst)) #: instrs in
                        let () = (Tac.Store (dst, oper)) #: instrs in
                        PlainOperand dst
                end

            | _, Ast.Unary (Ast.Rvalue, src) -> parseExpr src
            | typ, Ast.Unary (op, expr) ->
                let src = parseExpr_lval_convert expr in
                let dst = Tac.Var (Temp.newTemp(), parseType typ) in
                let op = parseUnaryOp op in
                let () = (Tac.Unary (op, src, dst)) #: instrs in
                PlainOperand dst

            | _, Ast.Dereference expr ->
                DereferencedPointer (unpointerOnce (parseExpr_lval_convert expr))

            | typ, Ast.AddressOf expr ->
                let oper = parseExpr expr in
                begin match oper with
                    | PlainOperand oper ->
                        let dst = Tac.Var (Temp.newTemp(), parseType typ) in
                        let () = (Tac.GetAddress (oper, dst)) #: instrs in
                        PlainOperand dst
                    | DereferencedPointer oper ->
                        PlainOperand oper
                end

            | _, Ast.BinarySp (Ast.LogAnd, (left, between), right) ->
                let false_lbl = Label.newLbl() in
                let end_lbl = Label.newLbl() in
                let left = parseExpr_lval_convert left in
                let () = (Tac.JumpIfZero (left, false_lbl)) #: instrs in
                let () = List.iter (fun stmt -> parseStmt stmt) between in
                let right = parseExpr_lval_convert right in
                let () = (Tac.JumpIfZero (right, false_lbl)) #: instrs in
                let result = Tac.Var (Temp.newTemp(), Tac.Int32 true) in
                let () = (Tac.Copy (Tac.Constant (Tac.I (Z.one, Tac.Int32 true)), result)) #: instrs in
                let () = (Tac.Jump end_lbl) #: instrs in
                let () = (Tac.Label false_lbl) #: instrs in
                let () = (Tac.Copy (Tac.Constant (Tac.I (Z.zero, Tac.Int32 true)), result)) #: instrs in
                let () = (Tac.Label end_lbl) #: instrs in
                PlainOperand result

            | _, Ast.BinarySp (Ast.LogOr, (left, between), right) ->
                let true_lbl = Label.newLbl() in
                let end_lbl = Label.newLbl() in
                let left = parseExpr_lval_convert left in
                let () = (Tac.JumpIfNotZero (left, true_lbl)) #: instrs in
                let () = List.iter (fun stmt -> parseStmt stmt) between in
                let right = parseExpr_lval_convert right in
                let () = (Tac.JumpIfNotZero (right, true_lbl)) #: instrs in
                let result = Tac.Var (Temp.newTemp(), Tac.Int32 true) in
                let () = (Tac.Copy (Tac.Constant (Tac.I (Z.zero, Tac.Int32 true)), result)) #: instrs in
                let () = (Tac.Jump end_lbl) #: instrs in
                let () = (Tac.Label true_lbl) #: instrs in
                let () = (Tac.Copy (Tac.Constant (Tac.I (Z.one, Tac.Int32 true)), result)) #: instrs in
                let () = (Tac.Label end_lbl) #: instrs in
                PlainOperand result

            | _, Ast.BinarySp (Ast.Comma, _, _) -> failwith "TODO: Add Comma"

            | typ, Ast.Binary (op, left, right) ->
                let src1 = parseExpr_lval_convert left in
                let src2 = parseExpr_lval_convert right in
                let dst = Tac.Var (Temp.newTemp(), parseType typ) in
                let op = parseBinaryOp op in
                let () = (Tac.Binary (op, src1, src2, dst)) #: instrs in
                PlainOperand dst

            | typ, Ast.BinaryAssign (op, dst, src, rhs_type_opt) ->
                (*let () = match dst with (_, Ast.Var _) -> () | _ -> failwith "BinaryAssign dst is not a var" in*)
                let src = parseExpr_lval_convert src in
                let dst = parseExpr dst in
                let op = parseBinaryOp op in
                begin match dst with
                    | PlainOperand oper -> (match rhs_type_opt with
                        | None ->
                            let () = (Tac.Binary (op, oper, src, oper)) #: instrs in
                            dst
                        | Some rhs_type ->
                            let bin_lhs = cast typ rhs_type oper in
                            let bin_var = Tac.Var (Temp.newTemp(), parseType rhs_type) in
                            let () = (Tac.Binary (op, bin_lhs, src, bin_var)) #: instrs in
                            let casted_back_rhs = cast rhs_type typ bin_var in
                            let () = (Tac.Copy (casted_back_rhs, oper)) #: instrs in
                            PlainOperand oper
                    )
                    | DereferencedPointer oper ->
                        let dst = Tac.Var (Temp.newTemp(), parseType typ) in
                        let () = (Tac.Load (oper, dst)) #: instrs in
                        (match rhs_type_opt with
                        | None ->
                            let () = (Tac.Binary (op, dst, src, dst)) #: instrs in
                            let () = (Tac.Store (dst, oper)) #: instrs in
                            PlainOperand dst
                        | Some rhs_type ->
                            let bin_lhs = cast typ rhs_type dst in
                            let bin_var = Tac.Var (Temp.newTemp(), parseType rhs_type) in
                            let () = (Tac.Binary (op, bin_lhs, src, bin_var)) #: instrs in
                            let casted_back_rhs = cast rhs_type typ bin_var in
                            let () = (Tac.Store (casted_back_rhs, oper)) #: instrs in
                            PlainOperand casted_back_rhs
                        )
                end

            | _, Ast.Assignment (left, right) ->
                (*let dst = (match left with (_, Ast.Var (v, Ast.AutoVariable _)) -> Tac.Var (v, parseType typ)*)
                (*                         | (_, Ast.Var (v, Ast.StaticVariable _)) -> Tac.StaticVar (v, parseType typ)*)
                (*                         | _ -> failwith "lvalue of Assignment is not a variable") in*)
                let src = parseExpr_lval_convert right in
                let dst = parseExpr left in
                begin match dst with
                    | PlainOperand dst ->
                        let () = (Tac.Copy (src, dst)) #: instrs in
                        PlainOperand dst
                    | DereferencedPointer dst ->
                        let () = (Tac.Store (src, dst)) #: instrs in
                        PlainOperand src
                end

            | typ, Ast.Ternary ((cond, postfix), th, el) -> 
                let cond = parseExpr_lval_convert cond in
                let else_lbl = Label.newLbl() in
                let end_lbl = Label.newLbl() in
                let result = Tac.Var(Temp.newTemp(), parseType typ) in
                let () = (Tac.JumpIfZero (cond, else_lbl)) #: instrs in
                let () = List.iter (fun stmt -> parseStmt stmt) postfix in
                let th = parseExpr_lval_convert th in
                let () = (Tac.Copy (th, result)) #: instrs in
                let () = (Tac.Jump end_lbl) #: instrs in
                let () = (Tac.Label else_lbl) #: instrs in
                let () = List.iter (fun stmt -> parseStmt stmt) postfix in
                let el = parseExpr_lval_convert el in
                let () = (Tac.Copy (el, result)) #: instrs in
                let () = (Tac.Label end_lbl) #: instrs in
                PlainOperand result

            | typ, Ast.Call (name, args) ->
                let args = List.map (fun arg -> parseExpr_lval_convert arg) args in
                let dst = Tac.Var(Temp.newTemp(), parseType typ) in
                let () = (Tac.Call (name, args, dst)) #: instrs in
                PlainOperand dst


    and parseStmt stmt =
        match stmt with
            | Ast.Return expr ->
                let src = parseExpr_lval_convert expr in
                (Tac.Return src) #: instrs
            | Ast.Expression expr -> let _ = parseExpr expr in ()

            | Ast.If ((cond, postfix), th, None) ->
                let newCond = helpParseConditionWithPostfix postfix cond in
                let cond = parseExpr_lval_convert newCond in
                let end_lbl = Label.newLbl() in
                let () = (Tac.JumpIfZero (cond, end_lbl)) #: instrs in
                let () = parseStmt th in
                (Tac.Label end_lbl) #: instrs
            | Ast.If ((cond, postfix), th, Some el) ->
                let newCond = helpParseConditionWithPostfix postfix cond in
                let cond = parseExpr_lval_convert newCond in
                let else_lbl = Label.newLbl() in
                let end_lbl = Label.newLbl() in
                let () = (Tac.JumpIfZero (cond, else_lbl)) #: instrs in
                let () = parseStmt th in
                let () = (Tac.Jump end_lbl) #: instrs in
                let () = (Tac.Label else_lbl) #: instrs in
                let () = parseStmt el in
                (Tac.Label end_lbl) #: instrs

            | Ast.Switch ((cond, postfix), cases, stmt, break, default) ->
                let newCond = helpParseConditionWithPostfix postfix cond in
                let cond = parseExpr_lval_convert newCond in
                let () = parseCases cond cases in
                let () = (Tac.Jump default) #: instrs in
                let () = parseStmt stmt in
                (Tac.Label break) #: instrs

            | Ast.DoWhile (body, (cond, postfix), (continue, break)) ->
                let begin_lbl = Label.newLbl() in
                let () = (Tac.Label begin_lbl) #: instrs in
                let () = parseStmt body in
                let () = (Tac.Label continue) #: instrs in
                let newCond = helpParseConditionWithPostfix postfix cond in
                let cond = parseExpr_lval_convert newCond in
                let () = (Tac.JumpIfNotZero (cond, begin_lbl)) #: instrs in
                (Tac.Label break) #: instrs

            | Ast.While ((cond, postfix), body, (continue, break)) ->
                let () = (Tac.Label continue) #: instrs in
                let newCond = helpParseConditionWithPostfix postfix cond in
                let cond = parseExpr_lval_convert newCond in
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
                let begin_lbl = Label.newLbl() in
                let () = (Tac.Label begin_lbl) #: instrs in
                let cond = begin match cond_opt with
                    | None -> None
                    | Some (cond, postfix) ->
                        let newCond = helpParseConditionWithPostfix postfix cond in
                        Some (parseExpr_lval_convert newCond)
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
                let src = parseExpr_lval_convert (typ, expr) in
                (Tac.Copy (src, Tac.Var(id, parseType typ))) #: instrs

            | Ast.VarDecl (id, None, typ, Some Ast.Static) ->
                localStatics := (Tac.StaticVariable (id, false, Tac.I (Z.zero, parseType typ))) :: !localStatics

            | Ast.VarDecl (id, Some expr , typ, Some Ast.Static) ->
                let i = Const.parseConstExpr (typ, expr) (*(Some globalEnv)*) in
                localStatics := (Tac.StaticVariable (id, false, (const_to_tacky i (parseType typ)))) :: !localStatics

            | _ -> ()

    and parseBlockItems block_items = match block_items with
        | [] -> ()
        | (Ast.S stmt) :: rest -> parseStmt stmt; parseBlockItems rest
        | (Ast.D decl) :: rest -> parseDecl decl; parseBlockItems rest

    in let rec parseTopLevel tls = match tls with
        | [] -> []
        | tl :: rest -> begin match tl with
            | Ast.FunDecl (name, params, block_items, ret_type, _) ->
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

                let ret_type = parseType ret_type in
                let zero_number = Tac.number_zero_operand ret_type in

                let () = (Tac.Return zero_number) #: instrs in
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
                | Environment.Tentative -> (Tac.StaticVariable (id, is_global, Tac.number_zero (parseType typ))) :: acc
                | Environment.Initial i -> (Tac.StaticVariable (id, is_global, (const_to_tacky i (parseType typ)))) :: acc
            end
        | Environment.FunAttr ((id,_,_,is_defined),is_global) ->
            let () = if (not is_defined) && is_global then undefinedNames := Environment.setAdd id !undefinedNames
            in acc
    ) globalEnv []


    in let replaceIllegalSSE toplevels =
        let new_toplevels = List.map (fun tl -> (match tl with
            | Tac.Function (name, is_global, params, instructions) ->
                let rec iter instrs = match instrs with
                    | [] -> []
                    | h :: rest -> begin match h with
                        | Tac.Return (Tac.Constant D num) ->
                            Tac.Return (Tac.StaticVar (Label.getLabelDouble num, Tac.Float64)) :: iter rest
                        | Tac.FloatToInt (Tac.Constant D num, (Tac.Var (_, typ) as dst))
                        | Tac.FloatToUInt (Tac.Constant D num, (Tac.Var (_, typ) as dst)) ->
                            Tac.Copy (Tac.Constant (Tac.I (Const.trunc (if Float.is_nan num then Z.one else Z.of_float num) (Tac.to_ast_type typ), typ)), dst) :: iter rest
                        | Tac.IntToFloat (Tac.Constant (Tac.I (num, _)), (Tac.Var (_, Tac.Float64) as dst))
                        | Tac.UIntToFloat (Tac.Constant (Tac.I (num, _)), (Tac.Var (_, Tac.Float64) as dst)) ->
                            Tac.Copy (Tac.StaticVar (Label.getLabelDouble (Z.extract num 0 64 |> Z.to_float), Tac.Float64), dst) :: iter rest


                        | Tac.Unary (Tac.Negate, (Tac.Constant D num), dst) ->
                            Tac.Binary (Tac.Xor, Tac.StaticVar ((Label.getLabelDouble (-0.0)), Tac.Float64), Tac.StaticVar ((Label.getLabelDouble num), Tac.Float64), dst) :: iter rest

                        | Tac.Unary (Tac.Negate, src, dst) when Tac.operand_type src = Float64 ->
                            Tac.Binary (Tac.Xor, Tac.StaticVar ((Label.getLabelDouble (-0.0)), Tac.Float64), src, dst) :: iter rest

                        | Tac.Unary (op, (Tac.Constant D num), dst) ->
                            Tac.Unary (op, Tac.StaticVar ((Label.getLabelDouble num), Tac.Float64), dst) :: iter rest


                        | Tac.Binary (op, (Tac.Constant D num1), (Tac.Constant D num2), dst) ->
                            Tac.Binary (op, Tac.StaticVar ((Label.getLabelDouble num1), Tac.Float64), Tac.StaticVar ((Label.getLabelDouble num2), Tac.Float64), dst) :: iter rest
                        | Tac.Binary (op, (Tac.Constant D num), src2, dst) ->
                            Tac.Binary (op, Tac.StaticVar ((Label.getLabelDouble num), Tac.Float64), src2, dst) :: iter rest
                        | Tac.Binary (op, src1, (Tac.Constant D num), dst) ->
                            Tac.Binary (op, src1, Tac.StaticVar ((Label.getLabelDouble num), Tac.Float64), dst) :: iter rest

                        | Tac.Copy ((Tac.Constant D num), dst) ->
                            Tac.Copy (Tac.StaticVar ((Label.getLabelDouble num), Tac.Float64), dst) :: iter rest

                        | Tac.Store ((Tac.Constant D num), dst) ->
                            Tac.Store (Tac.StaticVar ((Label.getLabelDouble num), Tac.Float64), dst) :: iter rest

                        | Tac.JumpIfZero ((Tac.Constant D num), lbl) ->
                            Tac.JumpIfZero (Tac.StaticVar ((Label.getLabelDouble num), Tac.Float64), lbl) :: iter rest
                        | Tac.JumpIfNotZero ((Tac.Constant D num), lbl) ->
                            Tac.JumpIfNotZero (Tac.StaticVar ((Label.getLabelDouble num), Tac.Float64), lbl) :: iter rest

                        | Tac.Call (name, args, dst) ->
                            let new_args = List.map (fun arg -> match arg with
                                | Tac.Constant D num -> Tac.StaticVar (Label.getLabelDouble num, Tac.Float64)
                                | _ -> arg
                            ) args in
                            Tac.Call (name, new_args, dst) :: iter rest

                        | _ -> h :: iter rest
                    end
                in let new_instrs = iter instructions
                in Tac.Function (name, is_global, params, new_instrs)
            | _ -> tl)) toplevels
        in new_toplevels @ (Label.labelDoubleFlushToList() |> List.map (fun (num, lbl) -> Tac.StaticConst (lbl, Tac.D num)))


    in try match ast with
        | Ast.Program tls -> let p = (parseTopLevel tls) @ (parseStaticVarsAndNoticeUndefinedExternFunctions())
                             in let p = replaceIllegalSSE p
                             in Tac.Program (p @ !localStatics), !undefinedNames
    with Environment.EnvironmentError e -> raise (TackyError e)

