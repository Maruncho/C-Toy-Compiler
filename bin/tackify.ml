
module Tac = Tacky

exception TackyError of string

type lval = PlainOperand of Tac.operand
          | DereferencedPointer of Tac.operand

let voidOperand = (Tac.Var("VOIDVAR", Tac.Void))

let parseUnaryOp = function
        | Ast.Negate -> Tac.Negate
        | Ast.Complement -> Tac.Complement
        | Ast.LogNot -> Tac.Not
        | Ast.Increment -> Tac.Incr
        | Ast.Decrement -> Tac.Decr
        | Ast.PtrIncrement | Ast.PtrDecrement -> failwith "Pointer arithmetic should be handled separatedly in parseUnary"
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
        | Ast.PtrAdd | Ast.PtrSub | Ast.PtrPtrSub -> failwith "Pointer arithmetic should be handled separatedly in parseBinary"
        | Ast.Assign -> failwith "assignment operator is not handled by parseBinary"

let const_to_tacky c typ = match c with
    | Const.I n -> Tac.I (n, typ)
    | Const.D n -> Tac.D n
    | Const.S str -> Tac.S str


let add_padding current typ =
    let bytes = typ |> Tac.to_ast_type |> Ast.indexing_size in
    let modulo = Int64.rem current bytes in
    if Int64.equal modulo 0L then 0L else Int64.sub bytes modulo

let compound_align_and_count ast_typ =
    let size = Ast.indexing_size ast_typ in

    let align = Ast.alignment ast_typ in
    let modulo = Int64.rem size align in
    let padding = if Int64.equal modulo 0L then 0L else Int64.sub align modulo in

    let size = Int64.add size padding in

    align, (Int64.div size align)

let unpointerOnce = function
    | Tac.Var (i, Tac.Ptr t) -> Tac.Var (i, t)
    | Tac.StaticVar (i, Tac.Ptr t) -> Tac.StaticVar (i, t)
    | _ -> failwith "Don't use unpointerOnce() with non-pointer"

let pointerOnce = function
    | Tac.Var (i, t) -> Tac.Var (i, Tac.Ptr t)
    | Tac.StaticVar (i, t) -> Tac.StaticVar (i, Tac.Ptr t)
    | _ -> failwith "Don't use pointerOnce() with non-pointer"

let decayArray = function
    | Tac.Var (i, Tac.ArrObj (t, _)) -> Tac.Var (i, Tac.Ptr t)
    | Tac.StaticVar (i, Tac.ArrObj (t, _)) -> Tac.StaticVar (i, Tac.Ptr t)
    | x -> x

let makeLongIntoPointer ptr = function
    | Tac.Var (i, Tac.Int64 _) -> Tac.Var (i, ptr)
    | Tac.StaticVar (i, Tac.Int64 _) -> Tac.StaticVar (i, ptr)
    | Tac.Constant (I (n, Tac.Int64 _)) -> Tac.Constant (I (n, ptr))
    | _ -> failwith "Don't use makeLongIntoPointer with non-long integers"

let makePointerIntoLong sign = function
    | Tac.Var (i, Tac.Ptr _) -> Tac.Var (i, Tac.Int64 sign)
    | Tac.StaticVar (i, Tac.Ptr _) -> Tac.StaticVar (i, Tac.Int64 sign)
    | _ -> failwith "Don't use makePointerIntoULong with non-pointers"

let changePtrType oper new_ptr = match oper with
    | Tac.Var (i, Tac.Ptr _) -> Tac.Var (i, new_ptr)
    | Tac.StaticVar (i, Tac.Ptr _) -> Tac.StaticVar (i, new_ptr)
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
            | Ast.Expression (typ, Ast.Unary (Ast.PtrIncrement, (_, Ast.Var (old, StaticVariable _)))) -> ((old, Temp.newTemp()), (parseType typ, true)) :: lst
            | Ast.Expression (typ, Ast.Unary (Ast.PtrIncrement, (_, Ast.Var (old, _)))) -> ((old, Temp.newTemp()), (parseType typ, false)) :: lst
            | Ast.Expression (typ, Ast.Unary (Ast.PtrDecrement, (_, Ast.Var (old, StaticVariable _)))) -> ((old, Temp.newTemp()), (parseType typ, true)) :: lst
            | Ast.Expression (typ, Ast.Unary (Ast.PtrDecrement, (_, Ast.Var (old, _)))) -> ((old, Temp.newTemp()), (parseType typ, false)) :: lst
            | _ -> lst
        )) [] postfix) |> List.split
        in let derefsToVars = List.fold_left (fun lst stmt -> (match stmt with
            | Ast.Expression (typ, Ast.Unary (Ast.Increment, (_, Ast.Dereference _ as deref)))
            | Ast.Expression (typ, Ast.Unary (Ast.Decrement, (_, Ast.Dereference _ as deref)))
            | Ast.Expression (typ, Ast.Unary (Ast.PtrIncrement, (_, Ast.Dereference _ as deref)))
            | Ast.Expression (typ, Ast.Unary (Ast.PtrDecrement, (_, Ast.Dereference _ as deref)))
            | Ast.Expression (typ, Ast.Unary (Ast.Increment, (_, Ast.Subscript _ as deref)))
            | Ast.Expression (typ, Ast.Unary (Ast.Decrement, (_, Ast.Subscript _ as deref)))
            | Ast.Expression (typ, Ast.Unary (Ast.PtrIncrement, (_, Ast.Subscript _ as deref)))
            | Ast.Expression (typ, Ast.Unary (Ast.PtrDecrement, (_, Ast.Subscript _ as deref))) ->
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
            | typ, Ast.Subscript (sub1, sub2) -> begin match List.assoc_opt expr derefsToVars with
                | None -> typ, Ast.Subscript ((walkExpr sub1), (walkExpr sub2))
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
            | typ, Ast.String str -> typ, Ast.String str
            | typ, Ast.SizeOf t_expr -> typ, Ast.SizeOf (walkExpr t_expr)
            | typ, Ast.SizeOfT x -> typ, Ast.SizeOfT x

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

    and parseLiteral : Ast.lit -> Tac.constant = function
        | Ast.Int8 num -> Tac.I (Z.of_int num, Tac.Int8 true)
        | Ast.Int32 num -> Tac.I (Z.of_int32 num, Tac.Int32 true)
        | Ast.Int64 num -> Tac.I (Z.of_int64 num, Tac.Int64 true)
        | Ast.UInt8 num -> Tac.I (Z.of_int num, Tac.Int8 false)
        | Ast.UInt32 num -> Tac.I (Z.of_int32 num, Tac.Int32 false)
        | Ast.UInt64 num -> Tac.I (Z.of_int64 num, Tac.Int64 false)
        | Ast.Float64 num -> Tac.D num

    and parseType = function
        | Ast.Char -> Tac.Int8 true
        | Ast.SChar -> Tac.Int8 true
        | Ast.Int -> Tac.Int32 true
        | Ast.Long -> Tac.Int64 true
        | Ast.UChar -> Tac.Int8 false
        | Ast.UInt -> Tac.Int32 false
        | Ast.ULong -> Tac.Int64 false
        | Ast.Double -> Tac.Float64
        | Ast.Ptr x -> Tac.Ptr (parseType x)
        | Ast.Array (t, s) -> Tac.ArrObj (parseType t, s) (*failwith "DEBUG: SEE IF parseTYPE IS CALLED WITH ARRAY."*)
        | Ast.Void -> Tac.Void
        | Ast.FunType _ -> failwith "parseType should not handle funtype"

    and flipIsSigned =
        let flipType = function
            | Tac.Int8 s -> Tac.Int8 (not s)
            | Tac.Int32 s -> Tac.Int32 (not s)
            | Tac.Int64 s -> Tac.Int64 (not s)
            | Tac.Float64 -> failwith "Cannot call flipIsSigned with float"
            | Tac.Ptr _ -> failwith "Cannot call flipIsSigned with ptr"
            | Tac.ArrObj _ -> failwith "Cannot call flipIsSigned with arrObj"
            | Tac.Void -> failwith "Cannot call flisIsSigned with void"
        in function
            | Tac.Constant Tac.I (n, t) -> Tac.Constant (Tac.I (n, flipType t))
            | Tac.Var (n, t) -> Tac.Var (n, flipType t)
            | Tac.StaticVar (n, t) -> Tac.StaticVar (n, flipType t)
            | Tac.Constant Tac.D _ -> failwith "Cannot call flipIsSigned with float"
            | Tac.Constant Tac.S _ -> failwith "Cannot call flipIsSigned with string"
            | Tac.Constant Tac.ZeroInit _ -> failwith "Cannot call flipIsSigned with ZeroInit"

    and subParseBinary op typ src1 src2 dst = match op with
        | Ast.PtrAdd ->
            (Tac.AddPtr (src1, src2, Ast.array_scale typ, dst)) #: instrs
        | Ast.PtrSub ->
            let negated = Tac.Var (Temp.newTemp(), parseType Ast.Long) in
            let () = (Tac.Unary (Tac.Negate, src2, negated)) #: instrs in
            (Tac.AddPtr (src1, negated, Ast.array_scale typ, dst)) #: instrs
        | Ast.PtrPtrSub ->
            let array_scale = src1 |> Tac.operand_type |> Tac.to_ast_type |> Ast.array_scale in
            let scale_const = Tac.Constant (Tac.I (Z.of_int64 array_scale, Tac.Int64 true)) in
            let longed_src1 = makePointerIntoLong (Ast.signed typ) src1 in
            let longed_src2 = makePointerIntoLong (Ast.signed typ) src2 in
            let temp_dst = Tac.Var (Temp.newTemp(), parseType Ast.Long) in
            let () = (Tac.Binary (Tac.Subtract, longed_src1, longed_src2, temp_dst)) #: instrs in
            (Tac.Binary (Tac.Divide, temp_dst, scale_const, dst)) #: instrs
        | _ ->
            let op = parseBinaryOp op in
            (Tac.Binary (op, src1, src2, dst)) #: instrs

    and cast old_type new_type tacExpr =
        let () = print_string((Ast.string_data_type old_type) ^ " " ^ (Ast.string_data_type new_type) ^ " " ^ (Tac.typ_str (Tac.operand_type tacExpr)) ^ " \n") in
        if old_type = new_type then tacExpr else

        if (Ast.Void = new_type) then voidOperand else

        if (Ast.isPointer old_type) && (Ast.isPointer new_type) then
            changePtrType tacExpr (parseType new_type)
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
                | Ast.Char
                | Ast.SChar
                | Ast.Int
                | Ast.Long -> (Tac.IntToFloat (tacExpr, dst)) #: instrs
                | Ast.UChar
                | Ast.UInt
                | Ast.ULong -> (Tac.UIntToFloat (tacExpr, dst)) #: instrs
                | Ast.Double -> failwith "Impossible."
                | Ast.FunType _ -> failwith "Impossible."
                | Ast.Ptr _ -> failwith "Impossible."
                | Ast.Array _ -> failwith "Impossible."
                | Ast.Void -> failwith "Impossible."
            end
            else if (Ast.isFloatingPoint old_type) then
            begin match new_type with
                | Ast.Char
                | Ast.SChar
                | Ast.Int
                | Ast.Long -> (Tac.FloatToInt (tacExpr, dst)) #: instrs
                | Ast.UChar
                | Ast.UInt
                | Ast.ULong -> (Tac.FloatToUInt (tacExpr, dst)) #: instrs
                | Ast.Double -> failwith "Impossible."
                | Ast.FunType _ -> failwith "Impossible."
                | Ast.Ptr _ -> failwith "Impossible."
                | Ast.Array _ -> failwith "Impossible."
                | Ast.Void -> failwith "Impossible."
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

            | char_ptr, Ast.String str ->
                let src = Tac.StaticVar ((Label.getLabelString str), parseType char_ptr) in
                let dst = Tac.Var (Temp.newTemp(), parseType char_ptr) in
                let () = (Tac.GetAddress (src, dst)) #: instrs in
                PlainOperand dst

            | _, Ast.Cast (new_type, ((inner_type, _) as inner_expr)) ->
                let result = parseExpr_lval_convert inner_expr in
                PlainOperand (cast inner_type new_type result)

            | typ, Ast.Unary ((Ast.Increment as op), dst)
            | typ, Ast.Unary ((Ast.PtrIncrement as op), dst) ->
                let dst = parseExpr dst in
                begin match dst with
                    | PlainOperand oper ->
                        if (op = Ast.Increment) then
                            let () = (Tac.Unary (Tac.Incr, oper, oper)) #: instrs in
                            dst
                        else
                            let () = (Tac.AddPtr (oper, Tac.Constant (Tac.I (Z.one, Tac.Int64 true)), Ast.array_scale typ, oper)) #: instrs in
                            dst
                    | DereferencedPointer oper ->
                        let dst = Tac.Var (Temp.newTemp(), parseType typ) in
                        let () = (Tac.Load (oper, dst)) #: instrs in
                        let () = if (op = Ast.Increment) then
                            (Tac.Unary (Tac.Incr, dst, dst)) #: instrs
                        else
                            (Tac.AddPtr (dst, Tac.Constant (Tac.I (Z.one, Tac.Int64 true)), Ast.array_scale typ, dst)) #: instrs
                        in let () = (Tac.Store (dst, oper)) #: instrs in
                        PlainOperand dst
                end

            | typ, Ast.Unary ((Ast.Decrement as op), dst)
            | typ, Ast.Unary ((Ast.PtrDecrement as op), dst) ->
                let dst = parseExpr dst in
                begin match dst with
                    | PlainOperand oper ->
                        if (op = Ast.Decrement) then
                            let () = (Tac.Unary (Tac.Decr, oper, oper)) #: instrs in
                            dst
                        else
                            let () = (Tac.AddPtr (oper, Tac.Constant (Tac.I (Z.minus_one, Tac.Int64 true)), Ast.array_scale typ, oper)) #: instrs in
                            dst
                    | DereferencedPointer oper ->
                        let dst = Tac.Var (Temp.newTemp(), parseType typ) in
                        let () = (Tac.Load (oper, dst)) #: instrs in
                        let () = if (op = Ast.Decrement) then
                            (Tac.Unary (Tac.Decr, dst, dst)) #: instrs
                        else
                            (Tac.AddPtr (dst, Tac.Constant (Tac.I (Z.minus_one, Tac.Int64 true)), Ast.array_scale typ, dst)) #: instrs
                        in let () = (Tac.Store (dst, oper)) #: instrs in
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
                        PlainOperand (decayArray oper)
                end

            | typ, Ast.Subscript (src1, src2) ->
                let src1 = parseExpr_lval_convert src1 in
                let src2 = parseExpr_lval_convert src2 in
                let dst = Tac.Var (Temp.newTemp(), parseType typ) in
                let () = (Tac.AddPtr (src1, src2, (Ast.indexing_size typ), dst)) #: instrs in
                DereferencedPointer dst

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
                let () = subParseBinary op typ src1 src2 dst
                in PlainOperand dst

            | typ, Ast.BinaryAssign (op, dst, src, rhs_type_opt) ->
                let src = parseExpr_lval_convert src in
                let dst = parseExpr dst in
                (*let op = parseBinaryOp op in*)
                begin match dst with
                    | PlainOperand oper -> (match rhs_type_opt with
                        | None ->
                            (*let () = (Tac.Binary (op, oper, src, oper)) #: instrs in*)
                            let () = subParseBinary op typ oper src oper in
                            dst
                        | Some rhs_type ->
                            let bin_lhs = cast typ rhs_type oper in
                            let bin_var = Tac.Var (Temp.newTemp(), parseType rhs_type) in
                            (*let () = (Tac.Binary (op, bin_lhs, src, bin_var)) #: instrs in*)
                            let () = subParseBinary op typ bin_lhs src bin_var in
                            let casted_back_rhs = cast rhs_type typ bin_var in
                            let () = (Tac.Copy (casted_back_rhs, oper)) #: instrs in
                            PlainOperand oper
                    )
                    | DereferencedPointer oper ->
                        let dst = Tac.Var (Temp.newTemp(), parseType typ) in
                        let () = (Tac.Load (oper, dst)) #: instrs in
                        (match rhs_type_opt with
                        | None ->
                            (*let () = (Tac.Binary (op, dst, src, dst)) #: instrs in*)
                            let () = subParseBinary op typ dst src dst in
                            let () = (Tac.Store (dst, oper)) #: instrs in
                            PlainOperand dst
                        | Some rhs_type ->
                            let bin_lhs = cast typ rhs_type dst in
                            let bin_var = Tac.Var (Temp.newTemp(), parseType rhs_type) in
                            (*let () = (Tac.Binary (op, bin_lhs, src, bin_var)) #: instrs in*)
                            let () = subParseBinary op typ bin_lhs src bin_var in
                            let casted_back_rhs = cast rhs_type typ bin_var in
                            let () = (Tac.Store (casted_back_rhs, oper)) #: instrs in
                            PlainOperand casted_back_rhs
                        )
                end

            | _, Ast.Assignment (left, right) ->
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
                let result = if typ = Ast.Void then voidOperand else Tac.Var(Temp.newTemp(), parseType typ) in
                let () = (Tac.JumpIfZero (cond, else_lbl)) #: instrs in
                let () = List.iter (fun stmt -> parseStmt stmt) postfix in
                let th = parseExpr_lval_convert th in
                let () = if typ = Ast.Void then () else (Tac.Copy (th, result)) #: instrs in
                let () = (Tac.Jump end_lbl) #: instrs in
                let () = (Tac.Label else_lbl) #: instrs in
                let () = List.iter (fun stmt -> parseStmt stmt) postfix in
                let el = parseExpr_lval_convert el in
                let () = if typ = Ast.Void then () else (Tac.Copy (el, result)) #: instrs in
                let () = (Tac.Label end_lbl) #: instrs in
                PlainOperand result

            | typ, Ast.Call (name, args) ->
                let args = List.map (fun arg -> parseExpr_lval_convert arg) args in
                if typ = Ast.Void then
                    let () = (Tac.Call (name, args, None)) #: instrs in
                    PlainOperand voidOperand
                else
                    let dst = (Tac.Var(Temp.newTemp(), parseType typ)) in
                    let () = (Tac.Call (name, args, Some dst)) #: instrs in
                    PlainOperand dst

            | (size_t, SizeOf ((typ, _) as t_expr)) ->
                begin match t_expr with
                    | _, Ast.String str -> PlainOperand (Tac.Constant (Tac.I (Z.of_int (String.length str), parseType size_t)))
                    | _ -> PlainOperand (Tac.Constant (Tac.I ((Z.of_int64 (Ast.indexing_size (typ))), parseType size_t)))
                end
            | (size_t, SizeOfT typ) ->
                PlainOperand (Tac.Constant (Tac.I ((Z.of_int64 (Ast.indexing_size (typ))), parseType size_t)))


    and parseStmt stmt =
        match stmt with
            | Ast.Return None ->
                (Tac.Return None) #: instrs
            | Ast.Return (Some expr) ->
                let src = parseExpr_lval_convert expr in
                (Tac.Return (Some src)) #: instrs
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
            | Ast.VarDecl (id, None, typ, None) -> begin match typ with
                | Ast.Array _ ->
                    let (aln, cnt) = compound_align_and_count typ in
                    (Tac.DeclCompound (id, aln, cnt)) #: instrs
                | _ -> ()
            end
            | Ast.VarDecl (id, Some init, typ, None) -> 
                begin match init with
                    | Ast.SingleInit _ ->
                        let srcs = parseInitialiser init in
                        (Tac.Copy (List.hd srcs, Tac.Var(id, parseType typ))) #: instrs
                    | Ast.CompoundInit _ ->
                        let obj = Tac.Var(id, parseType typ) in
                        let (aln, cnt) = compound_align_and_count typ in
                        (Tac.DeclCompound (id, aln, cnt)) #: instrs;
                        let srcs = parseInitialiser init in
                        let _ = List.fold_left (fun off src -> (
                            let off = Int64.add off (add_padding off (Tac.operand_type src)) in
                            let () = (Tac.CopyToOffset (src, obj, off)) #: instrs in
                            Int64.add off (src |> Tac.operand_type |> Tac.to_ast_type |> Ast.indexing_size)
                        )) 0L srcs
                        in ()
                end

            | Ast.VarDecl (id, None, typ, Some Ast.Static) ->
                localStatics := (Tac.StaticVariable (id, false, [Tac.ZeroInit (Ast.aligned_size typ)], Ast.aligned_size typ, Ast.alignment typ)) :: !localStatics

            | Ast.VarDecl (id, Some init , typ, Some Ast.Static) ->
                let i = Const.parseInitialiserWithTypes init (*(Some globalEnv)*) in
                let nums = List.map (fun (init, typ) -> const_to_tacky init (parseType typ)) i in
                let pad = Int64.sub (Ast.aligned_size typ) (Ast.indexing_size typ) in
                let nums = if Int64.compare pad 0L > 0 then nums @ [Tac.ZeroInit pad] else nums in
                localStatics := (Tac.StaticVariable (id, false, nums, Ast.aligned_size typ, Ast.alignment typ)) :: !localStatics

            | _ -> ()

    and parseInitialiser init = match init with
        | Ast.SingleInit expr -> [parseExpr_lval_convert expr]
        | Ast.CompoundInit inits -> List.fold_left (fun acc init -> acc @ (parseInitialiser init)) [] inits

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

                let () = (Tac.Return (Some zero_number)) #: instrs in
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
                    | Environment.Tentative -> Tac.StaticVariable (id, is_global, [Tac.ZeroInit (Ast.indexing_size typ)], Ast.indexing_size typ, Ast.alignment typ) :: acc
                | Environment.Initial i ->
                    let nums = List.map (fun (init, typ) -> const_to_tacky init (parseType typ)) i in
                    let pad = Int64.sub (Ast.aligned_size typ) (Ast.indexing_size typ) in
                    let nums = if Int64.compare pad 0L > 0 then nums @ [Tac.ZeroInit pad] else nums in
                    (Tac.StaticVariable (id, is_global, nums, Ast.indexing_size typ, Ast.alignment typ)) :: acc
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
                        | Tac.Return Some (Tac.Constant D num) ->
                            Tac.Return (Some (Tac.StaticVar (Label.getLabelDouble num, Tac.Float64))) :: iter rest
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

                        | Tac.CopyToOffset ((Tac.Constant D num), dst, off) ->
                            Tac.CopyToOffset (Tac.StaticVar ((Label.getLabelDouble num), Tac.Float64), dst, off) :: iter rest

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
        in new_toplevels @ (Label.labelDoubleFlushToList() |> List.map (fun (num, lbl) -> Tac.StaticConst (lbl, [Tac.D num])))
                         @ (Label.labelStringFlushToList() |> List.map (fun (str, lbl) -> Tac.StaticConst (lbl, [Tac.S str])))


    in try match ast with
        | Ast.Program tls -> let p = (parseTopLevel tls) @ (parseStaticVarsAndNoticeUndefinedExternFunctions())
                             in let p = replaceIllegalSSE p
                             in Tac.Program (p @ !localStatics), !undefinedNames
    with Environment.EnvironmentError e -> raise (TackyError e)

