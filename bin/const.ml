
exception ConstError of string

module Tac = Tacky

let parseUnaryOp = function
        | Ast.Negate -> Tac.Negate
        | Ast.Complement -> Tac.Complement
        | Ast.LogNot -> Tac.Not
        | Ast.Increment -> Tac.Incr
        | Ast.Decrement -> Tac.Decr
        | Ast.Rvalue -> failwith "Rvalue is a useless unop and should be just unboxed(tackifyConst.ml)"

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

let trunc num typ = match typ with
    | Ast.Long -> Z.signed_extract num 0 64
    | Ast.ULong -> Z.extract num 0 64
    | Ast.Int -> Z.signed_extract num 0 32
    | Ast.UInt -> Z.extract num 0 32

let assert_fit num typ = let r, typ_str = match typ with
    | Ast.Long -> Z.fits_int64_unsigned num || Z.fits_int64 num, "long"
    | Ast.ULong -> Z.fits_int64_unsigned num || Z.fits_int64 num, "ulong"
    | Ast.Int -> Z.fits_int32_unsigned num || Z.fits_int32 num, "int"
    | Ast.UInt -> Z.fits_int32_unsigned num || Z.fits_int32 num, "uint"
    in if not r then failwith ("DEBUG ASSERT: Number " ^ Z.to_string num ^ " doesn't fit in " ^ typ_str ^ ".")
    else num

let parseConstExpr typed_expr =
    let rec parse (typed_expr:Ast.typed_expr) seen =
        match typed_expr with
            | (_, Ast.Literal lit) -> (match lit with Ast.Int32 num -> Z.of_int32 num
                                                    | Ast.UInt32 num -> (Z.of_int32 num |> Z.extract) 0 32
                                                    | Ast.Int64 num -> Z.of_int64 num
                                                    | Ast.UInt64 num -> (Z.of_int64 num |> Z.extract) 0 64)
            | (_, Ast.Var _) -> raise (ConstError "Cannot use variables in constant expressions")

            | (_, Ast.Cast(new_type, ((old_type, _) as typed_expr))) ->
                let parsed = parse typed_expr seen in
                if old_type = new_type then parsed else

                if (Ast.size new_type) = (Ast.size old_type) then
                    parsed
                else
                    trunc parsed new_type

            | (_, Ast.Unary (Ast.Rvalue, src)) -> parse src seen
            | (typ, Ast.Unary (op, typed_expr)) ->
                let src = parse typed_expr seen in
                let result = begin match parseUnaryOp op with
                    | Tac.Complement -> Z.lognot src
                    | Tac.Negate -> Z.neg src
                    | Tac.Not -> if Z.compare src Z.zero = 0 then Z.zero else Z.one
                    | _ -> raise (ConstError "Increment/Decrement is not a constant expression operator")
                end in trunc result typ

            | (_, Ast.BinarySp (Ast.LogAnd, (left, _), right)) ->
                let left = parse left seen in
                if Z.compare left Z.zero = 0 then Z.zero else parse right seen

            | (_, Ast.BinarySp (Ast.LogOr, (left, _), right)) ->
                let left = parse left seen in
                if Z.compare left Z.zero = 0 then parse right seen else Z.one

            | (_, Ast.BinarySp (Ast.Comma, _, _)) -> failwith "TODO: Add Comma"

            | (typ, Ast.Binary (op, left, right)) ->
                let left = parse left seen in
                let right = parse right seen in
                let result = begin match parseBinaryOp op with
                    | Tac.Add -> Z.add left right
                    | Tac.Subtract -> Z.sub left right
                    | Tac.Divide -> Z.div left right
                    | Tac.Multiply -> Z.mul left right
                    | Tac.Remainder -> Z.rem left right
                    | Tac.And -> Z.logand left right
                    | Tac.Or -> Z.logor left right
                    | Tac.Xor -> Z.logxor left right
                    | Tac.LShift ->
                        let () = if (Z.compare right Z.zero) < 0 || (Z.compare right (Z.of_int 32)) > 0 then
                            Log.warning "shift count >= width of type" in
                        Z.shift_left left (Z.to_int right)
                    | Tac.RShift ->
                        let () = if (Z.compare right Z.zero) < 0 || (Z.compare right (Z.of_int 32)) > 0 then
                            Log.warning "shift count >= width of type" in
                        Z.shift_right left (Z.to_int right)
                    | Tac.Equal -> if Z.equal left right then Z.one else Z.zero
                    | Tac.NotEqual -> if Z.equal left right then Z.zero else Z.one
                    | Tac.LessThan -> if (Z.compare left right) < 0 then Z.one else Z.zero
                    | Tac.LessOrEqual -> if (Z.compare left right) <= 0 then Z.one else Z.zero
                    | Tac.GreaterThan -> if (Z.compare left right) > 0 then Z.one else Z.zero
                    | Tac.GreaterOrEqual -> if (Z.compare left right) >= 0 then Z.one else Z.zero
                end in trunc result typ

            | (_, Ast.Assignment _)
            | (_, Ast.BinaryAssign _) ->
                raise (ConstError "Cannot use assignment operator in constant expressions")

            | (_, Ast.Ternary ((cond, _), th, el)) -> 
                let cond = parse cond seen in
                if Z.compare cond Z.zero <> 0 then parse th seen else parse el seen

            | (_, Ast.Call (_, _)) ->
                raise (ConstError "Cannot call functions in constant expresisons")

    in let result = parse typed_expr [] in
    (assert_fit result (fst typed_expr))


