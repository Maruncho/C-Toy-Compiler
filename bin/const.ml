
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
    | _ -> failwith "Cannot use with non-integral types."

type number = I of Z.t | D of float
type numberPair = Ip of Z.t * Z.t | Dp of float * float

let toString ?(decimal=false) = function
    | I n -> Z.to_string n
    | D n -> if decimal then
                    Int64.bits_of_float n |> Int64.to_string
             else
                Float.to_string n

let isZero = function
    | I n -> (Z.compare Z.zero n) = 0
    | D n -> ((Float.compare Float.zero n) = 0) && (not (Float.sign_bit n)) (* is not -0.0 *)

let isIntegerZero = function
    | I n -> (Z.compare Z.zero n) = 0
    | D _ -> false

let truncWrapper num typ = match typ with
    | Ast.Long
    | Ast.ULong
    | Ast.Int
    | Ast.UInt -> (match num with I num -> I (trunc num typ) | D _ -> failwith "Fix your cringe logic.")
    | Ast.Double -> num
    | Ast.Ptr _ -> num (*failwith "Impossible ptr in const.ml"*)
    | Ast.FunType _ -> failwith "Impossible func in const.ml"


let assert_fit num typ =
    let integer = match num with
        | I _ when Ast.isFloatingPoint typ -> failwith ("DEBUG ASSERT: Number is not floating point")
        | I n -> n
        | D _ -> Z.zero
    in let _ = match num with
        | D n when Ast.isFloatingPoint typ -> n
        | D _ -> failwith ("DEBUG ASSERT: Number is not integer.")
        | I _ -> Float.zero
    in let r, typ_str = match typ with
        | Ast.Long -> Z.fits_int64_unsigned integer || Z.fits_int64 integer, "long"
        | Ast.ULong -> Z.fits_int64_unsigned integer || Z.fits_int64 integer, "ulong"
        | Ast.Int -> Z.fits_int32_unsigned integer || Z.fits_int32 integer, "int"
        | Ast.UInt -> Z.fits_int32_unsigned integer || Z.fits_int32 integer, "uint"
        | Ast.Double -> true, "double"
        | Ast.Ptr _ -> true, "ulong" (*failwith "Impossible ptr in const.ml"*)
        | Ast.FunType _ -> failwith "Impossible func in const.ml"
    in if not r then failwith ("DEBUG ASSERT: Number " ^ (Z.to_string integer) ^ " doesn't fit in " ^ typ_str ^ ".")
    else num

let parseConstExpr typed_expr =
    let rec parse (typed_expr:Ast.typed_expr) seen =
        match typed_expr with
            | (_, Ast.Literal lit) -> (match lit with Ast.Int32 num -> I (Z.of_int32 num)
                                                    | Ast.UInt32 num -> I ((Z.of_int32 num |> Z.extract) 0 32)
                                                    | Ast.Int64 num -> I (Z.of_int64 num)
                                                    | Ast.UInt64 num -> I ((Z.of_int64 num |> Z.extract) 0 64)
                                                    | Ast.Float64 num -> D num)
            | (_, Ast.Var _) -> raise (ConstError "Cannot use variables in constant expressions")

            | (_, Ast.Cast(new_type, ((old_type, _) as typed_expr))) ->
                let parsed = parse typed_expr seen in
                if old_type = new_type || Ast.isPointer new_type then parsed else

                if (Ast.size new_type) = (Ast.size old_type) then
                    parsed
                else begin match parsed with
                    | I num when (Ast.isFloatingPoint new_type) -> D (Z.to_float num)
                    | I num -> I (trunc num new_type)
                    | D _ when (Ast.isFloatingPoint new_type) -> failwith "float32 not implemented"
                    | D num -> I (Z.of_float num)
                end

            | (_, Ast.Unary (Ast.Rvalue, src)) -> parse src seen
            | (typ, Ast.Unary (op, typed_expr)) ->
                let src = parse typed_expr seen in
                let result = begin match parseUnaryOp op with
                    | Tac.Complement -> (match src with I num -> I (Z.lognot num) | D _ -> raise (ConstError "Can't complement a float"))
                    | Tac.Negate -> (match src with I num -> I (Z.neg num) | D num -> D (Float.neg num))
                    | Tac.Not -> (match src with
                                    | I num -> if Z.compare num Z.zero = 0 then I Z.zero else I Z.one
                                    | D num -> if Float.compare num Float.zero = 0 then I Z.zero else I Z.one)
                    | Tac.Incr | Tac.Decr -> raise (ConstError "Increment/Decrement is not a constant expression operator")
                end in truncWrapper result typ

            | (_, Ast.Dereference _) -> raise (ConstError "Cannot use dereference operator in constant expressions.")
            | (_, Ast.AddressOf _) -> raise (ConstError "Cannot use addressOf operator in constant expressions.")

            | (_, Ast.BinarySp (Ast.LogAnd, (left, _), right)) ->
                let toBool num = begin match num with
                    | I num -> if Z.compare num Z.zero = 0 then Z.zero else Z.one
                    | D num -> if Float.compare num Float.zero = 0 then Z.zero else Z.one
                end in
                let left = parse left seen in
                let right = parse right seen in (*cannot have side effects, so it's okay*)
                if Z.compare (toBool left) Z.zero = 0 then I Z.zero else I (toBool right)

            | (_, Ast.BinarySp (Ast.LogOr, (left, _), right)) ->
                let toBool num = begin match num with
                    | I num -> if Z.compare num Z.zero = 0 then Z.zero else Z.one
                    | D num -> if Float.compare num Float.zero = 0 then Z.zero else Z.one
                end in
                let left = parse left seen in
                let right = parse right seen in (*cannot have side effects, so it's okay*)
                if Z.compare (toBool left) Z.one = 0 then I Z.one else I (toBool right)

            | (_, Ast.BinarySp (Ast.Comma, _, _)) -> failwith "TODO: Add Comma"

            | (typ, Ast.Binary (op, left, right)) ->
                let left = parse left seen in
                let right = parse right seen in
                let pair = (match (left, right) with
                    | I x, I y -> Ip (x, y)
                    | D x, D y -> Dp (x, y)
                    | _ -> failwith "DEBUG: Const: Type mismatch in binary"
                ) in
                let result = begin match parseBinaryOp op with
                    | Tac.Add -> (match pair with Ip (l, r) -> I (Z.add l r) | Dp (l, r) -> D (Float.add l r))
                    | Tac.Subtract -> (match pair with Ip (l, r) -> I (Z.sub l r) | Dp (l, r) -> D (Float.sub l r))
                    | Tac.Divide -> (match pair with Ip (l, r) -> I (Z.div l r) | Dp (l, r) -> D (Float.div l r))
                    | Tac.Multiply -> (match pair with Ip (l, r) -> I (Z.mul l r) | Dp (l, r) -> D (Float.mul l r))
                    | Tac.Remainder -> (match pair with Ip (l, r) -> I (Z.rem l r) | Dp _ -> raise (ConstError "Can't use remainder on float"))
                    | Tac.And -> (match pair with Ip (l, r) -> I (Z.logand l r) | Dp _ -> raise (ConstError "Can't use bitwise and on float"))
                    | Tac.Or -> (match pair with Ip (l, r) -> I (Z.logor l r) | Dp _ -> raise (ConstError "Can't use bitwise or on float"))
                    | Tac.Xor -> (match pair with Ip (l, r) -> I (Z.logxor l r) | Dp _ -> raise (ConstError "Can't use bitwise xor on float"))
                    | Tac.LShift ->
                        (*Sadly, there is no easy way to do logical shifts with Zarith*)
                        raise (ConstError "Left shifting is not supported in const expressions, my bad.")
                        (*let () = if (Z.compare right Z.zero) < 0 || (Z.compare right (Z.of_int 32)) > 0 then*)
                        (*    Log.warning "shift count >= width of type" in*)
                        (*Z.shift_left left (Z.to_int right)*)
                    | Tac.RShift ->
                        (*Sadly, there is no easy way to do logical shifts with Zarith*)
                        raise (ConstError "Right shifting is not supported in const expressions, my bad.")
                        (*let () = if (Z.compare right Z.zero) < 0 || (Z.compare right (Z.of_int 32)) > 0 then*)
                        (*    Log.warning "shift count >= width of type" in*)
                        (*Z.shift_right left (Z.to_int right)*)
                    | Tac.Equal -> if (match pair with Ip (l, r) -> Z.compare l r | Dp (l, r) -> Float.compare l r) = 0
                                   then I Z.one else I Z.zero
                    | Tac.NotEqual -> if (match pair with Ip (l, r) -> Z.compare l r | Dp (l, r) -> Float.compare l r) <> 0
                                   then I Z.one else I Z.zero
                    | Tac.LessThan -> if (match pair with Ip (l, r) -> Z.compare l r | Dp (l, r) -> Float.compare l r) < 0
                                   then I Z.one else I Z.zero
                    | Tac.LessOrEqual -> if (match pair with Ip (l, r) -> Z.compare l r | Dp (l, r) -> Float.compare l r) <= 0
                                   then I Z.one else I Z.zero
                    | Tac.GreaterThan -> if (match pair with Ip (l, r) -> Z.compare l r | Dp (l, r) -> Float.compare l r) > 0
                                   then I Z.one else I Z.zero
                    | Tac.GreaterOrEqual -> if (match pair with Ip (l, r) -> Z.compare l r | Dp (l, r) -> Float.compare l r) >= 0
                                   then I Z.one else I Z.zero
                end in truncWrapper result typ

            | (_, Ast.Assignment _)
            | (_, Ast.BinaryAssign _) ->
                raise (ConstError "Cannot use assignment operator in constant expressions")

            | (_, Ast.Ternary ((cond, _), th, el)) -> 
                let cond = parse cond seen in
                if (match cond with I c -> Z.compare c Z.zero <> 0 | D c -> Float.compare c Float.zero <> 0)
                then parse th seen else parse el seen

            | (_, Ast.Call (_, _)) ->
                raise (ConstError "Cannot call functions in constant expresisons")

    in let result = try parse typed_expr []
    with | Z.Overflow -> raise (ConstError "Constant expression number conversion failed somewhere.")
         | Division_by_zero -> raise (ConstError "Constant expression division by zero somewhere.")
    in (assert_fit result (fst typed_expr))


