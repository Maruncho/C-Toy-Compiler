
module Tac = Tacky

let rec list_take_drop num lst = match lst, num with
    | [], _ -> ([], [])
    | lst, 0 -> ([], lst)
    | h::t, x -> let next = list_take_drop (x-1) t in
                 (h::(fst next), snd next)

let parseUnaryOp = function
    | Tac.Negate -> Asmt.Neg
    | Tac.Complement -> Asmt.Not
    | Tac.Not -> failwith "Tacky Unary Operator is not simple to Asmt."
    | Tac.Incr | Tac.Decr -> failwith "Tacky Increment and Decrement are not handled as a normal unary"

let parseBinaryOp op signed = match op with
    | Tac.Add -> Asmt.Add
    | Tac.Subtract -> Asmt.Sub
    | Tac.Multiply -> Asmt.Mul
    | Tac.And -> Asmt.And
    | Tac.Or -> Asmt.Or
    | Tac.Xor -> Asmt.Xor
    | Tac.LShift when signed -> Asmt.Sal
    | Tac.LShift -> Asmt.Shl
    | Tac.RShift when signed-> Asmt.Sar
    | Tac.RShift -> Asmt.Shr
    | _ -> failwith "Tacky Binary Operator is not simple to Asmt."

let isConditional op = match op with
    | Tac.Add
    | Tac.Subtract
    | Tac.Multiply
    | Tac.Divide
    | Tac.Remainder
    | Tac.And
    | Tac.Or
    | Tac.Xor
    | Tac.LShift
    | Tac.RShift -> false
    | Tac.Equal
    | Tac.NotEqual
    | Tac.LessThan
    | Tac.LessOrEqual
    | Tac.GreaterThan
    | Tac.GreaterOrEqual -> true

let parseCondOp op signed = match op with
    | Tac.Equal -> Asmt.E
    | Tac.NotEqual -> Asmt.NE
    | Tac.LessThan when signed -> Asmt.L
    | Tac.LessThan -> Asmt.B
    | Tac.LessOrEqual when signed -> Asmt.LE
    | Tac.LessOrEqual -> Asmt.BE
    | Tac.GreaterThan when signed -> Asmt.G
    | Tac.GreaterThan -> Asmt.A
    | Tac.GreaterOrEqual when signed -> Asmt.GE
    | Tac.GreaterOrEqual -> Asmt.AE
    | _ -> failwith "Incorrect usage of parseCondOp."

let chooseBinop binop src1 src2 dst (typ, signed) = match binop with
    | Tac.Divide when typ = Asmt.Double ->
        [Asmt.Mov (typ, src1, dst);
         Asmt.Binary (typ, Asmt.DivSSE, src2, dst)]
    | Tac.Divide when signed ->
        [Asmt.Mov (typ, src1, Asmt.Reg Asmt.RAX);
         Asmt.SignExtend typ;
         Asmt.Idiv (typ, src2);
         Asmt.Mov (typ, Asmt.Reg Asmt.RAX, dst)]
    | Tac.Divide ->
        [Asmt.Mov (typ, src1, Asmt.Reg Asmt.RAX);
         Asmt.Binary (Asmt.QuadWord, Asmt.Xor, Asmt.Reg Asmt.RDX, Asmt.Reg Asmt.RDX);
         Asmt.Div (typ, src2);
         Asmt.Mov (typ, Asmt.Reg Asmt.RAX, dst)]

    | Tac.Remainder when signed ->
        [Asmt.Mov (typ, src1, Asmt.Reg Asmt.RAX);
         Asmt.SignExtend typ;
         Asmt.Idiv (typ, src2);
         Asmt.Mov (typ, Asmt.Reg Asmt.RDX, dst)]
    | Tac.Remainder ->
        [Asmt.Mov (typ, src1, Asmt.Reg Asmt.RAX);
         Asmt.Binary (Asmt.QuadWord, Asmt.Xor, Asmt.Reg Asmt.RDX, Asmt.Reg Asmt.RDX);
         Asmt.Div (typ, src2);
         Asmt.Mov (typ, Asmt.Reg Asmt.RDX, dst)]

    | Tac.Add | Tac.Subtract | Tac.Multiply | Tac.And | Tac.Or | Tac.Xor | Tac.LShift | Tac.RShift ->
        let binop = parseBinaryOp binop signed in
        (if src1 = dst then [] else [Asmt.Mov (typ, src1, dst)]) @
        [Asmt.Binary (typ, binop, src2, dst)]

    (*NaN support*)
    | Tac.Equal | Tac.NotEqual | Tac.LessThan | Tac.LessOrEqual | Tac.GreaterThan | Tac.GreaterOrEqual 
    when typ = Double ->
        let tmp = Asmt.Pseudo (Temp.newTemp()) in
        let tmpDst = Asmt.Reg Asmt.R11 in (*The destination for cmov must be 0ed and cannot be mem. If it is mem, the fixup stage will replace it with a register, which would not be zeroed that way.*)
        let cc = parseCondOp binop signed in
        if cc = Asmt.NE then
            [Asmt.Mov (Asmt.QuadWord, Asmt.Imm Z.one, tmpDst);
             Asmt.Binary (Asmt.QuadWord, Asmt.Xor, tmp, tmp);
             Asmt.Cmp (typ, src2, src1);
             Asmt.SetCC (cc, tmp);
             Asmt.Cmov (Asmt.QuadWord, Asmt.NP, tmp, tmpDst);
             Asmt.Mov (Asmt.QuadWord, tmpDst, dst)]
        else
            [Asmt.Binary (Asmt.QuadWord, Asmt.Xor, tmpDst, tmpDst);
             Asmt.Binary (Asmt.QuadWord, Asmt.Xor, tmp, tmp);
             Asmt.Cmp (typ, src2, src1);
             Asmt.SetCC (Asmt.NP, tmp);
             Asmt.Cmov (Asmt.QuadWord, cc, tmp, tmpDst);
             Asmt.Mov (Asmt.QuadWord, tmpDst, dst)]

    | Tac.Equal | Tac.NotEqual | Tac.LessThan | Tac.LessOrEqual | Tac.GreaterThan | Tac.GreaterOrEqual ->
        let cc = parseCondOp binop signed in
        [Asmt.Binary (Asmt.QuadWord, Asmt.Xor, dst, dst);
         Asmt.Cmp (typ, src2, src1);
         Asmt.SetCC (cc, dst)]

let parseType typ =
    match typ with
        | Tac.Int8 s -> Asmt.Byte, s
        | Tac.Int32 s -> Asmt.LongWord, s
        | Tac.Int64 s -> Asmt.QuadWord, s
        | Tac.Float64 -> Asmt.Double, false
        | Tac.Ptr _ -> Asmt.QuadWord, false
        | Tac.ArrObj (typ, s) -> Asmt.ByteArray (s, typ |> Tac.to_ast_type |> Ast.alignment), false

let classify_parameters typs =
    let rec iter typs i f s = match typs with
        | [] -> []
        | ((Tac.Int64 _) as typ) :: t
        | ((Tac.Int8 _) as typ) :: t
        | ((Tac.Ptr _) as typ) :: t
        | ((Tac.Int32 _) as typ) :: t ->
            let (reg, i, s) = (match i with
                | 1 -> Asmt.Reg Asmt.RDI, i+1, s
                | 2 -> Asmt.Reg Asmt.RSI, i+1, s
                | 3 -> Asmt.Reg Asmt.RDX, i+1, s
                | 4 -> Asmt.Reg Asmt.RCX, i+1, s
                | 5 -> Asmt.Reg Asmt.R8, i+1, s
                | 6 -> Asmt.Reg Asmt.R9, i+1, s
                | _ -> Asmt.Memory (Asmt.RBP, Int64.of_int (8*s+8), None, None), i, s+1 (*+8 is return adress*)
            )
            in (fst (parseType typ), reg) :: iter t i f s
        | (Tac.Float64 as typ) :: t ->
            let (reg, f, s) = (match f with
                | 1 -> Asmt.Reg Asmt.XMM0, f+1, s
                | 2 -> Asmt.Reg Asmt.XMM1, f+1, s
                | 3 -> Asmt.Reg Asmt.XMM2, f+1, s
                | 4 -> Asmt.Reg Asmt.XMM3, f+1, s
                | 5 -> Asmt.Reg Asmt.XMM4, f+1, s
                | 6 -> Asmt.Reg Asmt.XMM5, f+1, s
                | 7 -> Asmt.Reg Asmt.XMM6, f+1, s
                | 8 -> Asmt.Reg Asmt.XMM7, f+1, s
                | _ -> Asmt.Memory (Asmt.RBP, Int64.of_int (8*s+8), None, None), f, s+1 (*+8 is return adress*)
            )
            in (fst (parseType typ), reg) :: iter t i f s
        | Tac.ArrObj _ :: _ -> failwith "Function parameters cannot be ArrObjs"

    in iter typs 1 1 1


let parseOperand ?(offset=None) opr =
    match opr with
        | Tac.Constant Tac.I (num, typ) -> parseType typ, Asmt.Imm num
        | Tac.Constant Tac.D _ -> failwith "DEBUG: Double immediates are not allowed."
        | Tac.Constant Tac.S _ -> failwith "DEBUG: String immediates are not allowed."
        | Tac.Var (id, typ) ->
            let typ = parseType typ in
            if Option.is_some offset then typ, Asmt.PseudoMem (id, (Option.get offset))
            else typ, Asmt.Pseudo id
        | Tac.StaticVar (id, typ) ->
            let typ = parseType typ in
            if Option.is_some offset then typ, Asmt.Data (id, Some (Option.get offset))
            else typ, Asmt.Data (id, None)
        | Tac.Constant ZeroInit _ -> failwith "DEBUG: ZeroInit immediates caught in the wild."


let rec parseInstruction inst =
    match inst with
        | Tac.Return d ->
            let ((typ,_), d) = parseOperand d in
            let dst_reg = if typ = Asmt.Double then Asmt.XMM0 else Asmt.RAX in
           [
            Asmt.Mov (typ, d, Asmt.Reg dst_reg);
            Asmt.Ret]
        | Tac.SignExtend (s, d) ->
            let (s_typ, src) = parseOperand s in
            let (d_typ, dst) = parseOperand d in
            if s_typ = d_typ then failwith "DEBUG: Assemble: SignExtend SRC and DST types mismatch." else
            [Asmt.Movsx ((fst s_typ, src), (fst d_typ, dst))]
        | Tac.ZeroExtend (s, d) ->
            let (s_typ, src) = parseOperand s in
            let (d_typ, dst) = parseOperand d in
            if s_typ = d_typ then failwith "DEBUG: Assemble: ZeroExtend SRC and DST types mismatch." else
            [Asmt.Movzx ((fst s_typ, src), (fst d_typ, dst))]
        | Tac.FloatToInt (s, d) ->
            let (s_typ, src) = parseOperand s in
            let (d_typ, dst) = parseOperand d in
            if s_typ = d_typ then failwith "DEBUG: Assemble: FloatToInt SRC and DST types mismatch." else
            begin match (fst d_typ) with
                | Asmt.LongWord | Asmt.QuadWord ->
                    [Asmt.Cvttsx2si ((fst s_typ, src), (fst d_typ, dst))]
                | Asmt.Byte ->
                   [
                    Asmt.Cvttsx2si ((fst s_typ, src), (Asmt.LongWord, Asmt.Reg Asmt.RAX));
                    Asmt.Mov (Asmt.Byte, Asmt.Reg Asmt.RAX, dst)]
                | _ -> failwith "Not implemented"
            end
        | Tac.FloatToUInt (s, d) ->
            let (s_typ, src) = parseOperand s in
            let (d_typ, dst) = parseOperand d in
            if s_typ = d_typ then failwith "DEBUG: Assemble: FloatToUInt SRC and DST types mismatch." else
            begin match (fst d_typ) with
                | Asmt.Byte ->
                   [
                    Asmt.Cvttsx2si ((fst s_typ, src), (Asmt.LongWord, Asmt.Reg Asmt.RAX));
                    Asmt.Mov (Asmt.Byte, Asmt.Reg Asmt.RAX, dst)]
                | Asmt.LongWord ->
                    let mid = Asmt.Pseudo (Temp.newTemp()) in
                   [Asmt.Cvttsx2si ((fst s_typ, src), (Asmt.QuadWord, mid));
                    Asmt.Mov (Asmt.LongWord, mid, dst)]
                | Asmt.QuadWord ->
                    let max_long_plus_one = 9223372036854775808.0 in
                    let max_long_plus_one_int = Asmt.Imm (Z.of_int64 9223372036854775808L) in
                    let max_long_plus_one_double = Asmt.Data (Label.getLabelDouble max_long_plus_one, None) in
                    let lbl_out_of_range = Label.newLbl() in
                    let lbl_end = Label.newLbl() in
                    let temp = Asmt.Pseudo (Temp.newTemp()) in
                   [
                    Asmt.Cmp (Asmt.Double, max_long_plus_one_double, src);
                    Asmt.JmpCC (Asmt.AE, lbl_out_of_range);
                    Asmt.Cvttsx2si ((fst s_typ, src), (Asmt.QuadWord, dst));
                    Asmt.Jmp lbl_end;
                    Asmt.Label lbl_out_of_range;
                    Asmt.Mov (Asmt.Double, src, temp);
                    Asmt.Binary (Asmt.Double, Asmt.Sub, max_long_plus_one_double, temp);
                    Asmt.Cvttsx2si ((fst s_typ, temp), (Asmt.QuadWord, dst));
                    Asmt.Binary (Asmt.QuadWord, Asmt.Add, max_long_plus_one_int, dst);
                    Asmt.Label lbl_end]
                | _ -> failwith "Not implemented"
            end
        | Tac.IntToFloat (s, d) ->
            let (s_typ, src) = parseOperand s in
            let (d_typ, dst) = parseOperand d in
            if s_typ = d_typ then failwith "DEBUG: Assemble: IntToFloat SRC and DST types mismatch." else
            begin match (fst s_typ) with
                | Asmt.LongWord | Asmt.QuadWord ->
                    [Asmt.Cvtsi2sx ((fst s_typ, src), (fst d_typ, dst))]
                | Asmt.Byte ->
                   [
                    Asmt.Movsx ((Asmt.Byte, src), (Asmt.LongWord, Asmt.Reg Asmt.RAX));
                    Asmt.Cvtsi2sx ((Asmt.LongWord, Asmt.Reg Asmt.RAX), (fst d_typ, dst))]
                | _ -> failwith "Not implemented"
            end
        | Tac.UIntToFloat (s, d) ->
            let (s_typ, src) = parseOperand s in
            let (d_typ, dst) = parseOperand d in
            if s_typ = d_typ then failwith "DEBUG: Assemble: UIntToFloat SRC and DST types mismatch." else
            begin match (fst s_typ) with
                | Asmt.Byte ->
                    [Asmt.Movzx ((Asmt.Byte, src), (Asmt.LongWord, Asmt.Reg Asmt.RAX));
                    Asmt.Cvtsi2sx ((Asmt.LongWord, Asmt.Reg Asmt.RAX), (fst d_typ, dst))]
                | Asmt.LongWord ->
                    let mid = Asmt.Pseudo (Temp.newTemp()) in
                    [Asmt.Movzx ((Asmt.LongWord, src), (Asmt.QuadWord, mid));
                    Asmt.Cvtsi2sx ((Asmt.QuadWord, mid), (fst d_typ, dst))]
                | Asmt.QuadWord ->
                    let lbl_out_of_range = Label.newLbl() in
                    let lbl_end = Label.newLbl() in
                    let temp = Asmt.Pseudo (Temp.newTemp()) in
                    let srcCopy = Asmt.Pseudo (Temp.newTemp()) in
                   [
                    Asmt.Cmp (Asmt.QuadWord, Asmt.Imm Z.zero, src);
                    Asmt.JmpCC (Asmt.L, lbl_out_of_range);
                    Asmt.Cvtsi2sx ((Asmt.QuadWord, src), (fst d_typ, dst));
                    Asmt.Jmp lbl_end;
                    Asmt.Label lbl_out_of_range;
                    Asmt.Mov (Asmt.QuadWord, src, srcCopy);
                    Asmt.Mov (Asmt.QuadWord, src, temp);
                    Asmt.Binary (Asmt.QuadWord, Asmt.Shr, Asmt.Imm Z.one, temp);
                    Asmt.Binary (Asmt.QuadWord, Asmt.And, Asmt.Imm Z.one, srcCopy);
                    Asmt.Binary (Asmt.QuadWord, Asmt.Or, srcCopy, temp);
                    Asmt.Cvtsi2sx ((Asmt.QuadWord, temp), (fst d_typ, dst));
                    Asmt.Binary (Asmt.Double, Asmt.Add, dst, dst);
                    Asmt.Label lbl_end]
                | _ -> failwith "Not implemented"
            end
        | Tac.Truncate (s, d) ->
            let (s_typ, src) = parseOperand s in
            let (d_typ, dst) = parseOperand d in
            if s_typ = d_typ then failwith "DEBUG: Assemble: Truncate SRC and DST types mismatch." else
            [Asmt.Mov (fst d_typ, src, dst)]

        | Tac.Unary (Tac.Not, s ,d) ->
            let zero = Tac.number_zero_operand (Tac.operand_type s) in
            parseInstruction (Tac.Binary (Tac.Equal, s, zero, d))

        | Tac.Unary (Tac.Incr, d, _) when Tac.operand_type d = Tac.Float64 ->
            let one = Tac.StaticVar(Label.getLabelDouble Float.one, Tac.Float64) in
            parseInstruction (Tac.Binary (Tac.Add, d, one, d))
        | Tac.Unary (Tac.Incr, d, _) -> let (typ, d) = parseOperand d in [Asmt.Incr (fst typ, d)]

        | Tac.Unary (Tac.Decr, d, _) when Tac.operand_type d = Tac.Float64 ->
            let one = Tac.StaticVar(Label.getLabelDouble Float.one, Tac.Float64) in
            parseInstruction (Tac.Binary (Tac.Subtract, d, one, d))
        | Tac.Unary (Tac.Decr, d, _) -> let (typ, d) = parseOperand d in [Asmt.Decr (fst typ, d)]

        | Tac.Unary (unop, s, d) ->
            let (s_typ, src) = parseOperand s in
            let (d_typ, dst) = parseOperand d in
            if s_typ <> d_typ then failwith "DEBUG: Assemble: Unary SRC and DST types mismatch." else
            let unop = parseUnaryOp unop in
          [
            Asmt.Mov (fst s_typ, src, dst);
            Asmt.Unary (fst s_typ, unop, dst)]

        | Tac.Binary (binop, s1, s2, d) ->
            (*let print (typ, signed) = (print_string (Asmt.type_to_string typ ^ " " ^ (if signed then "signed" else "unsigned") ^ "\n")) in *)
            let (s1_typ, src1) = parseOperand s1 in
            let (s2_typ, src2) = parseOperand s2 in
            let (d_typ, dst) = parseOperand d in
            (*let () = print s1_typ; print s2_typ; print d_typ in*)
            if (s1_typ <> s2_typ)  then failwith "DEBUG: Assemble: SRC1 and SRC2 types mismatch in BINARY." else
            if not (isConditional binop) && (s2_typ <> d_typ) then failwith "DEBUG: Assemble: SRC1, SRC2 and DST types mismatch." else
            chooseBinop binop src1 src2 dst s1_typ
        | Tac.Copy (s, d) ->
            let (s_typ, src) = parseOperand s in
            let (d_typ, dst) = parseOperand d in
            if s_typ <> d_typ then failwith "DEBUG: Assemble: Copy SRC and DST types mismatch." else
            [Asmt.Mov (fst s_typ, src, dst)]

        | Tac.GetAddress (s, d) ->
            let (typ, src) = parseOperand s in
            let (_, dst) = parseOperand d in
            (match (fst typ, src) with
                | (Asmt.ByteArray _, Asmt.Pseudo id) -> [Asmt.Lea (Asmt.PseudoMem (id, 0L), dst)]
                | (Asmt.ByteArray _, Asmt.Data (id, None)) -> [Asmt.Lea (Asmt.Data (id, None), dst)]
                | (Asmt.ByteArray _, _) -> failwith "Cannot have ByteArray src in GetAddress which is not a Pseudo or Data"
                | _ -> [Asmt.Lea (src, dst)]
            )

        | Tac.Load (s, d) ->
            let (_, src) = parseOperand s in
            let (d_typ, dst) = parseOperand d in
           [
            Asmt.Mov (Asmt.QuadWord, src, Asmt.Reg Asmt.RAX);
            Asmt.Mov (fst d_typ, Asmt.Memory(Asmt.RAX, 0L, None, None), dst)]

        | Tac.Store (s, d) ->
            let (s_typ, src) = parseOperand s in
            let (_, dst) = parseOperand d in
           [
            Asmt.Mov (Asmt.QuadWord, dst, Asmt.Reg Asmt.RAX);
            Asmt.Mov (fst s_typ, src, Asmt.Memory(Asmt.RAX, 0L, None, None))]

        (*It's metainfo for the memory-register allocator*)
        | Tac.DeclCompound (id, align, count) -> [Asmt.DeclCompound (id, align, count)]

        | Tac.AddPtr (p, i, scale, d) ->
            let (_, ptr) = parseOperand p in
            let (_, index) = parseOperand i in
            let (_, dst) = parseOperand d in
            begin match index with
                | Asmt.Imm index ->
                   [Asmt.Mov (Asmt.QuadWord, ptr, Asmt.Reg Asmt.RAX);
                    Asmt.Lea (Asmt.Memory (Asmt.RAX, Int64.mul scale (Z.to_int64 index), None, None), dst)]

                | _ ->
                   [
                    Asmt.Mov (Asmt.QuadWord, ptr, Asmt.Reg Asmt.RAX);
                    Asmt.Mov (Asmt.QuadWord, index, Asmt.Reg Asmt.RDX)] @
                    (if (match scale with 1L | 2L | 4L | 8L -> true | _ -> false) then
                        [Asmt.Lea (Asmt.Memory (Asmt.RAX, 0L, Some Asmt.RDX, Some scale), dst)]
                    else
                       [Asmt.Binary (Asmt.QuadWord, Asmt.Mul, Asmt.Imm (Z.of_int64 scale), Asmt.Reg Asmt.RDX);
                        Asmt.Lea (Asmt.Memory (Asmt.RAX, 0L, Some Asmt.RDX, None), dst)])
            end

        | Tac.CopyToOffset (s, d , off) ->
            let (s_typ, src) = parseOperand s in
            let (_, dst) = parseOperand d ~offset:(Some off) in
           [Asmt.Mov (fst s_typ, src, dst)]

        | Tac.Jump lbl ->
            [Asmt.Jmp lbl]
        | Tac.JumpIfZero (v, lbl) ->
            let (typ, value) = parseOperand v in

            if (fst typ) = Asmt.Double then
            let nan_lbl = Label.newLbl() in
          [
            Asmt.Cmp (Asmt.Double, value, value);
            Asmt.JmpCC (Asmt.P, nan_lbl);
            Asmt.Binary (Asmt.Double, Asmt.Xor, Asmt.Reg Asmt.XMM0, Asmt.Reg Asmt.XMM0);
            Asmt.Cmp (Asmt.Double, Asmt.Reg Asmt.XMM0, value);
            Asmt.JmpCC (Asmt.E, lbl);
            Asmt.Label nan_lbl]

            else
          [
            Asmt.Cmp (fst typ, Asmt.Imm Z.zero, value);
            Asmt.JmpCC (Asmt.E, lbl)]

        | Tac.JumpIfNotZero (v, lbl) ->
            let (typ, value) = parseOperand v in

            if (fst typ) = Asmt.Double then
          [
            Asmt.Cmp (Asmt.Double, value, value);
            Asmt.JmpCC (Asmt.P, lbl);
            Asmt.Binary (Asmt.Double, Asmt.Xor, Asmt.Reg Asmt.XMM0, Asmt.Reg Asmt.XMM0);
            Asmt.Cmp (Asmt.Double, Asmt.Reg Asmt.XMM0, value);
            Asmt.JmpCC (Asmt.NE, lbl)]

            else
          [
            Asmt.Cmp (fst typ, Asmt.Imm Z.zero, value);
            Asmt.JmpCC (Asmt.NE, lbl)]

        | Tac.Label lbl ->
            [Asmt.Label lbl]
        | Tac.Call (name, params, dst) ->
            let srcs = (List.map (fun x -> snd (parseOperand x)) params) in
            let types_and_dsts = classify_parameters (List.map Tac.operand_type params) in
            let (inReg, inStack) = List.partition (fun ((_, x), _) -> match x with Asmt.Memory _ -> false | _ -> true) (List.combine types_and_dsts srcs) in
            let extraPadding = (List.length inStack) mod 2 <> 0 in
            let deallocSize = Int64.of_int (8 * ((List.length inStack) + if extraPadding then 1 else 0)) in

            let regInstrs =  List.map (fun ((typ, dst), src) -> Asmt.Mov (typ, src, dst)) inReg in
            let stackInstrs = List.map (fun ((typ, _), src) -> match src with
                | Asmt.Imm _ | Asmt.Reg _ ->
                    [Asmt.Push (Asmt.QuadWord, src)]
                | _ when typ = Asmt.QuadWord || typ = Asmt.Double ->
                    [Asmt.Push (Asmt.QuadWord, src)]

                | Asmt.Pseudo _ | Asmt.Memory _ | Asmt.Data _ | Asmt.PseudoMem _ ->
                    [Asmt.Movsx ((typ, src), (Asmt.QuadWord, Asmt.Reg Asmt.RAX));
                     Asmt.Push (QuadWord, (Asmt.Reg Asmt.RAX))])

                (List.rev inStack) |> List.flatten in
            let stackInstrs = if extraPadding then (Asmt.AllocateStack 8L) :: stackInstrs else stackInstrs in

            let (dst_type, dst) = parseOperand dst in
            let dst_reg = if fst dst_type = Asmt.Double then Asmt.XMM0 else Asmt.RAX in
            let callInstrs = [Asmt.Call (name);
                              Asmt.DeallocateStack deallocSize;
                              Asmt.Mov(fst dst_type, Asmt.Reg dst_reg, dst)] in
            regInstrs @ stackInstrs @ callInstrs

let parseProgram tacky =
    let func = ref [] in
    let data = ref [] in
    let bss = ref [] in
    let ro = ref [] in
    let rec iter tls = match tls with
        | Tac.Function (name, is_global, params, instructions) :: rest ->
            let (names, types) = List.split params in
            let types_and_srcs = classify_parameters types in
            let preInstrs = List.map (fun ((typ, src), name) -> Asmt.Mov(typ, src, Asmt.Pseudo name))
                (List.combine types_and_srcs names) in
            let fn = (name, List.fold_left (fun acc inst -> acc @ (parseInstruction inst)) preInstrs instructions, is_global) in
            func := fn :: !func; iter rest
        | Tac.StaticVariable (name, is_global, inits, size_bytes, alignment) :: rest ->
            let processed = List.map (fun init -> match init with
                    | Tac.I (num, typ) -> Const.I num, typ |> parseType |> fst
                    | Tac.D num -> Const.D num, Tac.Float64 |> parseType |> fst
                    | Tac.S str ->
                        let length = String.length str |> Int64.of_int in
                        let null_terminated = String.ends_with ~suffix:"\x00" str in
                        let str = if null_terminated then String.sub str 0 (String.length str - 1) else str in
                        Const.S str, Asmt.String (length, null_terminated)
                    | Tac.ZeroInit s  -> Const.I (Z.of_int64 s), Asmt.ByteArray (s, alignment)
            ) inits in
            if List.exists (fun (num, typ) -> not (Const.isZero num || match typ with Asmt.ByteArray _ -> true | _ -> false)) processed then
                (data := (name, Asmt.ByteArray (size_bytes, alignment), processed, is_global) :: !data; iter rest)
            else
                (bss := (name, Asmt.ByteArray (size_bytes, alignment), is_global) :: !bss; iter rest)
        | Tac.StaticConst (name, init) :: rest ->
            if List.length init <> 1 then failwith "Fix The StaticConst implementation to support number lists" else
            let init, typ = match (List.hd init) with
                | Tac.I (num, typ) -> Const.I num, typ |> parseType |> fst
                | Tac.D num -> Const.D num, Tac.Float64 |> parseType |> fst
                | Tac.S str ->
                    let length = String.length str |> Int64.of_int in
                    let null_terminated = String.ends_with ~suffix:"\x00" str in
                        let str = if null_terminated then String.sub str 0 (String.length str - 1) else str in
                    Const.S str, Asmt.String (length, null_terminated)
                | Tac.ZeroInit _ -> failwith "StaticConst not implemented with zeroinit" in
            (ro := (name, init, typ) :: !ro; iter rest)
        | [] -> ()
    in let () = match tacky with
        | Tac.Program tls -> iter tls

    in let newRos = Label.labelDoubleFlushToList() |> List.map (fun (num, lbl) -> (lbl, Const.D num, Asmt.Double))
    in (!func, !bss, !data, newRos @ !ro)

let replacePseudos (name, instructions, is_global) =
    let dict = ref [] in
    let f operand typ ((o16, o8, o4, o2, o1) as offs) = match operand with 
        | Asmt.Imm _ | Asmt.Reg _ | Asmt.Memory _ | Asmt.Data _ | Asmt.PseudoMem _ -> offs
        | Asmt.Pseudo id -> if List.mem id !dict then offs else
            let offs = begin match typ with
                | Asmt.Byte ->     (o16, o8, o4, o2, o1+1)
                | Asmt.Word ->     (o16, o8, o4, o2+1, o1)
                | Asmt.LongWord -> (o16, o8, o4+1, o2, o1)
                | Asmt.QuadWord -> (o16, o8+1, o4, o2, o1)
                | Asmt.Double ->   (o16, o8+1, o4, o2, o1)
                | Asmt.ByteArray _ -> failwith "ByteArray in replacePseudos"
                | Asmt.String _ -> failwith "String in replacePseudos"
            end
            in let () = dict := id :: !dict in offs

    in let (o16, o8, o4, o2, o1) = List.fold_left (fun acc instr -> match instr with
        | Asmt.Mov (typ, s, d)
        | Asmt.Binary (typ, _, s, d)
        | Asmt.Cmp (typ, s, d) -> (f s typ acc) |> (f d typ)
        | Asmt.Unary (typ, _, d) -> f d typ acc
        | Asmt.Incr (typ, d)
        | Asmt.Decr (typ, d) -> f d typ acc
        | Asmt.Idiv (typ, s)
        | Asmt.Div (typ, s)
        | Asmt.Push (typ, s) -> f s typ acc
        | Asmt.SetCC (_, s) -> f s Asmt.Byte acc
        | Asmt.Movsx ((typ_s, s), (typ_d, d)) -> (f s typ_s acc) |> (f d typ_d)
        | Asmt.Movzx ((typ_s, s), (typ_d, d)) -> (f s typ_s acc) |> (f d typ_d)
        | Asmt.Lea (s, d) -> (f s QuadWord acc) |> (f d QuadWord)
        | Asmt.Cvtsi2sx ((typ_s, s), (typ_d, d)) -> (f s typ_s acc) |> (f d typ_d)
        | Asmt.Cvttsx2si ((typ_s, s), (typ_d, d)) -> (f s typ_s acc) |> (f d typ_d)
        | Asmt.Cmov (typ, _, s, d) -> (f s typ acc) |> (f d typ)

        | Asmt.DeclCompound (id, align, count) ->
            let (o16, o8, o4, o2, o1) = acc in
            let () = dict := id :: !dict in
            begin match align with
            | 16L-> (o16 + (Int64.to_int count), o8, o4, o2, o1)
            | 8L -> (o16, o8 + (Int64.to_int count), o4, o2, o1)
            | 4L -> (o16, o8, o4 + (Int64.to_int count), o2, o1)
            | 2L -> (o16, o8, o4, o2 + (Int64.to_int count), o1)
            | 1L -> (o16, o8, o4, o2, o1 + (Int64.to_int count))
            | _ -> acc
        end

        | Asmt.Jmp _
        | Asmt.JmpCC _
        | Asmt.Label _
        | Asmt.Call _
        | Asmt.SignExtend _
        | Asmt.AllocateStack _
        | Asmt.DeallocateStack _
        | Asmt.Nop _
        | Asmt.Ret -> acc

    ) (0, 0, 0, 0, 0) instructions in

    let offset16 = ref 0L in
    let offset8 = ref (Int64.of_int(o16*16)) in
    let offset4 = ref (Int64.of_int(o16*16+o8*8)) in
    let offset2 = ref (Int64.of_int(o16*16+o8*8+o4*4)) in
    let offset1 = ref (Int64.of_int(o16*16+o8*8+o4*4+o2*2)) in
    let dict = ref [] in
    let f operand typ = match operand with
        | Asmt.Imm _ | Asmt.Reg _ | Asmt.Memory _ | Asmt.Data _ -> operand
        | Asmt.Pseudo id -> begin match (List.assoc_opt id (!dict)) with
            | Some operand -> operand
            | None ->
                let offset = begin match typ with
                    | Asmt.Byte -> let () = offset1 := Int64.add !offset1 1L in !offset1
                    | Asmt.Word -> let () = offset2 := Int64.add !offset2 2L in !offset2
                    | Asmt.LongWord -> let () = offset4 := Int64.add !offset4 4L in !offset4
                    | Asmt.QuadWord -> let () = offset8 := Int64.add !offset8 8L in !offset8
                    | Asmt.Double -> let () = offset8 := Int64.add !offset8 8L in !offset8
                    | Asmt.ByteArray _ -> failwith "ByteArray in replacePseudos"
                    | Asmt.String _ -> failwith "String in replacePseudos"
                end in
                let operand = Asmt.Memory (Asmt.RBP, Int64.neg offset, None, None) in
                let () = dict := ((id, operand) :: !dict) in
                operand
        end
        | Asmt.PseudoMem (id, off) -> begin match (List.assoc id (!dict)) with
            | Asmt.Memory (Asmt.RBP, root, x, y) ->
                Asmt.Memory (Asmt.RBP, Int64.add root off, x, y)
            | _ -> failwith "Invalid root of PseudoMem."
        end


    in let newInstructions = List.map (fun instr -> match instr with
        | Asmt.Mov (typ, s, d) -> Asmt.Mov (typ, f s typ, f d typ)
        | Asmt.Movsx ((typ_s, s), (typ_d, d)) -> Asmt.Movsx ((typ_s, f s typ_s), (typ_d, f d typ_d))
        | Asmt.Movzx ((typ_s, s), (typ_d, d)) -> Asmt.Movzx ((typ_s, f s typ_s), (typ_d, f d typ_d))
        | Asmt.Lea (s, d) -> Asmt.Lea (f s QuadWord, f d QuadWord)
        | Asmt.Cvtsi2sx ((typ_s, s), (typ_d, d)) -> Asmt.Cvtsi2sx ((typ_s, f s typ_s), (typ_d, f d typ_d))
        | Asmt.Cvttsx2si ((typ_s, s), (typ_d, d)) -> Asmt.Cvttsx2si ((typ_s, f s typ_s), (typ_d, f d typ_d))
        | Asmt.Unary (typ, x1, d) -> Asmt.Unary (typ, x1, f d typ)
        | Asmt.Incr (typ, d) -> Asmt.Incr (typ, (f d typ))
        | Asmt.Decr (typ, d) -> Asmt.Decr (typ, (f d typ))
        | Asmt.Binary (typ, x1, s, d) -> Asmt.Binary (typ, x1, f s typ, f d typ)
        | Asmt.Cmp (typ, s, d) -> Asmt.Cmp (typ, f s typ, f d typ)
        | Asmt.Idiv (typ, s) -> Asmt.Idiv (typ, f s typ)
        | Asmt.Div (typ, s) -> Asmt.Div (typ, f s typ)
        | Asmt.SetCC (x1, s) -> Asmt.SetCC (x1, f s Asmt.Byte)
        | Asmt.Cmov (typ, x1, s, d) -> Asmt.Cmov (typ, x1, f s typ, f d typ)

        | Asmt.DeclCompound (id, align, count) ->
            let off = match align with
                | 16L-> let () = offset16:= Int64.add !offset16 (Int64.mul 16L count) in !offset16
                | 8L -> let () = offset8 := Int64.add !offset8 (Int64.mul 8L count) in !offset8
                | 4L -> let () = offset4 := Int64.add !offset4 (Int64.mul 4L count) in !offset4
                | 2L -> let () = offset2 := Int64.add !offset2 (Int64.mul 2L count) in !offset2
                | 1L -> let () = offset1 := Int64.add !offset1 (Int64.mul 1L count) in !offset1
                | _ -> failwith "INVALID OFFSET"
            in
            let operand = Asmt.Memory (Asmt.RBP, Int64.neg off, None, None) in
            let () = dict := ((id, operand) :: !dict) in Asmt.Nop true


        | Asmt.Jmp _
        | Asmt.JmpCC _
        | Asmt.Label _
        | Asmt.Call _
        | Asmt.SignExtend _
        | Asmt.AllocateStack _
        | Asmt.DeallocateStack _
        | Asmt.Nop _
        | Asmt.Ret -> instr

        | Asmt.Push (typ, s) -> Asmt.Push (typ, f s typ)
    ) instructions

    in let roundAlloc offset =
        let remainder = Int64.rem (Int64.add 0L offset) 16L in
        let pad = if remainder = 0L then 0L else Int64.sub 16L remainder in
        Int64.add offset pad

    in (name, newInstructions, is_global), roundAlloc (Int64.of_int (o16*16+o8*8+o4*4+o2*2+o1))

let fixUp (name, instructions, is_global) allocateBytes =
    let rec fixErroneous instrs = match instrs with
        | [] -> []

        (*Remove unnecessary jumps*)
        | Asmt.Jmp jmp :: (Asmt.Label lbl as l) :: t when jmp = lbl -> l ::(fixErroneous t)
        | Asmt.JmpCC (_, jmp) :: (Asmt.Label lbl as l) :: t when jmp = lbl -> l :: (fixErroneous t)

        | h :: t -> begin match h with

            (*Cleanup nops*)
            | Asmt.Nop true -> (fixErroneous t)

            (*Xor-zeroing a mem is slower than a mov 0*)
            | Asmt.Binary (ty, Asmt.Xor, (Asmt.Memory (Asmt.RBP, k1,_,_) as d), (Asmt.Memory (Asmt.RBP, k2,_,_)))
              when (Int64.compare k1 k2) = 0 ->
                (Asmt.Mov (ty, Asmt.Imm Z.zero, d)) :: (fixErroneous t)
            | Asmt.Binary (ty, Asmt.Xor, (Asmt.Data (k1,_) as d), (Asmt.Data (k2,_)))
              when (String.compare k1 k2) = 0 ->
                (Asmt.Mov (ty, Asmt.Imm Z.zero, d)) :: (fixErroneous t)

            | Asmt.Binary (ty, Asmt.Xor, (Asmt.Memory (Asmt.RBP, k1,_,_) as d), (Asmt.Memory (Asmt.RBP, k2,_,_)))
              when (Int64.compare k1 k2) = 0 ->
                (Asmt.Mov (ty, Asmt.Imm Z.zero, d)) :: (fixErroneous t)
            | Asmt.Binary (ty, Asmt.Xor, (Asmt.Data (k1,_) as d), (Asmt.Data (k2,_)))
              when (String.compare k1 k2) = 0 ->
                (Asmt.Mov (ty, Asmt.Imm Z.zero, d)) :: (fixErroneous t)

            (*SSE binop instrunctions can't have mem dst*)
            | Asmt.Binary (Asmt.Double, binop, s, (Asmt.Memory _ as d))
            | Asmt.Binary (Asmt.Double, binop, s, (Asmt.Data _ as d)) ->
                (Asmt.Mov (Asmt.Double, d, Asmt.Reg Asmt.XMM15)) ::
                (Asmt.Binary (Asmt.Double, binop, s, Asmt.Reg Asmt.XMM15)) ::
                (Asmt.Mov (Asmt.Double, Asmt.Reg Asmt.XMM15, d)) :: (fixErroneous t)

            (*Imul cannot do mem as dst*)
            | Asmt.Binary (ty, Asmt.Mul, s, (Asmt.Memory _ as d))
            | Asmt.Binary (ty, Asmt.Mul, s, (Asmt.Data _ as d)) ->
                (Asmt.Mov (ty, d, Asmt.Reg Asmt.R11)) ::
                (Asmt.Binary (ty, Asmt.Mul, s, Asmt.Reg Asmt.R11)) ::
                (Asmt.Mov (ty, Asmt.Reg Asmt.R11, d)) :: (fixErroneous t)

            (*Shifts are restrictive and c standard is ambiguous*)
            | Asmt.Binary (ty, Asmt.Sal, (Asmt.Imm k), d)
            | Asmt.Binary (ty, Asmt.Sar, (Asmt.Imm k), d)
            | Asmt.Binary (ty, Asmt.Shl, (Asmt.Imm k), d)
            | Asmt.Binary (ty, Asmt.Shr, (Asmt.Imm k), d) when
            (Z.compare k Z.zero) < 0 || (Z.compare k (Z.of_int 31)) > 0 ->
                let () = Log.warning "shift count >= width of type" in
                (Asmt.Mov (ty, Asmt.Imm Z.zero, d)) :: (fixErroneous t) (*gcc and clang do this*)

            (*k must be either an immediate or in %cl*)
            (*also doesn't agree with c standard per se. x86 and-masks the 5 lower bits of %cl as opposed to overshift d to 0*)
            | Asmt.Binary (ty, (Asmt.Sal as op), (Asmt.Reg _ as k), d)
            | Asmt.Binary (ty, (Asmt.Sar as op), (Asmt.Reg _ as k), d)
            | Asmt.Binary (ty, (Asmt.Sal as op), (Asmt.Memory _ as k), d)
            | Asmt.Binary (ty, (Asmt.Sar as op), (Asmt.Memory _ as k), d)
            | Asmt.Binary (ty, (Asmt.Sal as op), (Asmt.Data _ as k), d)
            | Asmt.Binary (ty, (Asmt.Sar as op), (Asmt.Data _ as k), d)
            | Asmt.Binary (ty, (Asmt.Shl as op), (Asmt.Reg _ as k), d)
            | Asmt.Binary (ty, (Asmt.Shr as op), (Asmt.Reg _ as k), d)
            | Asmt.Binary (ty, (Asmt.Shl as op), (Asmt.Memory _ as k), d)
            | Asmt.Binary (ty, (Asmt.Shr as op), (Asmt.Memory _ as k), d)
            | Asmt.Binary (ty, (Asmt.Shl as op), (Asmt.Data _ as k), d)
            | Asmt.Binary (ty, (Asmt.Shr as op), (Asmt.Data _ as k), d) ->
                (*the code emission phase will make %rcx in the 2nd instruction into %cl*)
                (Asmt.Mov (ty, k, Asmt.Reg Asmt.RCX)) :: (Asmt.Binary (ty, op, Asmt.Reg Asmt.RCX, d)) :: (fixErroneous t)

            | Asmt.Cmp (Asmt.Double, s, (Asmt.Memory _ as d))
            | Asmt.Cmp (Asmt.Double, s, (Asmt.Data _ as d)) ->
                (Asmt.Mov (Asmt.Double, d, Asmt.Reg Asmt.XMM15)) ::
                (Asmt.Cmp (Asmt.Double, s, Asmt.Reg Asmt.XMM15)) :: (fixErroneous t)

            | Asmt.Cvttsx2si (ss, (d_typ, (Asmt.Memory _ as d)))
            | Asmt.Cvttsx2si (ss, (d_typ, (Asmt.Data _ as d))) ->
                (Asmt.Cvttsx2si (ss, (d_typ, (Asmt.Reg Asmt.R11)))) ::
                (Asmt.Mov (d_typ, Asmt.Reg Asmt.R11, d)) :: (fixErroneous t)

            | Asmt.Cvtsi2sx (ss, (Asmt.Double, (Asmt.Memory _ as d)))
            | Asmt.Cvtsi2sx (ss, (Asmt.Double, (Asmt.Data _ as d))) ->
                (Asmt.Cvtsi2sx (ss, (Asmt.Double, (Asmt.Reg Asmt.XMM15)))) ::
                (Asmt.Mov (Asmt.Double, Asmt.Reg Asmt.XMM15, d)) :: (fixErroneous t)

            (* double mem *)
            | Asmt.Mov (Asmt.Double, (Asmt.Memory _ as s), (Asmt.Memory _ as d))
            | Asmt.Mov (Asmt.Double, (Asmt.Memory _ as s), (Asmt.Data _ as d))
            | Asmt.Mov (Asmt.Double, (Asmt.Data _ as s), (Asmt.Memory _ as d))
            | Asmt.Mov (Asmt.Double, (Asmt.Data _ as s), (Asmt.Data _ as d)) ->
                (Asmt.Mov (Asmt.Double, s, Asmt.Reg Asmt.XMM14)) :: (Asmt.Mov (Asmt.Double, Asmt.Reg Asmt.XMM14, d)) :: (fixErroneous t)

            | Asmt.Mov (ty, (Asmt.Memory _ as s), (Asmt.Memory _ as d))
            | Asmt.Mov (ty, (Asmt.Memory _ as s), (Asmt.Data _ as d))
            | Asmt.Mov (ty, (Asmt.Data _ as s), (Asmt.Memory _ as d))
            | Asmt.Mov (ty, (Asmt.Data _ as s), (Asmt.Data _ as d)) ->
                (Asmt.Mov (ty, s, Asmt.Reg Asmt.R10)) :: (Asmt.Mov (ty, Asmt.Reg Asmt.R10, d)) :: (fixErroneous t)

            (*| Asmt.Cmov (Asmt.Double, cc, (Asmt.Memory _ as s), (Asmt.Memory _ as d))*)
            (*| Asmt.Cmov (Asmt.Double, cc, (Asmt.Memory _ as s), (Asmt.Data _ as d))*)
            (*| Asmt.Cmov (Asmt.Double, cc, (Asmt.Data _ as s), (Asmt.Memory _ as d))*)
            (*| Asmt.Cmov (Asmt.Double, cc, (Asmt.Data _ as s), (Asmt.Data _ as d)) ->*)
            (*    (Asmt.Mov (Asmt.Double, s, Asmt.Reg Asmt.XMM14)) :: (Asmt.Cmov (Asmt.Double, cc, Asmt.Reg Asmt.XMM14, d)) :: (fixErroneous t)*)
            (* *)
            (*| Asmt.Cmov (ty, cc, (Asmt.Memory _ as s), (Asmt.Memory _ as d))*)
            (*| Asmt.Cmov (ty, cc, (Asmt.Memory _ as s), (Asmt.Data _ as d))*)
            (*| Asmt.Cmov (ty, cc, (Asmt.Data _ as s), (Asmt.Memory _ as d))*)
            (*| Asmt.Cmov (ty, cc, (Asmt.Data _ as s), (Asmt.Data _ as d)) ->*)
            (*    (Asmt.Mov (ty, s, Asmt.Reg Asmt.R10)) :: (Asmt.Cmov (ty, cc, Asmt.Reg Asmt.R10, d)) :: (fixErroneous t)*)
            (* *)

            | Asmt.Binary (ty, binop, (Asmt.Memory _ as s), (Asmt.Memory _ as d))
            | Asmt.Binary (ty, binop, (Asmt.Memory _ as s), (Asmt.Data _ as d))
            | Asmt.Binary (ty, binop, (Asmt.Data _ as s), (Asmt.Memory _ as d))
            | Asmt.Binary (ty, binop, (Asmt.Data _ as s), (Asmt.Data _ as d)) ->
                (Asmt.Mov (ty, s, Asmt.Reg Asmt.R10)) :: (Asmt.Binary (ty, binop, Asmt.Reg Asmt.R10, d)) :: (fixErroneous t)

            | Asmt.Cmp (ty, (Asmt.Memory _ as s), (Asmt.Memory _ as d))
            | Asmt.Cmp (ty, (Asmt.Memory _ as s), (Asmt.Data _ as d))
            | Asmt.Cmp (ty, (Asmt.Data _ as s), (Asmt.Memory _ as d))
            | Asmt.Cmp (ty, (Asmt.Data _ as s), (Asmt.Data _ as d)) ->
                (Asmt.Mov (ty, s, Asmt.Reg Asmt.R10)) :: (Asmt.Cmp (ty, Asmt.Reg Asmt.R10, d)) :: (fixErroneous t)

            (*Lea cannot have mem dst*)
            | Asmt.Lea (s, (Asmt.Memory _ as d))
            | Asmt.Lea (s, (Asmt.Data _ as d)) ->
                (Asmt.Lea (s, Asmt.Reg Asmt.R11)) :: (Asmt.Mov (Asmt.QuadWord, Asmt.Reg Asmt.R11, d)) :: (fixErroneous t)

            (*Push cannot have xmm*)
            | Asmt.Push (_, (Asmt.Reg reg as d)) when Asmt.isXMM reg ->
                (Asmt.Binary (Asmt.QuadWord, Asmt.Sub, Asmt.Imm (Z.of_int 8), Asmt.Reg Asmt.RSP)) ::
                (Asmt.Mov (Asmt.Double, d, Asmt.Memory (Asmt.RSP, 0L,None,None))) :: (fixErroneous t)

            (* movsx cannot have imm as src *)
            | Asmt.Movsx ((ty_src, (Asmt.Imm _ as imm)), (ty_dst, dst)) ->
                (Asmt.Mov(ty_src, imm, Asmt.Reg Asmt.R10)) :: (Asmt.Movsx ((ty_src, Asmt.Reg Asmt.R10), (ty_dst, dst))) :: (fixErroneous t)

            (* movzx cannot have imm as src *)
            | Asmt.Movzx ((ty_src, (Asmt.Imm _ as imm)), (ty_dst, dst)) ->
                (Asmt.Mov(ty_src, imm, Asmt.Reg Asmt.R10)) :: (Asmt.Movzx ((ty_src, Asmt.Reg Asmt.R10), (ty_dst, dst))) :: (fixErroneous t)

            (* cmov cannot have imm as src *)
            | Asmt.Cmov (ty, cc, (Asmt.Imm _ as imm), dst) ->
                (Asmt.Mov(ty, imm, Asmt.Reg Asmt.R10)) :: (Asmt.Cmov (ty, cc, Asmt.Reg Asmt.R10, dst)) :: (fixErroneous t)

            (* cmp cannot have an imm d*)
            | Asmt.Cmp (ty, s, (Asmt.Imm _ as d)) ->
                (Asmt.Mov (ty, d, Asmt.Reg Asmt.R11)) :: (Asmt.Cmp (ty, s, Asmt.Reg Asmt.R11)) :: (fixErroneous t)

            (*[I]div cannot do imm*)
            | Asmt.Idiv (ty, (Asmt.Imm _ as imm)) ->
                (Asmt.Mov (ty, imm, Asmt.Reg Asmt.R10)) :: (Asmt.Idiv (ty, Asmt.Reg Asmt.R10)) :: (fixErroneous t)
            | Asmt.Div (ty, (Asmt.Imm _ as imm)) ->
                (Asmt.Mov (ty, imm, Asmt.Reg Asmt.R10)) :: (Asmt.Div (ty, Asmt.Reg Asmt.R10)) :: (fixErroneous t)

            | _ -> h :: (fixErroneous t)
        end in
    let rec fixErroneousAgain instrs = match instrs with
        | [] -> []
        | h :: t -> begin match h with

            (* movsx cannot have mem as dst *)
            | Asmt.Movsx ((ty_src, src), (ty_dst, (Asmt.Memory _ as dst)))
            | Asmt.Movsx ((ty_src, src), (ty_dst, (Asmt.Data _ as dst))) ->
                (Asmt.Movsx ((ty_src, src), (ty_dst, (Asmt.Reg Asmt.R11)))) :: (Asmt.Mov (ty_dst, Asmt.Reg Asmt.R11, dst)) :: (fixErroneousAgain t)

            (* movzlq doesn't exist *)
            | Asmt.Movzx ((Asmt.LongWord, src), (Asmt.QuadWord, (Asmt.Reg _ as dst))) ->
                (Asmt.Mov (Asmt.LongWord, src, dst)) :: (fixErroneousAgain t)
            | Asmt.Movzx ((Asmt.LongWord, src), (Asmt.QuadWord, dst)) ->
                (Asmt.Mov (Asmt.LongWord, src, Asmt.Reg Asmt.R11)) :: (Asmt.Mov (Asmt.QuadWord, Asmt.Reg Asmt.R11, dst)) :: (fixErroneousAgain t)

            (* movzx cannot have mem as dst *)
            | Asmt.Movzx ((ty_src, src), (ty_dst, (Asmt.Memory _ as dst)))
            | Asmt.Movzx ((ty_src, src), (ty_dst, (Asmt.Data _ as dst))) ->
                (Asmt.Movzx ((ty_src, src), (ty_dst, (Asmt.Reg Asmt.R11)))) :: (Asmt.Mov (ty_dst, Asmt.Reg Asmt.R11, dst)) :: (fixErroneousAgain t)

            (*Prevent xorpd from reading out_of_range 8bytes when src is 8byte mem*)
            | Asmt.Binary (Asmt.Double, Asmt.Xor, (Asmt.Memory _ as src), dst)
            | Asmt.Binary (Asmt.Double, Asmt.Xor, (Asmt.Data _ as src), dst) ->
                (Asmt.Mov (Asmt.Double, src, Asmt.Reg Asmt.XMM14)) ::
                (Asmt.Binary (Asmt.Double, Asmt.Xor, Asmt.Reg Asmt.XMM14, dst)) :: (fixErroneousAgain t)

            (* if src imm is more than 32bit number *)

            | Asmt.Binary (Asmt.QuadWord, binop, (Asmt.Imm num as imm), dst) when not (Z.fits_int32 num) ->
                (Asmt.Mov (Asmt.QuadWord, imm, Asmt.Reg Asmt.R10)) :: (Asmt.Binary (Asmt.QuadWord, binop, Asmt.Reg Asmt.R10, dst)) :: (fixErroneousAgain t)
            | Asmt.Cmp (Asmt.QuadWord, (Asmt.Imm num as imm), dst) when not (Z.fits_int32 num) ->
                (Asmt.Mov (Asmt.QuadWord, imm, Asmt.Reg Asmt.R10)) :: (Asmt.Cmp (Asmt.QuadWord, Asmt.Reg Asmt.R10, dst)) :: (fixErroneousAgain t)
            | Asmt.Push (Asmt.QuadWord, (Asmt.Imm num as imm)) when not (Z.fits_int32 num) ->
                (Asmt.Mov (Asmt.QuadWord, imm, Asmt.Reg Asmt.R10)) :: (Asmt.Push (Asmt.QuadWord, Asmt.Reg Asmt.R10)) :: (fixErroneousAgain t)

            (* cannot mov 64bit imm into mem *)
            | Asmt.Mov (Asmt.QuadWord, (Asmt.Imm num as imm), dst) when not (Z.fits_int32 num) ->
                (Asmt.Mov (Asmt.QuadWord, imm, Asmt.Reg Asmt.R10)) :: (Asmt.Mov (Asmt.QuadWord, Asmt.Reg Asmt.R10, dst)) :: (fixErroneousAgain t)

            (* Truncate imms here to leave the assembler to relax *)
            | Asmt.Mov (Asmt.LongWord, Asmt.Imm num, dst) ->
                (Asmt.Mov (Asmt.LongWord, Asmt.Imm (Z.signed_extract num 0 32), dst)) :: (fixErroneousAgain t)
            | Asmt.Mov (Asmt.Word, Asmt.Imm num, dst) ->
                (Asmt.Mov (Asmt.Word, Asmt.Imm (Z.signed_extract num 0 16), dst)) :: (fixErroneousAgain t)
            | Asmt.Mov (Asmt.Byte, Asmt.Imm num, dst) ->
                (Asmt.Mov (Asmt.Byte, Asmt.Imm (Z.signed_extract num 0 8), dst)) :: (fixErroneousAgain t)

            (* cvtsi2sx can't have imm as src*)
            | Asmt.Cvtsi2sx ((s_typ, (Asmt.Imm _ as s)), dd) ->
                (Asmt.Mov (s_typ, s, Asmt.Reg Asmt.R10)) ::
                (Asmt.Cvtsi2sx ((s_typ, Asmt.Reg Asmt.R10), dd)) :: (fixErroneousAgain t)

            | _ -> h :: (fixErroneousAgain t)
        end
    in (name,
        (Asmt.AllocateStack allocateBytes) :: (instructions |> fixErroneous |> fixErroneousAgain),
        is_global
    )




let assemble tacky =
    let (text, bss, data, ro) = parseProgram tacky in
    (List.map (fun t ->
        let (tl, stackOffset) = replacePseudos t in
        fixUp tl stackOffset
    ) text), bss, data, ro

