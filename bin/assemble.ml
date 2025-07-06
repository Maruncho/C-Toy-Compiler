
module Tac = Tacky

let parseUnaryOp = function
    | Tac.Negate -> Asmt.Neg
    | Tac.Complement -> Asmt.Not
    | Tac.Not -> failwith "Tacky Unary Operator is not simple to Asmt."
    | Tac.Incr | Tac.Decr -> failwith "Tacky Increment and Decrement are not handled as a normal unary"

let parseBinaryOp = function
    | Tac.Add -> Asmt.Add
    | Tac.Subtract -> Asmt.Sub
    | Tac.Multiply -> Asmt.Mul
    | Tac.And -> Asmt.And
    | Tac.Or -> Asmt.Or
    | Tac.Xor -> Asmt.Xor
    | Tac.LShift -> Asmt.Sal
    | Tac.RShift -> Asmt.Sar
    | _ -> failwith "Tacky Binary Operator is not simple to Asmt."

let parseCondOp = function
    | Tac.Equal -> Asmt.E
    | Tac.NotEqual -> Asmt.NE
    | Tac.LessThan -> Asmt.L
    | Tac.LessOrEqual -> Asmt.LE
    | Tac.GreaterThan -> Asmt.G
    | Tac.GreaterOrEqual -> Asmt.GE
    | _ -> failwith "Incorrect usage of parseCondOp."

let chooseBinop binop src1 src2 dst typ = match binop with
    | Tac.Divide ->
        [Asmt.Mov (typ, src1, Asmt.Reg Asmt.RAX);
         Asmt.SignExtend typ;
         Asmt.Idiv (typ, src2);
         Asmt.Mov (typ, Asmt.Reg Asmt.RAX, dst)]
    | Tac.Remainder ->
        [Asmt.Mov (typ, src1, Asmt.Reg Asmt.RAX);
         Asmt.SignExtend typ;
         Asmt.Idiv (typ, src2);
         Asmt.Mov (typ, Asmt.Reg Asmt.RDX, dst)]

    | Tac.Add | Tac.Subtract | Tac.Multiply | Tac.And | Tac.Or | Tac.Xor | Tac.LShift | Tac.RShift ->
        let binop = parseBinaryOp binop in
        [Asmt.Mov (typ, src1, dst);
         Asmt.Binary (typ, binop, src2, dst)]

    | Tac.Equal | Tac.NotEqual | Tac.LessThan | Tac.LessOrEqual | Tac.GreaterThan | Tac.GreaterOrEqual ->
        let cc = parseCondOp binop in
        [Asmt.Binary (Asmt.QuadWord, Asmt.Xor, dst, dst);
         Asmt.Cmp (typ, src2, src1);
         Asmt.SetCC (cc, dst)]

let getParamOperand = function
    | 0 -> Asmt.Reg Asmt.RDI
    | 1 -> Asmt.Reg Asmt.RSI
    | 2 -> Asmt.Reg Asmt.RDX
    | 3 -> Asmt.Reg Asmt.RCX
    | 4 -> Asmt.Reg Asmt.R8
    | 5 -> Asmt.Reg Asmt.R9
    | x when x < 0 -> failwith "Negative index getParamOperand assemble.ml"
    | x -> Asmt.Stack (Int64.of_int (8*(x-5)+8 (*+8 is return adress*)))

let parseType typ =
    match typ with
        | Tac.Int32 -> Asmt.LongWord
        | Tac.Int64 -> Asmt.QuadWord

let parseOperand opr =
    match opr with
        | Tac.Constant (num, typ) -> parseType typ, Asmt.Imm num
        | Tac.Var (id, typ) -> parseType typ, Asmt.Pseudo id
        | Tac.StaticVar (id, typ) -> parseType typ, Asmt.Data id


let rec parseInstruction inst =
    match inst with
        | Tac.Return d ->
            let (typ, d) = parseOperand d in
           [
            Asmt.Mov (typ, d, Asmt.Reg Asmt.RAX);
            Asmt.Ret]
        | Tac.SignExtend (s, d) ->
            let (s_typ, src) = parseOperand s in
            let (d_typ, dst) = parseOperand d in
            if s_typ = d_typ then failwith "DEBUG: Assemble: SRC and DST types mismatch." else
            [Asmt.Movsx ((s_typ, src), (d_typ, dst))]
        | Tac.Truncate (s, d) ->
            let (s_typ, src) = parseOperand s in
            let (d_typ, dst) = parseOperand d in
            if s_typ = d_typ then failwith "DEBUG: Assemble: SRC and DST types mismatch." else
            [Asmt.Mov (d_typ, src, dst)]
        | Tac.Unary (Tac.Not, s ,d) -> parseInstruction (Tac.Binary (Tac.Equal, s, Tac.Constant (Z.zero, Tac.operand_type s), d))
        | Tac.Unary (Tac.Incr, d, _) -> let (typ, d) = parseOperand d in [Asmt.Incr (typ, d)]
        | Tac.Unary (Tac.Decr, d, _) -> let (typ, d) = parseOperand d in [Asmt.Decr (typ, d)]
        | Tac.Unary (unop, s, d) ->
            let (s_typ, src) = parseOperand s in
            let (d_typ, dst) = parseOperand d in
            if s_typ <> d_typ then failwith "DEBUG: Assemble: SRC and DST types mismatch." else
            let unop = parseUnaryOp unop in
          [
            Asmt.Mov (s_typ, src, dst);
            Asmt.Unary (s_typ, unop, dst)]
        | Tac.Binary (binop, s1, s2, d) ->
            let (s1_typ, src1) = parseOperand s1 in
            let (s2_typ, src2) = parseOperand s2 in
            let (d_typ, dst) = parseOperand d in
            if s1_typ <> s2_typ || s2_typ <> d_typ then failwith "DEBUG: Assemble: SRC1, SRC2 and DST types mismatch." else
            chooseBinop binop src1 src2 dst s1_typ
        | Tac.Copy (s, d) ->
            let (s_typ, src) = parseOperand s in
            let (d_typ, dst) = parseOperand d in
            if s_typ <> d_typ then failwith "DEBUG: Assemble: SRC and DST types mismatch." else
            [Asmt.Mov (s_typ, src, dst)]
        | Tac.Jump lbl ->
            [Asmt.Jmp lbl]
        | Tac.JumpIfZero (v, lbl) ->
            let (typ, value) = parseOperand v in
          [
            Asmt.Cmp (typ, Asmt.Imm Z.zero, value);
            Asmt.JmpCC (Asmt.E, lbl)]
        | Tac.JumpIfNotZero (v, lbl) ->
            let (typ, value) = parseOperand v in
          [
            Asmt.Cmp (typ, Asmt.Imm Z.zero, value);
            Asmt.JmpCC (Asmt.NE, lbl)]
        | Tac.Label lbl ->
            [Asmt.Label lbl]
        | Tac.Call (name, params, dst) ->
            let inReg = List.take 6 params in
            let inStack = List.drop 6 params |> List.rev in
            let extraPadding = (List.length inStack) mod 2 <> 0 in
            let deallocSize = Int64.of_int (8 * ((List.length inStack) + if extraPadding then 1 else 0)) in

            let regInstrs =  List.mapi (fun i x ->
                let (typ, x) = parseOperand x in Asmt.Mov (typ, x, getParamOperand i)) inReg in
            let stackInstrs = List.map (fun x -> let (typ, arg) = parseOperand x in match arg with
                | Asmt.Imm _ | Asmt.Reg _ -> [Asmt.Push (Asmt.QuadWord, arg)]
                | _ when typ = QuadWord -> [Asmt.Push (Asmt.QuadWord, arg)]
                | Asmt.Pseudo _ | Asmt.Stack _ | Asmt.Data _ -> [Asmt.Mov (typ, arg, Asmt.Reg Asmt.RAX);
                                                   Asmt.Push (QuadWord, (Asmt.Reg Asmt.RAX))])

                inStack |> List.flatten in
            let stackInstrs = if extraPadding then (Asmt.AllocateStack 8L) :: stackInstrs else stackInstrs in

            let (dst_type, dst) = parseOperand dst in
            let callInstrs = [Asmt.Call (name);
                              Asmt.DeallocateStack deallocSize;
                              Asmt.Mov(dst_type, Asmt.Reg Asmt.RAX, dst)] in
            regInstrs @ stackInstrs @ callInstrs

let parseProgram tacky =
    let func = ref [] in
    let data = ref [] in
    let bss = ref [] in
    let rec iter tls = match tls with
        | Tac.Function (name, is_global, params, instructions) :: rest ->
            let preInstrs = List.mapi (fun i (p, typ) -> Asmt.Mov(parseType typ, getParamOperand i, Asmt.Pseudo p)) params in
            let fn = (name, List.fold_left (fun acc inst -> acc @ (parseInstruction inst)) preInstrs instructions, is_global) in
            func := fn :: !func; iter rest
        | Tac.StaticVariable (name, is_global, init, typ) :: rest ->
            if Z.equal Z.zero init then
                (bss := (name, parseType typ, is_global) :: !bss; iter rest)
            else
                (data := (name, init, parseType typ, is_global) :: !data; iter rest)
        | [] -> ()
    in let () = match tacky with
        | Tac.Program tls -> iter tls
    in (!func, !bss, !data)

let replacePseudos (name, instructions, is_global) =
    let dict = ref [] in
    let f operand typ ((o8, o4, o2, o1) as offs) = match operand with 
        | Asmt.Imm _ | Asmt.Reg _ | Asmt.Stack _ | Asmt.Data _ -> offs
        | Asmt.Pseudo id -> if List.mem id !dict then offs else
            let offs = begin match typ with
                | Asmt.Byte ->     (o8, o4, o2, o1+1)
                | Asmt.Word ->     (o8, o4, o2+1, o1)
                | Asmt.LongWord -> (o8, o4+1, o2, o1)
                | Asmt.QuadWord -> (o8+1, o4, o2, o1)
            end
            in let () = dict := id :: !dict in offs

    in let (o8, o4, o2, o1) = List.fold_left (fun acc instr -> match instr with
        | Asmt.Mov (typ, s, d)
        | Asmt.Binary (typ, _, s, d)
        | Asmt.Cmp (typ, s, d) -> (f s typ acc) |> (f d typ)
        | Asmt.Unary (typ, _, d) -> f d typ acc
        | Asmt.Incr (typ, d)
        | Asmt.Decr (typ, d) -> f d typ acc
        | Asmt.Idiv (typ, s)
        | Asmt.Push (typ, s) -> f s typ acc
        | Asmt.SetCC (_, s) -> f s Asmt.Byte acc
        | Asmt.Movsx ((typ_s, s), (typ_d, d)) -> (f s typ_s acc) |> (f d typ_d)

        | Asmt.Jmp _
        | Asmt.JmpCC _
        | Asmt.Label _
        | Asmt.Call _
        | Asmt.SignExtend _
        | Asmt.AllocateStack _
        | Asmt.DeallocateStack _
        | Asmt.Ret -> acc

    ) (0, 0, 0, 0) instructions in

    let offset8 = ref 0L in
    let offset4 = ref (Int64.of_int(o8*8)) in
    let offset2 = ref (Int64.of_int(o8*8+o4*4)) in
    let offset1 = ref (Int64.of_int(o8*8+o4*4+o2*2)) in
    let dict = ref [] in
    let f operand typ = match operand with
        | Asmt.Imm _ | Asmt.Reg _ | Asmt.Stack _ | Asmt.Data _ -> operand
        | Asmt.Pseudo id -> begin match (List.assoc_opt id (!dict)) with
            | Some operand -> operand
            | None ->
                let offset = begin match typ with
                    | Asmt.Byte -> let () = offset1 := Int64.add !offset1 1L in !offset1
                    | Asmt.Word -> let () = offset2 := Int64.add !offset2 2L in !offset2
                    | Asmt.LongWord -> let () = offset4 := Int64.add !offset4 4L in !offset4
                    | Asmt.QuadWord -> let () = offset8 := Int64.add !offset8 8L in !offset8
                end in
                let operand = Asmt.Stack (Int64.neg offset) in
                let () = dict := ((id, operand) :: !dict) in
                operand
        end

    in let newInstructions = List.map (fun instr -> match instr with
        | Asmt.Mov (typ, s, d) -> Asmt.Mov (typ, f s typ, f d typ)
        | Asmt.Movsx ((typ_s, s), (typ_d, d)) -> Asmt.Movsx ((typ_s, f s typ_s), (typ_d, f d typ_d))
        | Asmt.Unary (typ, x1, d) -> Asmt.Unary (typ, x1, f d typ)
        | Asmt.Incr (typ, d) -> Asmt.Incr (typ, (f d typ))
        | Asmt.Decr (typ, d) -> Asmt.Decr (typ, (f d typ))
        | Asmt.Binary (typ, x1, s, d) -> Asmt.Binary (typ, x1, f s typ, f d typ)
        | Asmt.Cmp (typ, s, d) -> Asmt.Cmp (typ, f s typ, f d typ)
        | Asmt.Idiv (typ, s) -> Asmt.Idiv (typ, f s typ)
        | Asmt.SetCC (x1, s) -> Asmt.SetCC (x1, f s Asmt.Byte)

        | Asmt.Jmp _
        | Asmt.JmpCC _
        | Asmt.Label _
        | Asmt.Call _
        | Asmt.SignExtend _
        | Asmt.AllocateStack _
        | Asmt.DeallocateStack _
        | Asmt.Ret -> instr

        | Asmt.Push (typ, s) -> Asmt.Push (typ, f s typ)
    ) instructions

    in let roundAlloc offset =
        let remainder = Int64.rem (Int64.add 0L offset) 16L in
        let pad = if remainder = 0L then 0L else Int64.sub 16L remainder in
        Int64.add offset pad

    in (name, newInstructions, is_global), roundAlloc (Int64.of_int (o8*8+o4*4+o2*2+o1))

let fixUp (name, instructions, is_global) allocateBytes =
    let rec fixErroneous instrs = match instrs with
        | [] -> []

        (*Remove unnecessary jumps*)
        | Asmt.Jmp jmp :: (Asmt.Label lbl as l) :: t when jmp = lbl -> l ::(fixErroneous t)
        | Asmt.JmpCC (_, jmp) :: (Asmt.Label lbl as l) :: t when jmp = lbl -> l :: (fixErroneous t)

        | h :: t -> begin match h with

            (*Xor-zeroing a mem is slower than a mov 0*)
            | Asmt.Binary (ty, Asmt.Xor, (Asmt.Stack k1 as d), (Asmt.Stack k2))
              when (Int64.compare k1 k2) = 0 ->
                (Asmt.Mov (ty, Asmt.Imm Z.zero, d)) :: (fixErroneous t)
            | Asmt.Binary (ty, Asmt.Xor, (Asmt.Data k1 as d), (Asmt.Data k2))
              when (String.compare k1 k2) = 0 ->
                (Asmt.Mov (ty, Asmt.Imm Z.zero, d)) :: (fixErroneous t)

            (*Imul cannot do mem as dst*)
            | Asmt.Binary (ty, Asmt.Mul, s, (Asmt.Stack _ as d))
            | Asmt.Binary (ty, Asmt.Mul, s, (Asmt.Data _ as d)) ->
                (Asmt.Mov (ty, d, Asmt.Reg Asmt.R11)) ::
                (Asmt.Binary (ty, Asmt.Mul, s, Asmt.Reg Asmt.R11)) ::
                (Asmt.Mov (ty, Asmt.Reg Asmt.R11, d)) :: (fixErroneous t)

            (*Shifts are restrictive and c standard is ambiguous*)
            | Asmt.Binary (ty, Asmt.Sal, (Asmt.Imm k), d)
            | Asmt.Binary (ty, Asmt.Sar, (Asmt.Imm k), d) when
            (Z.compare k Z.zero) < 0 || (Z.compare k (Z.of_int 31)) > 0 ->
                let () = Log.warning "shift count >= width of type" in
                (Asmt.Mov (ty, Asmt.Imm Z.zero, d)) :: (fixErroneous t) (*gcc and clang do this*)

            (*k must be either an immediate or in %cl*)
            (*also doesn't agree with c standard per se. x86 and-masks the 5 lower bits of %cl as opposed to overshift d to 0*)
            | Asmt.Binary (ty, (Asmt.Sal as op), (Asmt.Reg _ as k), d)
            | Asmt.Binary (ty, (Asmt.Sar as op), (Asmt.Reg _ as k), d)
            | Asmt.Binary (ty, (Asmt.Sal as op), (Asmt.Stack _ as k), d)
            | Asmt.Binary (ty, (Asmt.Sar as op), (Asmt.Stack _ as k), d)
            | Asmt.Binary (ty, (Asmt.Sal as op), (Asmt.Data _ as k), d)
            | Asmt.Binary (ty, (Asmt.Sar as op), (Asmt.Data _ as k), d) ->
                (*the code emission phase will make %rcx in the 2nd instruction into %cl*)
                (Asmt.Mov (ty, k, Asmt.Reg Asmt.RCX)) :: (Asmt.Binary (ty, op, Asmt.Reg Asmt.RCX, d)) :: (fixErroneous t)


            (* double mem *)
            | Asmt.Mov (ty, (Asmt.Stack _ as s), (Asmt.Stack _ as d))
            | Asmt.Mov (ty, (Asmt.Stack _ as s), (Asmt.Data _ as d))
            | Asmt.Mov (ty, (Asmt.Data _ as s), (Asmt.Stack _ as d))
            | Asmt.Mov (ty, (Asmt.Data _ as s), (Asmt.Data _ as d)) ->
                (Asmt.Mov (ty, s, Asmt.Reg Asmt.R10)) :: (Asmt.Mov (ty, Asmt.Reg Asmt.R10, d)) :: (fixErroneous t)

            | Asmt.Binary (ty, binop, (Asmt.Stack _ as s), (Asmt.Stack _ as d))
            | Asmt.Binary (ty, binop, (Asmt.Stack _ as s), (Asmt.Data _ as d))
            | Asmt.Binary (ty, binop, (Asmt.Data _ as s), (Asmt.Stack _ as d))
            | Asmt.Binary (ty, binop, (Asmt.Data _ as s), (Asmt.Data _ as d)) ->
                (Asmt.Mov (ty, s, Asmt.Reg Asmt.R10)) :: (Asmt.Binary (ty, binop, Asmt.Reg Asmt.R10, d)) :: (fixErroneous t)

            | Asmt.Cmp (ty, (Asmt.Stack _ as s), (Asmt.Stack _ as d))
            | Asmt.Cmp (ty, (Asmt.Stack _ as s), (Asmt.Data _ as d))
            | Asmt.Cmp (ty, (Asmt.Data _ as s), (Asmt.Stack _ as d))
            | Asmt.Cmp (ty, (Asmt.Data _ as s), (Asmt.Data _ as d)) ->
                (Asmt.Mov (ty, s, Asmt.Reg Asmt.R10)) :: (Asmt.Cmp (ty, Asmt.Reg Asmt.R10, d)) :: (fixErroneous t)

            (* movsx cannot have imm as src *)
            | Asmt.Movsx ((ty_src, (Asmt.Imm _ as imm)), (ty_dst, dst)) ->
                (Asmt.Mov(ty_src, imm, Asmt.Reg Asmt.R10)) :: (Asmt.Movsx ((ty_src, Asmt.Reg Asmt.R10), (ty_dst, dst))) :: (fixErroneous t)

            (* cmp cannot have an imm d*)
            | Asmt.Cmp (ty, s, (Asmt.Imm _ as d)) ->
                (Asmt.Mov (ty, d, Asmt.Reg Asmt.R11)) :: (Asmt.Cmp (ty, s, Asmt.Reg Asmt.R11)) :: (fixErroneous t)

            (*Idiv cannot do imm*)
            | Asmt.Idiv (ty, (Asmt.Imm _ as imm)) ->
                (Asmt.Mov (ty, imm, Asmt.Reg Asmt.R10)) :: (Asmt.Idiv (ty, Asmt.Reg Asmt.R10)) :: (fixErroneous t)

            | _ -> h :: (fixErroneous t)
        end in
    let rec fixErroneousAgain instrs = match instrs with
        | [] -> []
        | h :: t -> begin match h with

            (* movsx cannot have mem as dst *)
            | Asmt.Movsx ((ty_src, src), (ty_dst, (Asmt.Stack _ as dst)))
            | Asmt.Movsx ((ty_src, src), (ty_dst, (Asmt.Data _ as dst))) ->
                (Asmt.Movsx ((ty_src, src), (ty_dst, (Asmt.Reg Asmt.R11)))) :: (Asmt.Mov (ty_dst, Asmt.Reg Asmt.R11, dst)) :: (fixErroneousAgain t)

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

            | _ -> h :: (fixErroneousAgain t)
        end
    in (name,
        (Asmt.AllocateStack allocateBytes) :: (fixErroneous instructions |> fixErroneousAgain),
        is_global
    )




let assemble tacky =
    let (text, bss, data) = parseProgram tacky in
    (List.map (fun t ->
        let (tl, stackOffset) = replacePseudos t in
        fixUp tl stackOffset
    ) text), bss, data

