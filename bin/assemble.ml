
module Tac = Tacky

let parseUnaryOp = function
    | Tac.Negate -> Asmt.Neg
    | Tac.Complement -> Asmt.Not
    | Tac.Not -> failwith "Tacky Unary Operator is not simple to Asmt."

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

let chooseBinop binop src1 src2 dst = match binop with
    | Tac.Divide ->
        [Asmt.Mov (src1, Asmt.Reg Asmt.RAX);
         Asmt.Cdq;
         Asmt.Idiv src2;
         Asmt.Mov (Asmt.Reg Asmt.RAX, dst)]
    | Tac.Remainder ->
        [Asmt.Mov (src1, Asmt.Reg Asmt.RAX);
         Asmt.Cdq;
         Asmt.Idiv src2;
         Asmt.Mov (Asmt.Reg Asmt.RDX, dst)]

    | Tac.Add | Tac.Subtract | Tac.Multiply | Tac.And | Tac.Or | Tac.Xor | Tac.LShift | Tac.RShift ->
        let binop = parseBinaryOp binop in
        [Asmt.Mov (src1, dst);
         Asmt.Binary (binop, src2, dst)]

    | Tac.Equal | Tac.NotEqual | Tac.LessThan | Tac.LessOrEqual | Tac.GreaterThan | Tac.GreaterOrEqual ->
        let cc = parseCondOp binop in
        [Asmt.Binary (Asmt.Xor, dst, dst);
         Asmt.Cmp (src2, src1);
         Asmt.SetCC (cc, dst)]

let rec parseOperand opr =
    match opr with
        | Tac.Constant num -> Asmt.Imm num
        | Tac.Var id -> Asmt.Pseudo id

and parseInstruction inst =
    match inst with
        | Tac.Return d -> [
            Asmt.Mov (parseOperand d, Asmt.Reg Asmt.RAX);
            Asmt.Ret]
        | Tac.Unary (Tac.Not, s ,d) -> parseInstruction (Tac.Binary (Tac.Equal, s, Tac.Constant 0l, d))
        | Tac.Unary (unop, s, d) ->
            let src = parseOperand s in
            let dst = parseOperand d in
            let unop = parseUnaryOp unop in
          [
            Asmt.Mov (src, dst);
            Asmt.Unary (unop, dst)]
        | Tac.Binary (binop, s1, s2, d) ->
            let src1 = parseOperand s1 in
            let src2 = parseOperand s2 in
            let dst = parseOperand d in
            chooseBinop binop src1 src2 dst
        | Tac.Copy (s, d) ->
            let src = parseOperand s in
            let dst = parseOperand d in
            [Asmt.Mov (src, dst)]
        | Tac.Jump lbl ->
            [Asmt.Jmp lbl]
        | Tac.JumpIfZero (v, lbl) ->
            let value = parseOperand v in
          [
            Asmt.Cmp (Asmt.Imm 0l, value);
            Asmt.JmpCC (Asmt.E, lbl)]
        | Tac.JumpIfNotZero (v, lbl) ->
            let value = parseOperand v in
          [
            Asmt.Cmp (Asmt.Imm 0l, value);
            Asmt.JmpCC (Asmt.NE, lbl)]
        | Tac.Label lbl ->
            [Asmt.Label lbl]

let parseTopLevel tl =
    match tl with
        | Tac.Function (name, instructions) -> Asmt.Function (name, 
            List.fold_left (fun acc inst -> acc @ (parseInstruction inst)) [] instructions)


let parseProgram tacky = 
    match tacky with
        | Tac.Program tl -> Asmt.Program (parseTopLevel tl)

let replacePseudos (Asmt.Program (Asmt.Function (name, instructions))) =
    let offset = ref 0L in
    let dict = ref [] in
    let f operand = match operand with
        | Asmt.Imm _ | Asmt.Reg _ | Asmt.Stack _ -> operand
        | Asmt.Pseudo id -> begin
            match (List.assoc_opt id (!dict)) with
                | Some operand -> operand
                | None ->
                    let () = offset := Int64.add !offset 4L in
                    let operand = Asmt.Stack !offset in
                    let () = dict := ((id, operand) :: !dict) in
                    operand
        end

    in let newInstructions = List.map (fun instr -> match instr with
        | Asmt.Mov (s, d) -> Asmt.Mov (f s, f d)
        | Asmt.Unary (x1, d) -> Asmt.Unary (x1, f d)
        | Asmt.Binary (x1, s, d) -> Asmt.Binary (x1, f s, f d)
        | Asmt.Cmp (s, d) -> Asmt.Cmp (f s, f d)
        | Asmt.Idiv s -> Asmt.Idiv (f s)
        | Asmt.SetCC (x1, s) -> Asmt.SetCC (x1, f s)

        | Asmt.Jmp _
        | Asmt.JmpCC _
        | Asmt.Label _
        | Asmt.Cdq
        | Asmt.AllocateStack _
        | Asmt.Ret -> instr
    ) instructions

    in (Asmt.Program (Asmt.Function (name, newInstructions)), !offset)

let fixUp (Asmt.Program (Asmt.Function (name, instructions))) allocateBytes =
    let rec fixErroneous instrs = match instrs with
        | [] -> []
        | h :: t -> begin match h with
            (*Xor-zeroing a mem is slower than a mov 0*)
            | Asmt.Binary (Asmt.Xor, (Asmt.Stack k1 as d), (Asmt.Stack k2))
              when (Int64.compare k1 k2) = 0 ->
                (Asmt.Mov (Asmt.Imm 0l, d)) :: (fixErroneous t)

            (*Imul cannot do mem as dst*)
            | Asmt.Binary (Asmt.Mul, s, (Asmt.Stack _ as d)) ->
                (Asmt.Mov (d, Asmt.Reg Asmt.R11)) ::
                (Asmt.Binary (Asmt.Mul, s, Asmt.Reg Asmt.R11)) ::
                (Asmt.Mov (Asmt.Reg Asmt.R11, d)) :: (fixErroneous t)

            (*Shifts are restrictive and c standard is ambiguous*)
            | Asmt.Binary (Asmt.Sal, (Asmt.Imm k), d)
            | Asmt.Binary (Asmt.Sar, (Asmt.Imm k), d) when
            (Int32.compare k 0l) < 0 || (Int32.compare k 31l) > 0 ->
                let () = Log.warning "shift count >= width of type" in
                (Asmt.Mov (Asmt.Imm 0l, d)) :: (fixErroneous t) (*gcc and clang do this*)

            (*k must be either an immediate or in %cl*)
            (*also doesn't agree with c standard per se. x86 and-masks the 5 lower bits of %cl as opposed to overshift d to 0*)
            | Asmt.Binary (Asmt.Sal as op, (Asmt.Reg _ as k), d)
            | Asmt.Binary (Asmt.Sar as op, (Asmt.Reg _ as k), d)
            | Asmt.Binary (Asmt.Sal as op, (Asmt.Stack _ as k), d)
            | Asmt.Binary (Asmt.Sar as op, (Asmt.Stack _ as k), d) ->
                (*the code emission phase will make %rcx in the 2nd instruction into %cl*)
                (Asmt.Mov (k, Asmt.Reg Asmt.RCX)) :: (Asmt.Binary (op, Asmt.Reg Asmt.RCX, d)) :: (fixErroneous t)


            (* double mem *)
            | Asmt.Mov ((Asmt.Stack _ as s), (Asmt.Stack _ as d)) ->
                (Asmt.Mov (s, Asmt.Reg Asmt.R10)) :: (Asmt.Mov (Asmt.Reg Asmt.R10, d)) :: (fixErroneous t)
            | Asmt.Binary (binop, (Asmt.Stack _ as s), (Asmt.Stack _ as d)) ->
                (Asmt.Mov (s, Asmt.Reg Asmt.R10)) :: (Asmt.Binary (binop, Asmt.Reg Asmt.R10, d)) :: (fixErroneous t)
            | Asmt.Cmp ((Asmt.Stack _ as s), (Asmt.Stack _ as d)) ->
                (Asmt.Mov (s, Asmt.Reg Asmt.R10)) :: (Asmt.Cmp (Asmt.Reg Asmt.R10, d)) :: (fixErroneous t)

            (* cmp cannot have an imm d*)
            | Asmt.Cmp (s, (Asmt.Imm _ as d)) ->
                (Asmt.Mov (d, Asmt.Reg Asmt.R11)) :: (Asmt.Cmp (s, Asmt.Reg Asmt.R11)) :: (fixErroneous t)

            (*Idiv cannot do imm*)
            | Asmt.Idiv (Asmt.Imm _ as imm) ->
                (Asmt.Mov (imm, Asmt.Reg Asmt.R10)) :: (Asmt.Idiv (Asmt.Reg Asmt.R10)) :: (fixErroneous t)

            | _ -> h :: (fixErroneous t)
        end
    in Asmt.Program (Asmt.Function (name,
        (Asmt.AllocateStack allocateBytes) :: (fixErroneous instructions)
    ))




let assemble tacky =
    let asmt = parseProgram tacky in
    let (asmt, stackOffset) = replacePseudos asmt in
    let asmt = fixUp asmt stackOffset in
    asmt

