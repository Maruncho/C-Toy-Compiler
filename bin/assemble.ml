
module Tac = Tacky

let parseUnaryOp = function
    | Tac.Negate -> Asmt.Neg
    | Tac.Complement -> Asmt.Not

let rec parseOperand opr =
    match opr with
        | Tac.Constant num -> Asmt.Imm num
        | Tac.Var id -> Asmt.Pseudo id

and parseInstruction inst =
    match inst with
        | Tac.Return d -> [
            Asmt.Mov (parseOperand d, Asmt.Reg Asmt.RAX);
            Asmt.Ret]
        | Tac.Unary (unop, s, d) ->
            let src = parseOperand s in
            let dst = parseOperand d in
            let unop = parseUnaryOp unop in
          [
            Asmt.Mov (src, dst);
            Asmt.Unary (unop, dst)]

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

        | Asmt.AllocateStack _
        | Asmt.Ret -> instr
    ) instructions

    in (Asmt.Program (Asmt.Function (name, newInstructions)), !offset)

let fixUp (Asmt.Program (Asmt.Function (name, instructions))) allocateBytes =
    let rec fixDoubleMem instrs = match instrs with
        | [] -> []
        | h :: t -> begin match h with
            | Asmt.Mov ((Asmt.Stack _ as s), (Asmt.Stack _ as d)) ->
                (Asmt.Mov (s, Asmt.Reg Asmt.R10)) :: (Asmt.Mov (Asmt.Reg Asmt.R10, d)) :: (fixDoubleMem t)
            | _ -> h :: (fixDoubleMem t)
        end
    in Asmt.Program (Asmt.Function (name,
        (Asmt.AllocateStack allocateBytes) :: (fixDoubleMem instructions)
    ))




let assemble tacky =
    let asmt = parseProgram tacky in
    let (asmt, stackOffset) = replacePseudos asmt in
    let asmt = fixUp asmt stackOffset in
    asmt

