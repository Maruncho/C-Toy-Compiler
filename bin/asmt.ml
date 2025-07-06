
let debug = ref false;

type identifier = string
type translationUnitIdentifiersDict = unit Environment.Env.t

type assembly_type = Byte | Word | LongWord | QuadWord

type cond_code = E | NE | G | GE | L | LE

type register = RAX | RCX |
                RDX | RDI |
                RSI | RSP |
                R8  | R9  |
                R10 | R11

type unop = Neg | Not
type binop = Add | Sub | Mul |
             And | Or | Xor | Sal | Sar

type operand = Imm of Z.t
             | Reg of register
             | Pseudo of identifier
             | Data of identifier
             | Stack of Int64.t

type instruction = Mov of assembly_type * operand * operand
                 | Movsx of (assembly_type * operand) * (assembly_type * operand)
                 | Unary of assembly_type * unop * operand
                 | Incr of assembly_type * operand
                 | Decr of assembly_type * operand
                 | Binary of assembly_type * binop * operand * operand
                 | Cmp of assembly_type * operand * operand
                 | Idiv of assembly_type * operand
                 | SignExtend of assembly_type
                 | Jmp of identifier
                 | JmpCC of cond_code * identifier
                 | SetCC of cond_code * operand
                 | Label of identifier
                 | AllocateStack of Int64.t
                 | DeallocateStack of Int64.t
                 | Push of assembly_type * operand
                 | Call of identifier
                 | Ret

type func = string * instruction list * bool
type bss = string * assembly_type * bool
type data = string * Z.t * assembly_type * bool

type program = func list * bss list * data list

let cond_code_str = function
    | E -> "e"
    | NE -> "ne"
    | G -> "g"
    | GE -> "ge"
    | L -> "l"
    | LE -> "le"

let type_to_size = function
    | Byte -> 1
    | Word -> 2
    | LongWord -> 4
    | QuadWord -> 8

let type_to_string = function
    | Byte -> "byte"
    | Word -> "word"
    | LongWord -> "long"
    | QuadWord -> "quad"

let register_str reg = function
     | Byte -> (match reg with
        | RAX -> "%al"
        | RCX -> "%cl"
        | RDX -> "%dl"
        | RDI -> "%dil"
        | RSI -> "%sil"
        | RSP -> "%spl"
        | R8  -> "%r8b"
        | R9  -> "%r9b"
        | R10 -> "%r10b"
        | R11 -> "%r11b"
    )| Word -> (match reg with
        | RAX -> "%ax"
        | RCX -> "%cx"
        | RDX -> "%dx"
        | RDI -> "%di"
        | RSI -> "%si"
        | RSP -> "%sp"
        | R8  -> "%r8w"
        | R9  -> "%r9w"
        | R10 -> "%r10w"
        | R11 -> "%r11w"
    )| LongWord -> (match reg with
        | RAX -> "%eax"
        | RCX -> "%ecx"
        | RDX -> "%edx"
        | RDI -> "%edi"
        | RSI -> "%esi"
        | RSP -> "%esp"
        | R8  -> "%r8d"
        | R9  -> "%r9d"
        | R10 -> "%r10d"
        | R11 -> "%r11d"
    )| QuadWord -> (match reg with
        | RAX -> "%rax"
        | RCX -> "%rcx"
        | RDX -> "%rdx"
        | RDI -> "%rdi"
        | RSI -> "%rsi"
        | RSP -> "%rsp"
        | R8  -> "%r8"
        | R9  -> "%r9"
        | R10 -> "%r10"
        | R11 -> "%r11"
    )

let p = function
    | Byte -> "b"
    | Word -> "w"
    | LongWord -> "l"
    | QuadWord -> "q"

let unop_str op typ = (match op with
    | Neg -> "neg"
    | Not -> "not"
    ) ^ (p typ) ^ "\t"

let binop_str op typ = (match op with
    | Add -> "add"
    | Sub -> "sub"
    | Mul -> "imul"
    | And -> "and"
    | Or  -> "or"
    | Xor -> "xor"
    | Sal -> "sal"
    | Sar -> "sar"
    ) ^ (p typ) ^ "\t"

let operand_str asm_type oper externalNames =
    match oper with
        | Imm num -> "$" ^ (Z.to_string num)
        | Reg reg -> register_str reg asm_type
        | Pseudo id -> if not !debug then failwith "PseudoRegister in prod" else "%" ^ id
        | Data id -> (if Environment.setMem id externalNames then id^"@PLT" else id) ^ "(%rip)"
        | Stack num -> (Int64.to_string num)^"(%rbp)"

let instruction_str inst externalNames =
    let en = externalNames in
    (match inst with Label _ -> "" | _ -> "\t") ^ (*ugly, but outliers do exist in simpler models*)
    (match inst with
        | Mov (typ, s, d) -> "mov"^(p typ)^"\t" ^ (operand_str typ s en) ^ ", " ^ (operand_str typ d en)
        | Movsx ((typ_s, s), (typ_d, d)) -> "movs"^(p typ_s)^(p typ_d)^"\t" ^ (operand_str typ_s s en) ^ ", " ^ (operand_str typ_d d en)
        | Unary (typ, unop, d) -> (unop_str unop typ) ^ (operand_str typ d en)

        | Decr (typ, d) -> "dec"^(p typ)^"\t" ^ (operand_str typ d en)
        | Incr (typ, d) -> "inc"^(p typ)^"\t" ^ (operand_str typ d en)

        | Binary (typ, (Sal as binop), s, d)
        | Binary (typ, (Sar as binop), s, d) -> (binop_str binop typ) ^ (operand_str Byte s en) ^ ", " ^ (operand_str typ d en)
        | Binary (typ, binop, s, d) -> (binop_str binop typ) ^ (operand_str typ s en) ^ ", " ^ (operand_str typ d en)

        | Cmp (typ, s, d) -> "cmp"^(p typ)^"\t" ^ (operand_str typ s en) ^ ", " ^ (operand_str typ d en)
        | Idiv (typ, s) -> "idiv"^(p typ)^"\t" ^ (operand_str typ s en)
        | SignExtend Byte -> failwith "SignExtend Byte doesn't exist."
        | SignExtend Word -> "cwd"
        | SignExtend LongWord -> "cdq"
        | SignExtend QuadWord -> "cqo"
        | Jmp lbl -> "jmp\t" ^ lbl
        | JmpCC (cc, lbl) -> "j"^(cond_code_str cc)^"\t" ^ lbl
        | SetCC (cc, d) -> "set"^(cond_code_str cc)^"\t" ^ (operand_str Byte d en)
        | Label lbl -> lbl^":"
        | AllocateStack bytes -> "subq\t$" ^ (Int64.to_string bytes) ^ ", %rsp"
        | DeallocateStack bytes -> "addq\t$" ^ (Int64.to_string bytes) ^ ", %rsp"
        | Push (typ, s) -> "push"^(p typ)^"\t" ^ (operand_str QuadWord s en)
        | Call lbl -> "call\t" ^ (if Environment.setMem lbl externalNames then lbl^"@PLT" else lbl)
        | Ret -> "movq\t%rbp, %rsp\n\tpopq\t%rbp\n\tret"
    ) ^ "\n"

let func_str (name, instructions, is_global) externalNames =
    (if is_global then "\t.globl " ^ name ^ "\n" else "")  ^
    name ^ ":\n" ^
    "\tpushq\t%rbp\n" ^
    "\tmovq\t%rsp, %rbp\n" ^
    (List.fold_left (fun acc inst -> acc ^ (instruction_str inst externalNames)) "" instructions) ^
    "\n"

let bss_str (name, typ, is_global) =
    (if is_global then "\t.globl " ^ name ^ "\n" else "")  ^
    name ^ ":\n" ^
    "\t.zero "^(type_to_size typ |> string_of_int)^"\n"

let data_str (name, init, typ, is_global) =
    (if is_global then "\t.globl " ^ name ^ "\n" else "")  ^
    name ^ ":\n" ^
    "\t."^(type_to_string typ)^" "^(Z.to_string init)^"\n"


let string_of_asmt (fns, (bsses:bss list), (datas:data list)) externalNames =
    let bsses = List.sort (fun (_,typ1,_) (_,typ2,_) -> ((type_to_size typ2) - (type_to_size typ1))) bsses in
    let datas = List.sort (fun (_,_,typ1,_) (_,_,typ2,_) -> ((type_to_size typ2) - (type_to_size typ1))) datas in

    (if not (List.is_empty bsses) then
        "\t.bss\n\t.align 8\n" ^
        List.fold_left (fun acc x -> acc ^ (bss_str x)) "" bsses
    else "") ^ 
    (if not (List.is_empty datas) then
        "\n\t.data\n\t.align 8\n" ^
        List.fold_left (fun acc x -> acc ^ (data_str x)) "" datas
    else "") ^
    (if not (List.is_empty fns) then
        "\n\t.text\n" ^
        List.fold_left (fun acc x -> acc ^ (func_str x externalNames)) "" fns
    else "") ^

    "\t.section .note.GNU-stack,\"\",@progbits\n"

let string_of_asmt_debug asmt externalNames = 
    (*Thread safety is not my expertise*)
    let () = debug := true in
    let str = string_of_asmt asmt externalNames in
    let () = debug := false in
    str

