
exception ParserError of string

let compare n1 n2 = match n1, n2 with
    | Const.I _, Const.D _ -> -1
    | Const.D _, Const.I _ -> -1
    | Const.D n1, Const.D n2 -> Float.compare n1 n2
    | Const.I n1, Const.I n2 -> Z.compare n1 n2

    | Const.I _, Const.S _
    | Const.D _, Const.S _
    | Const.S _, Const.I _
    | Const.S _, Const.D _
    | Const.S _, Const.S _ -> failwith "Don't use SemantSwitch compare with string literals"

module Env = Set.Make(struct type t = Const.result let compare = compare end)

let parse (program:Ast.program) =
    let toNumber = function
        | Ast.Int8 num -> Const.I (Z.of_int num)
        | Ast.UInt8 num -> Const.I (Z.of_int num)
        | Ast.Int32 num -> Const.I (Z.of_int32 num)
        | Ast.Int64 num -> Const.I (Z.of_int64 num)
        | Ast.UInt32 num -> Const.I (Z.of_int32 num)
        | Ast.UInt64 num -> Const.I (Z.of_int64 num)
        | Ast.Float64 num -> Const.D num
    in let rec parseStatement stmt switch env default = match stmt with
        | Ast.Case (c, _) -> if not switch then raise (ParserError "Case statement cannot be outside of switch.")
                             else if Env.mem (toNumber c) env then raise (ParserError ("Duplicate case " ^ (Const.toString (toNumber c))))
                             else default, (Env.add (toNumber c) env)
        | Ast.Default _ -> if not switch then raise (ParserError "Default statement cannot be outside of switch.")
                           else if default then raise (ParserError "Duplicate default.")
                           else true, env

        | Ast.If (_, th, Some el) ->
            let d1, env = parseStatement th switch env default in
            let d2, env =  parseStatement el switch env d1 in d2, env
        | Ast.If (_, th, None) ->
            let denv = parseStatement th switch env default in denv

        | Ast.Compound block ->
            let denv = parseBlock block switch env default in denv

        | Ast.While (_, body, _) ->
            let denv = parseStatement body switch env default in denv

        | Ast.DoWhile (body, _, _) ->
            let denv = parseStatement body switch env default in denv

        | Ast.For (_, _, _, body, _) ->
            let denv = parseStatement body switch env default in denv

        | Ast.Switch (_, _, stmt, _, _) ->
            let _ = parseStatement stmt true (Env.empty) false in default, env

        | _ -> default, env


    and parseBlock block switch env default = match block with
        | [] -> default, env
        | (Ast.S h) :: t -> let d, env = parseStatement h switch env default in
                            parseBlock t switch env d
        | _ :: t -> parseBlock t switch env default

    in let parseToplevel = function
        | Ast.FunDecl (_, _, Some body, _, _) -> let _ = parseBlock body false (Env.empty) false in ()
        | _ -> ()
    in
    match program with
        | Ast.Program toplevel -> List.iter (fun x -> parseToplevel x) toplevel
