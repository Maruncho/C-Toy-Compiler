
module L = Lexer

type identifer = string
type size = Int64.t

exception ParserDeclaratorError of string

type declarator = Ident of identifer
                | PointerDeclarator of declarator
                | ArrayDeclarator of declarator * size
                | FunDeclarator of param_info list * declarator

and param_info = Ast.data_type * declarator

type abstract_declarator = AbstractPointer of abstract_declarator
                         | AbstractArray of abstract_declarator * size
                         | AbstractBase

let rec string_abstract_decl d = match d with
    | AbstractPointer p -> "ptr(" ^ (string_abstract_decl p) ^ ")"
    | AbstractArray (a, s) -> "arr(" ^ (string_abstract_decl a) ^ ", " ^ (Int64.to_string s) ^ ")"
    | AbstractBase -> "base"

let process_abstract_declarator tokens base_type expr_parser =
    let nextToken() = match !tokens with
            | [] -> failwith "Went beyond EOF"
            | t :: _ -> t
    in let eatToken() = match !tokens with
            | [] -> failwith "Trying to eat beyond EOF"
            | h :: t -> let () = tokens := t in h
    in let expect expected = let t = eatToken() in if t <> expected then
                             raise (ParserDeclaratorError ("Expected " ^ (L.string_of_token expected) ^ ", but got " ^ (L.string_of_token t)))

    in let isDecl tok = match tok with
        | L.ASTERISK
        | L.LBRACK
        | L.LPAREN -> true
        | _ -> false

    in let rec parseArrayBrackets prev =
        if nextToken() = L.LBRACK then
            let _ = eatToken() in
            let const = try Const.parseConstExpr (expr_parser())
                        with Const.ConstError msg -> raise (ParserDeclaratorError ("Error while parsing array declaration:\n\t" ^ msg))
            in let size = match const with
                | Const.I n ->
                    if Z.leq n Z.zero then raise (ParserDeclaratorError "Array size must be >= 0")
                    else Z.to_int64_unsigned n
                | _ -> raise (ParserDeclaratorError "Array size must be an integer.")
            in let () = expect L.RBRACK
            in parseArrayBrackets (AbstractArray (prev, size))
        else
            prev

    in let rec parseAbstractDeclarator() = match nextToken() with
        | L.ASTERISK -> let _ = eatToken() in
                        if isDecl (nextToken()) then
                            AbstractPointer (parseAbstractDeclarator())
                        else
                            AbstractPointer AbstractBase
        | _ -> parseDirectAbstractDeclarator()

    and parseDirectAbstractDeclarator() = match nextToken() with
        | L.LPAREN -> let _ = eatToken() in
                      let r = parseAbstractDeclarator() in
                      let _ = expect L.RPAREN in
                      parseArrayBrackets r
        | L.LBRACK -> parseArrayBrackets AbstractBase
        | _ -> raise (ParserDeclaratorError "Invalid Abstract Declarator")

    in let rec process_abstract_declarator declarator base_type = match declarator with
        | AbstractBase -> base_type
        | AbstractPointer subDecl ->
            let derived_type = Ast.Ptr base_type in
            (process_abstract_declarator subDecl derived_type)
        | AbstractArray (subDecl, size) ->
            let derived_type = Ast.Array (base_type, size) in
            (process_abstract_declarator subDecl derived_type)

    in
        let decl = if isDecl (nextToken()) then
            parseAbstractDeclarator()
        else
            AbstractBase
        in
        (*let () = print_string ((string_abstract_decl decl) ^ "\n") in*)
        process_abstract_declarator decl base_type


let process_declarator tokens base_type type_parser expr_parser =
    let nextToken() = match !tokens with
            | [] -> failwith "Went beyond EOF"
            | t :: _ -> t
    in let eatToken() = match !tokens with
            | [] -> failwith "Trying to eat beyond EOF"
            | h :: t -> let () = tokens := t in h
    in let expect expected = let t = eatToken() in if t <> expected then
                             raise (ParserDeclaratorError ("Expected " ^ (L.string_of_token expected) ^ ", but got " ^ (L.string_of_token t)))

    in let isTypeSpec = function
        | L.DOUBLE
        | L.INT
        | L.UNSIGNED
        | L.SIGNED
        | L.LONG -> true
        | _ -> false

    in let rec parseSimpleDeclarator() = match nextToken() with
        | L.LPAREN -> let _ = eatToken() in
                      let r = parseDeclarator() in
                      let _ = expect L.RPAREN in r
        | L.ID id -> let _ = eatToken() in Ident id

        | _ -> raise (ParserDeclaratorError "Invalid Declarator")

    and parseDirectDeclarator() =
        let simple = parseSimpleDeclarator() in
        match nextToken() with
            | L.LPAREN ->
                let _ = eatToken() in
                let r =
                    if nextToken() = L.VOID then
                        let _ = eatToken() in
                        FunDeclarator ([], simple)
                    else
                        FunDeclarator (parseParamList(), simple) in
                let _ = expect L.RPAREN in r

            | L.LBRACK ->
                let rec iter prev =
                    if nextToken() = L.LBRACK then
                        let _ = eatToken() in
                        let const = try Const.parseConstExpr (expr_parser())
                                    with Const.ConstError msg -> raise (ParserDeclaratorError ("Error while parsing array declaration:\n\t" ^ msg))
                        in let size = match const with
                            | Const.I n ->
                                if Z.leq n Z.zero then raise (ParserDeclaratorError "Array size must be >= 0")
                                else Z.to_int64_unsigned n
                            | _ -> raise (ParserDeclaratorError "Array size must be an integer.")
                        in let () = expect L.RBRACK
                        in iter (ArrayDeclarator (prev, size))
                    else
                        prev
                in iter simple

            | _ -> simple

    and parseDeclarator() = match nextToken() with
        | L.ASTERISK -> let _ = eatToken() in PointerDeclarator (parseDeclarator())
        | _ -> parseDirectDeclarator()

    and parseParamList() = match nextToken() with
            | x when isTypeSpec x ->
                let typ = type_parser() in
                let decl = parseDeclarator() in

                if nextToken() = L.COMMA then
                    let _ = eatToken() in
                    (typ, decl) :: parseParamList()
                else
                    (typ, decl) :: []

            | t -> raise (ParserDeclaratorError ("Expected parameter, but got " ^ (L.string_of_token t)))

    in let rec process_declarator declarator base_type = match declarator with
        | Ident name -> (name, base_type, [])
        | PointerDeclarator subDecl ->
            let derived_type = Ast.Ptr base_type in
            (process_declarator subDecl derived_type)
        | ArrayDeclarator (subDecl, size) ->
            let derived_type = Ast.Array (base_type, size) in
            (process_declarator subDecl derived_type)
        | FunDeclarator (params, subDecl) -> begin match subDecl with
            | Ident name ->
                let (p_types, p_names) = List.fold_left (fun (acc_types, acc_names) (param_t, param_decl) -> (
                    let name, typ, _ = process_declarator param_decl param_t in
                    let () = begin match typ with
                        | Ast.FunType _ -> raise (ParserDeclaratorError "Function pointers in parameters aren't supported")
                        | _ -> ()
                    end in
                    (typ::acc_types, name::acc_names)
                )) ([],[]) params
                in
                let derived_type = Ast.FunType (p_types |> List.rev, base_type) in
                (name, derived_type, p_names |> List.rev)
            | _ -> raise (ParserDeclaratorError "Can't apply additional type derivations to a function type")
        end



    in
        let decl = parseDeclarator() in
        process_declarator decl base_type
