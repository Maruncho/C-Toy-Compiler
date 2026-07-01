
module L = Lexer

type identifer = string
type size = Int64.t

exception ParserDeclaratorError of string

type declarator = Ident of identifer
                | PointerDeclarator of declarator
                | ArrayDeclarator of declarator * size
                | FunDeclarator of param_info list * declarator
                | Ellipsis

and param_info = Ast.data_type * declarator

type abstract_param = AbstractType of Ast.data_type | AbstractEllipsis
and abstract_declarator = AbstractPointer of abstract_declarator
                         | AbstractArray of abstract_declarator * size
                         | AbstractFunction of abstract_param list * abstract_declarator
                         | AbstractBase

let rec string_abstract_decl d = match d with
    | AbstractPointer p -> "ptr(" ^ (string_abstract_decl p) ^ ")"
    | AbstractArray (a, s) -> "arr(" ^ (string_abstract_decl a) ^ ", " ^ (Int64.to_string s) ^ ")"
    | AbstractFunction (_, s) -> "fun(" ^ (string_abstract_decl s) ^ ")"
    | AbstractBase -> "base"

let process_abstract_declarator tokens base_type isTypeSpecFun type_parser expr_parser =
    let nextToken() = match !tokens with
            | [] -> failwith "Went beyond EOF"
            | (t, _, _) :: _ -> t
    in let nextNextToken() = match !tokens with
            | _ :: (t, _, _) :: _ -> t
            | _ -> failwith "Went beyond EOF"
    in let eatToken() = match !tokens with
            | [] -> failwith "Trying to eat beyond EOF"
            | (h, _, _) :: t -> let () = tokens := t in h
    in let expect expected = let t = eatToken() in if t <> expected then
                             raise (ParserDeclaratorError ("Expected " ^ (L.string_of_token expected) ^ ", but got " ^ (L.string_of_token t)))

    in let isDecl tok = match tok with
        | L.ASTERISK
        | L.LBRACK
        | L.LPAREN -> true
        | _ -> false

    in let rec parseParamList() = match nextToken() with
            | x when isTypeSpecFun x ->
                let typ = AbstractType (type_parser()) in

                if nextToken() = L.COMMA then
                    let _ = eatToken() in
                    typ :: parseParamList()
                else
                    typ :: []

            | L.ELLIPSIS ->
                let _ = eatToken() in
                if nextToken() = L.COMMA then
                    raise (ParserDeclaratorError ("Variadic functions cannot have named parameters after the ellipsis."))
                else
                    AbstractEllipsis :: []

            | t -> raise (ParserDeclaratorError ("Expected parameter, but got " ^ (L.string_of_token t)))

    in let rec parseArrayBracketsAndFunctions prev =
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
            in parseArrayBracketsAndFunctions (AbstractArray (prev, size))

        else if nextToken() = L.LPAREN then
            let _ = eatToken() in
            let r =
                if nextToken() = L.VOID && nextNextToken() = L.RPAREN then
                    let _ = eatToken() in
                    AbstractFunction ([], prev)
                else
                    AbstractFunction (parseParamList(), prev) in
            let _ = expect L.RPAREN
            in parseArrayBracketsAndFunctions r

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
        | L.LPAREN when isTypeSpecFun (nextNextToken()) ->
            parseArrayBracketsAndFunctions AbstractBase
        | L.LBRACK ->
            parseArrayBracketsAndFunctions AbstractBase

        | L.LPAREN ->
            let _ = eatToken() in
            let r = parseAbstractDeclarator() in
            let _ = expect L.RPAREN in
            parseArrayBracketsAndFunctions r
        | _ -> raise (ParserDeclaratorError "Invalid Abstract Declarator")

    in let rec process_abstract_declarator declarator base_type = match declarator with
        | AbstractBase -> base_type
        | AbstractPointer subDecl ->
            let derived_type = Ast.Ptr base_type in
            (process_abstract_declarator subDecl derived_type)
        | AbstractFunction (params, subDecl) -> 
            let derived_type =
                if (Ast.isFunctionType base_type) then raise (ParserDeclaratorError "Functions cannot return other functions") else

                let params, is_variadic = List.fold_left (fun (acc_types, acc_variadic) param -> (
                    match param with
                        | AbstractType t -> 
                            if t = Ast.Void then raise (ParserDeclaratorError "Cannot declare void parameters.") else
                            let t = begin match t with
                                | Ast.FunType _ -> Ast.Ptr t
                                | _ -> t
                            end in (t::acc_types, acc_variadic)
                        | AbstractEllipsis -> (acc_types, true)
                    )) ([], false) params in

                Ast.FunType (params |> List.rev, base_type, is_variadic)
            in
            (process_abstract_declarator subDecl derived_type)
        | AbstractArray (subDecl, size) ->
            if not (Ast.isComplete base_type) then raise (ParserDeclaratorError "Can't declare an array of incomplete type") else
            if (Ast.isFunctionType base_type) then raise (ParserDeclaratorError "Can't declare an array of function type") else
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


let process_declarator ?(in_struct=false) tokens base_type isTypeSpecFun type_parser expr_parser =
    let nextToken() = match !tokens with
            | [] -> failwith "Went beyond EOF"
            | (t, _, _) :: _ -> t
    in let nextNextToken() = match !tokens with
            | _ :: (t, _, _) :: _ -> t
            | _ -> failwith "Went beyond EOF"
    in let eatToken() = match !tokens with
            | [] -> failwith "Trying to eat beyond EOF"
            | (h, _, _) :: t -> let () = tokens := t in h
    in let expect expected = let t = eatToken() in if t <> expected then
                             raise (ParserDeclaratorError ("Expected " ^ (L.string_of_token expected) ^ ", but got " ^ (L.string_of_token t)))


    in let rec parseSimpleDeclarator() = match nextToken() with
        | L.LPAREN -> let _ = eatToken() in
                      let r = parseDeclarator() in
                      let _ = expect L.RPAREN in r
        | L.ID id -> let _ = eatToken() in Ident id

        | _ when not in_struct -> Ident ""
        | _ -> raise (ParserDeclaratorError "Invalid Declarator")

    and parseDirectDeclarator() =
        let simple = parseSimpleDeclarator() in
        match nextToken() with
            | L.LPAREN ->
                let _ = eatToken() in
                let r =
                    if nextToken() = L.VOID && nextNextToken() = L.RPAREN then
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
            | x when isTypeSpecFun x ->
                let typ = type_parser() in

                let decl = parseDeclarator() in

                if nextToken() = L.COMMA then
                    let _ = eatToken() in
                    (typ, decl) :: parseParamList()
                else
                    (typ, decl) :: []

            | L.ELLIPSIS ->
                let _ = eatToken() in
                if nextToken() = L.COMMA then
                    raise (ParserDeclaratorError ("Variadic functions cannot have named parameters after the ellipsis."))
                else
                    (Ast.Void, Ellipsis) :: []

            | t -> raise (ParserDeclaratorError ("Expected parameter, but got " ^ (L.string_of_token t)))

    in let rec process_declarator declarator base_type = match declarator with
        | Ellipsis -> failwith "Ellipsis outside of function"
        | Ident name ->
            (name, base_type, [])
        | PointerDeclarator subDecl ->
            let derived_type = Ast.Ptr base_type in
            (process_declarator subDecl derived_type)
        | ArrayDeclarator (subDecl, size) ->
            if not (Ast.isComplete base_type) then raise (ParserDeclaratorError "Can't declare an array of incomplete type") else
            if (Ast.isFunctionType base_type) then raise (ParserDeclaratorError "Can't declare an array of function type") else
            let derived_type = Ast.Array (base_type, size) in
            (process_declarator subDecl derived_type)
        | FunDeclarator (params, subDecl) ->
            let derived_type, p_names =
                if (Ast.isFunctionType base_type) then raise (ParserDeclaratorError "Functions cannot return other functions") else

                let ellipsis, params = List.partition (fun (_, p_decl) -> p_decl = Ellipsis) params in
                let is_variadic = not (List.is_empty ellipsis) in

                let (p_types, p_names) = List.fold_left (fun (acc_types, acc_names) (param_t, param_decl) -> (
                    let name, typ, _ = process_declarator param_decl param_t in
                    if typ = Ast.Void then raise (ParserDeclaratorError "Cannot declare void parameters.") else
                    let typ = begin match typ with
                        | Ast.FunType _ -> Ast.Ptr typ
                        | _ -> typ
                    end in
                    (typ::acc_types, name::acc_names)
                )) ([],[]) params
                in
                (Ast.FunType (p_types |> List.rev, base_type, is_variadic), p_names |> List.rev)
            in
            let (name, typ, deeper_p_names) = (process_declarator subDecl derived_type) in
            (name, typ, if List.is_empty deeper_p_names then p_names else deeper_p_names)



    in
        let decl = parseDeclarator() in
        process_declarator decl base_type
