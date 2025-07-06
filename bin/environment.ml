
type fun_data = string * Ast.data_type list * Ast.data_type * bool (* name, params, ret_type, is_defined *)

type initial_value = Tentative | Initial of Z.t | NoInitializer

type decl_type = Var of string * Ast.data_type
               | StaticVar of string * Ast.data_type
               | Func of fun_data
               (*| Type (* for now it's just int *) *)

type identifier_attrs = FunAttr of fun_data * bool(*is_global*)
                      | VarAttr of string * initial_value * Ast.data_type * bool(*is_global*)

type data = decl_type * int (* new identifier * scope level *)
type dataGlobal = identifier_attrs

module Env = Map.Make(struct type t = string let compare = String.compare end)

module Set = Set.Make(struct type t = string let compare = String.compare end)
let setEmpty = Set.empty
let setAdd = Set.add
let setMem = Set.mem

type env = data Env.t
let empty : env = Env.empty

type envGlobal = dataGlobal Env.t
let emptyGlobal : envGlobal = Env.empty

type envSemantGoto = string Env.t
let emptySemantGoto : envSemantGoto = Env.empty

let isInScope identifier level (env:env) = match Env.find_opt identifier env with
    | None -> false
    | Some (_, lvl) -> level = lvl

let find_opt = Env.find_opt
let add  = Env.add
let fold = Env.fold

let printSemantGoto = Env.iter (fun k v -> print_string (k ^ " -> " ^ v ^ "\n"))

exception EnvironmentError of string

(*HELL BELOW*)

(*let isGlobal globalEnv id = match Env.find_opt id globalEnv with*)
(*    | Some (VarAttr (_, _, isGlobal)) -> isGlobal*)
(*    | Some (FunAttr (_, isGlobal)) -> isGlobal*)
(*    | None -> failwith ("DEBUG: Couldn't find global definition of " ^ id)*)

let isDefinition = function
    | Tentative | NoInitializer -> false
    | Initial _  -> true

(*let isGlobalOpt globalEnv id = match Env.find_opt id globalEnv with*)
(*    | None -> None*)
(*    | _ -> Some (isGlobal globalEnv id)*)

let tentativeIfEmpty (localEnv:env) globalEnv id typ is_external =
    match find_opt id globalEnv with
        | None -> (add id (StaticVar (id, typ), 0) localEnv, add id (VarAttr (id, Tentative, typ, is_external)) globalEnv)
        | Some (FunAttr _) -> raise (EnvironmentError ("Ambiguous declaration of '"^id^"'. Declared first as a function."))
        | Some (VarAttr (_, initial, was_typ, was_global)) ->
            if is_external <> was_global then raise (EnvironmentError ("Cannot declare '"^id^"' as both extern and static.")) else
            if was_typ <> typ then raise (EnvironmentError ("Type mismatch in multiple declarations of "^id^"."))
            else begin match initial with
                | Tentative | Initial _ -> (localEnv, globalEnv) (*Don't touch anything.*)
                | NoInitializer -> (add id (StaticVar (id, typ), 0) localEnv, (add id (VarAttr (id, Tentative, typ, is_external)) globalEnv))
            end

let resolveMatchingVars globalEnv oldVar newVar id =
    let (_, oldInit, oldType, oldExternal) = oldVar in
    let (newId, newInit, newType, newExternal) = newVar in

    let () = if isDefinition newInit && isDefinition oldInit
        then raise (EnvironmentError ("Ambiguous definition of '"^id^"'.")) in

    (*if the first is a definition and the second is a declaration*)
    let newInit = match oldInit, newInit with
        | (Tentative, NoInitializer) -> oldInit
        | (NoInitializer, Tentative) -> newInit
        | _ -> if isDefinition oldInit then oldInit else newInit

    in let () = if oldExternal <> newExternal
        then raise (EnvironmentError ("Cannot declare '"^id^"' as both extern and static."))
    in let () = if oldType <> newType
        then raise (EnvironmentError ("Type mismatch in multiple declarations of "^id^".")) in

    add id (VarAttr (newId, newInit, newType, newExternal)) globalEnv

let defineGlobalVar localEnv globalEnv lvl id init_expr typ is_external =
    let init = try Initial (Const.parseConstExpr init_expr) with Const.ConstError e -> raise (EnvironmentError e) in
    match find_opt id globalEnv with
        | None -> (add id (StaticVar (id, typ), lvl) localEnv, add id (VarAttr (id, init, typ, is_external)) globalEnv)
        | Some (FunAttr _) -> raise (EnvironmentError ("Ambiguous definition of '"^id^"'. Defined first as a function."))
        | Some (VarAttr (x,y,z,t)) -> (localEnv,
            resolveMatchingVars globalEnv (x,y,z,t) (id, init, typ, is_external) id)

let declareGlobalVar localEnv globalEnv lvl id typ is_external = 
    match find_opt id globalEnv with
        | None -> (add id (StaticVar (id, typ), lvl) localEnv, add id (VarAttr (id, NoInitializer, typ, is_external)) globalEnv)
        | Some (FunAttr _) -> raise (EnvironmentError ("Ambiguous declaration of '"^id^"'. Declared first as a function."))
        | Some (VarAttr (x,y,z,t)) -> (localEnv,
            resolveMatchingVars globalEnv (x,y,z,t) (id, NoInitializer, typ, is_external) id)

let tryAddVariable (localEnv: env) (globalEnv: envGlobal) level storage_opt identifier new_identifier init_opt typ =
    if level <= 0 then (* file scope *)
        match storage_opt, init_opt with
            | (None, None) -> tentativeIfEmpty localEnv globalEnv identifier typ true
            | (None, Some init) -> defineGlobalVar localEnv globalEnv level identifier init typ true

            | (Some Ast.Static, None) -> tentativeIfEmpty localEnv globalEnv identifier typ false
            | (Some Ast.Static, Some init) -> defineGlobalVar localEnv globalEnv level identifier init typ false

            | (Some Ast.Extern, None) -> begin match find_opt identifier globalEnv with
                | Some (VarAttr (_, _, typ, isExtern)) -> declareGlobalVar localEnv globalEnv level identifier typ isExtern
                | _ -> declareGlobalVar localEnv globalEnv level identifier typ true
            end
            | (Some Ast.Extern, Some init) -> defineGlobalVar localEnv globalEnv level identifier init typ true
    else
        match storage_opt, init_opt with
            (* Most of the work is in the parser and the AST *)
            | (None, _) -> 
                if isInScope identifier level localEnv then raise (EnvironmentError (identifier ^ " is already in scope")) else
                (add identifier (Var (new_identifier, typ), level) localEnv), globalEnv
            | (Some Ast.Static, _) ->
                if isInScope identifier level localEnv then raise (EnvironmentError (identifier ^ " is already in scope"))
                else (add identifier (StaticVar (new_identifier, typ), level) localEnv), globalEnv
            | (Some Ast.Extern, Some _) -> raise (EnvironmentError "Cannot initialize extern variable inside a function.")
            | (Some Ast.Extern, None) ->
                begin match find_opt identifier localEnv with
                    | None ->
                        if Env.mem identifier globalEnv then failwith "Mismatch between local and global"
                        else (add identifier (StaticVar (identifier, typ), level) localEnv,
                              add identifier (VarAttr (identifier, NoInitializer, typ, true)) globalEnv)
                    | Some (StaticVar _, _) when Env.mem identifier globalEnv ->
                        let newLocal = (add identifier (StaticVar (identifier, typ), level) localEnv) in
                        begin match find_opt identifier globalEnv with
                            | Some (VarAttr (_, _, _, isExtern)) -> declareGlobalVar newLocal globalEnv level identifier typ isExtern
                            | _ -> failwith "Impossible."
                        end
                    | Some (_, lvl) ->
                        if level = lvl then raise (EnvironmentError (identifier ^ " is already in scope")) else
                        let newLocal = (add identifier (StaticVar (identifier, typ), level) localEnv) in
                        begin match find_opt identifier globalEnv with
                            | Some (VarAttr (_, _, typ, isExtern)) -> declareGlobalVar newLocal globalEnv level identifier typ isExtern
                            | _ -> declareGlobalVar newLocal globalEnv level identifier typ true
                        end
                end

let tryAddFunction (localEnv: env) (globalEnv: envGlobal) level storage identifier param_types ret_type body_opt = 
let thisIsDefined = Option.is_some body_opt in
let compareParams pExp pAct fnName =
    let pExpLength = List.length pExp in
    let pActLength = List.length pAct in
    if pExpLength <> pActLength then raise (EnvironmentError ("Inconsistent declaration of "^fnName^": Expected "^(string_of_int pExpLength)^" arguments, but got "^(string_of_int pActLength)^".")) else

    let rec iter i = function
        | hExp :: tExp, hAct :: tAct ->
            if hExp <> hAct then raise (EnvironmentError ("Inconsistent declaration of "^fnName^", parameter "^(string_of_int i)^": Expected "^(Ast.string_data_type hExp)^", but got "^(Ast.string_data_type hAct)^".")) else
            iter (i+1) (tExp, tAct)
        | [], [] -> ()
        | _ -> failwith "Impossible."
    in iter 0 (pExp, pAct)
in
let addFunction is_external =
    let () = if level > 0 then match find_opt identifier localEnv with
        | None -> ()
        | Some (old, oldLvl) -> begin match old with
            | Var _ | StaticVar _ ->
                if level = oldLvl then raise (EnvironmentError (identifier ^ " is already in scope"))
            | Func _ -> () (*locally nothing to check*)
    end in
    match find_opt identifier globalEnv with
        | None -> let fn = (identifier, param_types, ret_type, thisIsDefined) in
                  (add identifier (Func fn, level) localEnv, add identifier (FunAttr (fn, is_external)) globalEnv)
        | Some (VarAttr _) -> raise (EnvironmentError ("Identifier "^identifier^" is already a global variable"))
        | Some (FunAttr ((_, oldParamTypes, oldRetType, hasBody), wasExternal)) ->
            if thisIsDefined && hasBody then
                raise (EnvironmentError ("Re-definition of "^identifier^" is not allowed")) else
            let () = compareParams oldParamTypes param_types identifier in
            if oldRetType <> ret_type then
                raise (EnvironmentError ("Inconsistent declaration of "^identifier^", Expected return type of "^(Ast.string_data_type oldRetType)^", but got "^(Ast.string_data_type ret_type)^".")) else
            if is_external <> wasExternal then
                raise (EnvironmentError ("Cannot declare function static and extern: "^identifier)) else
            let defined = hasBody || thisIsDefined in
            let fn = (identifier, param_types, ret_type, defined) in
            (add identifier (Func fn, level) localEnv, add identifier (FunAttr (fn, is_external)) globalEnv)
    in

    if level <= 0 then (* file scope *)
        match storage, body_opt with
            | (Ast.Extern, _) -> begin match find_opt identifier globalEnv with
                | Some (FunAttr (_, isExtern)) -> addFunction isExtern
                | _ -> addFunction true
            end
            | (Ast.Static, _) -> addFunction false
    else
        match storage, body_opt with
            | (Ast.Extern, None) -> begin match find_opt identifier globalEnv with
                | Some (FunAttr (_, isExtern)) -> addFunction isExtern
                | _ -> addFunction true
            end
            | (Ast.Extern, Some _) -> raise (EnvironmentError "Cannot define a function inside another function.")
            | (Ast.Static, _) -> raise (EnvironmentError "Cannot declare a static function inside another function.")

(*let globalEnvString globalEnv =*)
(*    let initialStr = function*)
(*        | Initial x -> "Initial " ^ (Ast.string_literal x)*)
(*        | Tentative -> "Tentative"*)
(*        | SecondPass _ -> "SecondPass"*)
(*        | NoInitializer -> "NoInitializer" in*)
(*    let globalStr g = if g then "extern" else "static" in*)
(*    let definedStr g = if g then "definition" else "declaration" in*)
(*    Env.iter (fun key value -> (match value with*)
(*    | VarAttr (name, initial, _, is_global) ->*)
(*            print_string (key ^ " -> Var("^name^", "^(initialStr initial)^", "^(globalStr is_global)^")\n")*)
(*    | FunAttr ((name, params, is_defined), is_global) ->*)
(*            print_string (key ^ " -> Fun("^name^", "^(string_of_int params)^", "^(globalStr is_global)^", "^(definedStr is_defined)^")\n")*)
(*    )) globalEnv*)
