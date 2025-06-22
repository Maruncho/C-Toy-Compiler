
type fun_data = string * int * bool (* name, params, is_defined *)

type initial_value = Tentative | Initial of Int32.t | NoInitializer
                   | SecondPass of Ast.expr (*uses static vars, which must resolve in the first pass before they can be used*)

type decl_type = Var of string
               | StaticVar of string
               | Func of fun_data
               (*| Type (* for now it's just int *) *)

type identifier_attrs = FunAttr of fun_data * bool(*is_global*)
                      | VarAttr of string * initial_value * bool(*is_global*)

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

let parseConstExpr expr (*globalEnv_opt*) =
    let hasStaticVar = ref false in
    (*seen: For circular dependencies. The standard doesn't allow this, but consider it an extension. I want to suffer.*)
    let rec parse expr seen =
        match expr with
            | Ast.Int32 num -> num
            (* The book tests don't like this.*)
            (*| Ast.Var (id, Ast.StaticVariable) -> begin match globalEnv_opt with*)
            (*    | None -> let () = hasStaticVar := true in 0l*)
            (*    | Some globalEnv -> begin match find_opt id globalEnv with*)
            (*        | None -> raise (EnvironmentError ("Couldn't find static variable " ^ id))*)
            (*        | Some (FunAttr _) -> raise (EnvironmentError (id ^ " is not a static variable, but a function."))*)
            (*        | Some (VarAttr (_,init,_)) -> begin match init with*)
            (*            | NoInitializer -> raise (EnvironmentError (id ^ " is a extern uninitialized variable. Value must be know at compile time in the translation unit."))*)
            (*            | Tentative -> 0l*)
            (*            | Initial i -> i*)
            (*            | SecondPass expr ->*)
            (*                if List.mem id seen then*)
            (*                    raise (EnvironmentError ("Circular dependency in static variable initializers: " ^ id ^ " -> " ^ (String.concat " -> " seen)))*)
            (*                else parse expr (id::seen)*)
            (*        end*)
            (*    end*)
            (*end*)
            | Ast.Var _ -> raise (EnvironmentError "Cannot use variables in constant expressions")
            | Ast.Unary (Ast.Rvalue, src) -> parse src seen
            | Ast.Unary (op, expr) ->
                let src = parse expr seen in
                begin match parseUnaryOp op with
                    | Tac.Complement -> Int32.lognot src
                    | Tac.Negate -> Int32.neg src
                    | Tac.Not -> if Int32.compare src 0l = 0 then 0l else 1l
                    | _ -> raise (EnvironmentError "Increment/Decrement is not a constant expression operator")
                end

            | Ast.BinarySp (Ast.LogAnd, (left, _), right) ->
                let left = parse left seen in
                if Int32.compare left 0l = 0 then 0l else parse right seen

            | Ast.BinarySp (Ast.LogOr, (left, _), right) ->
                let left = parse left seen in
                if Int32.compare left 0l = 0 then parse right seen else 1l

            | Ast.BinarySp (Ast.Comma, _, _) -> failwith "TODO: Add Comma"

            | Ast.Binary (op, left, right) ->
                let left = parse left seen in
                let right = parse right seen in
                let () = if (Int32.compare right 0l) < 0 || (Int32.compare right 31l) > 0 then
                    Log.warning "shift count >= width of type" in
                begin match parseBinaryOp op with
                    | Tac.Add -> Int32.add left right
                    | Tac.Subtract -> Int32.sub left right
                    | Tac.Divide -> Int32.div left right
                    | Tac.Multiply -> Int32.mul left right
                    | Tac.Remainder -> Int32.rem left right
                    | Tac.And -> Int32.logand left right
                    | Tac.Or -> Int32.logor left right
                    | Tac.Xor -> Int32.logxor left right
                    | Tac.LShift ->
                        let () = if (Int32.compare right 0l) < 0 || (Int32.compare right 31l) > 0 then
                            Log.warning "shift count >= width of type" in
                        Int32.shift_left left (Int32.to_int right)
                    | Tac.RShift ->
                        let () = if (Int32.compare right 0l) < 0 || (Int32.compare right 31l) > 0 then
                            Log.warning "shift count >= width of type" in
                        Int32.shift_right left (Int32.to_int right)
                    | Tac.Equal -> if Int32.equal left right then 1l else 0l
                    | Tac.NotEqual -> if Int32.equal left right then 0l else 1l
                    | Tac.LessThan -> if (Int32.compare left right) < 0 then 1l else 0l
                    | Tac.LessOrEqual -> if (Int32.compare left right) <= 0 then 1l else 0l
                    | Tac.GreaterThan -> if (Int32.compare left right) > 0 then 1l else 0l
                    | Tac.GreaterOrEqual -> if (Int32.compare left right) >= 0 then 1l else 0l
                end

            | Ast.Assignment _
            | Ast.BinaryAssign _ ->
                raise (EnvironmentError "Cannot use assignment operator in constant expressions")

            | Ast.Ternary ((cond, _), th, el) -> 
                let cond = parse cond seen in
                if Int32.compare cond 0l <> 0 then parse th seen else parse el seen

            | Ast.Call (_, _) ->
                raise (EnvironmentError "Cannot call functions in constant expresisons")

    in let result = parse expr [] in
    if !hasStaticVar then None else Some result



(*let isGlobal globalEnv id = match Env.find_opt id globalEnv with*)
(*    | Some (VarAttr (_, _, isGlobal)) -> isGlobal*)
(*    | Some (FunAttr (_, isGlobal)) -> isGlobal*)
(*    | None -> failwith ("DEBUG: Couldn't find global definition of " ^ id)*)

let isDefinition = function
    | Tentative | NoInitializer -> false
    | Initial _ | SecondPass _ -> true

(*let isGlobalOpt globalEnv id = match Env.find_opt id globalEnv with*)
(*    | None -> None*)
(*    | _ -> Some (isGlobal globalEnv id)*)

let tentativeIfEmpty (localEnv:env) globalEnv id is_external =
    match find_opt id globalEnv with
        | None -> (add id (StaticVar id, 0) localEnv, add id (VarAttr (id, Tentative, is_external)) globalEnv)
        | Some (FunAttr _) -> raise (EnvironmentError ("Ambiguous declaration of '"^id^"'. Declared first as a function."))
        | Some (VarAttr (_, initial, was_global)) ->
            if is_external <> was_global then raise (EnvironmentError ("Cannot declare '"^id^"' as both extern and static."))
            else begin match initial with
                | Tentative | Initial _ | SecondPass _ -> (localEnv, globalEnv) (*Don't touch anything.*)
                | NoInitializer -> (add id (StaticVar id, 0) localEnv, (add id (VarAttr (id, Tentative, is_external)) globalEnv))
            end

let resolveMatchingVars globalEnv oldVar newVar id =
    let (_, oldInit, oldExternal) = oldVar in
    let (newId, newInit, newExternal) = newVar in

    let () = if isDefinition newInit && isDefinition oldInit
        then raise (EnvironmentError ("Ambiguous definition of '"^id^"'.")) in

    (*if the first is a definition and the second is a declaration*)
    let newInit = match oldInit, newInit with
        | (Tentative, NoInitializer) -> oldInit
        | (NoInitializer, Tentative) -> newInit
        | _ -> if isDefinition oldInit then oldInit else newInit

    in let () = if oldExternal <> newExternal
        then raise (EnvironmentError ("Cannot declare '"^id^"' as both extern and static.")) in

    add id (VarAttr (newId,newInit,newExternal)) globalEnv

let defineGlobalVar localEnv globalEnv lvl id init_expr is_external =
    let init = match parseConstExpr init_expr (*None*) with None -> SecondPass init_expr | Some s -> Initial s in
    match find_opt id globalEnv with
        | None -> (add id (StaticVar id, lvl) localEnv, add id (VarAttr (id, init, is_external)) globalEnv)
        | Some (FunAttr _) -> raise (EnvironmentError ("Ambiguous definition of '"^id^"'. Defined first as a function."))
        | Some (VarAttr (x,y,z)) -> (localEnv,
            resolveMatchingVars globalEnv (x,y,z) (id, init, is_external) id)

let declareGlobalVar localEnv globalEnv lvl id is_external = 
    match find_opt id globalEnv with
        | None -> (add id (StaticVar id, lvl) localEnv, add id (VarAttr (id, NoInitializer, is_external)) globalEnv)
        | Some (FunAttr _) -> raise (EnvironmentError ("Ambiguous declaration of '"^id^"'. Declared first as a function."))
        | Some (VarAttr (x,y,z)) -> (localEnv,
            resolveMatchingVars globalEnv (x,y,z) (id, NoInitializer, is_external) id)

let tryAddVariable (localEnv: env) (globalEnv: envGlobal) level storage_opt identifier new_identifier init_opt =
    if level <= 0 then (* file scope *)
        match storage_opt, init_opt with
            | (None, None) -> tentativeIfEmpty localEnv globalEnv identifier true
            | (None, Some init) -> defineGlobalVar localEnv globalEnv level identifier init true

            | (Some Ast.Static, None) -> tentativeIfEmpty localEnv globalEnv identifier false
            | (Some Ast.Static, Some init) -> defineGlobalVar localEnv globalEnv level identifier init false

            | (Some Ast.Extern, None) -> begin match find_opt identifier globalEnv with
                | Some (VarAttr (_, _, isExtern)) -> declareGlobalVar localEnv globalEnv level identifier isExtern
                | _ -> declareGlobalVar localEnv globalEnv level identifier true
            end
            | (Some Ast.Extern, Some init) -> defineGlobalVar localEnv globalEnv level identifier init true
    else
        match storage_opt, init_opt with
            (* Most of the work is in the parser and the AST *)
            | (None, _) -> 
                if isInScope identifier level localEnv then raise (EnvironmentError (identifier ^ " is already in scope")) else
                (add identifier (Var new_identifier, level) localEnv), globalEnv
            | (Some Ast.Static, _) ->
                if isInScope identifier level localEnv then raise (EnvironmentError (identifier ^ " is already in scope"))
                else (add identifier (StaticVar new_identifier, level) localEnv), globalEnv
            | (Some Ast.Extern, Some _) -> raise (EnvironmentError "Cannot initialize extern variable inside a function.")
            | (Some Ast.Extern, None) ->
                begin match find_opt identifier localEnv with
                    | None ->
                        if Env.mem identifier globalEnv then failwith "Mismatch between local and global"
                        else (add identifier (StaticVar identifier, level) localEnv,
                              add identifier (VarAttr (identifier, NoInitializer, true)) globalEnv)
                    | Some (StaticVar _, _) when Env.mem identifier globalEnv ->
                        let newLocal = (add identifier (StaticVar identifier, level) localEnv) in
                        begin match find_opt identifier globalEnv with
                            | Some (VarAttr (_, _, isExtern)) -> declareGlobalVar newLocal globalEnv level identifier isExtern
                            | _ -> failwith "Impossible."
                        end
                    | Some (_, lvl) ->
                        if level = lvl then raise (EnvironmentError (identifier ^ " is already in scope")) else
                        let newLocal = (add identifier (StaticVar identifier, level) localEnv) in
                        begin match find_opt identifier globalEnv with
                            | Some (VarAttr (_, _, isExtern)) -> declareGlobalVar newLocal globalEnv level identifier isExtern
                            | _ -> declareGlobalVar newLocal globalEnv level identifier true
                        end
                end

let tryAddFunction (localEnv: env) (globalEnv: envGlobal) level storage identifier paramCount body_opt = 
let thisIsDefined = Option.is_some body_opt in
let addFunction is_external =
    let () = if level > 0 then match find_opt identifier localEnv with
        | None -> ()
        | Some (old, oldLvl) -> begin match old with
            | Var _ | StaticVar _ ->
                if level = oldLvl then raise (EnvironmentError (identifier ^ " is already in scope"))
            | Func _ -> () (*locally nothing to check*)
    end in
    match find_opt identifier globalEnv with
        | None -> let fn = (identifier, paramCount, thisIsDefined) in
                  (add identifier (Func fn, level) localEnv, add identifier (FunAttr (fn, is_external)) globalEnv)
        | Some (VarAttr _) -> raise (EnvironmentError ("Identifier "^identifier^" is already a global variable"))
        | Some (FunAttr ((_, oldParamsCount, hasBody), wasExternal)) ->
            if thisIsDefined && hasBody then
                raise (EnvironmentError ("Re-definition of "^identifier^" is not allowed")) else
            if oldParamsCount <> paramCount then
                raise (EnvironmentError ("Inconsistent declarations of "^identifier)) else
            if is_external <> wasExternal then
                raise (EnvironmentError ("Cannot declare function static and extern: "^identifier)) else
            let defined = hasBody || thisIsDefined in
            let fn = (identifier, paramCount, defined) in
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

let globalEnvString globalEnv =
    let initialStr = function
        | Initial x -> "Initial " ^ (Int32.to_string x)
        | Tentative -> "Tentative"
        | SecondPass _ -> "SecondPass"
        | NoInitializer -> "NoInitializer" in
    let globalStr g = if g then "extern" else "static" in
    let definedStr g = if g then "definition" else "declaration" in
    Env.iter (fun key value -> (match value with
    | VarAttr (name, initial, is_global) ->
            print_string (key ^ " -> Var("^name^", "^(initialStr initial)^", "^(globalStr is_global)^")\n")
    | FunAttr ((name, params, is_defined), is_global) ->
            print_string (key ^ " -> Fun("^name^", "^(string_of_int params)^", "^(globalStr is_global)^", "^(definedStr is_defined)^")\n")
    )) globalEnv
