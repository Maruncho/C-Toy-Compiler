
(*type decl_type = Var of string*)
(*               | Type (* for now it's just int *) *)

type data = string * int (* new identifier * scope level *)

module Env = Map.Make(struct type t = string let compare = String.compare end)

type env = data Env.t

let empty : env = Env.empty

let isInScope identifier level (env:env) = match Env.find_opt identifier env with
    | None -> false
    | Some (_, lvl) -> level = lvl

let find_opt : (string -> env -> data option)  = Env.find_opt

let add : (string -> data -> env -> env) = Env.add
