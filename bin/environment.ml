
(*type decl_type = Var of string*)
(*               | Type (* for now it's just int *) *)

type data = string * int (* new identifier * scope level *)

module Env = Map.Make(struct type t = string let compare = String.compare end)

type env = data Env.t

type envSemantGoto = string Env.t

let empty : env = Env.empty

let emptySemantGoto : envSemantGoto = Env.empty

let isInScope identifier level (env:env) = match Env.find_opt identifier env with
    | None -> false
    | Some (_, lvl) -> level = lvl

let find_opt = Env.find_opt

let add  = Env.add

let printSemantGoto = Env.iter (fun k v -> print_string (k ^ " -> " ^ v ^ "\n"))
