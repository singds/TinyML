module TinyML.Utility

open Xunit
open Ast

let assert_fail msg =
    Assert.True (false, msg)

let type_error fmt = throw_formatted TypeError fmt

(*
l    = a list of bindings (pairs) to be added to the environment
env  = the environ.
Bindings inside <l> are prepended to <env> only if their identifier is different than
the ignore identifier, that is "_".
*)
let rec prepend_if_not_ignore l env =
    match l with
    | [] -> env
    | (id, e)::tail ->
        let env1 = prepend_if_not_ignore tail env
        if id <> "_" then (id, e)::env1 else env1

(* Check if the elements of the list are all equals.
*)
let list_all_equals l =
    let same = Set.ofList l
    if same.Count <> 1 then false else true

(* Get all the constructors in the environment as a plain list.
Each constructor is prepended with the name of the type it belongs to.
*)
let get_constr_list (tydefEnv: tyDef env) =
    List.fold (fun state (tyName, tyConstrs) ->
        let tyConstrs = List.map (fun constr -> (tyName, constr)) tyConstrs
        state @ tyConstrs
    ) [] tydefEnv

(* Get the first constructor in the type-def-env. with the given name.
uEnv   = union type environment
cn     = constructor name
*)
let get_constr_by_name (tydefEnv: tyDef env) (constrId: string) =
    let allConstr = get_constr_list tydefEnv
    let constr = List.find (function (tname, Constr (id, _)) -> id = constrId) allConstr
    constr