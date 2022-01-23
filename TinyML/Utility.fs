module TinyML.Utility

open Xunit
open Ast

let assert_fail msg =
    Assert.True (false, msg)

let type_error fmt = throw_formatted TypeError fmt

(*
l = a list of bindings (pairs) to be added to the environment
env = the environ.
Bindings inside <l> are prepended to <env> only if their identifier is different than
the ignore identifier, that is "_".
*)
let rec prepend_if_not_ignore l env =
    match l with
    | [] -> env
    | (id, e)::tail ->
        let env1 = prepend_if_not_ignore tail env
        if id <> "_" then (id, e)::env1 else env1

let list_all_equals l =
    let same = Set.ofList l
    if same.Count <> 1 then false else true
