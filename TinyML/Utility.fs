module TinyML.Utility

open Xunit
open Ast

let assert_fail msg =
    Assert.True (false, msg)

let type_error fmt = throw_formatted TypeError fmt
