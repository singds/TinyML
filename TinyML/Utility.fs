module TinyML.Utility

open Xunit

let assert_fail msg =
    Assert.True (false, msg)
