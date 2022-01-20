module TinyML.TypeChecking_Test

open Xunit
open Ast
open TypeChecking
open FSharp.Common
open Utility

let typecheck_expr_from_string (program:string) =
    let exp = Parsing.parse_from_string SyntaxError program "example" (1, 1) Parser.program Lexer.tokenize Parser.tokenTagToTokenId
    typecheck_expr [] exp

let test_typecheck_expr (program:string) (expected:ty) =
    let t = typecheck_expr_from_string program
    Assert.Equal (expected, t)

let test_typecheck_expr_error (program:string) =
    try
        let _ = typecheck_expr_from_string program
        assert_fail "exception not raised"
    with _ ->
        ()


type Test_typechecking_expr () =
    [<Fact>]
    let ``empty list with no type`` () =
        // empty lists must be annotated for the typechecker
        test_typecheck_expr_error "[]"

    [<Fact>]
    let ``empty list with type`` () =
        test_typecheck_expr "[int]" (TyList TyInt)

    [<Fact>]
    let ``list chain with compatible types`` () =
        test_typecheck_expr "1::[int]" (TyList TyInt)

    [<Fact>]
    let ``list chain with incompatible types`` () =
        test_typecheck_expr_error "1.2::[int]"

    [<Fact>]
    let ``list chain two elements`` () =
        test_typecheck_expr "1::2::[int]" (TyList TyInt)

    [<Fact>]
    let ``list is emtpy`` () =
        test_typecheck_expr "IsEmpty [int]" TyBool

    [<Fact>]
    let ``list match with correct types in the two breanches`` () =
        test_typecheck_expr
            "match [int] with x::y -> 1.1 | [] -> 2.2"
            TyFloat

    [<Fact>]
    let ``list match with wrong types in the two breanches`` () =
        test_typecheck_expr_error "match [int] with x::y -> 1.1 | [] -> 2"

    [<Fact>]
    let ``list match with something that is not a list`` () =
        test_typecheck_expr_error "match 1 with x::y -> 1.1 | [] -> 2.2"