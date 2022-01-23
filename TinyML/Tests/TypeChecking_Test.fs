module TinyML.TypeChecking_Test

open Xunit
open Ast
open TypeChecking
open FSharp.Common
open Utility

let typecheck_expr_from_string (program:string) =
    new_ty_id <- 1
    let exp = Parsing.parse_from_string SyntaxError program "example" (1, 1) Parser.program Lexer.tokenize Parser.tokenTagToTokenId
    typecheck_expr_expanded [] [] exp

let test_typecheck_expr (program:string) (expected:ty) =
    let t = typecheck_expr_from_string program
    Assert.Equal (expected, t)

let test_typecheck_expr_error (program:string) =
    let mutable ok = false
    try
        let _ = typecheck_expr_from_string program
        ok <- false
    with _ ->
        ok <- true
    if ok = false then assert_fail "exception not raised" else ()



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


// TYPES
type Test_typechecking_expr_type () =
    [<Fact>]
    let ``type: check constructor binded with simple type`` () =
        test_typecheck_expr "type color = Yellow of unit in Yellow ()"
            (TyUnion ("color"))

    [<Fact>]
    let ``type: check constructor binded with arrow type`` () =
        test_typecheck_expr "type color = Rgb of int in Rgb"
            (TyArrow (TyInt, (TyUnion "color")))

    [<Fact>]
    let ``type: check constructor binded with arrow type, two parameters`` () =
        test_typecheck_expr "type color = Rgb of int * int in Rgb"
            (TyArrow (TyTuple [TyInt; TyInt], TyUnion "color"))

    [<Fact>]
    let ``type: check constructor call with parameters`` () =
        test_typecheck_expr "type color = Rgb of int * int in Rgb ((1,2))"
            (TyUnion ("color"))

    [<Fact>]
    let ``type match with one simple constructor`` () =
        test_typecheck_expr "type color = Rgb of unit in matchf Rgb () with Rgb (x) -> 1"
            TyInt

    [<Fact>]
    let ``type match with one constructor, one parameter`` () =
        test_typecheck_expr "type color = Rgb of float in matchf (Rgb (1.1)) with Rgb (x) -> x"
            TyFloat

    [<Fact>]
    let ``type match with one constructor, two parameter`` () =
        test_typecheck_expr "type color = Rgb of int * float in matchf Rgb ((1, 2.2)) with Rgb (x) -> x"
            (TyTuple [TyInt; TyFloat])

    [<Fact>]
    let ``type match with two constructors in order`` () =
        test_typecheck_expr "type color = A of unit | B of unit in matchf A() with A (x) -> 1 | B (x) -> 2"
            TyInt

    [<Fact>]
    let ``type match with two constructors not in order`` () =
        test_typecheck_expr "type color = A of unit | B of unit in matchf A() with B (x) -> 2 | A (x) -> 1"
            TyInt

    [<Fact>]
    let ``(error) type match with two constructors incomplete match`` () =
        test_typecheck_expr_error "type color = A of unit | B of unit in matchf A () with A (x) -> 1"

    [<Fact>]
    let ``(error) type match with two constructors incompatible returns`` () =
        test_typecheck_expr_error "type color = A of unit | B of unit in matchf A () with A (x) -> 1 | B (x) -> 2.2"

    [<Fact>]
    let ``type constructor invocation with single parameter`` () =
        test_typecheck_expr "type color = A of int in A 1"
            (TyUnion "color")

    [<Fact>]
    let ``(error) type constructor invocation with single parameter of wring type`` () =
        test_typecheck_expr_error "type color = A of int in A 1.2"
    
