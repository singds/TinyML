module TinyML.Eval_Test

open Xunit
open Ast
open Eval
open FSharp.Common
open Utility

let eval_expr_from_string (program:string) =
    let exp = Parsing.parse_from_string SyntaxError program "example" (1, 1) Parser.program Lexer.tokenize Parser.tokenTagToTokenId
    eval_expr [] exp

let test_eval_expr (program:string) (expected:value) =
    let v = eval_expr_from_string program
    Assert.Equal (expected, v)

let test_eval_expr_error (program:string) =
    try
        let _ = eval_expr_from_string program
        assert_fail "exception not raised"
    with _ ->
        ()

type Test_eval_expr () =
    // let
    [<Fact>]
    let ``let simple value`` () =
        test_eval_expr
            "let x = 1 in x"
            (VLit (LInt (1)))

    // application
    [<Fact>]
    let ``application left associativity`` () =
        test_eval_expr
            "let f=fun x -> fun y -> x + y in f 1 2"
            (VLit (LInt (3)))

    // let rec
    [<Fact>]
    let ``let rec sum of the first n numbers`` () =
        test_eval_expr
            "let rec f=fun x -> if x > 0 then x + f (x - 1) else x in f 5"
            (VLit (LInt (15)))

    [<Fact>]
    let ``let rec fibonacci`` () =
        test_eval_expr
            "let rec fib=fun x -> if (x = 0) or (x = 1) then 1 else fib (x - 1) + fib (x - 2) in fib 6"
            (VLit (LInt (13)))

    [<Fact>]
    let ``recursive function with two parameters`` () =
        test_eval_expr
            "let rec f=fun x -> fun y ->
                if y > 0 then
                    if x then y + (f false (y - 1))
                    else (f true (y - 1))
                else 0
             in let f1 = f true
             in f1 5"
            (VLit (LInt (9)))

    // let tuple
    [<Fact>]
    let ``let tuple swap elements`` () =
        test_eval_expr
            "let (a,b)=(1,2) in (b,a)"
            (VTuple [VLit (LInt (2)); VLit (LInt (1))])

    [<Fact>]
    let ``let tuple ignored element`` () =
        test_eval_expr
            "let (_,b)=(1,2) in b"
            (VLit (LInt (2)))

    [<Fact>]
    let ``let tuple symbol _ not available`` () =
        test_eval_expr_error "let (_,b)=(1,2) in _"

    // if then else
    [<Fact>]
    let ``if then else true`` () =
        test_eval_expr
            "if true then 1 else 2"
            (VLit (LInt (1)))

    [<Fact>]
    let ``if then else false`` () =
        test_eval_expr
            "if false then 1 else 2"
            (VLit (LInt (2)))

    // minus operator
    [<Fact>]
    let ``minus operator for integers`` () =
        test_eval_expr "let f = fun x -> -x in f 1" (VLit (LInt (-1)))

    [<Fact>]
    let ``minus operator for floats`` () =
        test_eval_expr "let f = fun x -> -.x in f 1.1" (VLit (LFloat (-1.1)))

    // int to float conversion built-in functions
    [<Fact>]
    let ``int to float conversion`` () =
        test_eval_expr "Int (1.1)" (VLit (LInt (1)))

    [<Fact>]
    let ``float to int conversion`` () =
        test_eval_expr "Float (1)" (VLit (LFloat (1.0)))

    // sequence operator
    [<Fact>]
    let ``sequence operator pair`` () =
        test_eval_expr
            "();1"
            (VLit (LInt (1)))

    [<Fact>]
    let ``sequence operator multiple`` () =
        test_eval_expr
            "();();1"
            (VLit (LInt (1)))

    [<Fact>]
    let ``sequence operator complex expr as last`` () =
        test_eval_expr
            "();();let f=fun x -> x in f 1"
            (VLit (LInt (1)))

    [<Fact>]
    let ``sequence operator 3 complex exprs`` () =
        test_eval_expr
            "let (a,b)=((), 2) in a; (if true then () else ()); let f=fun x -> x in f 1"
            (VLit (LInt (1)))
