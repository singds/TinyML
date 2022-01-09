module TinyML.Eval_Test

open Xunit
open Ast
open Eval
open FSharp.Common

let eval_expr_from_string (program:string) =
    let exp = Parsing.parse_from_string SyntaxError program "example" (1, 1) Parser.program Lexer.tokenize Parser.tokenTagToTokenId
    eval_expr [] exp

let test_eval_expr (program:string) (expected:value) =
    let v = eval_expr_from_string program
    Assert.Equal (expected, v)

type Test_eval_expr () =
    [<Fact>]
    let ``application left associativity`` () =
        test_eval_expr
            "let f=fun x -> fun y -> x + y in f 1 2"
            (VLit (LInt (3)))
    
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
