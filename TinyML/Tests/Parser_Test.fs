module TinyML.Parser_Test

open Xunit
open Ast
open FSharp.Common
open Utility

let get_ast_from_string (program:string) =
    Parsing.parse_from_string SyntaxError program "example" (1, 1) Parser.program Lexer.tokenize Parser.tokenTagToTokenId

let test_ast (program:string) (expected:expr) =
    let ast = get_ast_from_string program
    Assert.Equal (expected, ast)

type Test_parser () =
    [<Fact>]
    let ``single value between parentheses not tuple`` () =
        test_ast "(1)" (Lit (LInt (1)))

    [<Fact>]
    let ``tuple with two expr.`` () =
        test_ast "(1,2)" (Tuple [Lit (LInt 1); Lit (LInt 2)])

    [<Fact>]
    let ``float plus`` () =
        test_ast "1.1 +. 2.2"
            (App (App (Var "+.", Lit (LFloat 1.1)), Lit (LFloat 2.2)))

    [<Fact>]
    let ``float minus`` () =
        test_ast "1.1 -. 2.2"
            (App (App (Var "-.", Lit (LFloat 1.1)), Lit (LFloat 2.2)))

    [<Fact>]
    let ``float star`` () =
        test_ast "1.1 *. 2.2"
            (App (App (Var "*.", Lit (LFloat 1.1)), Lit (LFloat 2.2)))

    [<Fact>]
    let ``float slash`` () =
        test_ast "1.1 /. 2.2"
            (App (App (Var "/.", Lit (LFloat 1.1)), Lit (LFloat 2.2)))

    [<Fact>]
    let ``float percent`` () =
        test_ast "1.1 %. 2.2"
            (App (App (Var "%.", Lit (LFloat 1.1)), Lit (LFloat 2.2)))

    [<Fact>]
    let ``int to float built in function`` () =
        test_ast "Float (1)"
            (App (Var "to_float", Lit (LInt 1)))

    [<Fact>]
    let ``float to int built in function`` () =
        test_ast "Int (1.1)"
            (App (Var "to_int", Lit (LFloat 1.1)))

    [<Fact>]
    let ``function applied to int builtin converion`` () =
        test_ast "f Int (1.1)"
            (App (Var "f", App (Var "to_int", Lit (LFloat 1.1))))

    [<Fact>]
    let ``function applied to float builtin converion`` () =
        test_ast "f Float (1.1)"
            (App (Var "f", App (Var "to_float", Lit (LFloat 1.1))))

