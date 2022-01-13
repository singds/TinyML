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
        test_ast "(1,2)" (Tuple [(Lit (LInt (1))); (Lit (LInt (2)))])

