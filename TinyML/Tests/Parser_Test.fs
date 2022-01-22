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
            (BinOp ((Lit (LFloat 1.1)), "+.", Lit (LFloat 2.2)))

    [<Fact>]
    let ``float minus`` () =
        test_ast "1.1 -. 2.2"
            (BinOp ((Lit (LFloat 1.1)), "-.", Lit (LFloat 2.2)))

    [<Fact>]
    let ``float star`` () =
        test_ast "1.1 *. 2.2"
            (BinOp ((Lit (LFloat 1.1)), "*.", Lit (LFloat 2.2)))

    [<Fact>]
    let ``float slash`` () =
        test_ast "1.1 /. 2.2"
            (BinOp ((Lit (LFloat 1.1)), "/.", Lit (LFloat 2.2)))

    [<Fact>]
    let ``float percent`` () =
        test_ast "1.1 %. 2.2"
            (BinOp ((Lit (LFloat 1.1)), "%.", Lit (LFloat 2.2)))

    [<Fact>]
    let ``int to float built in function`` () =
        test_ast "Float (1)"
            (UnOp ("to_float", Lit (LInt 1)))

    [<Fact>]
    let ``float to int built in function`` () =
        test_ast "Int (1.1)"
            (UnOp ("to_int", Lit (LFloat 1.1)))

    [<Fact>]
    let ``function applied to int builtin converion`` () =
        test_ast "f Int (1.1)"
            (App (Var ("f"), UnOp ("to_int", Lit (LFloat 1.1))))

    [<Fact>]
    let ``function applied to float builtin converion`` () =
        test_ast "f Float (1)"
            (App (Var "f", UnOp ("to_float", Lit (LInt 1))))

// LIST
type Test_parser_list () =
    [<Fact>]
    let ``empty list with no type`` () =
        test_ast "[]" (Empty None)

    [<Fact>]
    let ``empty list with type`` () =
        test_ast "[int]" (Empty (Some TyInt))

    [<Fact>]
    let ``list chain head plus empty with no type`` () =
        test_ast "1::[]" (List (Lit (LInt 1), Empty None))

    [<Fact>]
    let ``list chain head plus empty with type`` () =
        test_ast "1::[int]" (List (Lit (LInt 1), Empty (Some TyInt)))

    [<Fact>]
    let ``list chain two elements`` () =
        test_ast "1::2::[]" (List (Lit (LInt 1), (List (Lit (LInt 2), Empty (None)))))

    [<Fact>]
    let ``list is emtpy`` () =
        test_ast "IsEmpty x" (IsEmpty (Var ("x")))

    [<Fact>]
    let ``list match`` () =
        // This expression is clearly wrong but i just need to check the parser
        test_ast
            "match 1 with x::y -> 2 | [] -> 3"
            (Match (Lit (LInt 1), "x", "y", Lit (LInt 2), Lit (LInt 3)))

// TYPES
type Test_parser_type () =
    [<Fact>]
    let ``type with one simple constructor`` () =
        test_ast "type color = Yellow in x"
            (NewTy ("color", [Constr ("Yellow", None)], Var "x"))

    let ``type with two simple constructors`` () =
        test_ast "type color = Yellow | Red in x"
            (NewTy ("color", [Constr ("Yellow", None); Constr ("Red", None)], Var "x"))

    [<Fact>]
    let ``type with one constructor with attached data`` () =
        test_ast "type color = Rgb of int in x"
            (NewTy ("color", [Constr ("Rgb", Some (TyInt))], Var "x"))

    [<Fact>]
    let ``type with one constructor with attached tuple`` () =
        test_ast "type color = Rgb of int * bool * string in x"
            (NewTy ("color", [Constr ("Rgb", Some (TyTuple [TyInt; TyBool; TyString]))], Var "x"))

    [<Fact>]
    let ``type with one constructor recursive`` () =
        test_ast "type color = Rgb of color in x"
            (NewTy ("color", [Constr ("Rgb", Some (TyName "color"))], Var "x"))
