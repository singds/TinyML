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
    let mutable ok = false
    try
        let _ = eval_expr_from_string program
        ok <- false
    with _ ->
        ok <- true
    if ok = false then assert_fail "exception not raised" else ()

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

    // operators
    [<Fact>]
    let ``float plus operator`` () =
        test_eval_expr "1.2 +. 1.3" (VLit (LFloat (2.5)))

    [<Fact>]
    let ``integer plus operator`` () =
        test_eval_expr "1 + 2" (VLit (LInt (3)))


type Test_eval_expr_list () =
    [<Fact>]
    let ``empty list without type`` () =
        test_eval_expr "[]" VEmpty

    [<Fact>]
    let ``empty list with type`` () =
        test_eval_expr "[int]" VEmpty

    [<Fact>]
    let ``list chain with compatible types`` () =
        test_eval_expr "1::[int]" (VList (VLit (LInt 1), VEmpty))

    [<Fact>]
    let ``list chain two elements`` () =
        test_eval_expr "1::2::[int]" (VList (VLit (LInt 1), VList (VLit (LInt 2), VEmpty)))

    [<Fact>]
    let ``list is emtpy`` () =
        test_eval_expr "IsEmpty []" (VLit (LBool true))

    [<Fact>]
    let ``list is not emtpy`` () =
        test_eval_expr "IsEmpty (1::[])" (VLit (LBool false))

    [<Fact>]
    let ``list match, right branch`` () =
        test_eval_expr
            "match [] with h::t -> 1 | [] -> 2"
            (VLit (LInt 2))

    [<Fact>]
    let ``list match, left branch`` () =
        test_eval_expr
            "match 3::[] with h::t -> 1 | [] -> 2"
            (VLit (LInt 1))

    [<Fact>]
    let ``list match, return head`` () =
        test_eval_expr
            "match 3::4::[] with h::t -> h | [] -> 2"
            (VLit (LInt 3))

    [<Fact>]
    let ``list match, return tail`` () =
        test_eval_expr
            "match 3::4::[] with h::t -> t | [] -> 2"
            (VList (VLit (LInt 4), VEmpty))

    [<Fact>]
    let ``map function`` () =
        // int list -> int list
        test_eval_expr
            "
            let rec map f l =
                    match l with
                    h::t -> (f h)::(map f t)
                    | [] -> []
            in map (fun x -> x + 1) (1::2::[])
            "
            (VList (VLit (LInt 2), VList (VLit (LInt 3), VEmpty)))

    [<Fact>]
    let ``fold function`` () =
        // bool -> int list -> bool
        test_eval_expr
            "
            let rec fold f z l =
                    match l with
                    h::t -> fold f (f z h) t
                    | [] -> z
            in fold (fun z -> fun x -> z + x) 0 (1::2::3::[])
            "
            (VLit (LInt 6))

// TYPES
type Test_eval_expr_type () =
    [<Fact>]
    let ``type: check constructor binded with simple type`` () =
        test_eval_expr "type color = Yellow of unit in Yellow ()"
            (VUnion ("Yellow", VLit LUnit))

    [<Fact>]
    let ``type: check constructor binded with arrow type`` () =
        test_eval_expr "type color = Rgb of int in Rgb"
            (Closure ([], "x", Inst ("Rgb", Var "x")))

    [<Fact>]
    let ``type: check constructor binded with arrow type, two parameters`` () =
        test_eval_expr "type color = Rgb of int * int in Rgb"
            (Closure ([], "x", Inst ("Rgb", Var "x")))

    [<Fact>]
    let ``type: check constructor call with parameters`` () =
        test_eval_expr "type color = Rgb of int * int in Rgb ((1,2))"
            (VUnion ("Rgb", VTuple [VLit (LInt 1); VLit (LInt 2)]))

    [<Fact>]
    let ``type match with one simple constructor`` () =
        test_eval_expr "type color = Rgb of unit in matchf Rgb () with Rgb (x) -> 1"
            (VLit (LInt 1))

    [<Fact>]
    let ``type match with one constructor, one parameter`` () =
        test_eval_expr "type color = Rgb of float in matchf (Rgb (1.1)) with Rgb (x) -> x"
            (VLit (LFloat 1.1))

    [<Fact>]
    let ``type match with one constructor, two parameter`` () =
        test_eval_expr "type color = Rgb of int * float in matchf Rgb ((1, 2.2)) with Rgb (k) -> k"
            (VTuple [VLit (LInt 1); VLit (LFloat 2.2)])

    [<Fact>]
    let ``type match with two constructors in order`` () =
        test_eval_expr "type color = A of unit | B of unit in matchf A() with A (x) -> 1 | B (x) -> 2"
            (VLit (LInt 1))

    [<Fact>]
    let ``type match with two constructors not in order`` () =
        test_eval_expr "type color = A of unit | B of unit in matchf A() with B (x) -> 2 | A (x) -> 1"
            (VLit (LInt 1))

    [<Fact>]
    let ``type constructor invocation with single parameter`` () =
        test_eval_expr "type color = A of int in A 1"
            (VUnion ("A", VLit (LInt 1)))
    