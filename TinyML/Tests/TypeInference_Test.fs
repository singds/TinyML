module TinyML.TypeInference_Test

open Xunit
open Ast
open TypeInference
open FSharp.Common
open Utility

let typeinfer_expr_from_string (program:string) =
    fresh_tyvar <- 1
    let exp = Parsing.parse_from_string SyntaxError program "example" (1, 1) Parser.program Lexer.tokenize Parser.tokenTagToTokenId
    typeinfer_expr [] exp

let test_typeinfer_expr (program:string) (expected:ty) =
    let t,s = typeinfer_expr_from_string program
    Assert.Equal (expected, t)

let test_typeinfer_expr_error (program:string) =
    try
        let _,_ = typeinfer_expr_from_string program
        assert_fail "exception not raised"
    with _ ->
        ()

(* Unit tests for the <ty_contains_tyvar> function.
*)
type Test_ty_contains_tyvar () =
    [<Fact>]
    let ``variable true`` () =
        let t = TyVar(1)
        Assert.True (ty_contains_tyvar 1 t)

    [<Fact>]
    let ``variable false`` () =
        let t = TyVar(1)
        Assert.False (ty_contains_tyvar 2 t)

    [<Fact>]
    let ``arrow left true`` () =
        let t = TyArrow(TyVar(1),TyInt)
        Assert.True (ty_contains_tyvar 1 t)

    [<Fact>]
    let ``arrow left false`` () =
        let t = TyArrow(TyVar(1),TyInt)
        Assert.False (ty_contains_tyvar 2 t)

    [<Fact>]
    let ``arrow right true`` () =
        let t = TyArrow(TyInt, TyVar(1))
        Assert.True (ty_contains_tyvar 1 t)

    [<Fact>]
    let ``arrow right false`` () =
        let t = TyArrow(TyInt, TyVar(1))
        Assert.False (ty_contains_tyvar 2 t)

    [<Fact>]
    let ``tuple head true`` () =
        let t = TyTuple([TyVar(1); TyInt; TyBool])
        Assert.True (ty_contains_tyvar 1 t)

    [<Fact>]
    let ``tuple mid true`` () =
        let t = TyTuple([TyInt; TyVar(1); TyBool])
        Assert.True (ty_contains_tyvar 1 t)

    [<Fact>]
    let ``tuple tail true`` () =
        let t = TyTuple([TyInt; TyBool; TyVar(1)])
        Assert.True (ty_contains_tyvar 1 t)

    [<Fact>]
    let ``tuple false`` () =
        let t = TyTuple([TyVar(1); TyVar(2); TyInt; TyBool])
        Assert.False (ty_contains_tyvar 3 t)



(* Unit tests for the <compose_subst> function.
*)
type Test_compose_subst () =
    [<Fact>]
    let ``simple union`` () =
        let s1 = [(1, TyInt)]
        let s2 = [(2, TyBool)]
        let exp = [(1, TyInt); (2, TyBool)]
        Assert.Equal<subst> (exp, (compose_subst s2 s1))

    [<Fact>]
    let ``substitute right side`` () =
        let s1 = [(1, TyVar(2))]
        let s2 = [(2, TyVar(3))]
        let exp = [(1, TyVar(3)); (2, TyVar(3))]
        Assert.Equal<subst> (exp, (compose_subst s2 s1))

    [<Fact>]
    let ``same var on both side exception`` () =
        let s1 = [(1, TyVar(2))]
        let s2 = [(1, TyVar(3))]
        try
            let x = compose_subst s2 s1
            assert_fail "no exception raised"
        with UnexpectedError msg ->
            ()



(* Unit tests for the <compose_subst_list> function.
*)
type Test_compose_subst_list () =
    [<Fact>]
    let ``simple union`` () =
        let s1 = [(1, TyVar(2))]
        let s2 = [(3, TyVar(4))]
        let s3 = [(5, TyVar(6))]
        let exp = [(1, TyVar(2)); (3, TyVar(4)); (5, TyVar(6))]
        Assert.Equal<subst> (exp, (compose_subst_list [s3; s2; s1]))

    [<Fact>]
    let ``cascade substitution`` () =
        let s1 = [(1, TyVar(2))]
        let s2 = [(2, TyVar(3))]
        let s3 = [(3, TyVar(4))]
        let exp = [(1, TyVar(4)); (2, TyVar(4)); (3, TyVar(4))]
        Assert.Equal<subst> (exp, (compose_subst_list [s3; s2; s1]))

type Test_apply_subst_ty () =
    [<Fact>]
    let ``substitute type variable`` () =
        let t = TyVar(1)
        let s = [(1, TyInt)]
        Assert.Equal (TyInt, apply_subst_ty s t)

    let ``substitute arrow type`` () =
        let t = TyArrow(TyVar(1), TyVar(2))
        let s = [(1, TyBool); (2, TyString)]
        let exp = TyArrow(TyBool, TyString)
        Assert.Equal (exp, apply_subst_ty s t)

    let ``substitute arrow type`` () =
        let t = TyTuple [TyVar(1); TyVar(2)]
        let s = [(1, TyBool); (2, TyString)]
        let exp = TyTuple [TyBool; TyString]
        Assert.Equal (exp, apply_subst_ty s t)

type Test_apply_subst_scheme () =
    [<Fact>]
    let ``example ok`` () =
        let scheme = Forall ([2;3], TyArrow(TyVar(1), TyVar(2)))
        let substitution = [(1, TyInt)]
        let exp = Forall ([2;3], TyArrow(TyInt, TyVar(2)))
        Assert.Equal (exp, apply_subst_scheme substitution scheme)

    [<Fact>]
    let ``example exception`` () =
        let scheme = Forall ([1], TyVar(1))
        let substitution = [(1, TyInt)]
        try
            let x = apply_subst_scheme substitution scheme
            assert_fail "no exception raised"
        with UnexpectedError msg ->
            ()

type Test_apply_subst_env () =
    [<Fact>]
    let ``example ok`` () =
        let env = [("x",  Forall ([], TyVar(1)));
                   ("y",  Forall ([], TyVar(2)))
                  ]
        let substitution = [(1, TyInt); (2, TyBool)]

        let exp = [("x",  Forall ([], TyInt));
                   ("y",  Forall ([], TyBool))
                  ]
        Assert.Equal<scheme env> (exp, apply_subst_env substitution env)

type Test_unify () =
    [<Fact>]
    let ``unify compatible base types`` () =
        // the unification of two compatible base types must return the empty substitution
        Assert.Equal<subst> ([], unify TyBool TyBool)

    [<Fact>]
    let ``unify incompatible base types`` () =
        try
            let x = unify TyInt TyBool
            assert_fail "no exception raised"
        with TypeError msg ->
            ()

    [<Fact>]
    let ``unify a type variable with itself`` () =
        // U('a, 'a) = {}
        // when i unify a type variable with itself like unify('a,'a) i should get
        // the empty substitution
        let s = unify (TyVar(1)) (TyVar(1))
        Assert.Equal<subst> ([], s)

    [<Fact>]
    let ``unify two different type variables`` () =
        // U('a, 'b) = {'a > 'b}
        let s = unify (TyVar(1)) (TyVar(2))
        let exp = [(1, TyVar(2))]
        Assert.Equal<subst> (exp, s)

    [<Fact>]
    let ``unify type variable with base type on the right`` () =
        // U('a, int) = {'a > int}
        let s = unify (TyVar(1)) TyInt
        let exp = [(1, TyInt)]
        Assert.Equal<subst> (exp, s)

    [<Fact>]
    let ``unify type variable with base type on the left`` () =
        // U(int, 'a) = {'a > int}
        let s = unify TyInt (TyVar(1))
        let exp = [(1, TyInt)]
        Assert.Equal<subst> (exp, s)

    [<Fact>]
    let ``type occurence check fail - type on the left`` () =
        // U('a, 'a -> int) = error
        let t1 = TyVar(1)
        let t2 = TyArrow (TyVar(1), TyInt)
        try
            let x = unify t1 t2
            assert_fail "no exception raised"
        with TypeError msg ->
            ()

    [<Fact>]
    let ``type occurence check fail - type on the right`` () =
        // U('a -> int, 'a) = error
        let t1 = TyArrow (TyVar(1), TyInt)
        let t2 = TyVar(1)
        try
            let x = unify t1 t2
            assert_fail "no exception raised"
        with TypeError msg ->
            ()

    [<Fact>]
    let ``unify type variable with complex type - variable on the right`` () =
        // U('a, 'b -> 'c) = {'a, 'b -> 'c}
        let t1 = TyArrow (TyVar(2), TyVar(3))
        let t2 = TyVar(1)
        Assert.Equal<subst> ([(1, t1)], unify t1 t2)

    [<Fact>]
    let ``unify type variable with complex type - variable on the left`` () =
        // U('b -> 'c, 'a) = {'a, 'b -> 'c}
        let t1 = TyVar(1)
        let t2 = TyArrow (TyVar(2), TyVar(3))
        Assert.Equal<subst> ([(1, t2)], unify t1 t2)

    [<Fact>]
    let ``unify arrow type with arrow type made by base types`` () =
        // U('a -> 'b, int -> bool) = {'a > int, 'b > bool}
        let t1 = TyArrow (TyVar(1), TyVar(2))
        let t2 = TyArrow (TyInt, TyBool)
        let s = unify t1 t2
        let exp = [(1, TyInt); (2, TyBool)]
        Assert.Equal<subst> (exp, s)

    [<Fact>]
    let ``unify arrow type with arrow type triky`` () =
        // U('a -> 'a, 'b -> 'c) = {'a > 'c, 'b > 'c}
        // This is a special case that requires attention.
        // Check the comments on the TyArrow TyArrow case of the unify function
        let t1 = TyArrow (TyVar(1), TyVar(1))
        let t2 = TyArrow (TyVar(2), TyVar(3))
        let exp = [(1, TyVar(3)); (2, TyVar(3))]
        Assert.Equal<subst> (exp, unify t1 t2)
    
    [<Fact>]
    let ``unify tuple type with tuple type made by base types`` () =
        // U('a * 'b, int * bool) = {'a > int, 'b > bool}
        let t1 = TyTuple [TyVar(1); TyVar(2)]
        let t2 = TyTuple [TyInt; TyBool]
        let s = unify t1 t2
        Assert.Equal<subst> ([(1, TyInt); (2, TyBool)], s)

    [<Fact>]
    let ``unify tuple type with tuple type triky`` () =
        // U('a * 'a, 'b * 'c) = {'a > 'c, 'b > 'c}
        let t1 = TyTuple [TyVar(1); TyVar(1)]
        let t2 = TyTuple [TyVar(2); TyVar(3)]
        let s = unify t1 t2
        Assert.Equal<subst> ([(1, TyVar(3)); (2, TyVar(3))], s)


type Test_freevars_ty () =
    [<Fact>]
    let ``freevars of tuple type`` () =
        let t = TyTuple [TyVar(1); TyVar(2)]
        let freevars = freevars_ty t
        let exp = Set [1; 2]
        Assert.Equal<tyvar Set> (exp, freevars)

    [<Fact>]
    let ``freevars of arrow type`` () =
        let t = TyArrow (TyVar(1), TyVar(2))
        let freevars = freevars_ty t
        let exp = Set [1; 2]
        Assert.Equal<tyvar Set> (exp, freevars)

    [<Fact>]
    let ``freevars of base type`` () =
        Assert.Equal<tyvar Set> (Set.empty, freevars_ty TyInt)

    [<Fact>]
    let ``freevars of type variable`` () =
        Assert.Equal<tyvar Set> (Set [1], freevars_ty (TyVar(1)))

type Test_freevars_scheme () =
    [<Fact>]
    let ``freevars scheme relevant example`` () =
        let s = Forall ([1;2], TyTuple [TyVar(1); TyVar(2); TyVar(3)])
        let freevars = freevars_scheme s
        let exp = Set [3]
        Assert.Equal<tyvar Set> (exp, freevars)

type Test_freevars_env () =
    [<Fact>]
    let ``freevars env relevant example`` () =
        let env = [
            ("x", Forall ([], TyVar(1)));
            ("y", Forall ([], TyVar(2)))
            ("z", Forall ([3], TyVar(3))) // this is not a free variable
        ]
        let freevars = freevars_env env
        let exp = Set [1;2]
        Assert.Equal<tyvar Set> (exp, freevars)

type Test_inst_scheme () =
    [<Fact>]
    let ``inst single universally quantified variable`` () =
        // inst (forall 'a . 'a) = 'b
        fresh_tyvar <- 50
        let scheme = Forall ([1], TyVar(1))
        let exp = TyVar(51)
        Assert.Equal (exp, inst_scheme scheme)

    [<Fact>]
    let ``inst single non universally quantified variable`` () =
        // inst (forall . 'a) = 'a
        let scheme = Forall ([], TyVar(1))
        let exp = TyVar(1)
        Assert.Equal (exp, inst_scheme scheme)

    [<Fact>]
    let ``inst a type where a universally quantified variable appears multiple times`` () =
        // inst (forall 'a. 'a -> 'a) = 'b -> 'b
        fresh_tyvar <- 50
        let scheme = Forall ([1], TyArrow (TyVar(1), TyVar(1)))
        let exp = TyArrow (TyVar(51), TyVar(51))
        Assert.Equal (exp, inst_scheme scheme)

    [<Fact>]
    let ``inst relevant example`` () =
        // inst (forall 'a,'c . 'a * 'b * 'c * 'd) = 'e * 'b * 'f * 'd
        fresh_tyvar <- 50
        let scheme = Forall ([1;3], TyTuple [TyVar(1); TyVar(2); TyVar(3); TyVar(4)])
        let exp = TyTuple [TyVar(51); TyVar(2); TyVar(52); TyVar(4)]
        Assert.Equal (exp, inst_scheme scheme)

type Test_generalize_ty () =
    [<Fact>]
    let ``gen type variable when variable not in env.`` () =
        let exp = Forall ([1], TyVar(1))
        Assert.Equal (exp, generalize_ty [] (TyVar 1))

    [<Fact>]
    let ``gen type variable when variable present in env.`` () =
        let env = [("x", Forall([], TyVar 1))]
        let exp = Forall ([], TyVar 1)
        Assert.Equal (exp, generalize_ty env (TyVar 1))

    [<Fact>]
    let ``gen relevant example`` () =
        let env = [("x", Forall([], TyArrow (TyInt, TyVar 1)))]
        let t = TyTuple [TyVar 1; TyVar 2]
        Assert.Equal (Forall ([2], t), generalize_ty env t)

type Test_typeinfer_expr () =
    [<Fact>]
    let ``lambda int -> int`` () =
        test_typeinfer_expr
            "fun x -> x + 1"
            (TyArrow(TyInt, TyInt))

    [<Fact>]
    let ``ifThenElse with unification in then`` () =
        // int -> int -> int
        test_typeinfer_expr
            "fun x -> fun y -> if true then x + 1 else y"
            (TyArrow(TyInt, TyArrow (TyInt, TyInt)))

    [<Fact>]
    let ``ifThenElse with unification in else`` () =
        // int -> int -> int
        test_typeinfer_expr
            "fun x -> fun y -> if true then x else y + 1"
            (TyArrow(TyInt, TyArrow (TyInt, TyInt)))

    [<Fact>]
    let ``ifThenElse with unification in if`` () =
        // bool -> bool -> bool
        test_typeinfer_expr
            "fun x -> fun y -> if x then x else y"
            (TyArrow(TyBool, TyArrow (TyBool, TyBool)))

    [<Fact>]
    let ``lambda with unification in nested let`` () =
        // bool -> bool -> bool
        test_typeinfer_expr
            "fun y -> let x:int = y in x"
            (TyArrow(TyInt, TyInt))
    
    [<Fact>]
    let ``tuple made of base types`` () =
        // int * string * bool
        test_typeinfer_expr
            "(1, \"ciao\", true)"
            (TyTuple [TyInt; TyString; TyBool])

    [<Fact>]
    let ``tuple unification with type variable in decomposition`` () =
        // int * int -> int
        test_typeinfer_expr
            "fun x -> let (a,b)=x in a + b"
            (TyArrow (TyTuple [TyInt; TyInt], TyInt))

    [<Fact>]
    let ``tuple tricky`` () =
        // int -> int -> int -> (int, int, int)
        test_typeinfer_expr
            "fun x -> fun y -> fun z -> (if true then x else y, if true then x else z, z + 1)"
            (TyArrow (TyInt, TyArrow (TyInt, TyArrow (TyInt, TyTuple [TyInt; TyInt; TyInt]))))

    [<Fact>]
    let ``let rec sum of the first x numbers`` () =
        // int -> int
        test_typeinfer_expr
            "let rec f = fun x -> if x > 0 then x + (f (x - 1)) else 0 in f"
            (TyArrow (TyInt, TyInt))

    [<Fact>]
    let ``let rec defining a function not really recursive`` () =
        // int -> int
        test_typeinfer_expr
            "let rec f = fun x -> x + 1 in f"
            (TyArrow (TyInt, TyInt))

    [<Fact>]
    let ``binary operation tricky inference`` () =
        // x:int -> y:int ->
        //   f1:(int -> int) -> f2:(int -> int) -> f3:(int -> int) ->
        //     int * int * int * int * int
        test_typeinfer_expr
            "fun x -> fun y ->
                fun f1 -> fun f2 -> fun f3 ->
                    (f1 y, f2 y, f3 y, (((if true then f1 else f2) x) + ((if true then f1 else f3) x)), y + 1)"
            (TyArrow (TyInt, TyArrow (TyInt,
                 TyArrow (TyArrow(TyInt, TyInt), TyArrow (TyArrow(TyInt, TyInt), TyArrow (TyArrow(TyInt, TyInt),
                    TyTuple [TyInt; TyInt; TyInt; TyInt; TyInt]))))))

    [<Fact>]
    let ``sequence operator single pair`` () = 
        // float
        test_typeinfer_expr
            "(); 1.2"
            TyFloat

    [<Fact>]
    let ``sequence operator multiple`` () = 
        // float
        test_typeinfer_expr
            "(); (); 1.2"
            TyFloat

    [<Fact>]
    let ``sequence operator left side unification`` () = 
        // unit -> float
        test_typeinfer_expr
            "fun x -> x; 1.2"
            (TyArrow (TyUnit, TyFloat))

    [<Fact>]
    let ``sequence operator tricky inference`` () = 
        // int -> int -> int
        test_typeinfer_expr
            "fun x -> fun y -> let (a,b)=(if true then x else y, ()) in b; x + 1"
            (TyArrow (TyInt, TyArrow (TyInt, TyInt)))


[<Theory>]
[<InlineData("let rec f = f 1 in f")>]
let Test_typeinfer_expr_error (exp:string) =
    test_typeinfer_expr_error exp