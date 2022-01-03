module TinyML.TypeInference_Test

open Xunit
open Ast
open TypeInference

let assert_fail msg =
    Assert.True (false, msg)

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
