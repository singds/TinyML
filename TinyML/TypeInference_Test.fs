module TinyML.TypeInference_Test

open Xunit
open Ast
open TypeInference

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
            Assert.True(false, "no exception rised")
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