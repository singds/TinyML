module TinyML.TypeInference

open Ast

let type_error fmt = throw_formatted TypeError fmt

let rec apply_subst_ty (s : subst) (t : ty) : ty =
    match t with
    | TyName (n) ->
        t
    | TyVar (x) ->
        try
            // if this type variable is bound to another type inside the substitution, i substitute
            let _, newTy = List.find (fun (var, tipe) -> var = x) s
            newTy
        with _ ->
            t
    | TyArrow (t1,t2) ->
        TyArrow ((apply_subst_ty s t1), (apply_subst_ty s t2))
    | TyTuple (tl) ->
        TyTuple (List.map (apply_subst_ty s) tl)


let rec apply_subst_scheme (sub : subst) (sch : scheme) : scheme =
    match sch with
    // uql = universally quantified variable list
    | Forall (uql, tipe) ->
        // no universally quantified variable can appear inside the substitution
        let uqVars = Set uql
        let sVars = Set (List.map (fun (var, _) -> var) sub) 
        let intersect = Set.intersect uqVars sVars
        if Set.count intersect > 0
        then
            unexpected_error "apply_subst_scheme: substitution of a universally quantified variable, scheme=%s substitution=%s" (pretty_scheme sch) (pretty_subs sub)
        Forall (uql, apply_subst_ty sub tipe)

let rec apply_subst_env (sub : subst) (env : scheme env) : scheme env =
    match env with
    | [] -> []
    | (tvar, sch)::tail ->
        (tvar, apply_subst_scheme sub sch)::(apply_subst_env sub tail)

(* Check the given type variable appears somewhere in the given type.
*)
let rec ty_contains_tyvar (v : tyvar) (t : ty) : bool =
    match t with
    | TyName (n) ->
        false
    | TyVar (x) ->
        if x = v then true
        else false
    | TyArrow (t1,t2) ->
        (ty_contains_tyvar v t1) || (ty_contains_tyvar v t2)
    | TyTuple (tl) ->
        List.fold (fun (state:bool) (t:ty) -> state || (ty_contains_tyvar v t)) false tl

(* This returns s3 = s2 o s1.
Applying s3 is the same as applying s1 first and s2 next.
The order matters.
*)
let compose_subst (s2 : subst) (s1 : subst) : subst =
    // apply the substitution s2 to s1
    let newSub = List.map (fun (var, t) -> (var, apply_subst_ty s2 t)) s1
    let s1Vars = Set (List.map (fun (var, _) -> var) s1)
    let s2Vars = Set (List.map (fun (var, _) -> var) s2)
    let intersect = Set.intersect s1Vars s2Vars
    if Set.count (intersect) > 0
    then
        let check = fun (e:tyvar) ->
            let (_, t1) = List.find (fun (var, _) -> var = e) s1
            let (_, t2) = List.find (fun (var, _) -> var = e) s2
            if t1 <> t2
            then
                unexpected_error "compose_subst: incompatible substitution composition s2=%s s1=%s" (pretty_subs s1) (pretty_subs s2)
        Set.iter check intersect
    let s2 = List.filter (fun (var, _) -> not (Set.contains var intersect)) s2
    newSub @ s2

let rec compose_subst_list (subsList : subst list) : subst =
    match subsList with
    | [] -> []
    | x::tail ->
        compose_subst x (compose_subst_list tail)

(* return the most general unifier between the two types provided
the function returns a substitution that applied to both t1 and t2 produces the
same type : apply(substitution, t1) = apply(substitution, t1)

*)
let rec unify (t1 : ty) (t2 : ty) : subst =
    match t1, t2 with
    | TyName (a), TyName (b) ->
        if a <> b then
            type_error "unify: base type <%s> can't be unified with type <%s>" (pretty_ty t1) (pretty_ty t2)
        []

    | TyVar (a), TyVar (b) ->
        // if t1 and t2 are the same type variable, i produce the empty substitution
        if a = b then []
        else [(a, t2)]

    | TyVar (a), _ ->
        // the type variable 'a' must not appear in the type t2
        if ty_contains_tyvar a t2 then
            type_error "unify: type variable <%s> can't be unified with the type <%s>" (pretty_ty t1) (pretty_ty t2)
        [(a, t2)]

    | _, TyVar(a) ->
        // the type variable 'a' must not appear in the type t1
        if ty_contains_tyvar a t1 then
            type_error "unify: type variable <%s> can't be unified with the type <%s>" (pretty_ty t2) (pretty_ty t1)
        [(a, t1)]

    | TyArrow(ta1,ta2), TyArrow(ta3,ta4) ->
        let s = unify ta1 ta3
        // The substitution obtained from the unification of the left hand side
        // types, must be applied to the right hand side types before unifing them.
        // To better understand check this special case:
        // unify ('a -> 'a, 'b -> 'c)
        // If you don't apply the substitution before unifying t2 and t3, you get:
        //      S1 = U('a, 'b) = {'a -> 'b}
        //      S2 = U('a, 'c) = {'a -> 'c}
        //      S2 o S1 = {'a -> 'c} o {'a -> 'b} = {'a -> 'b}
        // If you do apply, you get:
        //      S1 = U('a, 'b) = {'a -> 'b}
        //      S2 = U(S1('a), S1('c)) = U('b -> 'c) = {'b -> 'c}
        //      S2 o S1 = {'b -> 'c} o {'a -> 'b} = {'a -> 'c, 'b -> 'c}
        let ta2 = apply_subst_ty s ta2
        let ta4 = apply_subst_ty s ta4
        compose_subst_list [unify ta2 ta4; s]

    | TyTuple(l1), TyTuple(l2) ->
        if l1.Length <> l2.Length then
            type_error "unify: tupe tuype <%s> does not match the number of fields of tuple type <%s>" (pretty_ty t1) (pretty_ty t2)

        // from the two lists (L1 and L2) I build a single list L with L[n] = (L1[n],L2[n])
        let pairs = List.zip l1 l2

        // Every time I compute a new subtitution, I have to apply it to the
        // following types before unifing them.
        // Check the special case: U('a * 'a, 'b * 'c)
        List.fold (fun (s:subst) (t1:ty, t2:ty) ->
            let t1 = apply_subst_ty s t1
            let t2 = apply_subst_ty s t2
            let subU = unify t1 t2
            compose_subst subU s
        ) [] pairs

    // this case encompasses all those cases:
    // (TyName, TyArrow) | (TyName, TyTuple) | (TyArrow, TyTuple)
    | _ -> type_error "unify: type %s can't be unified with type %s" (pretty_ty t1) (pretty_ty t2)

let rec freevars_ty (t : ty) : tyvar Set =
    match t with
    | TyName _ -> Set.empty
    | TyArrow (t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun set t -> Set.union set (freevars_ty t)) Set.empty ts 

let freevars_scheme (Forall (tvs, t)) : tyvar Set =
    Set.difference (freevars_ty t) (Set.ofList tvs)

let rec freevars_env (env: scheme env) : tyvar Set =
    match env with
    | [] -> Set.empty
    | (_,s)::tail ->
        Set.union (freevars_scheme s) (freevars_env tail)


let mutable fresh_tyvar :tyvar = 0
let get_new_fresh_tyvar () : tyvar =
    fresh_tyvar <- fresh_tyvar + 1
    fresh_tyvar

// scheme instantiation
let rec inst_scheme (s:scheme) : ty =
    match s with
    | Forall (uqv, t) ->
        let freeVars = freevars_ty t
        let toBeRefresh = Set.intersect freeVars (Set uqv)
        // build up a substitution mapping each of the type variable that needs to
        // be refresh, in a new fresh type type variable
        let sub = List.map (fun v -> (v, TyVar(get_new_fresh_tyvar ()))) (List.sort (Set.toList toBeRefresh))
        apply_subst_ty sub t

// type generalization
let generalize_ty (env: scheme env) (t: ty) : scheme =
    // uqv = universally quantified vars
    let uqv = Set.difference (freevars_ty t) (freevars_env env)
    Forall (Set.toList uqv, t)

// type inference
//

// challenging cases
// let f = fun x -> (x + 1) + (x + 1.1) in f 1
let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Lit (LBool _) -> (TyBool, [])
    | Lit (LFloat _) -> (TyFloat, [])
    | Lit (LString _) -> (TyString, [])
    | Lit (LInt _) -> (TyInt, [])
    | Lit (LUnit) -> (TyUnit, [])
    | Lit (LChar _) -> (TyChar, [])

    (* x | foo

    Algorithm W (Damas and Milner)
    W(A, e) = (S, T)
    W(A, x)
        x: forall a1...an t' in A
        S = empty substitution
        T = [bi / ai]t' where bi for i in [1..n] are new fresh type variables
    *)
    | Var x ->
        // lookup for the variable in the environment
        // return the instantiation of the associated scheme and an empty substitution
        try
            let _, s = List.find (fun (y, _) -> x = y) env
            (inst_scheme (s), [])
        with _ -> type_error "typeinfer_expr: use of undefined variable <%s>" x

    (* fun x -> e
    x = name of the lambda parameter
    e1 = the body of the lambda
    this is the lambda with no type annotation

    Algorithm W (Damas and Milner)
    W(A, e) = (S, T)
    W(A, fun x -> e1)
        B is a new fresh type variable
        W(A + {x: B}, e1) = (S1, t1)
        S = S1
        T = S1 B -> t1
    *)
    | Lambda (x, None, e1) ->
        // vParam = a new fresh type variable for the lambda parameter
        let vParam = TyVar(get_new_fresh_tyvar ())
        // enrich the type environment with a binding from the variable name to
        // the newly created type variable
        let env = (x,Forall ([], vParam))::env
        let codTy, s = typeinfer_expr env e1 // compute the type of the codomain
        let domTy = apply_subst_ty s vParam
        (TyArrow (domTy, codTy), s)

    (* e1 e2

    Algorithm W (Damas and Milner)
    W(A, e) = (S, T)
    W(A, let x = e1 in e2)
        W(A, e1) = (S1, t1)
        W(S1 A, e2) = (S2, t2)
        U(S2 t1, t2 -> B) = V
        B is a new fresh type variable
        S = V S2 S1
        T = V B
    *)
    | App (e1, e2) ->
        let codTy = TyVar(get_new_fresh_tyvar ())
        let t1, s1 = typeinfer_expr env e1
        // update the type environment with what learned inferring the type of e1
        let env = apply_subst_env s1 env
        let t2, s2 = typeinfer_expr env e2
        // update the type t1 with what lerned inferring the type of e2
        // typing the right hand side we may have lerned something about the type
        // of the left hand side
        let t1 = apply_subst_ty s2 t1
        let funType = TyArrow (t2, codTy)
        let s3 = unify t1 funType
        let s = compose_subst_list [s3; s2; s1]
        (apply_subst_ty s3 codTy, s)

    (* let x = e1 in e2

    Algorithm W (Damas and Milner)
    W(A, e) = (S, T)
    W(A, let x = e1 in e2)
        W(A, e1) = (S1, t1)
        W(S1 A + {x: gen(S1 A, t1), e2) = (S2, t2)
        S = S2 S1
        T = t2
    *)
    | Let (x, None, e1, e2) ->
        // first i infeer the type of the bunded expression
        let t1, s1 = typeinfer_expr env e1
        let env = apply_subst_env s1 env
        let tScheme = generalize_ty env t1 // generalize the resulted type producing a scheme
        // enrich the environment with that scheme bounded to the variable name
        let env = (x,tScheme)::env
        // evaluate the let body in that environment
        let t2, s2 = typeinfer_expr env e2
        let s = compose_subst_list [s2; s1]
        (t2, s)

    (* fun (x:<type>) -> e1
    t = type of the lambda parameter
    *)
    | Lambda (x, Some t, e1) ->
        // enrich the environment binding the type of the parameter
        let env = (x,Forall ([], t))::env
        let t1, s1 = typeinfer_expr env e1
        (TyArrow (t, t1), s1)

    (* let x:<type> = e1 in e2
    type annotations can't contain type variables

    Interesting expressions (ie):
    1) fun y -> let x:int = y in x
    *)
    | Let (x, Some t, e1, e2) ->
        // first i infer the type of the bunded expression
        let t1, s1 = typeinfer_expr env e1
        // t1 can be a type variable (see ie. (1))
        let su = unify t1 t
        let s = compose_subst_list [su; s1]
        let env = (x,Forall ([], t))::env
        let env = apply_subst_env s env
        let t2, s2 = typeinfer_expr env e2
        let s = compose_subst_list [s2; s]
        (t2, s)

    (* if e1 then e2 [else e3]
    
    Interesting expressions (ie):
    1) fun x -> if x then x + 1 else x (must produce an error)
    2) fun x -> fun y -> if x then y else y + 1
    *)
    | IfThenElse (e1, e2, e3o) ->
        let t1, s1 = typeinfer_expr env e1
        let su = unify t1 TyBool
        let s = compose_subst_list [su; s1]
        let env = apply_subst_env s env
        let t2, s2 = typeinfer_expr env e2
        let s = compose_subst_list [s2; s]

        match e3o with
        | None ->
            let su = unify t2 TyUnit
            let s = compose_subst_list [su; s]
            (TyUnit, s)
        | Some e3 ->
            let env = apply_subst_env s env
            let t3, s3 = typeinfer_expr env e3
            let t2 = apply_subst_ty s3 t2 // typing e3 i can learn something about the type of e2 (es. fun x -> if true then x else x + 1)
            let su = unify t2 t3
            let s = compose_subst_list [su; s3; s]
            (apply_subst_ty su t3, s)

    (* (e1, e2, .., en)

    Interesting expressions (ie):
    1) fun x -> fun y -> fun z -> (if true then x else y, if true then x else z)
        tricky example, the type should be: 'a -> 'a -> 'a -> ('a, 'a)
    2) fun x -> fun y -> fun z -> (if true then x else y, if true then x else z, z + 1)
        type: int -> int -> int -> (int, int, int)
    *)
    | Tuple es ->
        // first i get all the types and substitutions from inferring the type
        // for all the expressions in the tuple
        let state = List.fold (fun state exp ->
            match state with
            // env = the current refined environment
            // s = the current total composed substitution
            // ts = the list of inferred types
            | (env:scheme env, s:subst, ts:ty list) ->
                let env = apply_subst_env s env
                let tExp, sExp = typeinfer_expr env exp
                // I apply what I have learned from this step, to all the types previously found.
                // I keep all the types refined.
                let ts = List.map (fun t -> apply_subst_ty sExp t) ts
                let s = compose_subst_list [sExp; s]
                let ts = ts @ [tExp]
                (env, s, ts)) (env, [], []) es
        let (_, s, ts) = state // retrieve the substitution and the list of types from the fold state
        (TyTuple ts, s)

    (* let rec f = e1 in e2
    The identifier <f> can appear in the expression e1.
    The let rec must bind the identifier to a function.

    Interesting expressions (ie):
    1) let rec f = f 1 in f;; this must produce an error
    *)
    | LetRec (f, None, e1, e2) ->
        let funTy = TyArrow (TyVar (get_new_fresh_tyvar ()), TyVar (get_new_fresh_tyvar ()))
        let env1 = (f,Forall ([], funTy))::env
        let t1, s1 = typeinfer_expr env1 e1
        let funTy = apply_subst_ty s1 funTy // apply to <f> type what learned from typing <e1>
        let su = unify funTy t1             // the type of <e1> must unify with the type of <f>
        let t1 = apply_subst_ty su t1       // refine <t1> with what learned from unification
        let s = compose_subst_list [su; s1]
        let env2 = apply_subst_env s env
        // infer the type of <e2> in an environment enriched with <f> bounded to the generalization of <t1>
        let env2 = (f, generalize_ty env2 t1)::env2
        let t2, s2 = typeinfer_expr env2 e2
        let s = compose_subst_list [s2; s]
        (t2, s)

    (* let (id1,id2,..,idn) = e1 in e2
    This expression permits tuple decomposition, such that single elements of the
    tuple can be obtained.
    *)
    | LetTuple (ns, e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        let tupleTy = TyTuple (List.map (fun _ -> TyVar (get_new_fresh_tyvar ())) ns)
        let su = unify t1 tupleTy
        let t1 = apply_subst_ty su t1 // apply what i have learned from unification to t1
        let s = compose_subst_list [su; s1]

        match t1 with
        | TyTuple(ts) ->
            let validNames = List.filter (fun x -> x <> "_") ns
            // check that there are no duplicate names in the tuple decomposition
            let distinct = List.distinct validNames
            if distinct.Length < validNames.Length then
                type_error "repeated identifier in tuple decomposition (%s)" (pretty_tupled_string_list ns)
            
            let env = apply_subst_env s env                             // refine the environment applying what i have learned untill now
            let schemes = List.map (fun t -> generalize_ty env t) ts    // generalize all the types of the tuple
            let pairs = List.zip ns schemes                             // pair each identifier with the corresponding scheme
            let pairs = List.filter (fun (n,v) -> n <> "_") pairs       // remove ignored names
            let t2, s2 = typeinfer_expr (pairs @ env) e2                // add identifiers to the env. and typeinfer the body
            let s = compose_subst_list [s2; s]
            (t2, s)
        | _ -> type_error "expecting a tuple in decomposition (%s) but got type %s"
                    (pretty_tupled_string_list ns) (pretty_ty t1)

    (* e1; e2

    The left hand side of the sequence operator must have type Unit.
    *)
    | Seq (e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        let su = unify t1 TyUnit
        let s = compose_subst_list [su; s1]
        let env = apply_subst_env s env
        let t2, s2 = typeinfer_expr env e2
        let s = compose_subst_list [s2; s]
        (t2, s)

    (* e1 op e2
    
    Interesting expressions (ie.):
    1) fun x -> fun y ->
         fun f1 -> fun f2 -> fun f3 ->
           (f1 y, f2 y, f3 y, (((if true then f1 else f2) x) + ((if true then f1 else f3) x)))
    type:
       x:'a -> y:'a ->
         f1:('a -> int) -> f2:('a -> int) -> f3:('a -> int) ->
           int * int * int * int
    *)
    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        typeinfer_binop TyInt TyInt env e1 e2

    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        typeinfer_binop TyInt TyBool env e1 e2

    | BinOp (e1, ("and" | "or" as op), e2) ->
        typeinfer_binop TyBool TyBool env e1 e2

    | BinOp (_, op, _) -> unexpected_error "typeinfer_expr: unsupported binary operator (%s)" op
    
    (* op exp
    *)
    | UnOp ("not", e) ->
        typeinfer_unop TyBool TyBool env e
            
    | UnOp ("-", e) ->
        typeinfer_unop TyInt TyInt env e

    | UnOp (op, _) -> unexpected_error "typeinfer_expr: unsupported unary operator (%s)" op

    | _ -> unexpected_error "typeinfer_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e

and typeinfer_binop e1E2Type resType env e1 e2 =
    let t1, s1 = typeinfer_expr env e1
    let su = unify t1 e1E2Type
    let s = compose_subst_list [su; s1]
    let env = apply_subst_env s env
    let t2, s2 = typeinfer_expr env e2
    let su = unify t2 e1E2Type
    let s = compose_subst_list [su; s2; s]
    (resType, s)

and typeinfer_unop eType resType env exp =
    let t, s = typeinfer_expr env exp
    let su = unify t eType
    let s = compose_subst_list [su; s]
    (resType, s)
