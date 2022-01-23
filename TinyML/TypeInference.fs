module TinyML.TypeInference

open Ast
open Utility

(* apply substitution to type
*)
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
    | TyList (elemT) ->
        TyList (apply_subst_ty s elemT)

(* apply substitution to scheme
*)
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

(* apply substitution to environment
*)
let rec apply_subst_env (sub : subst) (env : scheme env) : scheme env =
    match env with
    | [] -> []
    | (tvar, sch)::tail ->
        (tvar, apply_subst_scheme sub sch)::(apply_subst_env sub tail)

(* Check if the given type variable appears somewhere in the given type.
return true if t.contains(v).
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
    | TyList (elemT) ->
        ty_contains_tyvar v elemT

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

(* compose a list of substitution: Sn o Sn-1 o .. o S2 o S1
The right-most substitution is the tail of the list.
The left-most substitution is the head of the list.
Applying the obtained subst is equivalent of applying in order S1,S2,..,Sn-1,Sn
*)
let rec compose_subst_list (subsList : subst list) : subst =
    match subsList with
    | [] -> []
    | x::tail ->
        compose_subst x (compose_subst_list tail)

(* return the most general unifier between the two types provided
The function returns a substitution that applied to both t1 and t2 produces the
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
        // The substitution obtained from the unification of the left-hand-side
        // types, must be applied to the right-hand-side types before unifing them.
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

    | TyList(te1), TyList(te2) ->
        unify te1 te2

    // this case encompasses all those cases:
    // (TyName, TyArrow) | (TyName, TyTuple) | (TyArrow, TyTuple)
    | _ -> type_error "unify: type %s can't be unified with type %s" (pretty_ty t1) (pretty_ty t2)

(* get the set of free-type-variables in the type
The ftv of a type are all the type vars appearing on the type.
*)
let rec freevars_ty (t : ty) : tyvar Set =
    match t with
    | TyName _ -> Set.empty
    | TyArrow (t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun set t -> Set.union set (freevars_ty t)) Set.empty ts
    | TyList elemT -> freevars_ty elemT

(* get the set of free-type-variables in the scheme.
The ftv of a scheme are all the type vars appearing on the type minus the universally
quantified vars.
*)
let freevars_scheme (Forall (tvs, t)) : tyvar Set =
    Set.difference (freevars_ty t) (Set.ofList tvs)

(* get the set of free-type-variables in the environment.
The ftv of an env. are the sum of all the ftv of the scheme that contains.
*)
let rec freevars_env (env: scheme env) : tyvar Set =
    match env with
    | [] -> Set.empty
    | (_,s)::tail ->
        Set.union (freevars_scheme s) (freevars_env tail)

(* produce a new fresh type variable
*)
let mutable fresh_tyvar :tyvar = 0
let get_new_fresh_tyvar () : tyvar =
    fresh_tyvar <- fresh_tyvar + 1
    fresh_tyvar

(* scheme instantiation
Instantiate the given scheme in a type.
The ty-vars universally quantified appearing on the type are substituted with
new fresh ty-vars.
*)
let rec inst_scheme (s:scheme) : ty =
    match s with
    | Forall (uqv, t) ->
        let freeVars = freevars_ty t
        let toBeRefresh = Set.intersect freeVars (Set uqv)
        // build up a substitution mapping each of the type variable that needs to
        // be refresh, in a new fresh type type variable
        let sub = List.map (fun v -> (v, TyVar(get_new_fresh_tyvar ()))) (List.sort (Set.toList toBeRefresh))
        apply_subst_ty sub t

(* type generalization
Generalize the given type in the given environment.
The generalization produces a scheme.
In the schema are universally quantified all the type-variable that appear on
the type <t> but don't appear free on the env.
*)
let generalize_ty (env: scheme env) (t: ty) : scheme =
    // uqv = universally quantified vars
    let uqv = Set.difference (freevars_ty t) (freevars_env env)
    Forall (Set.toList uqv, t)


(* type inference
Compute the principal type of the given expression in the provided environment.
??? Check if the principal type is a concept associated only with an expression or
if also the env. is involved.

env = the scheme environment
e   = the expression of which to infer the type
returns:
- the principal type of <e> in <env>
- the substitution produced inferring the type of <e>
*)
let rec typeinfer_expr_expanded (uEnv : unionTy env) (env : scheme env) (e : expr) : ty * subst =
    let typeinfer_expr = typeinfer_expr_expanded uEnv
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
        // Starting from the head of the tuple I infer each expression.
        // For each field of the tuple I get a type and a substitution.
        // Every time I get a new substitution i have to do two things:
        //  - Apply it to the environment before inferring the following expressions.
        //  - Apply it to all the types I have previously obtained.
        //    Doing so, at the end all types are refined.
        let state = List.fold (fun state exp ->
            match state with
            // env = the current refined environment
            // s   = the current total composed substitution
            // ts  = the list of inferred types
            | (env:scheme env, s:subst, ts:ty list) ->
                let env = apply_subst_env s env
                let tExp, sExp = typeinfer_expr env exp
                // I apply what I have learned from this step, to all the types previously found.
                // I keep all the types refined.
                let ts = List.map (fun t -> apply_subst_ty sExp t) ts
                let s = compose_subst_list [sExp; s]
                // Adding an element in this way at the end of the list is not efficient.
                // Consider producing a list in the reverse order and reverting it after the fold end.
                // I keep it in this way because it is clearer.
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

    (* []
    *)
    | Empty (None) -> (TyVar (get_new_fresh_tyvar ()), [])

    (* [<ty>]
    *)
    | Empty (Some t) -> (TyList t, [])
    
    (* e1::e2
    If e1 is a value of type T, e2 is a value of type T List. This is ensured
    by typecheck of typeinfer.

    interesting expressions:
    1) 1::[]               : int list
    2) fun x -> x::[int]   : int -> int list
    *)
    | List (e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        let env = apply_subst_env s1 env
        let t2, s2 = typeinfer_expr env e2
        let t1 = apply_subst_ty s2 t1
        let su = unify t2 (TyList t1)
        let s = compose_subst_list [su; s2; s1]
        (apply_subst_ty su t2, s)

    (* IsEmpty(e)
    This expression can be implemented using the match construct like this:
    match e with _::_ -> false | [] -> true
    *)
    | IsEmpty (e) ->
        typeinfer_expr env (Match (e, "_", "_", Lit (LBool false), Lit (LBool true)))

    // TODO take care of the _ identifier
    (* match e1 with id1::id2 -> e2 | [] -> e3
    id1 and id2 can be the ignore identifier "_".

    interestin expressions:
    1) fun l -> match l with h::t -> h | [] -> 1                      : int list -> int
    2) fun l -> fun x -> match l with h::t -> h + 1 | [] -> x         : int list -> int -> int
    *)
    | Match (e_list, head, tail, e_full, e_empty) ->
        // create a new fresh type representing the type of the elements in the list
        let elemT = TyVar (get_new_fresh_tyvar ())
        let t1, s1 = typeinfer_expr env e_list
        let su = unify t1 (TyList elemT)
        let elemT = apply_subst_ty su elemT

        let s = compose_subst_list [su; s1]
        let env = apply_subst_env s env

        // add the tail-id bind to the env. only if tail-id is not "_"
        // add the head-id bind to the env. only if head-id is not "_"
        let env1 = prepend_if_not_ignore [(head, Forall ([], elemT)); (tail, Forall ([], TyList elemT))] env
        let tf, sf = typeinfer_expr env1 e_full
        let env = apply_subst_env sf env
        let te, se = typeinfer_expr env e_empty
        let tf = apply_subst_ty se tf
        let su = unify tf te
        let s = compose_subst_list [su; se; sf; s]
        (apply_subst_ty su tf, s)


    (* type <name> = c1 | c2 of t1 | ...
    tn = the type name
    constrs = list of possible Data Constructors for this type
    e = the rest of the program
    *)
    | Type (tn, constrs, e) ->
        // all constructor names must be distinct
        let ids = List.map (fun x -> match x with Constr (s, _) -> s) constrs
        let distinct = Set.ofList ids
        if ids.Length <> distinct.Count then
            type_error "repeated constructor name in type %s" tn

        // types names must be different to builtin types
        if List.exists (fun x -> x = tn) builtin_types then
            type_error "type %s can't be defined becuse it is a builtin type" tn

        // types names must be unique
        // constructors can be shadowed but should not be
        if List.exists (fun (tname, _) -> tn = tname) uEnv then
            type_error "redefinition of perviously defined type %s" tn
        
        // When I find a constructor with no parameters I put the constructor identifier
        // in the environ. binding it to the new type.
        //
        // When I find a constructor with parameters I put the constructor identifier
        // in the environ. binding it to a function type. This function has a domain
        // that is the type specified in the constructor, and a codomain that is the
        // new type. This function doesn't really exists but we don't care.
        let cfs = List.map (fun x ->
            match x with
            | Constr (cid, t) -> (cid, Forall ([],TyArrow (t, TyName tn)))) constrs
        let env = cfs @ env
        let uEnv = (tn, constrs)::uEnv
        typeinfer_expr_expanded uEnv env e

    (* match e with c1 -> e1 | c2 (x) -> e2 | ...
    e = the expression to match
    cases = the match mases

    TODO handle the ignore case _
    *)
    | MatchFull (e, cases)->
        // understand the type that <e> must have looking the constructors
        // apearing on match cases.
        let cs = List.map (fun x -> match x with (Deconstr (id, _), _) -> get_constr_by_name uEnv id) cases
        let ts = List.map (fun (tipe, _) -> tipe) cs
        if not (list_all_equals ts) then
            type_error "deconstructors of different types in match cases"
        let e_type = ts.Head // the type that expression <e> must have
        
        // get the list of constructors for that type
        let (_, t_constrs) = List.find (fun (x, _) -> x = e_type) uEnv
        if cs.Length <> t_constrs.Length then
            type_error "missing constructors in match cases"

        let t, s = typeinfer_expr env e
        let su = unify t (TyName e_type)
        let t = apply_subst_ty su t
        let s = compose_subst_list [su; s]
        let env = apply_subst_env s env

        match t with
        | TyName (tn) ->
            try
                let case_ty = List.map (fun (_, c) -> match c with Constr (_, cty) -> cty) cs
                let cases = List.zip case_ty cases

                let state = List.fold (fun state case ->
                    match state with
                    // env       = the current refined environment
                    // s         = the current total composed substitution
                    // commonTy  = the common return type of all the cases
                    | (env:scheme env, s:subst, commonTy:ty option) ->
                        match case with
                        // case_ty = the type of the variable for this case
                        // id      = the name of the type constructor
                        // var     = the name of the variable that must be put in the
                        //           env. before evaluating this case expression.
                        // e       = the expression of this case
                        | (case_ty:ty, (Deconstr (id:string, var:string), e:expr)) ->
                            let env = apply_subst_env s env
                            let tExp, sExp = typeinfer_expr ((var, Forall ([], case_ty))::env) e
                            
                            match commonTy with
                            // this happens in the first iteration
                            | None ->
                                (env, sExp, Some tExp)
                            | Some tipe ->
                                // I first apply the substitution I get typing this
                                // case to the common type of all the previous cases.
                                let tipe = apply_subst_ty sExp tipe
                                // Next I unify the type of this case with the common type
                                let su = unify tipe tExp
                                let t = apply_subst_ty su tExp // this is equal to: apply_subst_ty su tipe

                                // I compose in proper order all the substitutions I get
                                // in thi iteration.
                                let s = compose_subst_list [su; sExp; s]
                                (env, s, Some t)
                            ) (env, [], None) cases

                let (_, subRet, tyRetOpt) = state // retrieve the substitution and the commmon type
                match tyRetOpt with
                | Some tyRet ->
                    (tyRet, subRet)
                | None -> unexpected_error "impossible none type after match fold"
            with _ ->
                type_error "invalid deconstructors in match cases"
            
        | _ -> type_error "incompatible type in match expression %s" (pretty_ty t)

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

    | BinOp (e1, ("+." | "-." | "/." | "%." | "*." as op), e2) ->
        typeinfer_binop TyFloat TyFloat env e1 e2

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
    | UnOp ("-.", e) ->
        typeinfer_unop TyFloat TyFloat env e

    (* Int(e1) | Float(e1)
    *)
    | UnOp ("to_int", e) ->
        typeinfer_unop TyFloat TyInt env e
    | UnOp ("to_float", e) ->
        typeinfer_unop TyInt TyFloat env e

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
