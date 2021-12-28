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

// this returns s3 = s2 o s1
// applying s3 is the same as applying s1 first and s2 next
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
        // TODO apply the substitution you get from the first unification to the
        // types you use on the second unification 
        compose_subst (unify ta1 ta3) (unify ta2 ta4)
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

let rec get_fresh_substitution (vars: tyvar list) : subst =
    match vars with
    |[] -> []
    |x::tail ->
        (x,TyVar(get_new_fresh_tyvar ()))::get_fresh_substitution tail

// scheme instantiation
let rec inst_scheme (s:scheme) : ty =
    match s with
    | Forall (uqv, t) ->
        let freeVars = freevars_ty t
        let toBeRefresh = Set.intersect freeVars (Set uqv)
        let sub = get_fresh_substitution (Set.toList toBeRefresh)
        apply_subst_ty sub t

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

    | Var x ->
        // lookup for the variable in the environment
        // return the instantiation of the associated scheme and an empty substitution
        try
            let _, s = List.find (fun (y, _) -> x = y) env
            (inst_scheme (s), [])
        with _ -> type_error "typeinfer_expr: use of undefined variable <%s>" x

    (* fun (x:<type>) -> e1
    <t> = type of the lambda parameter
    *)
    | Lambda (x, Some t, e1) ->
        let env1 = (x,Forall ([], t))::env
        let t1, s1 = typeinfer_expr env1 e1
        (TyArrow (t, t1), s1)

    | Lambda (x, None, e) ->
        // par = parameter variable type
        let par = TyVar(get_new_fresh_tyvar ())
        let env1 = (x,Forall ([], par))::env
        // ety = expression type
        // esb = expression substitution
        let ety, esb = typeinfer_expr env1 e
        (apply_subst_ty esb  (TyArrow (par, ety)), esb)

    | App (e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr (apply_subst_env s1 env) e2
        let retType = TyVar(get_new_fresh_tyvar ())
        let funType = TyArrow (t2, retType)
        let s3 = compose_subst_list [(unify funType t1); s2; s1]
        (apply_subst_ty s3 retType, s3)

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr env e2
        let s3 = compose_subst_list [(unify t1 TyInt); (unify t2 TyInt); s2; s1]
        (TyInt, s3)

    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr env e2
        let s3 = compose_subst_list [(unify t1 TyInt); (unify t2 TyInt); s2; s1]
        (TyBool, s3)

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr env e2
        let s3 = compose_subst_list [(unify t1 TyBool); (unify t2 TyBool); s2; s1]
        (TyBool, s3)

    | BinOp (_, op, _) -> unexpected_error "typeinfer_expr: unsupported binary operator (%s)" op
    
    | UnOp ("not", e) ->
        let t, s = typeinfer_expr env e
        let s = compose_subst_list [(unify t TyBool); s]
        (TyBool, s)
            
    | UnOp ("-", e) ->
        let t, s = typeinfer_expr env e
        let s = compose_subst_list [(unify t TyInt); s]
        (TyInt, s)

    | UnOp (op, _) -> unexpected_error "typeinfer_expr: typecheck_expr: unsupported unary operator (%s)" op

    (* let x:<type> = e1 in e2

    Interesting expressions (ie):
    1) fun y -> let x:int = y in x
    *)
    | Let (x, Some t, e1, e2) ->
        // first i infer the type of the bunded expression
        let t1, s1 = typeinfer_expr env e1
        // t1 can be a type variable (see ie. (1))
        let s = compose_subst_list [unify t1 t; s1]
        let env1 = (x,Forall ([], t))::env
        let t2, s2 = typeinfer_expr (apply_subst_env s env1) e2
        let s = compose_subst_list [s2; s]
        (apply_subst_ty s t2, s)

    (* let x = e1 in e2
    *)
    | Let (x, None, e1, e2) ->
        // first i infeer the type of the bunded expression
        let t1, s1 = typeinfer_expr env e1
        let sch = generalize_ty env t1 // generalize the resulted type producing a scheme
        let env1 = (x,sch)::env // enrich the environment with that scheme bounded to the variable name
        let t2, s2 = typeinfer_expr (apply_subst_env s1 env1) e2 // evaluate the let body in that environment
        let s3 = compose_subst_list [s2; s1]
        (apply_subst_ty s3 t2, s3)

    | Tuple es ->
        // first i get all the types and substitutions from inferring the type
        // for all the expressions in the tuple
        let tipesSubs = List.map (typeinfer_expr env) es
        let tipes = List.map (fun (t,s) -> t) tipesSubs // get the types list
        let subs = List.map (fun (t,s) -> s) tipesSubs // get the substitutions list
        let s = compose_subst_list subs
        (apply_subst_ty s (TyTuple tipes), s)

    (* if e1 then e2 [else e3]
    

    Interesting expressions (ie):
    1) fun x -> if x then x + 1 else x (must produce an error)
    *)
    | IfThenElse (e1, e2, e3o) ->
        let t1, s1 = typeinfer_expr env e1
        let s = compose_subst_list [unify t1 TyBool; s1]
        let env = apply_subst_env s env
        let t2, s2 = typeinfer_expr env e2
        let s = compose_subst_list [s2; s]
        let env = apply_subst_env s env
        match e3o with
        | None ->
            let s = compose_subst_list [unify t2 TyUnit; s]
            (TyUnit, s)
        | Some e3 ->
            let t3, s3 = typeinfer_expr env e3
            let s = compose_subst_list [unify t3 t2; s3; s]
            (apply_subst_ty s t2, s)

    | LetRec (f, None, e1, e2) ->
        let fType = TyArrow (TyVar (get_new_fresh_tyvar ()), TyVar (get_new_fresh_tyvar ()))
        let env1 = (f,Forall ([], fType))::env
        let t1, s1 = typeinfer_expr env1 e1
        let s = compose_subst_list [unify fType t1; s1]
        let env2 = (f,generalize_ty env (apply_subst_ty s t1))::env
        let t2, s2 = typeinfer_expr (apply_subst_env s env2) e2
        let s = compose_subst_list [s2; s]
        (apply_subst_ty s t2, s)

    | _ -> unexpected_error "typeinfer_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e