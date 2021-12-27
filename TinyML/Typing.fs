(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

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

// this returns s3 = s2 o s1
// applying s3 is the same as applying s1 first and s2 next
let compose_subst (s2 : subst) (s1 : subst) : subst =
    // apply the substitution s2 to s1
    let newSub = List.map (fun (var, tipe) -> (var, apply_subst_ty s2 tipe)) s1
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
        if a = b then []
        else type_error "unify: base type %s can't be unified with type %s" a b
    | TyVar (a), _ ->
        [(a, t2)]
    | _, TyVar(a) ->
        [(a, t1)]
    | TyArrow(ta1,ta2), TyArrow(ta3,ta4) ->
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

// type instantiation
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
        try
            let _, s = List.find (fun (y, _) -> x = y) env
            (inst_scheme (s), [])
        with _ -> type_error "typeinfer_expr: use of undefined variable %s" x

    // TODO check if this is correct
    //| Lambda (x, Some t, e) ->
    //    let env1 = (x,Forall ([], t))::env
    //    // ety = expression type
    //    // esb = expression substitution
    //    let ety, esb = typeinfer_expr env1 e
    //    if t <> ety then type_error "typeinfer_expr: wrong lambda body type, expexted %s but got %s" (pretty_ty t) (pretty_ty ety)
    //    (TyArrow (t, ety), esb)

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

    | Let (x, None, e1, e2) ->
        // first i infeer the type if the bunded expression
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

    | IfThenElse (e1, e2, e3o) ->
        let t1, s1 = typeinfer_expr env e1
        let s = compose_subst_list [unify t1 TyBool; s1]
        let t2, s2 = typeinfer_expr (apply_subst_env s env) e2
        let s = compose_subst_list [s2; s]
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
    


// type checker
//
    
let rec typecheck_expr (env : ty env) (e : expr) : ty =
    match e with
    | Lit (LInt _) -> TyInt
    | Lit (LFloat _) -> TyFloat
    | Lit (LString _) -> TyString
    | Lit (LChar _) -> TyChar
    | Lit (LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Var x ->
        try
            let _, t = List.find (fun (y, _) -> x = y) env
            t
        with _ -> type_error "typecheck_expr: use of undefined variable %s" x

    | Lambda (x, None, e) -> unexpected_error "typecheck_expr: unannotated lambda is not supported"
    
    | Lambda (x, Some t1, e) ->
        let t2 = typecheck_expr ((x, t1) :: env) e
        TyArrow (t1, t2)

    | App (e1, e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1 with
        | TyArrow (l, r) ->
            if l = t2 then r 
            else type_error "wrong application: argument type %s does not match function domain %s" (pretty_ty t2) (pretty_ty l)
        | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty t1)

    | Let (x, tyo, e1, e2) ->
        let t1 = typecheck_expr env e1
        match tyo with
        | None -> ()
        | Some t -> if t <> t1 then type_error "type annotation in let binding of %s is wrong: exptected %s, but got %s" x (pretty_ty t) (pretty_ty t1)
        typecheck_expr ((x, t1) :: env) e2

    | IfThenElse (e1, e2, e3o) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyBool then type_error "if condition must be a bool, but got a %s" (pretty_ty t1)
        let t2 = typecheck_expr env e2
        match e3o with
        | None ->
            if t2 <> TyUnit then type_error "if-then without else requires unit type on then branch, but got %s" (pretty_ty t2)
            TyUnit
        | Some e3 ->
            let t3 = typecheck_expr env e3
            if t2 <> t3 then type_error "type mismatch in if-then-else: then branch has type %s and is different from else branch type %s" (pretty_ty t2) (pretty_ty t3)
            t2

    | Tuple es ->
        TyTuple (List.map (typecheck_expr env) es)

    | LetRec (f, None, e1, e2) ->
        unexpected_error "typecheck_expr: unannotated let rec is not supported"
        
    | LetRec (f, Some tf, e1, e2) ->
        let env0 = (f, tf) :: env
        let t1 = typecheck_expr env0 e1
        match t1 with
        | TyArrow _ -> ()
        | _ -> type_error "let rec is restricted to functions, but got type %s" (pretty_ty t1)
        if t1 <> tf then type_error "let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)
        typecheck_expr env0 e2

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> TyInt
        | TyFloat, TyFloat -> TyFloat
        | TyInt, TyFloat
        | TyFloat, TyInt -> TyFloat
        | _ -> type_error "binary operator expects two int operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        
    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> ()
        | _ -> type_error "binary operator expects two numeric operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyBool, TyBool -> ()
        | _ -> type_error "binary operator expects two bools operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (_, op, _) -> unexpected_error "typecheck_expr: unsupported binary operator (%s)" op

    | UnOp ("not", e) ->
        let t = typecheck_expr env e
        if t <> TyBool then type_error "unary not expects a bool operand, but got %s" (pretty_ty t)
        TyBool
            
    | UnOp ("-", e) ->
        let t = typecheck_expr env e
        match t with
        | TyInt -> TyInt
        | TyFloat -> TyFloat
        | _ -> type_error "unary negation expects a numeric operand, but got %s" (pretty_ty t)

    | UnOp (op, _) -> unexpected_error "typecheck_expr: unsupported unary operator (%s)" op

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
