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
        let rec check (l:tyvar list) = 
            match l with
            | [] -> ()
            | x::tail ->
                if List.contains x uql
                then unexpected_error "apply_subst_scheme: substitution of a universally quantified variable"
                check tail
        Forall (uql, apply_subst_ty sub tipe)

let rec apply_subst_env (sub : subst) (env : scheme env) : scheme env =
    match env with
    | [] -> []
    | (tvar, sch)::tail ->
        (tvar, apply_subst_scheme sub sch)::(apply_subst_env sub tail)

// this returns s3 = s1 o s2
// applying s3 is the same as applying s2 first and s1 next
let compose_subst (s1 : subst) (s2 : subst) : subst =
    let newSub = List.map (fun (var, tipe) -> (var, apply_subst_ty s1 tipe)) s2
    let rec compute_to_add (src:subst) : subst = 
        match src with
        | [] -> []
        | (tvar,t)::tail ->
            try
                List.find (fun  (x,_) -> x = tvar) s2 |> ignore
                unexpected_error "compose_subst: the two substitutions contains the same type variable %s" (pretty_ty (TyVar (tvar)))
            with _ ->
            (tvar,t)::(compute_to_add tail)
    newSub @ (compute_to_add s1)


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

let freevars_scheme (Forall (tvs, t)) =
    Set.difference (freevars_ty t) (Set.ofList tvs)


let mutable fresh_tyvar :tyvar = 0
let get_new_fresh_tyvar : tyvar =
    fresh_tyvar <- fresh_tyvar + 1
    fresh_tyvar

// type instantiation
let rec inst_scheme (s:scheme) : ty =
    match s with
    // uql = universally quantified list
    | Forall (uql, t) ->
        match t with
        | TyName (_) ->
            t
        | TyArrow (t1, t2) ->
            let s1 = Forall (uql, t1)
            let s2 = Forall (uql, t2)
            TyArrow (inst_scheme s1, inst_scheme s2)
        | TyTuple (ts) ->
            TyTuple (List.map (fun (x:ty) -> inst_scheme (Forall (uql, x))) ts)
        | TyVar (x) ->
            // if this type variable is globally quantified i have to refresh it
            if List.contains x uql
            then
                TyVar (get_new_fresh_tyvar)
            else
                t

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

    | Lambda (x, Some t, e) ->
        let env1 = (x,Forall ([], t))::env
        // ety = expression type
        // esb = expression substitution
        let ety, esb = typeinfer_expr env1 e
        if t <> ety then type_error "typeinfer_expr: wrong lambda body type, expexted %s but got %s" (pretty_ty t) (pretty_ty ety)
        (TyArrow (t, ety), esb)

    | Lambda (x, None, e) ->
        // par = parameter variable type
        let par = TyVar(fresh_tyvar)
        let env1 = (x,Forall ([], par))::env
        // ety = expression type
        // esb = expression substitution
        let ety, esb = typeinfer_expr env1 e
        (apply_subst_ty esb  (TyArrow (par, ety)), esb)

    | App (e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr (apply_subst_env s1 env) e2
        let retType = TyArrow (t2, TyVar (get_new_fresh_tyvar))
        let s3 = unify t1 retType
        let s3 = compose_subst s3 s2
        let s3 = compose_subst s3 s1
        (apply_subst_ty s3 retType, s3)

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr env e2
        let s3 = compose_subst (unify t1 TyInt) (unify t2 TyInt)
        let s3 = compose_subst s3 s2
        let s3 = compose_subst s3 s1
        (TyInt, s3)
        
    | _ -> failwith "not implement"


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
