(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.TypeChecking

open Ast
open Utility

let mutable new_ty_id :tyvar = 0
let get_new_fresh_ty_id () : tyvar =
    new_ty_id <- new_ty_id + 1
    new_ty_id

let get_const_list (uEnv: unionTy env) =
    List.fold (fun s (tyname, c_list) ->
        let cl = List.map (fun c_single -> (tyname, c_single)) c_list
        s @ cl
    ) [] uEnv

// uEnv = union type environment
// cn = constructor name
let get_constr_by_name (uEnv: unionTy env) (cn: string) =
    let allconstr = get_const_list uEnv
    let c = List.find   (fun x ->
        match x with (tn, Constr (id, _)) -> id = cn
                        ) allconstr
    c

(* type checker
env = the type environment
e   = the expression of which you want to check the type
returns the type of <e>
*)
let rec typecheck_expr_expanded (uEnv : unionTy env) (env : ty env) (e : expr) : ty =
    let typecheck_expr = typecheck_expr_expanded uEnv
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
        with _ -> type_error "use of undefined variable %s" x

    | Lambda (x, None, e) -> unexpected_error "unannotated lambda is not supported"
    
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

    | LetTuple (ns, e1, e2) ->
        let t1 = typecheck_expr env e1
        match t1 with
        | TyTuple(ts) ->
            let actualNames = List.filter (fun x -> x <> "_") ns
            let distinct = List.distinct actualNames
            if distinct.Length < actualNames.Length then
                type_error "repeated identifier in tuple decomposition (%s)" (pretty_tupled_string_list ns)
            if ts.Length <> ns.Length then
                type_error "expecting a tuple with %d elements in decomposition (%s) but got %d elements with type %s"
                    ns.Length (pretty_tupled_string_list ns) ts.Length (pretty_ty t1)
            let pairs = List.zip ns ts
            let pairs = List.filter (fun (n,v) -> n <> "_") pairs
            typecheck_expr (pairs @ env) e2
        | _ -> type_error "expecting a tuple in decomposition (%s) but got type %s"
                    (pretty_tupled_string_list ns) (pretty_ty t1)

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

    | Seq (e1, e2) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyUnit then type_error "left side of the ; operator does not match Unit type"
        typecheck_expr env e2

    // list specific expressions
    | Empty (None) ->
        type_error "unannotated empty list is not supported"
    
    | Empty (Some t) ->
        TyList t
    
    | List (e1, e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t2 with
        | TyList t ->
            if t <> t1 then
                type_error "wrong types in :: operator, %s::%s" (pretty_ty t1) (pretty_ty t2)
            t2
        | _ -> type_error "left side of the :: operator is not a list"

    | IsEmpty (e) ->
        let t = typecheck_expr env e
        match t with
        | TyList _ ->
            TyBool
        | _ -> type_error "IsEmpty expected type bool but got %s" (pretty_ty t)

    (*
    id1 and id2 can be the ignore identifier "_".
    *)
    | Match (e_list, head, tail, e_full, e_empty) ->
        let t_list = typecheck_expr env e_list
        match t_list with
        | TyList t ->
            // add the tail-id bind to the env. only if tail-id is not "_"
            // add the head-id bind to the env. only if head-id is not "_"
            let env1 = prepend_if_not_ignore [(head, t); (tail, t_list)] env
            let t_full = typecheck_expr env1 e_full
            let t_empty = typecheck_expr env e_empty
            if t_full <> t_empty then
                type_error "type mismatch in match with: full list case has type %s while empty list case has type %s" (pretty_ty t_full) (pretty_ty t_empty)
            t_full
        | _ -> type_error "match expected a list type but got %s" (pretty_ty t_list)

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
        
        // When I find a constructor with no parameters I put the constructor identifier
        // in the environ. binding it to the new type.
        //
        // When I find a constructor with parameters I put the constructor identifier
        // in the environ. binding it to a function type. This function has a domain
        // that is the type specified in the constructor, and a codomain that is the
        // new type. This function doesn't really exists but we don't care.
        let cfs = List.map (fun x ->
            match x with
            | Constr (cid, t) -> (cid, TyArrow (t, TyUnion tn))) constrs
        let env = cfs @ env
        let uEnv = (tn, constrs)::uEnv
        typecheck_expr_expanded uEnv env e

    (* match e with c1 -> e1 | c2 (x) -> e2 | ...
    e = the expression to match
    cases = the match mases

    TODO handle the ignore case _
    TODO handle unordered match
    *)
    | MatchFull (e, cases)->

        /// none of the case deconstructor identifiers can be in the environment
        //let ids = List.map (fun (Deconstr (id, _), _) -> id) cases
        //let defined = List.map (fun id -> List.exists (fun (x, _) -> x = id) env) ids
        //let allUndef = List.fold (fun s x -> s && x) true defined
        //if allUndef <> true
        //    type_error "error"

        let t = typecheck_expr env e
        match t with
        | TyUnion (tn) ->
            try
                let cs = List.map (fun x -> match x with (Deconstr (id, _), _) -> get_constr_by_name uEnv id) cases
                let ts = List.map (fun (tipe, _) -> tipe) cs
                if not (list_all_equals ts) then
                    type_error "deconstructors of different types in match cases"
                
                let (_, ut_cs) = List.find (fun (x, _) -> x = ts.Head) uEnv
                if cs.Length <> ut_cs.Length then
                    type_error "missing constructors in match cases"

                let case_ty = List.map (fun (_, c) -> match c with Constr (_, cty) -> cty) cs
                let cases = List.zip case_ty cases
                let case_tipes = List.map   (fun (cty, (deconstr, e)) ->
                    match deconstr with
                    | Deconstr (_, tyid) -> typecheck_expr ((tyid, cty)::env) e
                                            ) cases
                if not (list_all_equals case_tipes) then
                    type_error "incompatible return types in match cases"
                case_tipes.Head
            with _ ->
                type_error "invalid deconstructors in match cases"
            
        | _ -> type_error "the expression %s has type %s that can't be matched" (pretty_expr e) (pretty_ty t)

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> TyInt
        | _ -> type_error "binary operator expects two int operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)

    | BinOp (e1, ("+." | "-." | "/." | "%." | "*." as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyFloat, TyFloat -> TyInt
        | _ -> type_error "binary operator expects two float operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        
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

    | BinOp (_, op, _) -> unexpected_error "unsupported binary operator (%s)" op

    | UnOp ("not", e) ->
        let t = typecheck_expr env e
        if t <> TyBool then type_error "unary not expects a bool operand, but got %s" (pretty_ty t)
        TyBool
            
    | UnOp ("-", e) ->
        let t = typecheck_expr env e
        match t with
        | TyInt -> TyInt
        | _ -> type_error "unary negation <-> expects a integer operand, but got %s" (pretty_ty t)
    | UnOp ("-.", e) ->
        let t = typecheck_expr env e
        match t with
        | TyFloat -> TyFloat
        | _ -> type_error "unary negation <-.> expects a float operand, but got %s" (pretty_ty t)

    // conversion operators
    | UnOp ("to_int", e) ->
        let t = typecheck_expr env e
        match t with
        | TyFloat -> TyInt
        | _ -> type_error "float to int conversion expects an integer operand, but got %s" (pretty_ty t)
    | UnOp ("to_float", e) ->
        let t = typecheck_expr env e
        match t with
        | TyFloat -> TyInt
        | _ -> type_error "int to float conversion expects a float operand, but got %s" (pretty_ty t)

    | UnOp (op, _) -> unexpected_error "unsupported unary operator (%s)" op

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
