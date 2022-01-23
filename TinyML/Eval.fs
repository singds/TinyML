(*
* TinyML
* Eval.fs: evaluator
*)

module TinyML.Eval

open Ast
open Utility


(* evaluator
env = the value environment (binds names to values)
e   = the expr. to eval.
returns the value of <e>
*)
let rec eval_expr (env : value env) (e : expr) : value =
    match e with
    (* 1, 2, true, false, unit
    *)
    | Lit lit -> VLit lit

    (* foo | x | y
    An expression can be a variable name.
    To evaluate a variable name we look into the env. and get the value bound to
    that name.
    *)
    | Var x ->
        try
            let _, v = List.find (fun (y, _) -> x = y) env
            v
        with _ ->
            unexpected_error "eval_expr: the variable <%s> is not available in the environment" (pretty_expr e)

    (* fun x -> e
    A lambda simply produces a closure that is a kind of value.
    The closure bring along the env. in which the lambda is defined, the name
    of the lambda parameter and the body of the lambda.
    *)
    | Lambda (x, _, e) -> Closure (env, x, e)

    | App (e1, e2) ->
        let v1 = eval_expr env e1
        let v2 = eval_expr env e2
        match v1 with
        | Closure (env1, x, e) -> eval_expr ((x, v2) :: env1) e
        | RecClosure (env1, f, x, e) -> eval_expr ((x, v2) :: (f, v1) :: env1) e
        | _ -> unexpected_error "eval_expr: non-closure in left side of application: %s" (pretty_value v1)
       
    (* if e1 then e2
    This always evaluates to Unit.
    The fact that e2 evaluates to Unit is verified by the type-checker or the type-inference.
    *)
    | IfThenElse (e1, e2, None) ->
        let v1 = eval_expr env e1
        match v1 with
        | VLit (LBool true) -> eval_expr env e2
        | VLit (LBool false) -> VLit LUnit
        | _ -> unexpected_error "eval_expr: non-boolean in if guard: %s" (pretty_value v1)
    
    (* if e1 then e2 else e3
    The type-checker or the type-inference enforces the same type for e2 and e2.
    *)
    | IfThenElse (e1, e2, Some e3) ->
        let v1 = eval_expr env e1 // first evaluate the guard expression
        eval_expr env (match v1 with
                       | VLit (LBool true) -> e2
                       | VLit (LBool false) -> e3
                       | _ -> unexpected_error "eval_expr: non-boolean in if guard: %s" (pretty_value v1)
                       )

    (* let x = e1 in e2 | let (x:<type>) = e1 in e2
    *)
    | Let (x, _, e1, e2) -> 
        let v1 = eval_expr env e1
        eval_expr ((x, v1) :: env) e2

    (* let (x1,..,xn) = e1 in e2 | let (_,x2,..,xn) = e1 in e2
    *)
    | LetTuple (ns, e1, e2) ->
        let v1 = eval_expr env e1
        match v1 with
        | VTuple(vs) ->                 // vs = list of values inside the tuple
            let pairs = List.zip ns vs  // bind each name with the corresponding value
            let pairs = List.filter (fun (n,v) -> n <> "_") pairs
            eval_expr (pairs @ env) e2
        | _ -> unexpected_error "eval_expr: non-tuple in let tuple decomposition: %s" (pretty_value v1)

    (* let rec f = e1 in e2
    <e1> must be a lambda expression an this is enforced by the typeinference.
    *)
    | LetRec (f, _, e1, e2) ->
        // Evaluating <e1> I get a closure.
        // The eval. of <e1> does not do something special, simply boxes the lambda.
        let v1 = eval_expr env e1
        let vc = (
            match v1 with
            // rebox the function closure in a recursive closure
            | Closure (env1, x, e) -> RecClosure (env1, f, x, e)
            | _ -> unexpected_error "eval_expr: expected closure in rec binding but got: %s" (pretty_value v1)
        )
        // Evaluate the rest of the body in an environment enriched with
        // the RecClosure bound to the name <f>
        eval_expr ((f,vc)::env) e2

    (* let (x1,..,xn) = e1 in e2
    Tuple decomposition. To access the single values of a tuple you can use the
    LetTuple expression.
    *)
    | Tuple (es) -> // simply evaluate all the expressions in the tuple
        VTuple (List.map (eval_expr env) es)

    (* e1; e2
    *)
    | Seq (e1, e2) ->
        let _ = eval_expr env e1
        eval_expr env e2

    (* [] | [<ty>]
    *)
    | Empty (_) -> VEmpty
    
    (* e1::e2
    If e1 is a value of type T, e2 is a value of type T List. This is ensured
    by typecheck of typeinfer.
    *)
    | List (e1, e2) ->
        let v1 = eval_expr env e1
        let v2 = eval_expr env e2
        VList (v1, v2)

    (* IsEmpty(e)
    This expression can be implemented using the match construct like this:
    match e with _::_ -> false | [] -> true
    *)
    | IsEmpty (e) ->
        eval_expr env (Match (e, "_", "_", Lit (LBool false), Lit (LBool true)))

    (* match e1 with id1::id2 -> e2 | [] -> e3
    e2 is the expression that is evaluated when the list is not empty.
    e3 is evaluated when the list is empty.
    id1 and id2 can be the ignore identifier "_".
    *)
    | Match (e_list, head, tail, e_full, e_empty) ->
        let v_list = eval_expr env e_list
        match v_list with
        | VEmpty ->
            eval_expr env e_empty
        | VList (vh, vt) ->
            // add the head-id bind to the env. only if head-id is not "_"
            // add the tail-id bind to the env. only if tail-id is not "_"
            let env = prepend_if_not_ignore [(head, vh); (tail, vt)] env
            eval_expr env e_full
        | _ -> unexpected_error "wrong value in match construct: expected VList or VEmpty but got %s" (pretty_value v_list)

    //(* type <name> = c1 | c2 of t1 | ...
    //name = the type name
    //constrs = list of possible Data Constructors for this type
    //e = the rest of the program
    //*)
    //| NewTy (name, constrs, e) ->
    //    let cfs = List.map  (fun x ->
    //        match x with
    //        | Constr (cid :string, None) ->
    //            // Add to the environ. a closure (a lambda) with name <cid>
    //            // <cid> = the constructor id
    //            // That closure, when called, produces a <custo type value>.
    //            // The custom type value brings along the name of the constructor
    //            // and the value parameters of the constructor.

    //            // let <cid> = fun x -> new (<cid>, ())
    //            (cid, Closure ([], "x", TyInst (cid, Lit (LUnit))))

    //        | Constr (cid :string, Some t) ->
    //            // let <cid> = fun x -> new (<cid>, x)
    //            (cid, Closure ([], "x", TyInst (cid, Var "x")))
    //                        ) constrs
    //    let env = cfs @ env
    //    eval_expr env e

    //(*
    //cid = constructor id
    //*)
    //| TyInst (cid, e) ->
    //    let v = eval_expr env e
    //    VNewTy (cid, v)

    //(* match e with c1 -> e1 | c2 (x) -> e2 | ...
    //e = the expression to match
    //cases = the match mases

    //TODO handle the ignore case _
    //TODO handle unordered match
    //*)
    //| MatchFull (e, cases)->
    //    let v = eval_expr env e
    //    // TODO check the type corrispondence ????

    //    match v with
    //    | VNewTy (cid, v) ->
    //        if cases.Length > constrs.Length then
    //            type_error "too many cases in match for type %s" (pretty_ty t)
    //        if cases.Length < constrs.Length then
    //            type_error "incomplete match for type %s" (pretty_ty t)
    //        let cases = List.zip cases constrs
    //        let tipes = List.map    (fun case ->
    //            match case with
    //            | ((Deconstr (n1, d1), e), Constr (n2, d2)) ->
    //                if n1 <> n2 then
    //                    type_error "deconstructor %s does not match the constructor %s" n1 n2
    //                match d1,d2 with
    //                // match a constructor with no parameters
    //                | None, None ->
    //                    typecheck_expr env e
    //                // match a constructor with parameters
    //                | Some idl, Some t ->
    //                    match t with
    //                    // constructor with multiple parameters
    //                    | TyTuple tl ->
    //                        if idl.Length <> tl.Length then
    //                            type_error "in %s deconstructor: ids does not match constructor parameters" n1
    //                        let env = (List.zip idl tl) @ env
    //                        typecheck_expr env e
    //                    // constructor with single parameter
    //                    | _ ->
    //                        if idl.Length <> 1 then
    //                            type_error "in %s deconstructor: ids qunatity does not match constructor parameters quantity" n1
    //                        let env = (idl.Head, t) :: env
    //                        typecheck_expr env e
    //                | _, _ ->
    //                    type_error "deconstructor mismatch"
    //                                ) cases
    //        let commonTy = tipes.Head
    //        let tyOk = List.fold (fun state x -> state && (x = commonTy)) true tipes
    //        if tyOk <> true then type_error "incompatible return types in match construct (%s)" (pretty_tupled pretty_ty tipes)
    //        commonTy
            
    //    | _ -> type_error "the expression %s has type %s that can't be matched" (pretty_expr e) (pretty_ty t)
    

    // thise binary operators support only integers
    // "+" | "-" | "/" | "%" | "*"
    | BinOp (e1, "+", e2) -> binop_int (+) env e1 e2 LInt
    | BinOp (e1, "-", e2) -> binop_int (-) env e1 e2 LInt
    | BinOp (e1, "/", e2) -> binop_int (/) env e1 e2 LInt
    | BinOp (e1, "%", e2) -> binop_int (%) env e1 e2 LInt
    | BinOp (e1, "*", e2) -> binop_int (*) env e1 e2 LInt

    // thise binary operators support only floats
    // "+" | "-" | "/" | "%" | "*"
    | BinOp (e1, "+.", e2) -> binop_float_to_float (+) env e1 e2
    | BinOp (e1, "-.", e2) -> binop_float_to_float (-) env e1 e2
    | BinOp (e1, "/.", e2) -> binop_float_to_float (/) env e1 e2
    | BinOp (e1, "%.", e2) -> binop_float_to_float (%) env e1 e2
    | BinOp (e1, "*.", e2) -> binop_float_to_float (*) env e1 e2

    // int binary operators
    // "<" | "<=" | ">" | ">=" | "=" | "<>"
    | BinOp (e1, "<" , e2) -> binop_int (<)  env e1 e2 LBool
    | BinOp (e1, "<=", e2) -> binop_int (<=) env e1 e2 LBool
    | BinOp (e1, ">" , e2) -> binop_int (>)  env e1 e2 LBool
    | BinOp (e1, ">=", e2) -> binop_int (>=) env e1 e2 LBool
    | BinOp (e1, "=" , e2) -> binop_int (=)  env e1 e2 LBool
    | BinOp (e1, "<>", e2) -> binop_int (<>) env e1 e2 LBool

    // boolean binary operators
    | BinOp (e1, "and", e2) -> binop_bool (&&) env e1 e2
    | BinOp (e1, "or", e2) -> binop_bool (||) env e1 e2

    // unary operators
    | UnOp ("not", e) ->
        let v = eval_expr env e
        match v with
        | VLit (LBool b) -> VLit (LBool (not b))
        | _ -> unexpected_error "eval_expr: non-bool in not operator <%s>" (pretty_value v)

    | UnOp ("-", e)
    | UnOp ("-.", e) ->
        let v = eval_expr env e
        match v with
        | VLit (LInt x) -> VLit (LInt (-x))
        | VLit (LFloat x) -> VLit (LFloat (-x))
        | _ -> unexpected_error "eval_expr: incompatible value in minus operator <%s>" (pretty_value v)

    // conversion operators
    | UnOp ("to_int", e)
    | UnOp ("to_float", e) ->
        let v = eval_expr env e
        match v with
        | VLit (LInt b) -> VLit (LFloat (float b))
        | VLit (LFloat b) -> VLit (LInt (int b))
        | _ -> unexpected_error "eval_expr: incompatible value in conversion operator <%s>" (pretty_value v)

    | _ -> unexpected_error "eval_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e

// This is a polymorphic recursive function
// A polymorhic recursive function must be fully annotated in F#
and binop_int<'a> (op:int->int->'a) (env:value env) (e1:expr) (e2:expr) (litResult:'a->lit) : value =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1,v2 with
    | VLit (LInt a), VLit (LInt b) -> VLit (litResult (op a b))
    | _ -> unexpected_error "eval_expr: illegal operands in binary operator: %s <op> %s" (pretty_value v1) (pretty_value v2)

and binop_bool op env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1,v2 with
    | VLit (LBool a), VLit (LBool b) -> VLit (LBool (op a b))
    | _ -> unexpected_error "eval_expr: illegal operands in binary operator: %s <op> %s" (pretty_value v1) (pretty_value v2)

and binop_float_to_float op env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1,v2 with
    | VLit (LFloat a), VLit (LFloat b) -> VLit (LFloat (op a b))
    | _ -> unexpected_error "eval_expr: illegal operands in binary operator: %s <op> %s" (pretty_value v1) (pretty_value v2)
