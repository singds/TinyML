(*
* TinyML
* Ast.fs: abstract syntax tree
*)

module TinyML.Ast

open Printf

// errors
//

exception SyntaxError of string * FSharp.Text.Lexing.LexBuffer<char>
exception TypeError of string
exception UnexpectedError of string

let throw_formatted exnf fmt = ksprintf (fun s -> raise (exnf s)) fmt

let unexpected_error fmt = throw_formatted UnexpectedError fmt


// AST type definitions
//

type tyvar = int

type ty =
    | TyName of string
    | TyArrow of ty * ty
    | TyVar of tyvar
    | TyTuple of ty list
    | TyList of ty  // a list which contains elements of type <ty>
    | TyUnion of string

// pseudo data constructors for literal types
let TyFloat = TyName "float"
let TyInt = TyName "int"
let TyChar = TyName "char"
let TyString = TyName "string"
let TyBool = TyName "bool"
let TyUnit = TyName "unit"

// active pattern for literal types
let private (|TyLit|_|) name = function
    | TyName s when s = name -> Some ()
    | _ -> None

let (|TyFloat|_|) = (|TyLit|_|) "float"
let (|TyInt|_|) = (|TyLit|_|) "int"
let (|TyChar|_|) = (|TyLit|_|) "char"
let (|TyString|_|) = (|TyLit|_|) "string"
let (|TyBool|_|) = (|TyLit|_|) "bool"
let (|TyUnit|_|) = (|TyLit|_|) "unit"


type scheme = Forall of tyvar list * ty

type lit = LInt of int
         | LFloat of float
         | LString of string
         | LChar of char
         | LBool of bool
         | LUnit 

type constr = Constr of string * ty
type unionTy = constr list
// a deconstructor: the constructor name plus an identifier
type deconstr = Deconstr of string * string

type binding = bool * string * ty option * expr    // (is_recursive, id, optional_type_annotation, expression)
and expr = 
    | Lit of lit
    | Lambda of string * ty option * expr
    | App of expr * expr
    | Var of string
    | LetIn of binding * expr
    | IfThenElse of expr * expr * expr option
    | Tuple of expr list
    | BinOp of expr * string * expr
    | UnOp of string * expr
    | LetTuple of string list * expr * expr
    | Seq of expr * expr // sequence expression, that is the ; operator
    | Empty of ty option // the empty list can be annotate
    | List of expr * expr // head element and list tail
    | IsEmpty of expr // to check if the list is empty
    | Match of expr * string * string * expr * expr // list, head, tail, non-empty body, empty body

    | Type of string * constr list * expr
    | MatchFull of expr * (deconstr * expr) list
    | TyInst of string * expr
   
let fold_params parms e0 = 
    List.foldBack (fun (id, tyo) e -> Lambda (id, tyo, e)) parms e0

let (|Let|_|) = function 
    | LetIn ((false, x, tyo, e1), e2) -> Some (x, tyo, e1, e2)
    | _ -> None
    
let (|LetRec|_|) = function 
    | LetIn ((true, x, tyo, e1), e2) -> Some (x, tyo, e1, e2)
    | _ -> None

type 'a env = (string * 'a) list  

type value =
    | VLit of lit
    | VTuple of value list
    | Closure of value env * string * expr
    | RecClosure of value env * string * string * expr
    | VEmpty // the empty list
    | VList of value * value // the first value is an element, the second value is a list
    | VUnion of string * value

type interactive = IExpr of expr | IBinding of binding

type subst = (tyvar * ty) list

// pretty printers
//

// utility function for printing lists by flattening strings with a separator 
let rec flatten p sep es =
    match es with
    | [] -> ""
    | [e] -> p e
    | e :: es -> sprintf "%s%s %s" (p e) sep (flatten p sep es)

// print pairs within the given env using p as printer for the elements bound within
let pretty_env p env = sprintf "[%s]" (flatten (fun (x, o) -> sprintf "%s=%s" x (p o)) ";" env)

// print any tuple given a printer p for its elements
// adds the "," separator between the printed elements
let pretty_tupled p l = flatten p ", " l
// print the string list separating the elements with the "," separator
let pretty_tupled_string_list l = pretty_tupled (sprintf "%s") l
// adds the "|" separator between the printed elements
let pretty_match p l = flatten p " | " l

let rec pretty_ty t =
    match t with
    | TyName s -> s
    | TyArrow (t1, t2) -> sprintf "%s -> %s" (pretty_ty t1) (pretty_ty t2)
    | TyVar n -> sprintf "'%d" n
    | TyTuple ts -> sprintf "(%s)" (pretty_tupled pretty_ty ts)
    | TyList elemT -> sprintf "%s list" (pretty_ty elemT)

let pretty_lit lit =
    match lit with
    | LInt n -> sprintf "%d" n
    | LFloat n -> sprintf "%g" n
    | LString s -> sprintf "\"%s\"" s
    | LChar c -> sprintf "%c" c
    | LBool true -> "true"
    | LBool false -> "false"
    | LUnit -> "()"

let pretty_constr constr =
    match constr with
    | Constr (name, t) -> sprintf "%s of %s" name (pretty_ty t)

let rec pretty_expr e =
    match e with
    | Lit lit -> pretty_lit lit

    | Lambda (x, None, e) -> sprintf "fun %s -> %s" x (pretty_expr e)
    | Lambda (x, Some t, e) -> sprintf "fun (%s : %s) -> %s" x (pretty_ty t) (pretty_expr e)
    
    | App (e1, e2) -> pretty_app e

    | Var x -> x

    | Let (x, None, e1, e2) ->
        sprintf "let %s = %s in %s" x (pretty_expr e1) (pretty_expr e2)

    | Let (x, Some t, e1, e2) ->
        sprintf "let %s : %s = %s in %s" x (pretty_ty t) (pretty_expr e1) (pretty_expr e2)

    | LetRec (x, None, e1, e2) ->
        sprintf "let rec %s = %s in %s" x (pretty_expr e1) (pretty_expr e2)

    | LetRec (x, Some tx, e1, e2) ->
        sprintf "let rec %s : %s = %s in %s" x (pretty_ty tx) (pretty_expr e1) (pretty_expr e2)

    | IfThenElse (e1, e2, e3o) ->
        let s = sprintf "if %s then %s" (pretty_expr e1) (pretty_expr e2)
        match e3o with
        | None -> s
        | Some e3 -> sprintf "%s else %s" s (pretty_expr e3)
        
    | Tuple es ->        
        sprintf "(%s)" (pretty_tupled pretty_expr es)

    | BinOp (e1, op, e2) -> sprintf "%s %s %s" (pretty_expr e1) op (pretty_expr e2)
    
    | UnOp (op, e) -> sprintf "%s %s" op (pretty_expr e)

    | LetTuple (l, e1, e2) -> sprintf "let (%s) = %s in %s" (pretty_tupled_string_list l) (pretty_expr e1) (pretty_expr e2)

    | Seq (e1, e2) -> sprintf "%s; %s" (pretty_expr e1) (pretty_expr e2)

    // list specific expressions
    | Empty (None) -> "[]"
    
    | Empty (Some t) -> sprintf "[%s]" (pretty_ty t)
    
    | List (head, tail) -> sprintf "%s::%s" (pretty_expr head) (pretty_expr tail)
    
    | IsEmpty (e) -> sprintf "IsEmpty (%s)" (pretty_expr e)
    
    | Match (l, h, t, e_full, e_empty) ->
        sprintf "match %s with %s::%s -> %s | [] -> %s" (pretty_expr l) h t (pretty_expr e_full) (pretty_expr e_empty)

    | Type (n, cl, e) -> // name, list of constructors, expr.
        sprintf "type %s = %s in %s" n (pretty_match pretty_constr cl) (pretty_expr e)

    | MatchFull (e, ml) -> // exp., match list
        sprintf "match %s with %s" (pretty_expr e) (pretty_match pretty_case ml)
        
    | _ -> unexpected_error "pretty_expr"

and pretty_app expr =
    match expr with
    | App (e1, e2) ->
        let stringE1 =
            match e1 with
            | Var _ 
            | Lit _ -> pretty_expr e1
            | App (_, _) -> pretty_app e1
            | _ -> sprintf "(%s)" (pretty_expr e1)
        let stringE2 =
            match e2 with
            | Var _ 
            | Lit _ -> pretty_expr e2
            | _ -> sprintf "(%s)" (pretty_expr e2)
        sprintf "%s %s" stringE1 stringE2
    | _ -> unexpected_error "pretty_app: the expression is not an application"

and pretty_case case =
    match case with
    | (Deconstr (n, id), e) ->
        sprintf "%s (%s) -> %s" n id (pretty_expr e)

let rec pretty_value v =
    match v with
    | VLit lit -> pretty_lit lit

    | VTuple vs -> pretty_tupled pretty_value vs

    | Closure (env, x, e) -> sprintf "<|%s;%s;%s|>" (pretty_env pretty_value env) x (pretty_expr e)
    
    | RecClosure (env, f, x, e) -> sprintf "<|%s;%s;%s;%s|>" (pretty_env pretty_value env) f x (pretty_expr e)

    | VEmpty -> "[]"

    // TODO pretty print a value that is a list
    | VList (head, tail) -> ""

let pretty_subs (subList:subst) =
    let print_one_sub (tvar, t) = sprintf "'%d\%s" tvar (pretty_ty t)
    sprintf "(%s)" (pretty_tupled_string_list (List.map (fun sub -> print_one_sub sub) subList))

let rec pretty_scheme (s:scheme) =
    match s with
    | Forall (uql, t) ->
        let univ_quant_str = List.fold (fun state var -> sprintf "%s,'%d" state var) "" uql
        sprintf "forall %s.%s" univ_quant_str (pretty_ty t)
