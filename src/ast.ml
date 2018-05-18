open Lexing

type context = string list
type info = position * position

type rule_name = APP1 | APP2 | APPABS | APPFULL
type rule = Rule of rule_name * info

type metavar = string

type node = { term:term; pos:info }
and term =
    | MAbs of node
    | FreeId of node
    | BoundId of int
    | Lamb of node
    | App of node * node
    | Judgement of node * node
    | Metavar of metavar
    | MApp of node * node
    | Id of string
 
type iexpr = node * rule * expr list * info
and expr =
    | Expr of iexpr
    | AExpr of iexpr

(* Useful constructors *)

(* build a term with a dummy position *)
let dummy_info = (Lexing.dummy_pos, Lexing.dummy_pos)
let create_dum term = { term=term; pos=dummy_info }

let bound_id i = create_dum (BoundId i)
let app (t1, t2) = create_dum (App (t1, t2))
let judgement (t1, t2) = create_dum (Judgement (t1, t2))
let mabs t = create_dum (MAbs t)
let lamb t = create_dum (Lamb t)
let free_id f = create_dum (FreeId f)
let mapp (t1, t2) = create_dum (MApp (t1,t2))
let meta id = create_dum (Metavar id)

let labs t = lamb (mabs t)

let create_node t p = { term = t; pos = p }
let create_judg n1 n2 p =
    create_node (Judgement (n1, n2)) p
let create_labs n p =
    create_node (Lamb (create_node (MAbs n) p)) p
let create_app n1 n2 p =
    create_node (App (n1, n2)) p
let create_free_id id p =
    create_node (FreeId (create_node (Id id) p)) p
let create_bound_id id p =
    create_node (BoundId id) p

(* Print functions *)
let rec print_node isolate n =
    match n.term with
    (*| Lamb { term = MAbs n; } -> "\\." ^ (print_node false n)*)
    | Lamb n ->
            let s = "\\" ^ (print_node false n) in
            if isolate then ("(" ^ s ^ ")") else s
    | App (n1, n2) ->
            let s = (print_node true n1) ^ " " ^ (print_node true n2) in
            if isolate then ("(" ^ s ^ ")") else s
    | Judgement(n1, n2) ->
            (print_node false n1) ^ " -> " ^ (print_node false n2)
    | FreeId id ->
            "F(" ^ print_node false id ^ ")"
    | MApp (n1, n2) ->
            (print_node true n1) ^ "[" ^ (print_node false n2) ^ "]"
    | MAbs n -> "{" ^ (print_node false n) ^ "}"
    | BoundId id -> string_of_int id
    | Metavar id ->  id
    | Id id -> id

let rule_name = function
    | APP1 -> "E-App1"
    | APP2 -> "E-App2"
    | APPABS -> "E-AppAbs"
    | APPFULL -> "E-AppFull"

let print_info inf = 
    let b, e = inf in
    if b.pos_lnum = e.pos_lnum then
        "Line " ^ string_of_int b.pos_lnum ^
         ", characters " ^ string_of_int (b.pos_cnum - b.pos_bol + 1) ^
         "-" ^ string_of_int (e.pos_cnum - e.pos_bol)
    else
        "Line " ^ string_of_int b.pos_lnum ^
         " character " ^ string_of_int (b.pos_cnum - b.pos_bol + 1) ^
         " to line " ^ string_of_int e.pos_lnum ^
         " character " ^ string_of_int (e.pos_cnum - e.pos_bol)
