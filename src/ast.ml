open Lexing

type info = position * position

type rule_name = APP1 | APP2 | APPABS | APPFULL | LETREC
type rule = Rule of rule_name * info

type metavar = int
type node = { term:term; pos:info }
and term =
    | Metavar of metavar * node list
    (* Abstractions *)
    | Mabs of node
    | Labs of node
    | LetRec of node * node
    (* Constructors *)
    | App of node * node
    | Judgement of node * node
    | FreeId of node
    | BoundId of int
    (* atomic *)
    | AStr of string

type context =
    | Proj of int
    | CStr of string
    | Cabs of metavar
    | CLabs of metavar
    | CLetRec of metavar * metavar
    | CFreeId of metavar
    | CApp of metavar * metavar
    | CJudgment of metavar * metavar
    (* For a closed term *)
    | Closed of node

type sub = { met:metavar; sub:context }

(* An expression can be nested into abstractions *)
type expr =
    | Expr of node * rule * expr list * info
    | AExpr of expr * info


(* Constraint type: stands for one equation to match, right-hand side has
 * to be closed, otherwise NonMatchingProblem could be raise *)
type constr = node * node

(* Useful constructors *)

(* build a term with a dummy position *)
let dummy_info = (Lexing.dummy_pos, Lexing.dummy_pos)
let create_dum term = { term=term; pos=dummy_info }

let bound_id i = create_dum (BoundId i)
let app (t1, t2) = create_dum (App (t1, t2))
let judgement (t1, t2) = create_dum (Judgement (t1, t2))
let mabs t = create_dum (Mabs t)
let labs t = create_dum (Labs t)
(*let lamb t = create_dum (Lamb t)*)
let free_id f = create_dum (FreeId f)
let astr s = create_dum (AStr s)
let app (t1, t2) = create_dum (App (t1, t2))
let letrec (t1, t2) = create_dum (LetRec (t1, t2))
let meta (id, par) = create_dum (Metavar (id, par))
let fmeta id = create_dum (Metavar (id, []))

let create_node t p = { term = t; pos = p }
let create_judg n1 n2 p =
    create_node (Judgement (n1, n2)) p
let create_labs n p =
    create_node (Labs n) p
let create_letrec n1 n2 p =
    create_node (LetRec (n1, n2)) p
let create_app n1 n2 p =
    create_node (App (n1, n2)) p
let create_free_id id p =
    create_node (FreeId (create_node (AStr id) p)) p
let create_bound_id id p =
    create_node (BoundId id) p

let rule_name = function
    | APP1 -> "E-App1"
    | APP2 -> "E-App2"
    | APPABS -> "E-AppAbs"
    | APPFULL -> "E-AppFull"
    | LETREC -> "E-LetRec"

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
