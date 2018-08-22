open Lexing

type info = position * position

type rule_name = APP1 | APP2 | APPABS | APPFULL | LETREC
type rule = rule_name * info

type metavar = int
type node = { term:term; pos:info }
and term =
    | Metavar of metavar * node list
    (* Abstractions *)
    | Labs of node
    | LetRec of node * node
    (* Constructors *)
    | App of node * node
    (* Lambda variable, eihter bound or free *)
    | LVar of node
    (* Var stands for a de bruijn index *)
    | Var of int
    (* Astr is now useless but show how to represant a builtin type *)
    | AStr of string

type judgement =
    | DeriveTo of node * node * info

type premises =
    (* the int stands for the number of abstractions around the tree *)
    | Premises of (int * ast) list
    | Empty

and ast = judgement * rule * premises * info

type context =
    | Proj of int
    | CStr of string
    (* When the variable is free *)
    | CVar of int
    | CLabs of metavar
    | CLetRec of metavar * metavar
    | CLVar of metavar
    | CApp of metavar * metavar
    (* For a closed term *)
    | Closed of node

type sub = { met:metavar; sub:context }

(* Constraint type: stands for one equation to match, right-hand side has
 * to be closed, otherwise NonMatchingProblem could be raise *)
type constr = node * node

(* Useful constructors *)

(* build a term with a dummy position *)
let dummy_info = (Lexing.dummy_pos, Lexing.dummy_pos)
let create_dum term = { term=term; pos=dummy_info }

let var i = create_dum (Var i)
let lvar i = create_dum (LVar i)
let lvarvar i = create_dum (LVar (var i))
let app (t1, t2) = create_dum (App (t1, t2))
let labs t = create_dum (Labs t)
let astr s = create_dum (AStr s)
let app (t1, t2) = create_dum (App (t1, t2))
let letrec (t1, t2) = create_dum (LetRec (t1, t2))
let meta (id, par) = create_dum (Metavar (id, par))
let fmeta id = create_dum (Metavar (id, []))

let create_deriv n1 n2 p = DeriveTo (n1, n2, p)

let create_node t p = { term = t; pos = p }
let create_labs n p =
    create_node (Labs n) p
let create_letrec n1 n2 p =
    create_node (LetRec (n1, n2)) p
let create_app n1 n2 p =
    create_node (App (n1, n2)) p
let create_lvar id p =
    create_node (LVar (create_node (Var id) p)) p

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
