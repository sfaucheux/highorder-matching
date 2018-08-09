open Ast
open Sstream

(* These functions don't support pretty print yet *)
let print_meta met =
    "M(" ^ (string_of_int met) ^ ")"
let print_meta_par met par =
    (print_meta met) ^ "[" ^
    (String.concat "," par ^ "]")
let print_bound id =
    "B(" ^ (string_of_int id) ^ ")"
let print_fid str =
    "F(" ^ str ^ ")"
let print_astr str =
    str
let print_mabs node =
    "()[ " ^ node ^ " ]"
let print_app n1 n2 =
    "(" ^ n1 ^ " " ^ n2 ^ ")"
let print_letrec n1 n2 =
    "let () () = " ^ n1 ^ " in " ^ n2
let print_judg n1 n2 =
    n1 ^ " -> " ^ n2
let print_labs node =
    "(\\" ^ node ^ ")"

(* Print functions *)
let rec print_node n =
    match n.term with
    (*| Lamb { term = Mabs n; } -> "\\." ^ (print_node false n)*)
    | Labs n ->
            print_labs (print_node n)
    | LetRec (n1, n2) ->
            print_letrec (print_node n1) (print_node n2)
    | App (n1, n2) ->
            print_app (print_node n1) (print_node n2)
    | Judgement(n1, n2) ->
            print_judg (print_node n1) (print_node n2)
    | FreeId n ->
            print_fid (print_node n)
    | Mabs n ->
            print_mabs (print_node n)
    | BoundId id ->
            print_bound id
    | Metavar (id, par) ->
            print_meta_par id (List.map print_node par)
    | AStr id ->
            print_astr id

(* print a context *)
let rec print_ctx_gen meta_printer ctx =
    match ctx with
    | Proj n -> "π" ^ (string_of_int n)
    | CFreeId m -> print_fid (meta_printer m)
    | CStr s -> print_astr s
    | Cabs m -> print_mabs (meta_printer m)
    (* constructors *)
    | CLabs m -> print_labs (meta_printer m)
    | CApp (m1, m2) -> print_app (meta_printer m1) (meta_printer m2)
    | CLetRec (m1, m2) -> print_letrec (meta_printer m1) (meta_printer m2)
    | CJudgment (m1, m2) -> print_judg (meta_printer m1) (meta_printer m2)
    | Closed node -> (print_node node)

(* print a context with id for metavariable *)
let rec print_ctx ctx =
    print_ctx_gen print_meta ctx

(* print a context by looking up and substitute the metavariables *)
let rec print_ctx_pos sub ctx = 
    let rec lookup_constraints subs meta =
        match subs with
        | [] -> "|any|"
        | head :: tail when head.met = meta -> print_ctx_pos subs head.sub
        | head :: tail -> lookup_constraints tail meta
    in
    print_ctx_gen (lookup_constraints sub) ctx

(* get a string for a substitution *)
let rec print_subs = function
    | hd :: tl ->
            (print_meta hd.met) ^ " <- " ^ (print_ctx hd.sub)
            ^ "\n" ^ print_subs tl
    | [] -> ""

(* print substitutions for user defined variables *)
let rec print_subs_pos sub =
    match sub with
    | hd :: tl ->
            (if hd.met >= 0 then
                (print_meta hd.met) ^ " <- " ^ (print_ctx_pos sub hd.sub) ^ "\n"
            else "")
            ^ print_subs_pos tl
    | [] -> ""

and print_constraint c =
    match c with
    | (l, r) :: tl ->
            (print_node l) ^ " <=> " ^ (print_node r) ^
            "\n" ^ (print_constraint tl)
    | [] -> ""

(* evaluate the stream of solutions to print it *)
and print_stream n = function
    | Some g ->
            print_string ("solution " ^ (string_of_int n) ^ ":\n");
            print_string (print_subs g.guess);
            print_newline ();
            if n < 11 then
                print_stream (n+1) (g.next ())
            else
                print_string "more...\n"
    | None -> print_string "End of solutions\n"
