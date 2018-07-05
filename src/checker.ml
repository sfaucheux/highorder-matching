open Ast
open Unify

(* functions to check the number of premises *)
exception Premise_num_error of int * int


let check_deriv pattern exprs concl =
    let pair_expr node expr =
        let rec extract_concl = function
            | Expr(judg, _, _, _) -> judg
            | AExpr(expr, pos) -> create_node (Mabs (extract_concl expr)) pos
        in
        (node, extract_concl expr)
    in
    try
        let constraints = List.map2 pair_expr pattern exprs in
        unify (concl :: constraints)
    with Invalid_argument _ ->
        raise (Premise_num_error (List.length exprs, List.length pattern))

let match_rule concl exprs rule =
    match rule with
    | APP1 ->
            (* premise: M -> N *)
            (* conclusion: M T -> N T *)
            let pattern = [ judgement (fmeta 0, fmeta 1)] in
            let concl_pattern =
                judgement (app (fmeta 0, fmeta 2), app (fmeta 1, fmeta 2))
            in
            check_deriv pattern exprs (concl_pattern, concl)
    | APP2 ->
            (* this rule is actually 2 *)
            (* conditions on fmetavar are not yet supported *)

            (* premise: M -> N *)
            (* conclusion: v M -> v N *)
            let of_normal v =
                judgement (app (v, fmeta 0), app (v, fmeta 1))
            in 
            (* for v = free id *)
            let free = free_id (fmeta 2) in
            let pattern = [judgement (fmeta 0, fmeta 1)] in
            let concl_pattern1 = of_normal free in
            begin match check_deriv pattern exprs (concl_pattern1, concl) with
            | Some s -> Some s
            | None ->
                    (* for v = (\x.T) *)
                    let abs = labs (fmeta 2) in
                    let concl_pattern2 = of_normal abs in
                    check_deriv pattern exprs (concl_pattern2, concl)
            end
    | APPABS ->
            let concl_pattern =
                (* conclusion: \(x)[M[x]] N -> M[N] *)
                judgement (app (labs (meta (0, [bound_id 0])), fmeta 1),
                           meta (0, [fmeta 1]))
            in
            check_deriv [] [] (concl_pattern, concl)
    | APPFULL ->
            let m = meta (0, [bound_id 0]) in
            let n = meta (1, [bound_id 0])in
            (* premise: (x) [M[x] -> N[x]] *)
            (* conclusion: \(x)[M[x]] -> \(x)[N[x]] *)
            let pattern = [mabs (judgement (m, n))] in
            let concl_pattern = judgement (labs m, labs n) in
            check_deriv pattern exprs (concl_pattern, concl)

let current = ref 0
(* substitute without shift *)
let rec substitute_node id sub node =
    let app = substitute_node id sub in
    let updated = 
        match node.term with
        | Mabs t -> Mabs (substitute_node (id + 1) sub t)
        | Labs t -> Labs (substitute_node (id + 1) sub t)
        | App (t1, t2) -> App (app t1, app t2)
        | Judgement (t1, t2) -> Judgement (app t1, app t2)
        | BoundId bid when bid = id -> sub
        | BoundId _
        | Metavar _ 
        | AStr _
        | FreeId _ -> node.term
    in
    { node with term = updated }

let rec substitute_expr id sub expr =
    match expr with
    | Expr(concl, rule, exprs, pos) ->
            let new_concl = substitute_node id sub concl in
            let new_exprs = List.map (substitute_expr id sub) exprs in
            Expr(new_concl, rule, new_exprs, pos)
    | AExpr(expr, pos) -> AExpr(substitute_expr (id + 1) sub expr, pos)

let rec check_ast ast =
    let rec get_inner_expr expr depth =
        match expr with
        | Expr (concl, rule, exprs, pos) -> (concl, rule, exprs, pos, depth)
        | AExpr (e, _) -> get_inner_expr e (depth + 1)
    in
    let (concl, (Rule(rule, _)), exprs, pos, depth) = get_inner_expr ast 0 in
    let rec apply_sub sub_func depth idx arg =
        if depth = 0 then
           arg
        else
            let sub_free = AStr ("_" ^ (string_of_int idx)) in
            let substituted = sub_func (depth - 1) sub_free arg in
            apply_sub sub_func (depth - 1) (idx + 1) substituted
    in
    let sub_concl = apply_sub substitute_node depth !current concl in
    let sub_exprs = List.map (apply_sub substitute_expr depth !current) exprs in
    current := !current + depth;
    try
        let result = match_rule sub_concl sub_exprs rule in
        match result with
        | Some _ ->
                ignore (check_premises sub_exprs)
        | None ->
                print_string (print_info pos);
                print_string (":\nExpression doesn't match the pattern of " 
                            ^ (rule_name rule) ^ "\n")
    with
        Premise_num_error (given, expect) ->
                print_string (print_info pos);
                print_string
                (":\nPremises number mismatch: " ^
                (string_of_int (given - 1)) ^ " given, but " ^
                (string_of_int (expect - 1)) ^ " expected for the rule " ^
                (rule_name rule) ^ "\n")

and check_premises exprs =
    match exprs with
    | [] -> ()
    | h :: t -> check_ast h
