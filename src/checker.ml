open Ast
open Unify

(* functions to check the number of premises *)
exception Premise_num_error of int * int


let check_deriv pattern exprs concl =
    let pair_expr node expr =
        let rec extract_concl = function
            | Expr(judg, _, _, _) -> judg
            | AExpr(expr, pos) -> create_node (MAbs (extract_concl expr)) pos
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
            let pattern = [ judgement (meta "M", meta "N")] in
            let concl_pattern =
                judgement (app (meta "M", meta "T"), app (meta "N", meta "T"))
            in
            check_deriv pattern exprs (concl_pattern, concl)
    | APP2 ->
            (* this rule is actually 2 *)
            (* conditions on metavar are not yet supported *)

            (* premise: M -> N *)
            (* conclusion: v M -> v N :- M -> N *)
            let of_normal v =
                judgement (app (v, meta "M"), app (v, meta "N"))
            in 
            (* for v = free id *)
            let free = free_id (meta "ID") in
            let pattern = [judgement (meta "M", meta "N")] in
            let concl_pattern1 = of_normal free in
            begin match check_deriv pattern exprs (concl_pattern1, concl) with
            | Some s -> Some s
            | None ->
                    (* for v = (\x.T) *)
                    let abs = labs (meta "T") in
                    let concl_pattern2 = of_normal abs in
                    check_deriv pattern exprs (concl_pattern2, concl)
            end
    | APPABS ->
            let concl_pattern =
                (* conclusion: M N -> M[N] *)
                judgement (app (lamb (meta "M"), meta "N"),
                           mapp (meta "M", meta "N"))
            in
            check_deriv [] [] (concl_pattern, concl)
    | APPFULL ->
            let m = meta "M" in
            let n = meta "N" in
            (* premise: (x) [M -> N] *)
            (* conclusion: \(x)[M] -> \(x)[N] *)
            let pattern = [mabs (judgement (m, n))] in
            let concl_pattern = judgement (lamb (mabs m), lamb (mabs n)) in
            check_deriv pattern exprs (concl_pattern, concl)

let rec check_ast ast =
    let rec get_inner_expr expr =
        match expr with
        | Expr (concl, rule, exprs, pos) -> (concl, rule, exprs, pos)
        | AExpr (e, _) -> get_inner_expr e
    in
    let (concl, (Rule(rule, _)), exprs, pos) = get_inner_expr ast in
    try
        let result = match_rule concl exprs rule in
        match result with
        | Some _ ->
                ignore (check_premises exprs)
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
