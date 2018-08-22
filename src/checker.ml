open Ast
open Unify

(* functions to check the number of premises *)
exception Premise_num_error of int * int
exception AbsError of int * int * info

let match_rule concl premises rule =
    match rule with
    | APP1 ->
            (* premise: M -> N *)
            (* conclusion: M T -> N T *)
            (* match conclusion *)
            let (c1, c2) =
                match concl with
                | DeriveTo (c1, c2, _) -> (c1, c2)
                (* | _ -> error *)
            in
            let (p1, p2, ctx_len) =
                match premises with
                (* get the number of nested abstractions (ctx_len) for each
                 * premise *)
                | [(ctx_len, (e1, _, _, pos))] ->
                        if ctx_len <> 0 then raise (AbsError (ctx_len, 0, pos));
                        begin match e1 with
                        | DeriveTo (p1, p2, _) -> (p1, p2, ctx_len)
                        (*| _ -> judg_error*)
                        end
                | _ -> raise (Premise_num_error (List.length premises, 1))
            in
            let pp1, pp2 = (fmeta 0, fmeta 1) in
            let cp1, cp2 = (app (fmeta 0, fmeta 2), app (fmeta 1, fmeta 2)) in
            (* When matching a premise, pass the number of nested abstractions
             * aroud the tree as threshold, the solver will thus seen the
             * variables as bound *)
            unify [(cp1, c1, 0); (cp2, c2, 0); (pp1, p1, ctx_len); (pp2, p2, ctx_len)]
    | APP2 ->
            (* this rule is actually 2 *)
            (* conditions on metavar are not supported *)

            (* premise: M -> N *)
            (* conclusion: v M -> v N *)
            let (c1, c2) =
                match concl with
                | DeriveTo (c1, c2, _) -> (c1, c2)
                (* | _ -> error *)
            in
            let (p1, p2, ctx_len) =
                match premises with
                | [(ctx_len, (e1, _, _, pos))] ->
                        if ctx_len <> 0 then raise (AbsError (ctx_len, 0, pos));
                        begin match e1 with
                        | DeriveTo (p1, p2, _) -> (p1, p2, ctx_len)
                        (*| _ -> judg_error*)
                        end
                | _ -> raise (Premise_num_error (List.length premises, 1))
            in
            let concl_pattern v =
                (app (v, fmeta 0), app (v, fmeta 1))
            in 
            (* for v = free id *)
            let variable = lvar (fmeta 2) in
            let pp1, pp2 = (fmeta 0, fmeta 1) in
            let cp1, cp2 = concl_pattern variable in
            let r1 = unify [(cp1, c1, 0); (cp2, c2, 0); (pp1, p1, ctx_len); (pp2, p2, ctx_len)] in
            begin match r1 with
            | None ->
                    (* for v = (\x.T) *)
                    let abs = labs (fmeta 2) in
                    let (cp1, cp2) = concl_pattern abs in
                    unify [(cp1, c1, 0); (cp2, c2, 0); (pp1, p1, ctx_len); (pp2, p2, ctx_len)]
            | _ -> r1
            end
    | APPABS ->
            (* conclusion: \(x)[M[x]] N -> M[N] *)
            let (c1, c2) =
                match concl with
                | DeriveTo (c1, c2, _) -> (c1, c2)
                (* | _ -> error *)
            in
            let () =
                match premises with
                | [] -> ()
                | _ -> raise (Premise_num_error (List.length premises, 0))
            in
            let cp1 = app (labs (meta (0, [lvarvar 0])), fmeta 1) in
            let cp2 = meta (0, [fmeta 1]) in
            unify [(cp1, c1, 0); (cp2, c2, 0)]
    | APPFULL ->
            let (c1, c2) =
                match concl with
                | DeriveTo (c1, c2, _) -> (c1, c2)
                (* | _ -> judg error *)
            in
            let (p1, p2, ctx_len) =
                match premises with
                | [(ctx_len, (e1, _, _, pos))] ->
                        if ctx_len <> 1 then raise (AbsError (ctx_len, 1, pos));
                        begin match e1 with
                        | DeriveTo (p1, p2, _) -> (p1, p2, ctx_len)
                        (*| _ -> judg_error*)
                        end
                | _ -> raise (Premise_num_error (List.length premises, 1))
            in

            let m = meta (0, [lvarvar 0]) in
            let n = meta (1, [lvarvar 0]) in
            (* premise: (x) [M[x] -> N[x]] *)
            (* conclusion: \(x)[M[x]] -> \(x)[N[x]] *)
            let pp1, pp2 = (m, n) in
            let cp1, cp2 = (labs m, labs n) in
            unify [(cp1, c1, 0); (cp2, c2, 0); (pp1, p1, ctx_len); (pp2, p2, ctx_len)]
    | LETREC ->
            let (c1, c2) =
                match concl with
                | DeriveTo (c1, c2, _) -> (c1, c2)
                (* | _ -> error *)
            in
            let () =
                match premises with
                | [] -> ()
                | _ -> raise (Premise_num_error (List.length premises, 0))
            in
            let e1_xy = meta (0, [lvarvar 1; lvarvar 0]) in
            let e2 = meta (1, [lvarvar 0]) in
            let e1_xz = meta (0, [lvarvar 0; lvarvar 1]) in
                (* let rec x y = E1[x,y] in E2[x] ->
                 * E2[\z. let rec x y = E1[x,y] in E1[x,z]]*)
            let cp1 = letrec (e1_xy, e2) in
            let cp2 = meta (1, [labs (letrec (e1_xy, e1_xz))]) in
            unify [(cp1, c1, 0); (cp2, c2, 0)]

let rec check_ast (concl, (rule, _), premises, pos) threshold =
    try
        let prems = match premises with Empty -> [] | Premises l -> l in
        let result = match_rule concl prems rule in
        match result with
        | Some _ ->
                (* ignore the number of abstractions on the top of the tree
                 * the bound variables by these ones are thus seen as free
                 * variables *)
                List.iter (fun (_, ast) -> check_ast ast threshold) prems
        | None ->
                print_string (print_info pos);
                print_string (":\nExpression doesn't match the pattern of " 
                            ^ (rule_name rule) ^ "\n")
    with
        | Premise_num_error (given, expect) ->
                print_string (print_info pos);
                print_string
                (":\nPremises number mismatch: " ^
                (string_of_int given) ^ " given, but " ^
                (string_of_int expect) ^ " expected for the rule " ^
                (rule_name rule) ^ "\n")
        | AbsError (given, expect, pos) ->
                print_string (print_info pos);
                print_string
                (":\nAbstractions number mismatch:\n" ^
                "This judgement is nested " ^ (string_of_int given) ^
                " time(s), but the rule " ^ (rule_name rule) ^ " expect a " ^
                (string_of_int expect) ^ " time(s) nested judgement for this premise\n")


