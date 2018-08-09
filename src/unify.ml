open Ast
open Sstream

(* Raised when the left-hand side of a constraint is matched against another
 * metavariable *)
exception NonMatchingProblem

(* Return a fresh metavariable
 * Since the identifier is negative, it should be different from all the other
 * ones *)
let current_meta = ref (-1)
let pick_fresh_name () =
    let m = !current_meta in
    decr current_meta; m

(* Check if a term is closed or not, should be implemented in the checker in
* the future *)
let rec is_closed node idx =
    match node.term with
    | Mabs n -> is_closed n (idx + 1)
    | Labs n -> is_closed n (idx + 1)
    | LetRec (n1, n2) -> (is_closed n1 (idx + 2)) && (is_closed n2 (idx + 1))
    | App (n1, n2)
    | Judgement (n1, n2) -> (is_closed n1 idx) && (is_closed n2 idx)
    | BoundId id when id >= idx -> false
    | BoundId _
    | Metavar _
    | AStr _
    | FreeId _ -> true

(* Shift indices by d from c index *)
let rec shift d c node =
    let app = shift d c in
    let updated = 
        match node.term with
        | Mabs t -> Mabs (shift d (c + 1) t)
        | Labs t -> Labs (shift d (c + 1) t)
        | LetRec (t1, t2) -> LetRec (shift d (c + 2) t1, shift d (c + 1) t2)
        | App (t1, t2) -> App (app t1, app t2)
        | Judgement (t1, t2) -> Judgement (app t1, app t2)
        | BoundId id when id >= c -> BoundId (id + d)
        | BoundId _
        | Metavar _ 
        | AStr _
        | FreeId _ -> node.term
    in
    { node with term = updated }

(* Head normalize
 * Since metavariables can take other metavariables as parameter, a recursive
 * call with all the previous solutions have to be done when substuting with a
 * projection *)
let head_normalize full_sols t =
    let shift_param par =
        (bound_id 0) :: List.map (shift 1 0) par
    in
    let rec hn sols t =
        match sols with
        | [] -> t
        | { met = s_id; sub = ctx } :: tail ->
                begin match t.term with
                | Metavar (id, par) -> 
                        if s_id = id then
                            begin match ctx with
                            | Cabs m ->
                                    mabs (meta (m, shift_param par))
                            | CLabs m ->
                                    labs (meta (m, shift_param par))
                            | CLetRec (m1,m2) ->
                                    let par1 = shift_param par in
                                    let par2 = shift_param par1 in
                                    letrec (meta (m1, par2), meta (m2, par1))
                            | Proj n ->
                                    hn full_sols (List.nth par n)
                            | CStr s ->
                                     astr s
                            | CFreeId m ->
                                    free_id (meta (m, par))
                            | CApp (m1, m2) ->
                                    app (meta (m1, par), meta (m2, par))
                            | CJudgment (m1, m2) ->
                                    judgement (meta (m1, par), meta (m2, par))
                            | Closed node ->
                                    node
                            end
                        else hn tail t
                | _ -> t
                end
    in hn full_sols t

(* Return some context of a given term or none if undifined *)
let context = function
    | FreeId c -> Some (CFreeId (pick_fresh_name ()))
    | Mabs _ -> Some (Cabs (pick_fresh_name ()))
    | LetRec _ -> Some (CLetRec (pick_fresh_name (), pick_fresh_name ()))
    | App _ -> Some (CApp (pick_fresh_name (), pick_fresh_name ()))
    | Judgement _ -> Some (CJudgment (pick_fresh_name (), pick_fresh_name ()))
    | Labs _ -> Some (CLabs (pick_fresh_name ()))
    | AStr s -> Some (CStr s)
    | BoundId _ -> None
    | Metavar _ -> raise NonMatchingProblem

(* Generate recursively a stream of n substitutions of id with the projection k
 * concatenated in front of sols *)
let rec gen_projections id n k t sols =
    if k = n then
        no_solution
    else
        let next () =
            gen_projections id n (k + 1) t sols
        in
        let s =
            (bind_meta id (Proj k)) :: sols
        in
        create_stream s next

(* Try to unify one constraint, return a stream of solutions, if it is a
 * match between two variables and they are equals, return one empty list
 * of substitution as the only solution, None otherwise *)
let rec unify_one (left, right) sols =
    let left' = head_normalize sols left in
    match left'.term, right.term with
    (* no new constraint current stream is valid *)
    | BoundId id1, BoundId id2 ->
            if id1 = id2 then create_eos sols else no_solution
    | AStr id1, AStr id2 ->
            if id1 = id2 then create_eos sols else no_solution
    | FreeId n1, FreeId n2
    | Labs n1, Labs n2
    | Mabs n1, Mabs n2 ->
            unify_one (n1, n2) sols
    | LetRec (m1, n1), LetRec (m2, n2)
    | App (m1, n1), App (m2, n2)
    | Judgement (m1, n1), Judgement (m2, n2) ->
            unify_head (m1, m2) [(n1, n2)] (create_eos sols)
    | Metavar (id, par), _ ->
            let arity = List.length par in
            if arity = 0 && (is_closed right 0)
            then
                create_eos ((bind_meta id (Closed right)) :: sols)
            else
                let proj () = gen_projections id arity 0 right.term sols in
                let new_stream =
                    begin match context right.term with
                    | None ->
                            proj ()
                    | Some ctx ->
                            create_stream ((bind_meta id ctx) :: sols) proj
                    end
                in
                unify_head (left', right) [] new_stream
    | _ -> no_solution

(* Take a list of constraints and a stream of possible substitutions 
 * (left, right) is the first constraint *)
and unify_head (left, right) tail stream =
    match stream with
    | Some current ->
            let next_try () = unify_head (left, right) tail (current.next ()) in
            (* try to unify the head and get the possible solutions *)
            let result = unify_one (left, right) current.guess in
            (* Return the new constraints generated by the
            * recursive call and concatenate the next_try at the end.
            * In case of a fail, next_try will be called (because concatenated
            * to None) *)
            begin match tail with
            | hd :: tl ->
                    concat_stream next_try (unify_head hd tl result)
            | [] -> concat_stream next_try result
            end
    (* ran out of solutions *)
    | None -> no_solution

(* Unify: take a list of constraints and return a stream of all the possible
 * solutions under the empty set of substitution *)
and unify = function
    | head :: tail ->
            unify_head head tail (create_eos [])
    | [] -> create_eos []

