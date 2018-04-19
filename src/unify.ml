open Ast

(* Raised when the right-hand side of a constraint is matched against a
 * non-closed term *)
exception NonMatchingProblem

(* Raised when a term other than a meta application or a metavariable is
 * matched as left-hand side of a meta application *)
exception InvalidPattern

(* Constraint type: stands for one equation to match, right-hand side has
 * to be closed, otherwise NonMatchingProblem could be raise *)
type constr = node * node

type sub = { id:metavar; sub:term; info:info }

(* Stream of solutions: used to store all the possible solutions during the
 * process, it is very useful to lazily generate future solutions to be tried
 * in a sub problem *)
type sol = { guess:sub list; next:unit -> stream }
and stream = sol option

(* bind_meta: generate a new substitution from a metavariable and a node *)
let bind_meta id n = { id = id; sub = n.term; info = n.pos }

let create_stream g n = Some { guess = g; next = n }

(* Create an end-of-stream element *)
let create_eos g = create_stream g (fun () -> None)

(* Replace the end of the stream by the given next function *)
let rec concat_stream n = function
    | Some g ->
            let next () = concat_stream n (g.next ()) in
            create_stream g.guess next
    | None -> n ()

(* Apply f to all the solutions of the stream *)
let rec map_stream f = function
    | Some g ->
            let next () = map_stream f (g.next ()) in
            create_stream (f g.guess) next
    | None -> None

(* Apply substitution (substitute metavariable by term) within a given node *)
let rec apply_sub sub node =
    let app = apply_sub sub in
    let update t = { node with term = t } in
    match node.term with
    | Lamb t -> update (Lamb (app t))
    | FreeId t -> update (FreeId (app t))
    | App (t1, t2) -> update (App (app t1, app t2))
    | MAbs t -> update (MAbs (app t))
    | MApp (t1, t2) -> update (MApp (app t1, app t2))
    | Judgement (t1, t2) -> update (Judgement (app t1, app t2))
    | Metavar id when id = sub.id -> { term = sub.sub; pos = sub.info }
    | Metavar _
    | BoundedId _
    | Id _ -> node

(* Substitute bounded variable by sub in the given node *)
let rec substite_bound sub n node =
    let app = substite_bound sub n in
    let update t = { node with term = t } in
    match node.term with
    | MAbs t -> update (MAbs (substite_bound sub (n+1) t))
    | Lamb t -> update (Lamb (app t))
    | App (t1, t2) -> update (App (app t1, app t2))
    | MApp (t1, t2) -> update (MApp (app t1, app t2))
    | Judgement (t1, t2) ->update  (Judgement (app t1, app t2))
    | BoundedId id when id = n -> sub
    | Metavar _ 
    | FreeId _
    | BoundedId _
    | Id _ -> node

(* Reduce a term to its normal form by applying full beta-reduction *)
let rec reduce node =
    let update t = { node with term = t } in
    match node.term with
    | MAbs t -> update (MAbs (reduce t))
    | MApp (t1, t2) ->
            let left = reduce t1 in
            let right = reduce t2 in
            begin match left.term with
            | MAbs t ->
                    let sub = reduce (substite_bound right 0 t) in
                    { term = sub.term; pos = right.pos }
            | _ -> update (MApp (left, right))
            end
    | Lamb t1 -> update (Lamb (reduce t1))
    | App (t1, t2) -> update (App (reduce t1, reduce t2))
    | Judgement (t1, t2) -> update (Judgement (reduce t1, reduce t2))
    | Metavar _
    | BoundedId _
    | FreeId _
    | Id _ -> node

(* Also reduce to normal form *)
let apply_subs_to_node subs node =
    List.fold_left (fun n s -> apply_sub s n) node subs
    |> reduce

(* Create n nested abstractions of a given node *)
let rec create_n_abs n node =
    match n with
    | 0 -> node
    | _ -> mabs (create_n_abs (n - 1) node)

(* Generate all the possible projections by returning a stream of all the
 * possible bounded variables nested n times in an abstraction.
 * next is a shorthand to concatenate one stream at the end without adding the
 * concat_stream indirection *)
let rec gen_projection id len n next =
    match n with
    | i when i = len -> next
    | _ -> let current = create_n_abs len (bound_id n) in
        let next () = gen_projection id len (n + 1) next in
        create_stream [bind_meta id current] next

(* Generate all the possible imitations for an unary constructor
 * example:
 * M N O = ctor(a) will generate a stream of substitutions for M made of:
 * \x.\y.ctor(x), \x.\y.ctor(y), \x.\y.ctor(a) *)
let gen_un_imitation id len ctor node =
    let imitate n = create_n_abs len (ctor n) in
    let rec gen_imi n =
        match n with
        | i when i = len -> None
        | _ -> let current = imitate (bound_id n) in
            let next () = gen_imi (n + 1) in
            create_stream [bind_meta id current] next
    (* add the given node as the first solution *)
    in create_stream [bind_meta id (imitate node)] (fun () -> gen_imi 0)

(* Same thing for binary constructors, it generates a stream of all the
 * possible pairs made of variables or the node itself, example:
 * M N b = ctor(a, b) will generate a stream of substitutions for M made of:
 * \x.\y.ctor(x, x), \x.\y.ctor(x, y)..., \x.\y.ctor(a, x)..., \x.\y.ctor(a, b)
 * *)
let gen_bin_imitation id len ctor n1 n2 =
    let imitate n1 n2 = create_n_abs len (ctor (n1, n2)) in
    let rec gen_imi n m =
        match n, m with
        (* stop at (n + 1) to add the node itself as solution at n *)
        | i1, i2 when i1 = len + 1 && i2 = len + 1 -> None
        | i1, i2 when i2 = len + 1 -> gen_imi (n + 1) 0
        | _ -> 
            let left = if n = len then n1 else (bound_id n) in
            let right = if m = len then n2 else (bound_id m) in
            let current = imitate left right in
            let next () = gen_imi n (m + 1) in
            create_stream [bind_meta id current] next
    in gen_imi 0 0

(* Build the stream of projections and imitations for an unary constructor *)
let gen_unary_subs id ctor len node =
    let imitation = gen_un_imitation id len ctor node in
    gen_projection id len 0 imitation

(* Build the stream of projections and imitations for a binary constructor *)
let gen_binary_subs id ctor len t1 t2 =
    let imitation = gen_bin_imitation id len ctor t1 t2 in
    gen_projection id len 0 imitation
        
(* For a constant, just build one imitation and the projections *)
let gen_nullary_subs id len node =
    let imitation = create_eos [bind_meta id (create_n_abs len node)] in
    gen_projection id len 0 imitation

(* Get all the possible substitutions when an application is matched against
 * a constructor *)
let gen_app_subs id len node =
    match node.term with
    | Lamb n -> gen_unary_subs id lamb len n
    | MAbs n -> gen_unary_subs id mabs len n
    | FreeId n -> gen_unary_subs id free_id len n
    | App (n1, n2) -> gen_binary_subs id app len n1 n2
    | Judgement (n1, n2) -> gen_binary_subs id judgement len n1 n2
    | BoundedId _
    | Id _ -> gen_nullary_subs id len node
    | MApp _
    | Metavar _ -> raise NonMatchingProblem

(* Look into a node to know the number of nested applications and the leftmost
 * metavariable, assuming that node is already the left-hand side of an app,
 * thus, the count starts at 1 *)
let rec flatten_app node =
    match node.term with
    | MApp (n1, n2) ->
            let id, num = (flatten_app n1) in (id, num + 1)
    | Metavar id -> (id, 1) 
    | _ -> print_string (print_node true node);
            raise InvalidPattern

(* Try to unify one constraint, return a stream of solutions, if it is a
 * match between two variables and they are equals, return one empty list
 * of substitution as the only solution, None otherwise *)
let rec unify_one (left, right) =
    match left.term, right.term with
    | Lamb n1, Lamb n2
    | MAbs n1, MAbs n2 ->
            unify_one (n1, n2)
    | App (n1, n1'), App (n2, n2')
    | Judgement (n1, n1'), Judgement (n2, n2') ->
            unify [(n1, n2); (n1', n2')]
    | FreeId id1, FreeId id2 ->
            unify_one (id1, id2)
    | BoundedId id1, BoundedId id2 ->
            if id1 = id2 then create_eos [] else None
    | Id id1, Id id2 -> 
            if id1 = id2 then create_eos [] else None
    | Metavar id, _ ->
            create_eos [bind_meta id right]
    | MApp (n1, n2), _ ->
            (* get the number of nested applications and the
            * leftmost metavariable *)
            let id, param_num = flatten_app n1 in
            (* generate a stream of all possible substitutions
            * for the metavariable *)
            let result = gen_app_subs id param_num right in
            (* try to unify again with the new stream of constraints *)
            unify_head (left, right) [] result
    | _ -> None

(* Take a list of constraints and a stream of possible substitutions 
 * (left, right) is the first constraint *)
and unify_head (left, right) tail = function
    | Some current ->
            let next_try () = unify_head (left, right) tail (current.next ()) in
            let normalized = apply_subs_to_node current.guess left in
            (* try to unify the head and get the possible solutions *)
            let result = unify_one (normalized, right) in
            (* add the current solution to the new given stream *)
            let new_stream = map_stream (fun l -> l @ current.guess) result in
            (* Return the new constraints generated by the
            * recursive call and concatenate the next_try at the end.
            * In case of a fail, next_try will be called (because concatenated
            * to None) *)
            begin match tail with
            | hd :: tl ->
                    concat_stream next_try (unify_head hd tl new_stream)
            | [] -> concat_stream next_try new_stream
            end
    (* ran out of solutions *)
    | None -> None

(* Unify: take a list of constraints and return a stream of all the possible
 * solutions under the empty set of substitution *)
and unify = function
    | head :: tail ->
            unify_head head tail (create_eos [])
    | [] -> create_eos []

(* get a string for a substitution *)
and print_subs = function
    | hd :: tl ->
            hd.id ^ " <- "
            ^ (print_node false { term = hd.sub; pos = dummy_info })
            ^ "\n" ^ print_subs tl
    | [] -> ""

and print_constraint c =
    match c with
    | (l, r) :: tl ->
            print_string ((print_node false l) ^ " <=> " ^ (print_node false r));
            print_newline ();
            print_constraint tl
    | [] -> ()


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


