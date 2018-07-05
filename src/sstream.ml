open Ast

(* Stream of solutions: used to store all the possible solutions during the
 * process, it is very useful to lazily generate future solutions to be tried
 * in a sub problem *)
type sol = { guess:sub list; next:unit -> stream }
and stream = sol option

(* bind_meta: generate a new substitution from a metavariable and a node *)
let bind_meta id ctx = { met = id; sub = ctx }

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

let no_solution = None

(* evaluate the stream of solutions to print it *)
let rec count_stream n = function
    | Some g ->
            count_stream (n+1) (g.next ())
    | None -> n
