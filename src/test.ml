open Unify
open Ast

exception AcceptFail of string
exception RejectFail of stream * string

let should_pass constraints =
    let r = unify constraints in
    match r with
    | Some s ->
            print_string (print_constraint constraints);
            print_string "OK (accepted)\n"
    | None ->
            raise (AcceptFail (print_constraint constraints))

let should_fail constraints =
    let r = unify constraints in
    match r with
    | None ->
            print_string (print_constraint constraints);
            print_string "OK (rejected)\n"
    | Some s ->
            raise (RejectFail (r, print_constraint constraints))
let _ =
    let fid id = free_id (create_dum (Id id)) in
    try
        should_pass [(meta "M", fid "id")];
        should_fail [(fid "id1", fid "id2")];
        should_pass
        [(mapp (mapp (meta "M", fid "x"), fid "y"), app (fid "x", fid "y"));
         (mapp (mapp (meta "M", fid "y"), fid "x"), app (fid "y", fid "x"))]
    with
    | AcceptFail str ->
            print_string ("Fail:\n" ^ str ^ " must be accepted.")
    | RejectFail (sol, str) ->
            print_string ("Fail:\n" ^ str ^ " must be rejected. solutions:\n ");
            print_stream 1 sol
