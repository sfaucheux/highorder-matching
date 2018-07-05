open Unify
open Sstream
open Ast
open Pp

exception AcceptFail of string
exception RejectFail of stream * string

let should_pass constraints =
    let r = unify constraints in
    match r with
    | Some s ->
            print_string (print_constraint constraints);
            print_string (print_subs_pos (List.rev s.guess));
            let num = (count_stream 0 (s.next ())) + 1 in
            print_string ("OK (accepted) with " ^ (string_of_int num) ^ " sols");
            print_newline ()
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
    let fid id = free_id (astr id) in
    try
        (* simple case *)
        (* M = id *)
        should_pass [(fmeta 0, fid "id")];
        (* id1 = id2 *)
        should_fail [(fid "id1", fid "id2")];
        (* congurence *)
        should_pass
        (* M[x, y] = x y *)
        (* M[y, x] = y x *)
        [(meta (0, [fid "x"; fid "y"]), app (fid "x", fid "y"));
         (meta (0, [fid "y"; fid "x"]), app (fid "y", fid "x"))];
        (* same with ids *)
        (* (x)[(y)[M[x, y] = x y]] *)
        (* (x)[(y)[M[y, x] = y x]] *)
        should_pass
        [(mabs (mabs (meta (0, [bound_id 0; bound_id 1]))),
          mabs (mabs (app (bound_id 0, bound_id 1))));
         (mabs (mabs (meta (0, [bound_id 1; bound_id 0]))),
          mabs (mabs (app (bound_id 1, bound_id 0))))];
        (* m[n[z, y]] = y y z
         * n[z, y] = y y 
         * n[y, x] = x x 
         * m[n[y, z]] = z z z
         * with m[x] = x z
         * and  n[x, y, z] = y y *)
        let m p = meta (0, [p]) in
        let n (p1, p2) = meta (1, [p1; p2]) in
        should_pass
        [
            (m (n (fid "z", fid "y")), app (app (fid "y", fid "y"), fid "z"));
            (n (fid "z", fid "x"), app (fid "x", fid "x"));
            (n (fid "x", fid "y"), app (fid "y", fid "y"));
            (m (n (fid "y", fid "z")), app (app (fid "z", fid "z"), fid "z"));
        ];
        should_pass
        [
            (mabs (meta (0, [bound_id 0])), mabs (app (app (fid "y", bound_id 0), fid "z")));
            (mabs (meta (1, [bound_id 0])), mabs (labs (labs (bound_id 2))));
            (mabs (meta (0, [meta (1, [bound_id 0])])), mabs (app (app (fid "y", labs (labs (bound_id 2))), fid "z")));
        ];
        should_fail
        [
            (mabs (meta (0, [bound_id 0])), mabs (app (app (fid "y", bound_id 0), fid "z")));
            (mabs (meta (1, [bound_id 0])), mabs (labs (labs (bound_id 2))));
            (mabs (meta (0, [meta (1, [bound_id 0])])), mabs (app (app (fid "y", labs (labs (bound_id 0))), fid "z")));
        ];
        let m (p1, p2, p3) = meta (0, [p1; p2; p3]) in
        let n (p1, p2, p3) = meta (1, [p1; p2; p3]) in
        let o (p1, p2, p3) = meta (2, [p1; p2; p3]) in
        let x = labs (fid "x") in
        let y = labs (fid "y") in
        let z = labs (fid "z") in
        should_fail
        [
            (* 16777216 solutions for the first 3 equations alone *)
            (m (x, y, z), app (app (app (x, y), app (z, x)), app (app (y, z), app (x, z))));
            (n (x, y, z), app (app (app (x, y), app (z, x)), app (app (y, z), app (x, z))));
            (o (x, y, z), app (app (app (x, y), app (z, x)), app (app (y, z), app (x, z))));
            (* 119 solutions for the last one but incompatible with the first ones *)
            (o (n (x, y, z), m(y, z, x), n (z, x, y)), app (z, z))
        ];

    with
    | AcceptFail str ->
            print_string ("Fail:\n" ^ str ^ "must be accepted.\n")
    | RejectFail (sol, str) ->
            print_string ("Fail:\n" ^ str ^ "must be rejected. solutions:\n ");
            print_stream 1 sol
