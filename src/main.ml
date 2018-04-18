open Checker
open Lexing
open Parsing

let dum = Lexing.dummy_pos
let _ =
    let lexbuf = Lexing.from_channel stdin in
    try
        let result = Parser.entrypoint Lexer.token lexbuf in
        (*print_graph result;*)
        check_ast result
    with
    | Parser.Error ->
            let error =
                Lexer.error
                (lexeme lexbuf)
                (lexeme_start_p lexbuf)
                (lexeme_end_p lexbuf)
            in
            print_string ("Syntax error " ^ error);
            print_newline ()
