%token LPAREN RPAREN
%token LBRA RBRA
%token LSBRA RSBRA
%token BY
%token LAMBDA
%token LETREC EQ IN
%token DOT
%token IS
%token SEMI
%token DQUOTE
%token EOF
%token <string> ID
%token <Ast.rule_name> RULENAME

%start entrypoint

%type <Ast.ast> entrypoint

%%

entrypoint:
    e = ast EOF
    {
        (* Free variable are saved as de bruijn indices
         * They are kept in the free_vars list
         * positive indices are bound variables
         * negative ones are the negation of the positions of the free ones in
         * the list regardless of the context *)

        (* These functions shift the index of a free variable to its real ones
         * they keep track of the index of the first free variable
         * then substract the negative index to it to have a possible index
         * greater than all the bound ones *)
        let rec shift_judg free_idx (Ast.DeriveTo (n1, n2, info)) =
            Ast.DeriveTo (shift_node free_idx n1, shift_node free_idx n2, info)
        and shift_prems free_idx = function
            | Ast.Premises prems ->
                    let shift_prem (len, ast) = (len, shift_ast (free_idx + len) ast) in
                    Ast.Premises (List.map shift_prem prems)
            | Ast.Empty -> Ast.Empty
        and shift_ast free_idx (concl, r, prems, info) =
            let concl' = shift_judg free_idx concl in
            let prems' = shift_prems free_idx prems in
            (concl', r, prems', info)
        and shift_node free_idx node =
            let updated =
                let open Ast in
                match node.term with
                | Labs t -> Labs (shift_node (free_idx + 1) t)
                | LVar t -> LVar (shift_node (free_idx) t)
                | LetRec (t1, t2) ->
                        LetRec (shift_node (free_idx + 2) t1, shift_node (free_idx + 1) t2)
                | App (t1, t2) -> App (shift_node free_idx t1, shift_node free_idx t2)
                | Var id when id < 0 -> Var (free_idx - id)
                | Var _ | Metavar _ | AStr _ -> node.term
            in
            { node with term = updated }
        in
        let free_vars = ref [] in
        let ast = e (free_vars, []) in
        shift_ast (-1) ast
    }

rule:
    name = RULENAME
    { (name, ($startpos, $endpos)) }


ast:
    e1 = judgement BY e2 = rule LBRA e3 = separated_list(SEMI, premise) RBRA
    {
        fun ctx ->
            let premises =
                match List.map (fun f -> f 0 ctx) e3  with
                | [] -> Ast.Empty
                | l -> Ast.Premises l
            in
            (e1 ctx, e2, premises, ($startpos, $endpos))
    }

premise:
    LPAREN id = ID RPAREN LSBRA e = premise RSBRA
    {
        fun count (free, ctx) ->
            e (count + 1) (free, id :: ctx)
    }
    | ast = ast
    {
        fun count ctx ->
            (count, ast ctx)
    }

judgement:
    DQUOTE e1 = term IS e2 = term DQUOTE
    {
        fun ctx ->
            Ast.create_deriv (e1 ctx) (e2 ctx) ($startpos, $endpos)
    }

term:
    LAMBDA id = ID DOT t = term
    {
        fun (free, ctx) ->
            Ast.create_labs (t (free, id :: ctx)) ($startpos, $endpos)
    }
    | LETREC x = ID y = ID EQ t1 = term IN t2 = term
    {
        fun (free, ctx) ->
            Ast.create_letrec (t1 (free, y :: x :: ctx)) (t2 (free, x :: ctx)) ($startpos, $endpos)
    }
    | e = app
    { e }

app:
    e1 = app e2 = id
    { fun ctx -> Ast.create_app (e1 ctx) (e2 ctx) ($startpos, $endpos)}
    | e = id
    { e }

id:
    id = ID
    { 
        (* First look if the variable is bound *)
        (* If not, look if we saw it before and then just use the negation of
         * the index in the list *)
        (* If not, add it to the free variables list *)
        fun (free, ctx) ->
            let rec lookup_free n ctx =
                match ctx with
                | [] -> free := !free @ [id]; n
                | h :: t -> if h = id then n else lookup_free (n - 1) t
            in
            let rec lookup_bound n ctx =
                match ctx with
                | [] -> lookup_free (-1) !free
                | h :: t -> if h = id then n else lookup_bound (n + 1) t
            in
            Ast.create_lvar (lookup_bound 0 ctx) ($startpos, $endpos)
    }
    | LPAREN e = term RPAREN
    { e }
