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

%type <Ast.expr> entrypoint
%type <string list -> Ast.expr> expr
%type <Ast.rule> rule
%type <string list -> Ast.node> term judgement

%%

entrypoint:
    e = expr EOF {e []}

rule:
    name = RULENAME
    { Rule (name, ($startpos, $endpos)) }


expr:
    e1 = judgement BY e2 = rule LBRA e3 = separated_list(SEMI, expr) RBRA
    {
        fun ctx ->
            Expr (e1 ctx, e2, List.map (fun e -> e ctx) e3, ($startpos, $endpos))
    }
    | LPAREN id = ID RPAREN LSBRA e = expr RSBRA
    {
        fun ctx ->
            AExpr (e (id :: ctx), ($startpos, $endpos))
    }

judgement:
    DQUOTE e1 = term IS e2 = term DQUOTE
    { fun ctx -> Ast.create_judg (e1 ctx) (e2 ctx) ($startpos, $endpos)}

term:
    LAMBDA id = ID DOT t = term
    { fun ctx -> Ast.create_labs (t (id :: ctx)) ($startpos, $endpos)}
    | LETREC x = ID y = ID EQ t1 = term IN t2 = term
    { fun ctx -> Ast.create_letrec (t1 (y :: x :: ctx)) (t2 (x :: ctx)) ($startpos, $endpos)}
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
        let rec lookup n ctx =
            match ctx with
            | [] -> Ast.create_free_id id ($startpos, $endpos)
            | h :: t ->
                    if h = id then
                        Ast.create_bound_id n ($startpos, $endpos)
                    else
                        lookup (n+1) t
        in lookup 0
    }
    | LPAREN e = term RPAREN
    { e }
