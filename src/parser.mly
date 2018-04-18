%token LPAREN RPAREN
%token LBRA RBRA
(*%token LSBRA RSBRA*)
%token BY
%token LAMBDA
%token DOT
%token IS
%token SEMI
%token DQUOTE
%token EOF
%token <string> ID
%token <Ast.rule_name> RULENAME

%start entrypoint
%type <Ast.expr> expr entrypoint
%type <Ast.rule> rule
%type <Ast.context -> Ast.node> term judgement

%%

entrypoint:
    e = expr EOF {e}

expr:
    e1 = judgement BY e2 = rule LBRA e3 = separated_list(SEMI, expr) RBRA
    { Expr ((e1 []), e2, e3, ($startpos, $endpos)) }

rule:
    name = RULENAME
    { Rule (name, ($startpos, $endpos)) }

judgement:
    DQUOTE e1 = term IS e2 = term DQUOTE
    { fun ctx -> Ast.create_judg (e1 ctx) (e2 ctx) ($startpos, $endpos)}
    (* We don't the user to be able to abstract everything yet *)
    (*| LPAREN id = ID RPAREN LSBRA DQUOTE e1 = term IS e2 = term DQUOTE RSBRA
    {
        fun ctx ->
            Ast.create_node
            (MAbs (Ast.create_judg (e1 (id :: ctx)) (e2 (id :: ctx))) $startpos))
            $startpos
    }*)
term:
    LAMBDA id = ID DOT t = term
    { fun ctx -> Ast.create_labs (t (id :: ctx)) ($startpos, $endpos)}
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
                        Ast.create_bounded_id n ($startpos, $endpos)
                    else
                        lookup (n+1) t
        in lookup 0
    }
    | LPAREN e = term RPAREN
    { e }
