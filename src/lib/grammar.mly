%{
  open ConcreteSyntax
%}

%token <int> NUMERAL
%token <string> ATOM
%token <string option> HOLE_NAME
%token COLON PIPE AT COMMA RIGHT_ARROW RRIGHT_ARROW UNDERSCORE
%token LPR RPR LBR RBR LSQ RSQ
%token EQUALS
%token TIMES FST SND
%token LAM LET IN END WITH
%token REC SUC NAT ZERO
%token QUIT NORMALIZE DEF
%token ID REFL MATCH
%token EOF

%start <ConcreteSyntax.signature> sign
%%

name:
  | s = ATOM
    { s }
  | UNDERSCORE
    { "_" }

decl:
  | DEF; nm = name; COLON; tp = term; EQUALS; body = term
    { Def {name = nm; def = body; tp} }
  | QUIT
    { Quit }
  | NORMALIZE; tm = term
    { NormalizeTerm tm }

sign:
  | EOF
    { [] }
  | d = decl; s = sign
    { d :: s }

atomic:
  | LBR; term = term; RBR
    { term }
  | a = name
    { Var a }
  | ZERO
    { Lit 0 }
  | n = NUMERAL
    { Lit n }
  | NAT
    { Nat }
  | REFL
    { Refl }
  | LSQ; left = term; COMMA; right = term; RSQ
    { Pair (left, right) }
  | name = HOLE_NAME
    { Hole name }

spine:
  | t = atomic 
    { Term t }

term:
  | f = atomic; args = list(spine)
    { match args with [] -> f | _ -> Ap (f, args) }
  | LET; name = name; COLON; tp = term; EQUALS; def = term; IN; body = term
    { Let (Check {term = def; tp}, B {name; body}) }
  | LET; name = name; EQUALS; def = term; IN; body = term; END
    { Let (def, B {name; body}) }
  | LPR t = term; AT; tp = term RPR
    { Check {term = t; tp} }
  | SUC; t = term
    { Suc t }
  | REC; n = term; AT; mot_name = name; RRIGHT_ARROW; mot = term; WITH; LSQ;
    option(PIPE); ZERO; RRIGHT_ARROW; case_zero = term;
    PIPE; SUC; LPR; suc_var = name; RRIGHT_ARROW; ih_var = name; RPR; RRIGHT_ARROW; case_suc = term; RSQ
    { NatElim 
       {mot = B {name = mot_name; body = mot};
        case_zero;
        case_suc = B2 {name1 = suc_var; name2 = ih_var; body = case_suc};
        scrut = n}
    }
  | ID; tp = atomic; left = atomic; right = atomic
    { Id (tp, left, right) }
  | MATCH; scrut = term; AT; name1 = name; name2 = name; name3 = name; RRIGHT_ARROW; mot_term = term; WITH; LSQ;
    option(PIPE); REFL; name = name; RRIGHT_ARROW; case_refl = term; RSQ
    { IdElim {mot = B3 {name1; name2; name3; body = mot_term}; case_refl = B {name; body = case_refl}; scrut} }
  | LAM; names = list(name); RRIGHT_ARROW; body = term
    { Lam (BN {names; body}) }
  | tele = nonempty_list(tele_cell); RIGHT_ARROW; cod = term
    { Pi (tele, cod) }
  | tele = nonempty_list(tele_cell); TIMES; cod = term
    { Sg (tele, cod) }
  | dom = atomic RIGHT_ARROW; cod = term
    { Pi ([Cell {name = ""; tp = dom}], cod) }
  | dom = atomic; TIMES; cod = term
    { Sg ([Cell {name = ""; tp = dom}], cod) }
  | FST; t = term 
    { Fst t }
  | SND; t = term 
    { Snd t }

tele_cell:
  | LPR name = name; COLON tp = term; RPR
    { Cell {name; tp} }
