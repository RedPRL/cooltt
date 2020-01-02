%{
  open ConcreteSyntax
%}

%token <int> NUMERAL
%token <string> ATOM
%token COLON PIPE AT COMMA RIGHT_ARROW UNDERSCORE ATSIGN
%token LPR RPR
%token EQUALS
%token TIMES FST SND
%token LAM LET IN END WITH
%token REC SUC NAT ZERO
%token QUIT NORMALIZE TYPE DEF
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
  | NORMALIZE; DEF; a = name
    { NormalizeDef a  }
  | NORMALIZE; tm = term; AT; tp = term
    { NormalizeTerm {term = tm; tp} }

sign:
  | EOF
    { [] }
  | d = decl; s = sign
    { d :: s }

atomic:
  | LPR; t = term; RPR
    { t }
  | a = name
    { Var a }
  | ZERO
    { Lit 0 }
  | n = NUMERAL
    { Lit n }
  | NAT
    { Nat }
  | REFL
    { Refl None }
  | LPR left = term; COMMA; right = term; RPR
    { Pair (left, right) }

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
  | REC; n = term; AT; mot_name = name; RIGHT_ARROW; mot = term; WITH;
    PIPE; ZERO; RIGHT_ARROW; zero_case = term;
    PIPE; SUC; LPR; suc_var = name; RIGHT_ARROW; ih_var = name; RPR; RIGHT_ARROW; suc_case = term
    { NRec {
        mot = B {name = mot_name; body = mot};
        zero = zero_case;
        suc = B2 {name1 = suc_var; name2 = ih_var; body = suc_case};
        nat = n
      }
    }
  | ID; tp = atomic; left = atomic; right = atomic
    { Id (tp, left, right) }
  | ATSIGN; REFL; t = atomic
    { Refl (Some t) }
  | MATCH; eq = term; AT; name1 = name; name2 = name; name3 = name; RIGHT_ARROW; mot_term = term; WITH
    PIPE; REFL; name = name; RIGHT_ARROW; refl = term;
    { J {mot = B3 {name1; name2; name3; body = mot_term}; refl = B {name; body = refl}; eq} }
  | LAM; names = nonempty_list(name); RIGHT_ARROW; body = term
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
