%{
  open ConcreteSyntax

  let locate loc node =
    {node; info = Some loc}

%}

%token <int> NUMERAL
%token <string> ATOM
%token <string option> HOLE_NAME
%token COLON PIPE AT COMMA RIGHT_ARROW RRIGHT_ARROW UNDERSCORE DIM COF BOUNDARY
%token LPR RPR LBR RBR LSQ RSQ
%token EQUALS JOIN MEET
%token UNIV
%token TIMES FST SND
%token LAM LET IN SUB
%token SUC NAT ZERO UNFOLD
%token PATH
%token COE COM HCOM
%token QUIT NORMALIZE DEF
%token ID REFL ELIM
%token EOF
%token TOPC BOTC

%start <ConcreteSyntax.signature> sign
%type <con_> plain_atomic plain_atomic_or_ap ap eq cof plain_term plain_term_or_cof bracketed
%type <pat> pat
%type <pat * con> case
%type <cell> tele_cell
%%

located(X):
  | e = X
    { locate $loc e }

term: t = located(plain_term) {t}
atomic: t = located(plain_atomic) {t}

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

eq:
  | r = atomic EQUALS s = atomic
    { CofEq (r, s) }

cof:
  | eq = eq
    { eq }
  | BOUNDARY t = term
    { CofBoundary t }
  | phi = located(plain_atomic_or_eq) JOIN psi = located(plain_atomic_or_eq)
    { Join (phi, psi) }
  | phi = located(plain_atomic_or_eq) MEET psi = located(plain_atomic_or_eq)
    { Meet (phi, psi) }

plain_atomic:
  | LBR t = plain_term_or_cof RBR
    { t }
  | a = ATOM
    { Var (`User a) }
  | ZERO
    { Lit 0 }
  | n = NUMERAL
    { Lit n }
  | NAT
    { Nat }
  | REFL
    { Refl }
  | UNIV
    { Univ }
  | name = HOLE_NAME
    { Hole name }
  | UNDERSCORE
    { Underscore }
  | DIM
    { Dim }
  | COF
    { Cof }
  | TOPC
    { TopC }
  | BOTC
    { BotC }

  | LSQ t = bracketed RSQ
    { t }

plain_atomic_or_eq: t = plain_atomic | t = eq {t}

plain_atomic_or_cof: t = plain_atomic | t = cof {t}

bracketed:
  | left = term COMMA right = term
    { Pair (left, right) }
  | cases = separated_list(PIPE, cof_case)
    { CofSplit cases }
  | PIPE cases = separated_list(PIPE, cof_case)
    { CofSplit cases }
  | t = located(plain_term_or_cof)
    { Prf t }

ap:
  | f = atomic; args = nonempty_list(atomic)
    { Ap (f, args) }

plain_atomic_or_ap : t = plain_atomic | t = ap {t}

plain_term:
  | t = plain_atomic_or_ap
    { t }
  | UNFOLD; names = nonempty_list(name); IN; body = term;
    { Unfold (names, body) }
  | LET; name = name; COLON; tp = term; EQUALS; def = term; IN; body = term
    { Let ({node = Ann {term = def; tp}; info = def.info}, B {name; body}) }
  | LET; name = name; EQUALS; def = term; IN; body = term
    { Let (def, B {name; body}) }
  | LPR t = term; AT; tp = term RPR
    { Ann {term = t; tp} }
  | SUC; t = term
    { Suc t }
  | ID; tp = atomic; left = atomic; right = atomic
    { Id (tp, left, right) }
  | LAM; names = list(name); RRIGHT_ARROW; body = term
    { Lam (BN {names; body}) }
  | LAM; ELIM; cases = cases
    { LamElim cases }
  | ELIM; scrut = term; AT; mot = motive; cases = cases
    { Elim {mot; cases; scrut}}
  | tele = nonempty_list(tele_cell); RIGHT_ARROW; cod = term
    { Pi (tele, cod) }
  | tele = nonempty_list(tele_cell); TIMES; cod = term
    { Sg (tele, cod) }
  | dom = located(plain_atomic_or_ap) RIGHT_ARROW cod = term
    { Pi ([Cell {name = "_"; tp = dom}], cod) }
  | dom = located(plain_atomic_or_ap) TIMES cod = term
    { Sg ([Cell {name = "_"; tp = dom}], cod) }
  | SUB tp = atomic phi = atomic tm = atomic
    { Sub (tp, phi, tm) }
  | FST; t = term
    { Fst t }
  | SND; t = term
    { Snd t }

  | PATH; tp = atomic; left = atomic; right = atomic
    { Path (tp, left, right) }

  | COE; fam = atomic; src = atomic; trg = atomic; body = atomic
    { Coe (fam, src, trg, body) }
  | HCOM; tp = atomic; src = atomic; trg = atomic; phi = atomic; body = atomic
    { HCom (tp, src, trg, phi, body) }
  | HCOM; tp = atomic; src = atomic; trg = atomic; body = atomic
    { AutoHCom (tp, src, trg, body) }
  | COM; fam = atomic; src = atomic; trg = atomic; phi = atomic; body = atomic
    { Com (fam, src, trg, phi, body) }

plain_term_or_cof: t = plain_term | t = cof {t}

motive:
  | LBR names = list(name) RRIGHT_ARROW body = term RBR
    { BN {names; body} }

cases:
  | LSQ option(PIPE) cases = separated_list(PIPE, case) RSQ
    { cases }

case:
  | p = pat RRIGHT_ARROW t = term
    { p, t }

cof_case:
  | phi = located(plain_atomic_or_cof) RRIGHT_ARROW t = term
    { phi, t }

pat_lbl:
  | REFL
    { "refl" }
  | ZERO
    { "zero" }
  | SUC
    { "suc" }
  | lbl = ATOM
    { lbl }


pat:
  | lbl = pat_lbl args = list(pat_arg)
   { Pat {lbl; args} }

pat_arg:
  | ident = name
    { `Simple (Some ident) }
  | LBR i0 = name RRIGHT_ARROW i1 = name RBR
    { `Inductive (Some i0, Some i1) }

tele_cell:
  | LPR name = name; COLON tp = term; RPR
    { Cell {name; tp} }
