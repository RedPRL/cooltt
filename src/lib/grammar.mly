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
%type <con_> atomic atomic_or_ap ap eq cof term term_or_cof bracketed
%type <pat> pat
%type <pat * con> case
%type <cell> tele_cell
%%


located(X):
  | e = X
    { locate $loc e }

name:
  | s = ATOM
    { s }
  | UNDERSCORE
    { "_" }

decl:
  | DEF; nm = name; COLON; tp = located(term); EQUALS; body = located(term)
    { Def {name = nm; def = body; tp} }
  | QUIT
    { Quit }
  | NORMALIZE; tm = located(term)
    { NormalizeTerm tm }

sign:
  | EOF
    { [] }
  | d = decl; s = sign
    { d :: s }

eq:
  | r = located(atomic) EQUALS s = located(atomic)
    { CofEq (r, s) }

cof:
  | eq = eq
    { eq }
  | BOUNDARY term = located(term)
    { CofBoundary term }
  | phi = located(atomic_or_eq) JOIN psi = located(atomic_or_eq)
    { Join (phi, psi) }
  | phi = located(atomic_or_eq) MEET psi = located(atomic_or_eq)
    { Meet (phi, psi) }

atomic:
  | LBR term = term_or_cof RBR
    { term }
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

atomic_or_eq: t = atomic | t = eq {t}

atomic_or_cof: t = atomic | t = cof {t}

bracketed:
  | left = located(term) COMMA right = located(term)
    { Pair (left, right) }
  | cases = separated_list(PIPE, cof_case)
    { CofSplit cases }
  | PIPE cases = separated_list(PIPE, cof_case)
    { CofSplit cases }
  | t = located(term_or_cof)
    { Prf t }

ap:
  | f = located(atomic); args = nonempty_list(located(atomic))
    { Ap (f, args) }

atomic_or_ap : t = atomic | t = ap {t}

term:
  | t = atomic_or_ap
    { t }
  | UNFOLD; names = nonempty_list(name); IN; body = located(term);
    { Unfold (names, body) }
  | LET; name = name; COLON; tp = located(term); EQUALS; def = located(term); IN; body = located(term)
    { Let ({node = Ann {term = def; tp}; info = def.info}, B {name; body}) }
  | LET; name = name; EQUALS; def = located(term); IN; body = located(term)
    { Let (def, B {name; body}) }
  | LPR t = located(term); AT; tp = located(term) RPR
    { Ann {term = t; tp} }
  | SUC; t = located(term)
    { Suc t }
  | ID; tp = located(atomic); left = located(atomic); right = located(atomic)
    { Id (tp, left, right) }
  | LAM; names = list(name); RRIGHT_ARROW; body = located(term)
    { Lam (BN {names; body}) }
  | LAM; ELIM; cases = cases
    { LamElim cases }
  | ELIM; scrut = located(term); AT; mot = motive; cases = cases
    { Elim {mot; cases; scrut}}
  | tele = nonempty_list(tele_cell); RIGHT_ARROW; cod = located(term)
    { Pi (tele, cod) }
  | tele = nonempty_list(tele_cell); TIMES; cod = located(term)
    { Sg (tele, cod) }
  | dom = located(atomic_or_ap) RIGHT_ARROW cod = located(term)
    { Pi ([Cell {name = "_"; tp = dom}], cod) }
  | dom = located(atomic_or_ap) TIMES cod = located(term)
    { Sg ([Cell {name = "_"; tp = dom}], cod) }
  | SUB tp = located(atomic) phi = located(atomic) tm = located(atomic)
    { Sub (tp, phi, tm) }
  | FST; t = located(term)
    { Fst t }
  | SND; t = located(term)
    { Snd t }

  | PATH; tp = located(atomic); left = located(atomic); right = located(atomic)
    { Path (tp, left, right) }

  | COE; fam = located(atomic); src = located(atomic); trg = located(atomic); body = located(atomic)
    { Coe (fam, src, trg, body) }
  | HCOM; tp = located(atomic); src = located(atomic); trg = located(atomic); phi = located(atomic); body = located(atomic)
    { HCom (tp, src, trg, phi, body) }
  | HCOM; tp = located(atomic); src = located(atomic); trg = located(atomic); body = located(atomic)
    { AutoHCom (tp, src, trg, body) }
  | COM; fam = located(atomic); src = located(atomic); trg = located(atomic); phi = located(atomic); body = located(atomic)
    { Com (fam, src, trg, phi, body) }

term_or_cof: t = term | t = cof {t}

motive:
  | LBR names = list(name) RRIGHT_ARROW body = located(term) RBR
    { BN {names; body} }

cases:
  | LSQ option(PIPE) cases = separated_list(PIPE, case) RSQ
    { cases }

case:
  | p = pat RRIGHT_ARROW t = located(term)
    { p, t }

cof_case:
  | phi = located(atomic_or_cof) RRIGHT_ARROW t = located(term)
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
  | LPR name = name; COLON tp = located(term); RPR
    { Cell {name; tp} }
