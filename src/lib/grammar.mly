%{
  open Concrete_syntax
%}

%token <int> NUMERAL
%token <string> ATOM
%token COLON PIPE AT COMMA RIGHT_ARROW DOT UNDERSCORE
%token LPR RPR LBR RBR LANGLE RANGLE
%token EQUALS
%token TIMES FST SND
%token LAM LET IN END WITH DEF
%token NEXT LATER DFIX
%token BOX SHUT OPEN
%token REC SUC NAT ZERO
%token UNIV
%token QUIT NORMALIZE
%token EOF

%start <Concrete_syntax.signature> sign
%%

decl:
  | LET; nm = ATOM; COLON; tp = term; EQUALS; body = term; DOT
    { Def {name = nm; def = body; tp} }
  | QUIT; DOT { Quit }
  | NORMALIZE; DEF; a = ATOM; DOT
    { NormalizeDef a  }
  | NORMALIZE; tm = term; AT; tp = term; DOT { NormalizeTerm {term = tm; tp} };

sign:
  | EOF { [] }
  | d = decl; s = sign { d :: s };

atomic:
  | LPR; t = term; RPR
    { t }
  | a = ATOM
    { Var a }
  | ZERO
    { Lit 0 }
  | n = NUMERAL
    { Lit n }
  | UNIV; LANGLE; i = NUMERAL; RANGLE
    { Uni i }
  | NAT { Nat }
  | LANGLE left = term; COMMA; right = term; RANGLE
    { Pair (left, right) }
  | LANGLE RANGLE { Bullet };

spine:
  | t = atomic { Term t }
  | LBR; t = term; RBR { Tick t };

term:
  | f = atomic; args = list(spine)
    { Ap (f, args) }
  | LET; name = ATOM; COLON; tp = term; EQUALS; def = term; IN; body = term; END
    { Let (Check {term = def; tp}, Binder {name; body}) }
  | LET; name = ATOM; EQUALS; def = term; IN; body = term; END
    { Let (def, Binder {name; body}) }
  | LPR t = term; AT; tp = term RPR
    { Check {term = t; tp} }
  | SUC; t = term { Suc t }
  | REC; n = term; AT; mot_name = ATOM; RIGHT_ARROW; mot = term; WITH;
    ZERO; RIGHT_ARROW; zero_case = term;
    PIPE; SUC; suc_var = ATOM; COMMA; ih_var = ATOM; RIGHT_ARROW; suc_case = term
    { NRec {
        mot = Binder {name = mot_name; body = mot};
        zero = zero_case;
        suc = Binder2 {name1 = suc_var; name2 = ih_var; body = suc_case};
        nat = n
      } }
  | LAM; name = ATOM; COLON; tp = term; RIGHT_ARROW; body = term
    { Lam (tp, Binder {name; body}) }
  | LPR name = ATOM; COLON; dom = term; RPR; RIGHT_ARROW; cod = term
    { Pi (dom, Binder {name; body = cod}) }
  | LPR name = ATOM; COLON; dom = term; RPR; TIMES; cod = term
    { Sig (dom, Binder {name; body = cod}) }
  | FST; t = term { Fst t }
  | SND; t = term { Snd t }
  | LATER; name = ATOM; RIGHT_ARROW; body = term
    { Later (Binder {name; body}) }
  | NEXT; name = ATOM; RIGHT_ARROW; body = term
    { Next (Binder {name; body}) }
  | BOX; t = term
    { Box t }
  | SHUT; t = term
    { Shut t }
  | OPEN; t = term
    { Open t }
  | DFIX; name = ATOM; COLON; LATER; UNDERSCORE; DOT; tp = term; RIGHT_ARROW; body = term
    { DFix (tp, Binder {name; body}) };
