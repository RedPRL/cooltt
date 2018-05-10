## nbe-for-mltt explained

The goal of this document is to give an explanation of
`src/lib/nbe.ml`. The rest of the code in this repository is just
scaffolding to allow the user to quickly interact with this code and
not of much interest.

First, let us define the type theory we're working with. It's a fairly
standard Martin-Löf type theory. I will not write down all the typing
rules since most are obvious and instead list the syntax of the type
theory.

 - We have natural numbers, so a type `Nat` with constructors `zero`
   and `(suc t)`. There is an elimination form
   `(nrec (n motive) z (p i s) n)`. This elimination form is
   characterized by the following rules

        (nrec (n motive) z (p i s) zero) ↦ z : (ap motive zero)
        (nrec (n motive) z (p i s) (suc n)) ↦ (ap (ap s n) (nrec ... n)) : (ap motive (suc n))

   For the convenience of the user of the system, plain old numeric
   literals are supported.

 - Dependent functions are standard, there is `(Pi from (x to))` and
   `(lam (x body))`. This type theory includes an eta rule for lambdas
   so that

        f = (lam (x (ap f x)))

 - Dependent pairs are also standard with `(Sig fst (x snd))` and
   `(pair l r)`. It comes equipped with the negative formulation of
   the eliminator: `(fst p)` and `(snd p)`. Like for functions,
   there's a corresponding eta rule

        p = (pair (fst p) (snd p))

 - Finally, there are universes. They don't do much of anything
   special in this code but there's a cumulative hierarchy.

The goal of this code is quite simple: take a term and its type in
this language and produce its beta-normal eta-long form. This
procedure is more than merely evaluating it: normalization like this
will proceed under binders and ensure that everything is fully
eta-expanded. This is useful because it produces a canonical member of
the equivalence class a term belongs to. Checking equivalence between
two terms can be done by normalizing and then comparing for alpha
equivalence. In particular, this is useful in something like a
type-checker where we might want to compare types for beta-eta
equality.

The central idea of this code, and normalization by evaluation in
general, is to break up the process of producing a normal form into
distinct steps. We first "evaluate" the code into a new representation
which does not admit any beta reductions and simultaneously tag every
part of the term that might need eta expansion. This representation is
the "semantic domain". Next we "quote" the term from the semantic
domain back into the syntax and perform the tagged eta
expansions. There are many variants on NbE but this variant seems
to strike a pleasant balance between scalability and simplicity.

First let us review the representation of the surface syntax.

``` ocaml
type uni_level = int
type t =
  | Var of int (* DeBruijn indices for variables *)

  (* nats *)
  | Nat
  | Zero
  | Suc of t
  | NRec of (* BINDS *) t * t * (* BINDS 2 *) t * t

  (* functions *)
  | Pi of t * (* BINDS *) t
  | Lam of (* BINDS *) t
  | Ap of t * t

  (* pairs *)
  | Sig of t * (* BINDS *) t
  | Pair of t * t
  | Fst of t
  | Snd of t

  (* universes *)
  | Uni of uni_level

type env = t list
```

This representation of terms is fairly standard. It is worth taking a
moment to clarify the binding structure. We use De Bruijn indices for
representing variables so the binding in terms is silent. In the
above, I have annotated which subterms bind variables with `(* BINDS
*)` and `(* BINDS 2 *)` in the case of the "successor" case of natrec
which binds 2 variables.

Next up is the semantic domain.
