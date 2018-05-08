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
the equivalence class a term belongs to; checking equivalence between
two terms can be done by normalizing and then comparing for alpha
equivalence. In particular, this is useful ins something like a
type-checker where we might want to decide.

The central idea of this code, and normalization by evaluation in
general, is to break up the process of producing a normal form into
distinct steps. Instead of some extremely complex process which
somehow crushes an arbitrary term directly into a beta-normal eta-long
form our program proceeds more incrementally.




 - First we convert a term into a beta-normal form tagged with places
   which must be considered for eta-expansion
 - WE
