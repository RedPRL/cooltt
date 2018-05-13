## nbe-for-mltt explained

The goal of this document is to give an explanation of
`src/lib/nbe.ml`. The rest of the code in this repository is just
scaffolding to allow the user to quickly interact with this code and
not of much interest.

First, let us define the type theory we're working with. It's a
variant of Martin-Löf type theory. I will not write down all the typing
rules since most are standard (and better explained at
length). Instead I will list the syntax of the type theory with some
informal explanation.

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
   the eliminator: `(fst p)` and `(snd p)`. Like functions, there's a
   corresponding eta rule

        p = (pair (fst p) (snd p))

 - Finally, there are universes. They don't do much of anything
   special in this code but there's a cumulative hierarchy.

The goal of this code is quite simple: take a term and its type in
this language and produce its beta-normal eta-long form. This
procedure is more than merely evaluating it: normalization like this
will proceed under binders and ensure that everything is fully
eta-expanded. This is useful because it produces a canonical member of
the equivalence class a term belongs to under definitional
equivalence. Checking equivalence between two terms can be done by
normalizing and then comparing for alpha equivalence. In particular,
this is useful in something like a type-checker where we might want to
compare types for equality.

The central idea of this code, and normalization by evaluation in
general, is to break up the process of producing a normal form into
distinct steps. We first "evaluate" the code into a new representation
which does not admit any beta reductions and simultaneously tag every
part of the term that might need eta expansion. This representation is
the "semantic domain". Next we "quote" the term from the semantic
domain back into the syntax and perform the tagged eta
expansions. There are many variants on NbE but this variant seems
to strike a pleasant balance between scalability and simplicity.

## Data Types

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

It is worth taking a moment to clarify the binding structure. We use
De Bruijn indices for representing variables so the binding in terms
is silent. In the above, I have annotated which subterms bind
variables with `(* BINDS *)` and `(* BINDS 2 *)` in the case of the
"successor" case of natrec which binds 2 variables.

As is good style, all of these declarations are contained in the
module `Syn`.

Next up is the semantic domain. The semantic domain is stratified into
3 separate syntactic categories: values, normal forms, and neutral
terms. These are represented with 3 different OCaml types and are all
contained in the module `D`.

``` ocaml
type env = t list
and clos = Clos of {term : Syn.t; env : env}
and clos2 = Clos2 of {term : Syn.t; env : env}
and t =
  | Lam of clos
  | Neutral of {tp : t; term : ne}
  | Nat
  | Zero
  | Suc of t
  | Pi of t * clos
  | Sig of t * clos
  | Pair of t * t
  | Uni of Syn.uni_level
and ne =
  | Var of int (* DeBruijn levels for variables *)
  | Ap of ne * nf
  | Fst of ne
  | Snd of ne
  | NRec of clos * nf * clos2 * ne
and nf =
  | Normal of {tp : t; term : t}
```

All 3 of the categories are mutually recursive. Values, in the code
`t`, contain terms which have evaluated to a constructor which does
not need to be reduced further. So for instance, `Lam` and `Pair` may
contain computation further inside the term but at least the outermost
constructor is stable and fully evaluated. Now goal is normalization,
which means that we have to deal with open terms. Even if at the
top-level we were to only invoke this procedure on closed terms in
order to normalize under a `Lam`, `Pi`, `Sig`, etc it becomes
necessary to work with open terms.

This means that we have to consider the case that something wants to
reduce further before becoming a value but cannot because its blocked
on something. These are called neutral terms. The canonical example of
a neutral term is just a variable `x`. It's not yet a value but
there's no way to convert it to a value since we have no information
on what `x` is yet. Similarly, if we have some neutral term and we
apply `Fst` to it it's clearly still not a value but we don't have any
way of reducing it further so what's there to do. There's a way of
including neutral terms into the general category of values with the
constructor `Neutral`. This constructor comes equipped with a type
annotation which will prove important later for bookkeeping
purposes. All in all, this means we have a syntactic category
comprised of "eliminators stacked onto variables" and that is all that
`ne` is.

The final category, `nf`, is a special class of values coming from the
style of NbE we use. It associates a type with a value so that later
during quotation we can eta expand it appropriately. In literature
this is usually written as a shift, ↑ᴬ. Since we use `nf` in various
places this ensures that as we go through the process of quotation we
always have sufficient annotations to determine how to quote a term.

One other design decision in the representation of terms under a
binders. In other words, what should `D.Lam` contain? Some
presentations of NbE make use of the host language's function space
for instance, so that `D.Lam` would take `D.t -> D.t`. This has the
advantage of being quite slick because application is free and binding
is simpler. On the other hand, it becomes more difficult to construct
the semantic domain mathematically (domains are often used) which
complicates the proof of correctness. For our purposes though we opt
for the "defunctionalized" variant where terms under a binder are
represented as closures. A closure is a syntactic term paired with the
environment in which it was being evaluated when evaluation was
paused.

This means that a closure is a syntactic term with `n + 1` free
variables and an environment of length `n`. The idea is that the `i`th
environment entry corresponds to the `i + 1`th variable in the
term. This information is stored in the record `{term : Syn.t; env :
env}`. Since we have one term which binds 2 variables (the successor
case in natrec) there's also `clos2`. Its underlying data is the same
but we use it only for terms with 2 free variables.

One final remark about the data types, unlike before we use DeBruijn
levels (they count the opposite way) instead of indices. This choice
is advantage because it means we never need to apply a "shift". In
fact by doing binding in these two distinct ways we never need to
perform any sort of substitution or apply adjustment functions to any
of the terms throughout the algorithm.

## Evaluation

With the data types in place, next we turn to defining the two steps
describe above: evaluation and quotation. Evaluation depends on a
collection of functions:

``` ocaml
(* Compute various eliminators *)
val do_rec : D.clos -> D.t -> D.clos2 -> D.t -> D.t
val do_fst : D.t -> D.t
val do_snd : D.t -> D.t

(* Various "application" like moves *)
val do_clos : D.clos -> D.t -> D.t
val do_clos2 : D.clos2 -> D.t -> D.t -> D.t
val do_ap : D.t -> D.t -> D.t

(* Main evaluation function *)
val eval : Syn.t -> D.env -> D.t
```

The evaluation function depends on a good number of extraneous helper
functions. In order to explain it, let us first start with the helper
function and then consider each helper function as it arises.

``` ocaml
let rec eval t env =
  match t with
```

Evaluation starts by casing on the syntactic term `t` and includes on
case for every possible constructor. The case for variables is just
straightforward lookup. One benefit of using DeBruijn indices is that
it's quite straightforward to represent the environment as a list.

``` ocaml
  | Syn.Var i -> List.nth env i
```

The cases for `Nat` and `Zero` are also quite direct because there is
no computation to perform with either of them.

``` ocaml
  | Syn.Nat -> D.Nat
  | Syn.Zero -> D.Zero
```

The case for successor requires slightly more work. The subterm `t`
of `Syn.Suc t` needs to be evaluated. This is done just by recursing
with `eval`. There's no need to worry about adjusting the environment
since no binding takes place.

``` ocaml
  | Syn.Suc t -> D.Suc (eval t env)
```

Next comes the most complicated case, `Syn.NRec`. Recall that `NRec`
takes 4 arguments:

 - The motive, which binds 1 argument
 - The zero case, which binds 0 arguments
 - The successor case, which binds 2 arguments
 - The actual number, which binds 0 arguments

In order to evaluate `NRec` we have the following clause

``` ocaml
  | Syn.NRec (tp, zero, suc, n) ->
    do_rec
      (Clos {term = tp; env})
      (eval zero env)
      (Clos2 {term = suc; env})
      (eval n env)
```

Before we call the helper function `do_rec` to actually do the
recursion we evaluate the closed terms further and construct closures
for the terms we cannot evaluate further. Then `do_rec` will actually
perform the computation.

``` ocaml
let rec do_rec tp zero suc n =
  match n with
  | D.Zero -> zero
  | D.Suc n -> do_clos2 suc n (do_rec tp zero suc n)
  | D.Neutral {term = e} ->
    let final_tp = do_clos tp n in
    let zero' = D.Normal {tp = do_clos tp D.Zero; term = zero} in
    D.Neutral {tp = final_tp; term = D.NRec (tp, zero', suc, e)}
  | _ -> raise (Nbe_failed "Not a number")
```

This function works by casing on `n`. There are 3 cases to
consider. If `n` is `Zero` then we return the `zero` case. If `n` is
`Suc n'`, then we apply the closure `suc` to `n'` and `do_rec tp zero
suc n'`. Let us postpone explaining how `do_clos` and `do_clos2` works
for a moment and instead consider the last case. When `n` is neutral
we cannot evaluate `NRec` in an meaningful way so we construct a new
neutral term. This is done by using `D.Neutral`. This needs the
type of the result which is given by instantiating the motive's
closure with `n`: `do_clos tp n`. Next, we need to convert `zero` from
`D.t` into `D.nf` which again requires a type, constructed in an
analogous way: `do_clos tp D.Zero`. We then produce the final neutral
term:

``` ocaml
D.Neutral {tp = final_tp; term = D.NRec (tp, zero', suc, e)}
```

Now the instantiating of closures uses `eval` again. Remember that
closures are just environments and syntactic term but lacking the last
addition to the environment. This lacking value is what we need to
instantiate the binder. Once we have that, we can just use `eval` to
normalize the term.

``` ocaml
let do_clos (Clos {term; env}) a = eval term (a :: env)

let do_clos2 (Clos2 {term; env}) a1 a2 = eval term (a2 :: a1 :: env)
```

Returning to `eval`, the next set of cases deal with `Pi`. Evaluating
`Syn.Pi` proceeds by normalizing the first subterm and creating a
closure for the second.

``` ocaml
  | Syn.Pi (src, dest) ->
    D.Pi (eval src env, (Clos {term = dest; env}))
```

Similarly for lambdas we just create a closure.

``` ocaml
  | Syn.Lam t -> D.Lam (Clos {term = t; env})
```

The case for application is slightly more involved. We do something to
similar to `do_rec`, it appeals to the helper function `do_ap`.

``` ocaml
  | Syn.Ap (t1, t2) -> do_ap (eval t1 env) (eval t2 env)
```

This helper function `do_ap` is similar to `do_rec`. It takes the
normalized subterms and performs the application when possible,
constructing the neutral term when it's not.

``` ocaml
let do_ap f a =
  match f with
  | D.Lam clos -> do_clos clos a
  | D.Neutral {tp; term = e} ->
    begin
      match tp with
      | D.Pi (src, dst) ->
        let dst = do_clos dst a in
        D.Neutral {tp = dst; term = D.Ap (e, D.Normal {tp = src; term = a})}
      | _ -> raise (Nbe_failed "Not a Pi in do_ap")
    end
  | _ -> raise (Nbe_failed "Not a function in do_ap")
```

This helper function again makes use of `do_clos` to actually do the
application. One quick point is that when applying a neutral type we
actually needed the type it was annotated with. Without this we could
not have determined the type to use for `D.Normal`.

The case for universes is quite direct, we just convert `Syn.Uni i`
to the corresponding `D.Uni i`.

``` ocaml
  | Syn.Uni i -> D.Uni i
```

All that's left is the cases for sigma types. The case for `Syn.Sig`
is identical to the case for `Syn.Pi`.

``` ocaml
  | Syn.Sig (t1, t2) -> D.Sig (eval t1 env, (Clos {term = t2; env}))
```

The case for pairs proceeds by evaluating both the left and the right
half and packs them back into `Syn.Pair`.

``` ocaml
  | Syn.Pair (t1, t2) -> D.Pair (eval t1 env, eval t2 env)
```

All that remains are the eliminators: `Fst` and `Snd`. For these we
again just appeal to some helper functions

``` ocaml
  | Syn.Fst t -> do_fst (eval t env)
  | Syn.Snd t -> do_snd (eval t env)
```

These helper functions again perform the evaluation if it's possible
and if it's not they construct a new neutral term. The only slight
complication is that `do_snd` must appeal to `do_fst`. This
dependency comes from the fact that the type of `Snd` mentions `Fst`:
`fst p : B (snd p)` if `p : Sig A B`. Below is the code for `do_snd`
since it includes everything interesting about `do_fst` so I have
elided it.

``` ocaml
let do_snd p =
  match p with
  | D.Pair (_, p2) -> p2
  | D.Neutral {tp = D.Sig (_, clo); term = ne} ->
    let fst = do_fst p in
    D.Neutral {tp = do_clos clo fst; term = D.Snd ne}
  | _ -> raise (Nbe_failed "Couldn't snd argument in do_snd")
```

## Read Back/Quotation

Now we have a way to take a syntactic term and convert it to a
semantic term which has no beta redexes. Now what remains is the
"quotation" side of the algorithm. We need a function converting
semantic terms back to syntactic ones.

These functions are the "read back" functions. We define 3 free forms
of read back: one for normal forms, one for neutral terms, and one for
types. The last one is slightly different than the original
presentation in Abel but simplifies the program. Since types can be
read back without a type annotation having a distinguished read back
for them which doesn't require annotations means that the motive in
`D.NRec` does not need an annotation. The signatures for the three
functions is as follows.

``` ocaml
val read_back_nf : int -> D.nf -> Syn.t
val read_back_tp : int -> D.t -> Syn.t
val read_back_ne : int -> D.ne -> Syn.t
```

All of these functions take a level to work with. It is the `int`
argument, say `n`. This is needed for places where we need to generate
a fresh variable. The semantic representation uses DeBruijn levels
though so the number of binders we're under in order to generate the
appropriate fresh variable. The invariant maintained is that the next
binder binds `D.Var n`.

Let us start with `read_back_nf`. The first case is for functions,
this is where eta expansion is performed.

``` ocaml
let rec read_back_nf size nf =
  match nf with
  | D.Normal {tp = D.Pi (src, dest); term = f} ->
    let arg = mk_var src size in
    let nf = D.Normal {tp = do_clos dest arg; term = do_ap f arg} in
    Syn.Lam (read_back_nf (size + 1) nf)
```

When we're quoting a normal form that is tagged as a function we
create a new fresh variable with `mk_var` at the type `src` and with
`size`. `mk_var` here is just shorthand for building a variable and
using the `Neutral` constructor to treat it as a value:

``` ocaml
let mk_var tp lev = D.Neutral {tp; term = D.Var lev}
```

With this, we can then apply the function to this new fresh argument
and create a new normal form at the output type. By then quoting this
and wrapping the result in a lambda we ensure that all functions are
eta long as we wanted. One thing to notice here is that we never
actually cared what `f` was. We rely on `do_ap` to handle actually
handling whatever forms a function can take and such details don't
need to appear in the read back code.

The code for pairs is similar, we also want to perform eta expansion
so we take `p` and quote `fst p` and `snd p` and return the pair of
those two terms.

``` ocaml
  | D.Normal {tp = D.Sig (fst, snd); term = p} ->
    let fst' = do_fst p in
    let snd = do_clos snd fst' in
    let snd' = do_snd p in
    Syn.Pair
      (read_back_nf size (D.Normal { tp = fst; term = fst'}),
       read_back_nf size (D.Normal { tp = snd; term = snd'}))
```

The code for numbers is less slick since we actually have to case on
what the number is. There's a case for zero, successor and neutral
terms. All of them proceed by recursing when necessary and appealing
to the appropriate read back function.

``` ocaml
  | D.Normal {tp = D.Nat; term = D.Zero} -> Syn.Zero
  | D.Normal {tp = D.Nat; term = D.Suc nf} ->
    Syn.Suc (read_back_nf size (D.Normal {tp = D.Nat; term = nf}))
  | D.Normal {tp = D.Nat; term = D.Neutral {term = ne}} -> read_back_ne size ne
```

Next comes a series of cases for reading back types. These are normal
forms where the type is `Uni i` for some `i`. All of these cases are
roughly the same. Below is the code for `Pi` as an example.

``` ocaml
  | D.Normal {tp = D.Uni i; term = D.Pi (src, dest)} ->
    let var = mk_var src size in
    Syn.Pi
      (read_back_nf size (D.Normal {tp = D.Uni i; term = src}),
       read_back_nf (size + 1) (D.Normal {tp = D.Uni i; term = do_clos dest var}))
```

This has the same flavor as the case for functions: we create a fresh
variable using `size` in order to apply the closure stored in
`dest`. Then we just read back the two subterms and store them in
`Syn.Pi`. Also notice that we increment `size` for the `dest` case
since we have to go under a binder.

The final case for just ensures that if we have a neutral type we
handle it correctly. A neutral type can only ever be occupied by a
neutral term so we just forward it to `read_back_ne`.

``` ocaml
  | D.Normal {tp = D.Neutral _; term = D.Neutral {term = ne}} -> read_back_ne size ne
```

The next function is `read_back_tp`. This is almost like the read back
for normal forms but deals directly with `D.t` so there is no
annotation tell us what type we're reading back at. The function
itself just assumes that `d` is some term of type `Uni i` for some
`i`. This, however, means that the cases are almost identical to the
type cases in `read_back_nf`. The pi case is presented again as a
contrast.

``` ocaml
  | D.Pi (src, dest) ->
    let var = mk_var src size in
    Syn.Pi (read_back_tp size src, read_back_tp (size + 1) (do_clos dest var))
```

The only difference is that we don't construct normal forms and we
call `read_back_tp` recursively. This just leaves us to discuss
`read_back_ne`. The first case handles the ugly conversion from
DeBruijn levels to indices.

``` ocaml
let read_back_ne size ne =
  match ne with
  | D.Var x -> Syn.Var (size - (x + 1))
```

This formula is slightly mysterious but correct. It can be derived by
writing out `0..n` in one direction in `n..0` in the other and
observing the relationship between the two numbers in each column. The
case for application is just done by calling the appropriate recursive
functions.

``` ocaml
  | D.Ap (ne, arg) ->
    Syn.Ap (read_back_ne size ne, read_back_nf size arg)
```

The case for `D.NRec` is unfortunately the worst piece of code in the
entire algorithm. The issue is that we have to construct all the types
to annotate things with before we can recursively quote the subterms.

``` ocaml
  | D.NRec (tp, zero, suc, n) ->
    let tp_var = mk_var D.Nat size in
    let applied_tp = do_clos tp tp_var in
    let applied_suc_tp = do_clos tp (D.Suc tp_var) in
    let tp' = read_back_tp (size + 1) applied_tp in
    let suc_var = mk_var applied_tp (size + 1) in
    let applied_suc = do_clos2 suc tp_var suc_var in
    let suc' =
      read_back_nf (size + 2) (D.Normal {tp = applied_suc_tp; term = applied_suc}) in
    Syn.NRec (tp', read_back_nf size zero, suc', read_back_ne size n)
```

This code is really doing just what the application case does. The
extra work is to find the right types for variables so that we can
instantiate closures. For instance, we make a variable of type `Nat`
so that we can instantiate `tp` before we quote it. For `succ` we have
to create a variable of type `Nat` and then a variable of type `tp X`
where `X` refers to the variable we just created. This is because
`succ` has a dependent type. Finally, once everything is instantiated
we just read it all back using the only functions of the correct type.

The final two cases are for `Fst` and `Snd`. They are both identical
and just read back the subterm using `read_back_ne`. There is no need
to adjust the environment nor instantiate any closures.

``` ocaml
  | D.Fst ne -> Syn.Fst (read_back_ne size ne)
  | D.Snd ne -> Syn.Snd (read_back_ne size ne)
```

This concludes the read back algorithm. Notice how easy it was to get
eta expansion. Since we had the types of what we were quoting if we
were ever quoting a normal form that we thought needed eta expansion
it was straightforward to just perform the expansion right then and
there.

## Putting It All Together

In order to actually run the algorithm, we need to write a little bit
more glue code. We are given a term, its type, and the environment it
lives in. The environment we're given is a syntactic environment so we
first have an algorithm to convert that into a semantic
environment. For each entry we use `eval` to convert it to a semantic
type, `tp` and then add a neutral term `Var i` at type `tp` where `i`
is the length of the prefix of the context we've converted. In code:

``` ocaml
let rec initial_env env =
  match env with
  | [] -> []
  | t :: env ->
    let env' = initial_env env in
    let d = D.Neutral {tp = eval t env'; term = D.Var (List.length env)} in
    d :: env'
```

This is just ensuring that we have an environment which will map the
`i`th variable to `Var i` with the appropriate type. Notice that we
don't need to worry about eta expanding them; all of that will be
handled in read back.

With this conversion defined it's straightforward to define
normalization. We first evaluate a term and its type in this
environment. We then read it back with `read_back_nf`.

``` ocaml
let normalize ~env ~term ~tp =
  let env' = initial_env env in
  let tp' = eval tp env' in
  let term' = eval term env' in
  read_back_nf (List.length env') (D.Normal {tp = tp'; term = term'})
```

The completes the presentation of this algorithm.
