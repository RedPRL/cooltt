## blott

An implementation of normalization by evaluation (nbe) & semantic type checking for Martin-Löf Type Theory
with dependent products, dependent sums, natural numbers, id, box, and a cumulative hierarchy of universes. This
implementation supports eta-rules for box, pi, and sigma.

For examples, see the `test/` directory.

## building

blott has been built with OCaml 4.06.1 and 4.07.1.

```
$ opam update
$ opam pin add -y blott .               # first time
$ opam upgrade                          # after packages change
```

After this, the executable `blott` should be available. The makefile can be used to rebuild the
package for small tests.

## syntax

This experimental proof assistant supports the following top-level declarations:

 - A definition, written `let NAME : TYPE = TERM`
 - A command to normalize a definition `normalize def NAME`
 - A command to normalize an expression `normalize TERM at TYPE`

Unlike in the paper, names instead of indices are used for the surface syntax. The following are
the valid expressions in blott.

``` ocaml
     (* Let bindings *)
     let NAME = TERM in TERM
     let NAME : TYPE = TERM in TERM
     (* Natural numbers *)
     nat, 0, 1, 2...
     (* Recursion on natural numbers *)
     rec NUMBER at x -> MOTIVE with
     | zero -> TERM
     | suc n, ih -> TERM

     (* Functions *)
     (NAME : TP) -> TP
     fun NAME -> TERM
     TERM TERM

     (* Pairs *)
     (NAME : TP) * TP
     <TERM, TERM>
     fst TERM
     snd TERM

     (* The box modality *)
     [box TP]
     [lock TERM]
     [unlock TERM]

     (* Universes *)
     U<0>,U<1>,...

     (* Identity types *)
     Id TYPE TERM TERM
     refl TERM
     match PRF at x y prf -> MOTIVE with
     | refl x -> TERM
```
