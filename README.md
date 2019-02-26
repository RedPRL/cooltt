## blott

An implementation of Normalization by Evaluation & semantic type checking for Martin-Löf Type Theory
with dependent products, dependent sums, natural numbers, id, box, and a cumulative hierarchy. This
implementation correctly handles eta for box, pi, and sigma.

For examples, see the `test/` directory.

## building


```
$ opam update
$ opam pin add -y blott . # the first time you build
$ opam upgrade            # after packages change
```

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
     Nat, 0, 1, 2...
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
     fst TERM
     snd TERM

     (* The Box modality *)
     Box TP
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
