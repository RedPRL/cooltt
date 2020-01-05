## cooltt

An implementation of normalization by evaluation (nbe) & elaboration for Martin-Löf Type
Theory with dependent products, dependent sums, natural numbers, and identity types.

For examples, see the `test/` directory.

This implementation is forked from `blott`, the implementation artifact of
[Implementing a Modal Dependent Type Theory](https://doi.acm.org/10.1145/3341711) by Gratzer,
Sterling, and Birkedal.

## building

cooltt has been built with OCaml 4.08.1 with [opam 2.0](https://opam.ocaml.org/). Once
these dependencies are installed cooltt can be built with the following set of commands.

```
$ opam update
$ opam pin add -y cooltt .               # first time
$ opam upgrade                          # after packages change
```

After this, the executable `cooltt` should be available. The makefile can be used to rebuild the
package for small tests. Locally, cooltt is built with [dune](https://dune.build), running the above
commands will also install dune. Once dune is available the executable can be locally changed and
run with the following:

```
$ dune exec ./src/bin/main.exe          # from the `cooltt` top-level directory
```

## syntax

This experimental proof assistant supports the following top-level declarations:

 - A definition, written `let NAME : TYPE = TERM`
 - A command to normalize an expression `normalize TERM`; in this command, `TERM` must be synthesizable. 

Unlike in the paper, names instead of indices are used for the surface syntax. The following are
the valid expressions in cooltt.

     -- Let bindings
     let NAME = TERM in TERM
     let NAME : TYPE = TERM in TERM

     -- Natural numbers 
     nat, 0, 1, 2...

     -- Recursion on natural numbers
     rec NUMBER at x => MOTIVE with [
     | zero => TERM
     | suc (n => ih) => TERM
     ]

     -- Functions
     (NAME : TP) -> TP
     \NAME => TERM
     TERM TERM

     -- Pairs
     (NAME : TP) * TP
     [TERM, TERM]
     fst TERM
     snd TERM

     -- Identity
     Id TYPE TERM TERM
     refl TERM
     match PRF at x y prf -> MOTIVE with
     | refl x -> TERM

A small collection of example programs is contained in the `test/` directory. See `test/README.md`
for a brief description of each program's purpose.
