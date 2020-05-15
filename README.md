## cooltt

A cool implementation of normalization by evaluation (nbe) & elaboration for
Cartesian cubical type theory.

For examples, see the `test/` directory.

This implementation is forked from `blott`, the implementation artifact of
[Implementing a Modal Dependent Type Theory](https://doi.acm.org/10.1145/3341711)
by Gratzer, Sterling, and Birkedal. Code has been incorporated from
[redtt](https://www.github.com/RedPRL/redtt), implemented by Sterling and
Favonia.

## building

cooltt has been built with OCaml 4.10.0 with [opam 2.0.5](https://opam.ocaml.org/). Once
these dependencies are installed cooltt can be built with the following set of commands.

```
$ opam update
$ opam pin add -y cooltt .              # first time
$ opam upgrade                          # after packages change
```

After this, the executable `cooltt` should be available. The makefile can be
used to rebuild the package for small tests. Locally, cooltt is built with
[dune](https://dune.build), running the above commands will also install dune.
Once dune is available the executable can be locally changed and run with the
following:

```
$ dune exec ./src/bin/main.exe          # from the `cooltt` top-level directory
```


A small collection of example programs is contained in the `test/` directory.
See `test/README.md` for a brief description of each program's purpose.
