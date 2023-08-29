## cooltt

A cool implementation of normalization by evaluation (NbE) & elaboration for
Cartesian cubical type theory.

For examples, see the `test/` directory.

This implementation is forked from `blott`, the implementation artifact of
[Implementing a Modal Dependent Type Theory](https://doi.acm.org/10.1145/3341711)
by Gratzer, Sterling, and Birkedal. Code has been incorporated from
[redtt](https://www.github.com/RedPRL/redtt), implemented by Sterling and
Favonia.

A small collection of example programs is contained in the `test/` directory.
See `test/README.md` for a brief description of each program's purpose.

## Building

cooltt has been built with OCaml 5.0 with [opam 2.0.8](https://opam.ocaml.org/).

### With OPAM

If you are running an older version of OCaml, try executing the following command:

```
$ opam switch create 5.0
```

Once these dependencies are installed cooltt can be built with the following set of commands.

```
$ opam update
$ opam pin add -y cooltt .              # first time
$ opam upgrade                          # after packages change
```

After this, the executable `cooltt` should be available. The makefile can be
used to rebuild the package for small tests. Locally, cooltt is built with
[dune](https://dune.build); running the above commands will also install dune.
Once dune is available the executable can be locally changed and run with the
following:

```
$ make upgrade-pins                     # update and upgrade dependencies in active development
$ dune exec cooltt                      # from the `cooltt` top-level directory
```

### With Nix

First, you'll need the [Nix package manager](https://nixos.org/download.html), and then
you'll need to [install or enable flakes](https://nixos.wiki/wiki/Flakes).

Then, cooltt can be built with the command

```
nix build --impure
```

to put a binary `cooltt` in `result/bin/cooltt`. This is good for if you just want to build
and play around with cooltt.

If you're working on cooltt, you can enter a development shell with an OCaml compiler, dune,
and other tools with

```
nix develop --impure
```

and then build as in the [with OPAM](https://github.com/RedPRL/cooltt/#with-opam=) section
above.

## Acknowledgments

This research was supported by the Air Force Office of Scientific Research under MURI grants FA9550-15-1-0053, FA9550-19-1-0216, and FA9550-21-1-0009. Any opinions, findings and conclusions or recommendations expressed in this material are those of the authors and do not necessarily reflect the views of any sponsoring institution, government or any other entity.
