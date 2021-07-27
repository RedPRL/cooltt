#! /bin/bash -l

eval $(opam env --root=/root/.opam --set-root)
make test
