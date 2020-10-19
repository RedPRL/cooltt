OPAM=opam
EXEC=${OPAM} config exec
DUNE=${EXEC} dune --

.PHONY: all build clean test top test doc

all: build

build:
	@${DUNE} build @install

clean:
	@${DUNE} clean

doc:
	@${DUNE} build @doc

install:
	${OPAM} reinstall --working-dir cooltt

test:
	@./test.sh
