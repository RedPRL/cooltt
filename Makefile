OPAM=opam
EXEC=${OPAM} config exec
DUNE=${EXEC} dune --
PIN_DEPENDS=bantorra yuujinchou

.PHONY: all build clean doc install test snapshot format

all: build

upgrade-pins:
	${OPAM} update --upgrade --quiet ${PIN_DEPENDS}

build:
	@${DUNE} build @install

clean:
	@${DUNE} clean

doc:
	@${DUNE} build @doc

install:
	${OPAM} reinstall cooltt

test:
	@${DUNE} build @install @runtest

snapshot:
	@${DUNE} promote

format:
	./format.sh
