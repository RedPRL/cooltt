OPAM=opam
EXEC=${OPAM} exec
DUNE=${EXEC} dune --
PIN_DEPENDS=bantorra

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
	@${DUNE} build --display=quiet @runtest @test-display

# Here we want full reproducible behavior, ideally, we build all the
# dependencies of the tests before actually running them, as to avoid
# interference. This is possible to do cleanly in Dune 3.0 as `alias`
# got the right semantics, so you can collect all of your tests deps
# in an alias and use `dune build @test-deps` instead of the
# hand-setup below.
TEST_FILE=test/test.exe
test-timings:
	@${DUNE} clean --display=quiet
	@${DUNE} build --display=quiet $(TEST_FILE) $(shell ls test/*.cooltt test/cooltt-lib)
	@${DUNE} build --display=quiet --cache=disabled @runtest @test-display

snapshot:
	@${DUNE} promote

format:
	./format.sh
