.PHONY: all test

all:
	dune build

test:
	dune exec yapa test/rw.v
	dune exec yapa test/datatypes.v
