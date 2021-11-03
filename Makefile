build:
	dune build

test:
	dune exec test/test.exe

clean:
	dune clean

.PHONY: build test clean
