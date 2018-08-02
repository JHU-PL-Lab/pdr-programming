.PHONY: all clean repl test

all:
	dune build --dev

repl:
	dune utop src -- -require pdr-programming

test:
	dune runtest -f --dev

clean:
	dune clean

