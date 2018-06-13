.PHONY: all clean repl test

all:
	jbuilder build --dev

repl:
	jbuilder utop src -- -require pdr-programming

test:
	jbuilder runtest -f --dev

clean:
	jbuilder clean

