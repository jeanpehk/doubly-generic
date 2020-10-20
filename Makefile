.PHONY: all clean

args = -impredicative-set

all:
	coqc $(args) utils.v
	coqc arity.v
	coqc $(args) univ.v
	coqc $(args) generic.v

clean:
	rm *.vok *.glob *.vo *.vos
