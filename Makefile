.PHONY: all clean

args = -impredicative-set

all:
	coqc $(args) init.v
	coqc $(args) utils.v
	coqc $(args) arity.v
	coqc $(args) univ.v
	coqc $(args) generic.v
	coqc $(args) examples.v
	coqc $(args) proofs.v

clean:
	rm *.vok *.glob *.vo *.vos
