.PHONY: all clean

args = -impredicative-set

all:
	coqc $(args) init.v
	coqc $(args) utils.v
	coqc $(args) univ.v
	coqc $(args) generic.v
	coqc $(args) tactics.v
	coqc $(args) ngmap.v
	coqc $(args) optngmap.v
	coqc $(args) gmap.v
	coqc $(args) examples.v
	coqc $(args) proofs.v

clean:
	rm *.vok *.glob *.vo *.vos *.aux
