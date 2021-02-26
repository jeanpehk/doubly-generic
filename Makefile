.PHONY: all clean

args = -impredicative-set

all:
	coqc $(args) init.v
	coqc $(args) utils.v
	coqc $(args) univ.v
	coqc $(args) generic.v
	coqc $(args) examples.v

clean:
	rm *.vok *.glob *.vo *.vos
