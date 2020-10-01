.PHONY: all clean

all:
	coqc -impredicative-set utils.v
	coqc arity.v
	coqc univ.v
	coqc -impredicative-set generic.v

clean:
	rm *.vok *.glob *.vo *.vos
