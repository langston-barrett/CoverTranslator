CFOP = cfop
# CFOP_FLAGS = -v 2

.PHONY: clean test

IMPORTS = -l Simple.hs -l PropPrelude.hs
SOURCE = Merge.hs

mkhcr = ghc -fextt-core -c
agdachecker = agdachecker ../../lib/prelude.agda

default : Merge.agda

%.hcr : %.hs
	$(mkhcr) $<

Simple.agda : Simple.hs
	hs2agda $<
	$(agdachecker) $@

PredPrelude.agda : PredPrelude.hs
	hs2agda $<
	$(agdachecker) $@ 

Merge.agda : Merge.hs Simple.agda PredPrelude.agda
	hs2agda Merge.hs
	$(agdachecker) Simple.agda PredPrelude.agda $@ 

test: 
	${CFOP} ${CFOP_FLAGS} ${IMPORTS} ${SOURCE}

agdaclean:
	rm Simple.agda PredPrelude.agda Merge.agda

clean:
	rm -f *prop_*.otter *.hcr *.o *~ *.hi *.log *.debug_CoverTranslator 

