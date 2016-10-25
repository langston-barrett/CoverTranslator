CFOP = cfop
# CFOP_FLAGS = -v 2

.PHONY: clean test

IMPORTS = -l PropPrelude.hs
SOURCE = Main.hs

test: 
	${CFOP} ${CFOP_FLAGS} ${IMPORTS} ${SOURCE}

clean:
	rm -f *prop_*.otter *.hcr *.o *~ *.hi *.log *.debug_CoverTranslator

