CFOP = cfop
# CFOP_FLAGS = -v 2

.PHONY: clean test

IMPORTS = -l PropPrelude.hs
SOURCE = Queue.hs

test: 
	${CFOP} ${CFOP_FLAGS} ${IMPORTS} ${SOURCE}

clean:
	rm -f *.otter *.hcr *.o *~ *.hi *.log *.debug_CoverTranslator

