# Makefile for CoverTranslator
# Author: Gregoire Hamon, 2004
# Modified: Oct 07 2004, Andreas Abel (haddock)

###################################################################
# WARNING: If you are looking at 'Makefile' here, do not edit it! #
# It has been automatically created from 'Makefile.in'.           #
###################################################################

SHELL = /bin/sh

GHC = ghc
HAPPY = happy
ALEX = alex
HADDOCK = haddock
BNFC = /home/greg/bin/bnfc

GHC_OPTS = -fglasgow-exts
HAPPY_OPTS = -acg

# do not erase ParserExternalCore.hs on a failed happy invocation
# abel, 2004-11-18 added because of happy problems on the SUNs

.PRECIOUS : ParserExternalCore.hs

default: CoverTranslator

CoverTranslator: Cl/Abs.hs Main.hs ParserExternalCore.hs \
	CaseAbstraction.hs LambdaLifting.hs Core2Agda.hs Core2Cl.hs Cl2Fol.hs \
	Fol.hs FolPP.hs FoFrontEnd.hs UnObfusc.hs
	$(GHC) $(GHC_OPTS) --make -package text Main.hs -o CoverTranslator

%/Print.hs %/Lex.x %/Par.y %/Abs.hs %/ErrM.hs: %.cf
	$(BNFC) -d $<

%.hs : %.x
	$(ALEX) $<

%.hs : %.y
	$(HAPPY) $(HAPPY_OPTS) $<

clean:
	rm -f *~ *.o *.hi *.hcr Main CoverTranslator ParserExternalCore.info \
		ParserExternalCore.hs Agda/*.o Agda/*.hi Cl/*.o Cl/*.hi

distclean: clean
	rm -rf Agda Cl
	rm -rf doc Makefile

######################### Build documentation ##################

# To build a HsDoc-style HTML-linked doc of the source, compile "HsDoc.hs"
# to "hsdoc" and do a "make doc".

# The following will created directory doc/ with HTML version of the 
# passed source files.  

doc:
	hsdoc *hs

hsfiles=CaseAbstraction.hs LambdaLifting.hs Core2Agda.hs Core2Cl.hs \
	FoFrontEnd.hs
doc=haddock
# where to put the haddock generated documentation
# Andreas: I changed this to 'haddock' since 'doc' is used by HsDoc

$(doc):
	mkdir -p $(doc)
	$(HADDOCK) -o $(doc) -h $(hsfiles)

.PHONY: doc $(doc) clean distclean
