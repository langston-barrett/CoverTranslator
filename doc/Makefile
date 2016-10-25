
all: html cfop.txt cfop.ps

html: cfop.html
	mkdir -p html
	(cd html; hacha ../cfop.html)

cfop.ps: cfop.dvi
	dvips -o cfop.ps cfop.dvi

cfop.dvi: cfop.tex
	latex cfop.tex
	latex cfop.tex

cfop.html: cfop.tex
	hevea cfop.tex

cfop.txt: cfop.tex
	hevea -text cfop.tex

clean: 
	rm -rf cfop.html cfop.txt *~ html *.aux *.dvi *.log *.out *.haux \
		*.htoc cfop.ps
