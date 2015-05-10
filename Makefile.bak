all:
	happy -gca Parshl.y
	alex -g Lexshl.x
	latex Docshl.tex; dvips Docshl.dvi -o Docshl.ps
	ghc --make Testshl.hs -o Testshl
clean:
	-rm -f *.log *.aux *.hi *.o *.dvi
	-rm -f Docshl.ps
distclean: clean
	-rm -f Docshl.* Lexshl.* Parshl.* Layoutshl.* Skelshl.* Printshl.* Testshl.* Absshl.* Testshl ErrM.* SharedString.* shl.dtd XMLshl.* Makefile*

