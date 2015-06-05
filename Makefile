all: interpreter
# all: interpreter deps

interpreter: Interpret.hs Interpreter.hs Misc.hs
	ghc --make Interpret.hs -o interpreter

deps :
	happy -gca Parshl.y
	alex -g Lexshl.x
	latex Docshl.tex; dvips Docshl.dvi -o Docshl.ps
	ghc --make Testshl.hs -o Testshl
clean:
	-rm -f *.log *.aux *.hi *.o *.dvi
	-rm -f Docshl.ps
	-rm -f interpreter
distclean: clean
	-rm -f Docshl.* Lexshl.* Parshl.* Layoutshl.* Skelshl.* Printshl.* Testshl.* Absshl.* Testshl ErrM.* SharedString.* shl.dtd XMLshl.* Makefile*

