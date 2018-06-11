all:
	happy -gca ParGrammar.y
	alex -g LexGrammar.x
	ghc -dynamic --make TestGrammar.hs -o TestGrammar
	ghc -dynamic --make Program -o zlci

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi TestGrammar zlci

distclean: clean
	-rm -f DocGrammar.* LexGrammar.* ParGrammar.* LayoutGrammar.* SkelGrammar.* PrintGrammar.* TestGrammar.* AbsGrammar.* TestGrammar ErrM.* SharedString.* ComposOp.* grammar.dtd XMLGrammar.* Makefile*
	

