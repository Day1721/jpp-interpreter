(bnfc -m --haskell .\grammar.cf) -and (make)
ghc --make -o xlc main.hs
