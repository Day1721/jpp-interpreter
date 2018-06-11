{-# LANGUAGE LambdaCase #-}
import System.Environment
import System.Exit

import ParGrammar
import ErrM

import TypeChecker
import Runner

main :: IO ()
main = getArgs >>= \case
    ["--help"] -> printUsage
    [filename] -> runFromFile filename
    [] -> runFromStdin
    _ -> printUsage

printUsage :: IO ()
printUsage = putStrLn "Usage: ./interpreter [filename]" >> exitFailure


runFromFile :: String -> IO ()
runFromFile filename = readFile filename >>= runInterperter

runFromStdin :: IO ()
runFromStdin = getContents >>= runInterperter

runInterperter :: String -> IO ()
runInterperter code = let
    toks = myLexer code
    in case pProgram toks of 
        Bad s -> putStrLn "Parse failed:" >> putStrLn s
        Ok tree -> case parseTypes tree of 
            Left err -> putStrLn "Type Checking failed:" >> putStrLn err
            Right p -> runProgram p

