module Language.Prolog.REPL where

import Control.Monad.Trans
import Data.Char
import Data.Term
import Language.Prolog.Parser
import Language.Prolog.Syntax
import Language.Prolog.Semantics
import Text.ParserCombinators.Parsec hiding (space)
import Text.PrettyPrint (vcat, punctuate, space)

import System.Environment
import System.Console.Haskeline

main = do
  args <- getArgs
  case args of
   []   -> start []
   [fp] -> either (error.show) start =<< parseFromFile program fp

start cc = do putStrLn usage
              runInputT defaultSettings (loop [c | Right c <- cc])

loop cc =  do
  c <- getInputLine "| "
  case c of
    Nothing   -> return ()
    Just line -> runCommand cc line

runCommand cc ('?':'-':rest) = do
  case parse goal "<goal>" (dropWhile isSpace rest) of
    Left err -> outputStrLn $ show err
    Right g  -> printSols (eval cc g)
  loop cc
runCommand cc ('?':'?':'-':rest) = do
  case parse goal "<goal>" (dropWhile isSpace rest) of
    Left err -> outputStrLn $ show err
    Right g  -> outputStrLn (show $ vcat $ punctuate space $ map ppr $ debug cc g)
  loop cc

runCommand cc "??" = outputStrLn (show $ ppr cc) >> loop cc
runCommand cc input = do
  case parse clause "<clause>"  (dropWhile isSpace input) of
    Left err -> outputStrLn $ show err
    Right c  -> loop (c ++ cc)

printSols [] = outputStrLn "no" >> return ()
printSols [s] | isEmpty s = outputStrLn "Yes"
printSols (s:rest) = do
  outputStr (show $ ppr s)
  l <- getInputLine "? "
  case l of
    Just ";" -> printSols rest
    _        -> outputStrLn "yes" >> return ()

usage = "food(apple). -- Add a clause.\n" ++
        "?- food(X).  -- Query.\n" ++
        "??- food(X). -- Trace query.\n" ++
        "??           -- Show all.\n"

