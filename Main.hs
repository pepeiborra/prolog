{-# LANGUAGE ScopedTypeVariables #-}

import System.IO

import Control.Applicative
import Control.Exception
import Control.Monad.State
import Data.IORef
import Data.List
import Language.Prolog.Syntax
import qualified Language.Prolog.Parser as P
import Language.Prolog.Semantics
import System.Console.Editline
import System.Console.Editline.Readline
import System.Environment
import Text.ParserCombinators.Parsec

type M a = StateT St IO a
data St  = St { db :: [Clause] }

commands = [("load", loadFile, True)
           ,("db",   const (get >>= (lift.print.ppr.db)), True)
           ,("quit", const(return ()), False)]

specialCommand :: String -> [String] -> M Bool
specialCommand cmd args =
    case find ((cmd `isPrefixOf`) . fst3) commands of
      Just (_,f,cont) -> f args >> return cont
      Nothing -> lift(putStrLn "Error: unknown command") >> return True

loadFile :: [String] -> M ()
loadFile [fn] = handleIt (\(e::IOException) -> lift(print e)) $ do
    ei_clauses <- lift$ parseFromFile P.program fn
    case ei_clauses of
      Left err -> lift (print err)
      Right cc -> do
        modify (\st -> st{db = cc ++ db st})
        lift$ putStrLn $ "Loaded " ++ show(length cc) ++ " clauses."

main = do
    let config = St { db = [] }
    runStateT (repl work) config
    return ()

repl process = do
         maybeLine <- lift$ readline "?-"
         case maybeLine of
             Nothing -> return () -- ctrl-D
             Just line -> do
                 lift$ addHistory line
                 continue <- process line
                 when continue (repl process)

work :: String -> M Bool
work (':':command) = specialCommand cmd args where
    cmd  = head $ words command
    args = tail $ words command

work query = do case parse P.predicate "" query of
                 Left  err -> lift(print err)
                 Right q   -> do st   <- get
                                 let sols = eval (db st) q
                                 lift$ if null sols then putStrLn "No." else printSols sols
                return True

printSols :: [Environment] -> IO ()
printSols []     = putStrLn "Done."
printSols (s:ss) = do
  print (ppr s)
  cont <- hGetChar stdin
  case cont of
    'q' -> return ()
    _   -> printSols ss

-- Auxiliar stuff
-- --------------
fst3 (a,b,c) = a

--handleIt :: Exception e => (e -> m a) -> m a -> m a
handleIt hnd m = do
  st     <- get
  (a,st') <- lift$ handle (hnd' st) (runStateT m st)
  put st'
  return a
    where hnd' st e = runStateT (hnd e) st