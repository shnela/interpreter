-- Jakub Kuszneruk jk320790

module Main where

import Control.Monad (liftM)
import System.Environment

import Lexshl
import Parshl
import Absshl
import Interpreter
import TypeChecker
import ErrM
import Control.Monad.Trans

import Misc

runFile :: FilePath -> IO ()
runFile f = putStrLn f >> readFile f >>= \s -> show_info s >> debug s >> run s
-- runFile f = putStrLn f >> readFile f >>= \s -> run s

main :: IO ()
main = do args <- getArgs
          case args of
            [] -> error "usage `interpreter <input file>`"
            fs -> mapM_ runFile fs


run :: String -> IO ()
run s = let ts = myLexer s in case pProg ts of
           Bad msg -> do putStrLn msg;
           Ok p   -> do
                      case (interpret p) of
                        Ok (St (_, _, _, _, Bst bst, _, _, _, _, _)) -> putStrLn $ show $ reverse bst
                        Bad c -> return()
                      return ();


-- print final state of a program
debug s = let ts = myLexer s in case pProg ts of
           Bad msg   -> do putStrLn msg;
           Ok p   -> do putStrLn $show (interpret p);
                        return ();


-- shows parsed file
show_info s = putStrLn $show (pProg $ myLexer s) 
