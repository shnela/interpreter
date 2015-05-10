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

runFile :: FilePath -> IO ()
runFile f = putStrLn f >> readFile f >>= run

main :: IO ()
main = do args <- getArgs
          case args of
            [] -> error "usage `interpreter <input file>`"
            fs -> mapM_ runFile fs


run :: String -> IO ()
run s = let ts = myLexer s in case pProg ts of
           Bad msg   -> do putStrLn msg;
           Ok p   -> do putStrLn $show (interpret p);
                        return ();
