module Main where

import System.Environment (getArgs)
import Alg (run)

main :: IO ()
main = do
  args <- getArgs
  case args of
    []     -> print "Error"
    file:_ -> run file