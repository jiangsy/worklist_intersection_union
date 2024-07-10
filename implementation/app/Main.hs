module Main where

import Alg (run)
import System.Environment (getArgs)
import System.Console.GetOpt

data Flag = FilePath String | MonoIU
  deriving (Eq, Show)

options :: [OptDescr Flag]
options =
  [ Option ['m'] ["mono"] (NoArg MonoIU) "mono intersection union",
    Option ['f'] ["file"] (ReqArg FilePath "FILE") "input FILE"
  ]

main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (flags,[file],[]) -> run file (MonoIU `elem` flags)
    (_,_,errs) -> print errs
