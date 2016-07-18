module Main where

import System.Environment
import Language.C
import Language.C.System.GCC
import Language.C.Transform

main :: IO ()
main = do
  cc <- return $ newGCC "gcc"
  options <- getArgs
  result <- parseCFile cc Nothing [] (options !! 0)
  case result of
    Left err -> putStr $ show err
    Right unit -> do 
      done <- transform unit
      print $ pretty done
