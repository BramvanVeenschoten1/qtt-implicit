module Main where

import Parser 
import Utils 
import Elaborator
import ElabMonad
import Prettyprint
--import Declaration
import Core
--import Elaborator
--import Normalization
--import Substitution
import Modules
--import Data.Functor
--import Data.Map
import System.Environment 
import Control.Monad.RWS
--import System.IO
--import Data.ByteString.Builder
--import Control.Monad
import Substitution

{- here we do IO
get modules and verify, print signatures
-}

{-
TODO:
- elaborator:
  - insert constraints
  - generate fresh metavariables
  - genterate guarded constants
  - build choice constraints
- constraint solver
  - reduce with metavariables
  - simplify use-env trees
  - detect and solve pattern constraints
  - solve choice constraints
-}

main :: IO ()
main = getArgs >>= openFiles >>= checkFiles where

  openFiles :: [String] -> IO [(String,String)]
  openFiles = mapM (\name -> do file <- readFile name; pure (name,file))

  checkFiles :: [(String,String)] -> IO ()
  checkFiles files = case mapM (uncurry parse) files >>= checkModules of
    Left e -> putStrLn e
    Right result -> do
      putStrLn result