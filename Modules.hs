module Modules where

import Control.Monad
import Control.Monad.State.Lazy
import Core
import Data.Either
import Data.Function
import Data.List as L
import Data.Map as M
import Data.Maybe
import Debug.Trace
import Declaration
import ElabMonad
import Lexer (Loc)
import Parser
import Prettyprint
import Utils

import Control.Monad.RWS

modName (n, _, _) = n

sortDependencies :: [Module] -> Either String [Module]
sortDependencies mods = fmap reverse (topological [] [] mods)
  where
    findModule name =
      maybe
        (Left ("unknown module: " ++ name))
        pure
        (find ((== name) . modName) mods)

    topological exploring explored [] = pure explored
    topological exploring explored (mod@(name, children, _) : mods)
      | name `elem` exploring = Left ("circular imports: " ++ unwords exploring)
      | name `elem` fmap modName explored = topological exploring explored mods
      | otherwise = do
        children' <- mapM findModule children
        explored' <- topological (name : exploring) explored children'
        topological exploring (mod : explored') mods

checkModules :: [Module] -> Either String String
checkModules mods = do
  runStateT
    (lift (sortDependencies mods) >>= mapM_ checkModule)
    (M.empty, mempty, 0, emptyElabState)

  pure ("\nok, defined modules:\n" ++ unlines (fmap modName mods))

checkModule :: Module -> StateT (Map Name NameSpace, Signature, Int, ElabState) (Either String) ()
checkModule (name, imports, decls) = do
  (names, sig, nextb, est) <- get

  let 
      st =
        DeclState
          { Declaration.moduleName = name,
            nextBlock = nextb,
            importedNames = L.foldl (\acc imp -> mergeNameSpace acc (names ! imp)) mempty imports,
            internalNames = mempty,
            Declaration.signature = sig,
            Declaration.elabState = est
          }

  (_, st') <- lift (runStateT (lift (groupDecls decls) >>= checkBlocks) st)

  put
    ( M.insert name (internalNames st') names,
      Declaration.signature st',
      nextBlock st',
      Declaration.elabState st'
    )