module Prettyprint where

import Core
import Utils

import Data.List as L
import Data.Map as M
import Control.Monad.RWS

-- TODO: add flag on whether to print lambda domains

dbiName :: Int -> Context -> String
dbiName n ctx = maybe
  ('$' : show n)
  (\hyp -> if Prelude.null (hypName hyp) then ('$' : show n) else hypName hyp)
  (nth n ctx)

embrace :: String -> String -> String -> String
embrace open close x = open ++ x ++ close

bracePi :: Term -> String -> String
bracePi Pi {} = embrace "(" ")"
bracePi _     = id

braceApp :: Term -> String -> String
braceApp App {}  = embrace "(" ")"
braceApp Lam {}  = embrace "(" ")"
braceApp Case {} = embrace "(" ")"
braceApp Pi {}   = embrace "(" ")"
braceApp Let {}  = embrace "(" ")"
braceApp _       = id

showArg :: Term -> Core String
showArg t = braceApp t <$> showTerm t

showLam :: String -> Term -> Core String
showLam acc (Lam p m name ta b) = do
  ta' <- showDomain p m name ta
  local (push (Hyp p m name ta Nothing)) (showLam (acc ++ ta') b)
showLam acc b = do
  b' <- showTerm b
  pure ("\\" ++ acc ++ ", " ++ b')

showPi :: String -> Term -> Core String
showPi acc (Pi p m name ta tb) = do
  ta' <- showDomain p m name ta
  local (push (Hyp p m name ta Nothing)) (showPi (acc ++ ta') tb)
showPi acc tb = do
  tb' <- showTerm tb
  pure ("Pi " ++ acc ++ ", " ++ tb')

showPlicity :: Plicity -> String -> String
showPlicity p = case p of
  Implicit -> embrace "{" "}"
  Explicit -> embrace "(" ")"
  Class    -> embrace "[" "]"
  Auto     -> embrace "[[" "]]"

showMult :: Mult -> String
showMult Zero = "0 "
showMult One  = "1 "
showMult Many = ""
showMult (MVar m) = "#" ++ show m ++ " "

showDomain :: Plicity -> Mult -> String -> Term -> Core String
showDomain p m n t = do
  t' <- showTerm t
  let n' = if Prelude.null n then "_" else n
  pure (showPlicity p (showMult m ++ n' ++ " : " ++ t'))

showTerm :: Term -> Core String
showTerm (Meta m)    = pure $ "?M" ++ show m
showTerm Type        = pure "Type"
showTerm Kind        = pure "Kind"
showTerm (DBI n)     = asks (dbiName n . context)
showTerm (Top s _)   = pure (showQName s)
showTerm app @ App {} = unwords <$> mapM showArg (f : reverse xs) where (f,xs) = unrollApp app
showTerm pi  @ Pi {}  = showPi [] pi
showTerm lam @ Lam {} = showLam [] lam
showTerm (Let m name ta a b) = do
  a' <- showTerm a
  b' <- local (push (Hyp Explicit m name ta (Just ta))) (showTerm b)
  pure ("let " ++ name ++ " = " ++ a' ++ " in " ++ b')
showTerm (Case _ scrut mot brans) = do
  scrut' <- showTerm scrut
  mot'   <- showTerm mot
  brans' <- unwords <$> mapM showArg brans
  pure ("case " ++ scrut' ++ " return " ++ mot' ++ " of " ++ brans')

showContext :: Core String
showContext = asks context >>= f where
  f :: Context -> Core String
  f [] = pure ""
  f (Hyp p m name ty def : ctx) = do
    ctx' <- f ctx
    ty'  <- local (\env -> env {context = ctx}) (showTerm ty)
    pure (ctx' ++ "\n" ++ name ++ " : " ++ ty')

showMetaEnv :: Map Int Term -> Core String
showMetaEnv m =
  foldM (\acc (key,val) -> do
    val' <- showTerm val
    pure (acc ++ "\n?M" ++ show key ++ " : " ++ val'))
    ""
    (assocs m)

showMetaSubst :: Map Int (Term,a) -> Core String
showMetaSubst m =
  foldM (\acc (key,(val,_)) -> do
    val' <- showTerm val
    pure (acc ++ "\n?M" ++ show key ++ " = " ++ val'))
    ""
    (assocs m)