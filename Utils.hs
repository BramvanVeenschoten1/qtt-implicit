module Utils where

import Core
import Data.List as L
import Data.Maybe

nth :: Int -> [a] -> Maybe a
nth 0 (x : _) = Just x
nth n (_ : xs) = nth (n-1) xs
nth _ _ = Nothing

{-
given an directed graph by a list of a and a function returning children,
returns a topologically sorted graph if it is acyclical, or the first cycle found

topoSort :: Ord a => (a -> [a]) -> [a] -> Either [a] [a]
topoSort children = f [] [] where
  f exploring explored [] = Right explored
  f exploring explored (node:nodes)
    | node `elem` exploring = Left exploring
    | node `elem` explored  = f exploring explored nodes
    | otherwise = do
      explored' <- f (node : exploring) explored (children node)
      f exploring (node : explored') nodes
-- -}

mkApp :: Term -> [Term] -> Term 
mkApp = L.foldl App

unrollApp :: Term -> (Term,[Term])
unrollApp (App fun arg) = (fun',arg:args) where
  (fun',args) = unrollApp fun
unrollApp other = (other,[])


map :: (Hypothesis -> k -> k) -> k ->
        (k -> Term -> Term) ->
        Term -> Term 
map push ctx f t = case t of
  App fun args -> App (f ctx fun) (f ctx args)
  Pi p m name src dst -> Pi p m name (f ctx src) (f (push (Hyp p m name src Nothing) ctx) dst)
  Lam p m name src dst -> Lam p m name (f ctx src) (f (push (Hyp p m name src Nothing) ctx) dst)
  Let m name ta a b -> Let m name (f ctx ta) (f ctx a) (f (push (Hyp Explicit m name ta (Just a)) ctx) b)
  Case m scrut motiv branches -> Case m (f ctx scrut) (f ctx motiv) (fmap (f ctx) branches)
  x -> x

fold :: (Hypothesis -> k -> k) -> k ->
        (k -> Term -> a -> a) ->
        Term -> a -> a
fold push ctx f t = case t of
  App fun args -> f ctx fun . (f ctx args)
  Pi p m name src dst -> f ctx src . f (push (Hyp p m name src Nothing) ctx) dst
  Lam p m name src dst -> f ctx src . f (push (Hyp p m name src Nothing) ctx) dst
  Let m name ta a b -> f ctx ta . f ctx a . f (push (Hyp Explicit m name ta (Just a)) ctx) b
  Case _ scrut motiv branches -> f ctx scrut . f ctx motiv . flip (L.foldr (f ctx)) branches
  _ -> id

dropDomains :: Int -> Term -> Term
dropDomains 0 tb = tb
dropDomains n (Pi _ _ _ _ tb) = dropDomains (n - 1) tb

push :: Hypothesis -> CoreEnv -> CoreEnv
push hyp env = env {context = hyp : context env}

showQName :: [String] -> String
showQName = intercalate "."