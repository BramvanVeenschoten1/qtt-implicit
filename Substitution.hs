module Substitution where

import Data.Maybe
import Core 
import Utils
import Debug.Trace

liftFrom :: Int -> Int -> Term -> Term
liftFrom k n = f k where
    f k (DBI m)
        | m >= k = DBI (m + n)
    f k t = Utils.map (const (+1)) k f t

lift :: Int -> Term -> Term
lift = liftFrom 0

psubst :: [Term] -> Term -> Term
psubst args = f 0 where
    nargs = length args

    f k t @ (DBI n)
        | n >= k + nargs = DBI (n - nargs)
        | n < k = t
        | otherwise = lift k (args !! (n - k))
    f k (App fun arg) = g (f k fun) (f k arg)
    f k x = Utils.map (const (+1)) k f x

    g (Lam p m n ta b) arg = psubst [arg] b
    g fun arg = App fun arg

-- abstract a free variable for generating a motive
abstractFreeVar :: Int -> Term -> Term
abstractFreeVar m = f 0 where
    f k t @ (DBI n)
        | n == m + k = DBI 0
        | n >= k     = DBI (n + 1)
        | otherwise  = t
    f k t = Utils.map (const (+1)) k f t

instantiateCtor :: [Term] -> Term -> Term
instantiateCtor params  = psubst (reverse params) . dropDomains (length params) 

-- substitute recursive occurrences of datatype or functions
substBlock :: Int -> Int -> Term -> Term -> Term
substBlock block upno arg = g () where

    g _ = uncurry h . unrollApp

    h (Top _ (Ind block' _)) args
        | block == block' = mkApp arg (drop upno args)
    h (Top _ (Def block' _ _ _)) args
        | block == block' = mkApp arg (fmap (g ()) (drop upno args))