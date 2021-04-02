module Reduction where

import Core 
import Utils 
import Substitution 
import Prettyprint

import Data.Bool
import Data.Maybe
import Data.Map as M
import Control.Monad
import Control.Applicative hiding (Top)
import Control.Monad.RWS.Lazy
import Debug.Trace

-- maybe reduce metavars or multvars
-- ensure proper sort checking
-- see if good old (&&) and (||) work with Reader

{-
We're already going to implement the necessary infrastructure for multvars and metavars
This reduction module exists in the trusted kernel so it will not try to solve constraints,
but we might want to have it look up metavars or multvars
-}

isDecidable :: Mode -> Bool
isDecidable Decidable = True
isDecidable _ = False

reduce :: Int -> Term -> Core Term
reduce delta t = f delta 0 [] t [] where
    f :: Int -> Int -> [Term] -> Term -> [Term] -> Core Term
    f d k e t @(DBI n) s
        | n < k = f d 0 [] (e !! n) s
        | otherwise = do
            ctx <- asks context
            case hypDef (ctx !! (n - k)) of
                Nothing -> unwind e t s
                Just x -> f d 0 [] (Substitution.lift (n - k - 1) x) s
    f d k e (App head arg) s = do
        arg' <- f d k e arg []
        f d k e head (arg' : s)
    f d k e (Lam _ _ _ _ t) (p : s) =
        f d (k + 1) (p : e) t s
    f d k e (Let _ _ _ a b) s = do
        a' <- f d k e a []
        f d (k + 1) (a' : e) b s
    f d k e t @ (Top _ ref @ (Def i j h decreases)) s = do
        decidable <- asks (isDecidable . mode)
        if not decidable || decreases
        then do
            def <- functionBody <$> getFunction ref
            f d 0 [] def s
        else unwind e t s
    f d k e t @ (Case m scrut mot branches) s = do
        decidable <- asks (isDecidable . mode)
        scrut' <- f 0 k e scrut []
        let (head,args) = unrollApp scrut'
            proceed (Top _ (Con _ _ i pno pos))
                | not decidable || pos =
                    f d k e (branches !! i) (Prelude.drop pno args ++ s)
            proceed _ = unwind e (Case m scrut' mot branches) s
        proceed head
    f d k e t s = unwind e t s

    unwind e t s = pure (mkApp (psubst e t) s)

-- if    flag
-- then  check a == b
-- else  check a <= b
sub :: Term -> Term -> Core Bool
sub t0 t1 = or' (alphaEq t0 t1) (machineEq t0 t1) where
    alphaEq Type Type = pure True
    alphaEq Kind Kind = pure True
    alphaEq (Meta m0) (Meta m1) = pure (m0 == m1)
    alphaEq (DBI n0) (DBI n1) = pure (n0 == n1)
    alphaEq (Top _ r0) (Top _ r1) = pure (r0 == r1)
    alphaEq (App f0 xs0) (App f1 xs1) = and'
        (sub f0 f1)
        (sub xs0 xs1)
    alphaEq (Lam p m n src t0) (Lam _ _ _ _ t1) =
        local (push (Hyp p m n src Nothing)) (sub t0 t1)
    alphaEq (Pi p m0 n src0 dst0) (Pi _ m1 _ src1 dst1) = and'
        (pure (m0 == m1))
        (and'
            (sub src1 src0)
            (local (push (Hyp p m0 n src0 Nothing)) (sub dst0 dst1)))
    alphaEq (Let m n ta0 a0 b0) (Let _ _ ta1 a1 b1) = and'
        (sub ta0 ta1)
        (and'
            (sub a0 a1)
            (local (push (Hyp Explicit m n ta0 (Just a0))) (sub b0 b1)))
    alphaEq (Case _ scr0 _ br0) (Case _ scr1 _ br1) = and'
        (sub scr0 scr1)
        (zipAnd sub br0 br1)
    alphaEq _ _ = pure False

    machineEq t0 t1 = do
        t0' <- reduce maxBound t0
        t1' <- reduce maxBound t1
        convertMachines t0' t1'

    -- the following three helpers are designed to preserve laziness
    -- the rightmost monadic expression will not be evaluated
    -- based on the assumption that conversion checks are infallible
    or' :: Core Bool -> Core Bool -> Core Bool
    or' x y = x >>= bool y (pure True)

    and' :: Core Bool -> Core Bool -> Core Bool
    and' x y = x >>= bool (pure False) y

    zipAnd :: (a -> a -> Core Bool) -> [a] -> [a] -> Core Bool
    zipAnd f (x:xs) (y:ys) = and' (f x y) (zipAnd f xs ys)
    zipAnd f _      _      = pure True

    isNorm t = case unrollApp t of
        (Top _ (Def _ _ _ False),_) -> True
        (Top _ (Def _ _ _ _), _) -> False
        _ -> True

    heightOf t = case unrollApp t of
        (Top _ (Def _ _ h _),_) -> h
        _ -> 0


    smallDeltaStep t0 t1 norm0 norm1 = do
        t0' <- reduce delta t0
        t1' <- reduce delta t1
        proceed t0 t1 t0' t1'
        where
            proceed t0 t1 t0' t1'
                | norm0 = convertMachines t0 t1'
                | norm1 = convertMachines t0' t1
                | otherwise = convertMachines t0' t1'

            delta
                | norm0 = h1 - 1
                | norm1 = h0 - 1
                | h0 == h1 = max 0 (h0 - 1)
                | otherwise = min h0 h1

            h0 = heightOf t0
            h1 = heightOf t1
    
    convertMachines t0 t1 = do
        let norm0 = isNorm t0
            norm1 = isNorm t1
        or' (alphaEq t0 t1)
            (bool
                (smallDeltaStep t0 t1 norm0 norm1)
                (pure False)
                (norm0 && norm1))
