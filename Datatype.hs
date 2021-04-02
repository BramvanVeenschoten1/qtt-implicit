module Datatype where

import Control.Monad.RWS
import Core
import Data.List as L
import Data.Map as M
import Data.Maybe
import Debug.Trace
import ElabMonad as EM
import Lexer (Loc)
import Prettyprint
import Reduction
import Substitution
import Utils

-- partial appliedness for datatypes is out of the question!
-- only current paramno is needed

-- check a constructor for strict positivity and well-formedness and
-- return the number of parameters that occur uniformly across recursive occurrences

-- from now on, non-positivity is not an error! 

assert = undefined

allOccurrencesPositive :: Loc -> Int -> Int -> Int -> Int -> Int -> Term -> Elab Int
allOccurrencesPositive loc defcount defno paramno n nn t = do
  ctx <- asks EM.context
  t' <- runCore (reduce 0 t)
  f ctx (unrollApp t')
  where
    f ctx (Pi p m name src dst,_) = do
      u <-
        if doesNotOccur (Hyp p m name src Nothing : ctx) 0 0 dst
          then strictlyPositive loc defcount n nn src
          else do
            assert (doesNotOccur ctx n nn src) (show loc ++ "Recursive arguments may not be depended upon")
            pure maxBound

      min u <$> local (EM.push (Hyp p m name src Nothing)) (allOccurrencesPositive loc defcount defno paramno (n + 1) (nn + 1) dst)
    f ctx (DBI m,args)
      | m == length ctx - defno - 1 = do
        u <- checkHomogeneousCall loc defcount n nn args
        assert
          (u >= paramno)
          ( show loc
              ++ "parameters are not uniformly applied in constructor return type ("
              ++ show u
              ++ "=/="
              ++ show paramno
              ++ ")"
          )
        pure u
    f ctx dst = undefined --err (show loc ++ "malformed constructor")

strictlyPositive :: Loc -> Int -> Int -> Int -> Term -> Elab Int
strictlyPositive loc defcount n nn t = do
  ctx <- asks EM.context
  t' <- runCore (reduce 0 t)
  f ctx (unrollApp t')
  where
    f ctx (t,_) | doesNotOccur ctx n nn t = pure maxBound
    f ctx (Pi p m name src dst,_) = do
      assert
        (doesNotOccur ctx n nn src)
        (show loc ++ "Recursive occurrence in negative position")

      local (EM.push (Hyp p m name src Nothing)) (strictlyPositive loc defcount (n + 1) (nn + 1) dst)
    f ctx (Top _ (Ind obj_id _), args) = do
      block <- asks (fromJust . M.lookup obj_id . fst . EM.signature)

      let upno = uniparamno block

          (left_params, right_params) = L.splitAt upno args

          ctors = concatMap introRules (dataDefs block)

      assert
        (all (doesNotOccur ctx n nn) right_params)
        (show loc ++ "Recursive occurrence may only be in uniform parameters of a previously defined inductive type")

      foldM
          (\acc -> fmap (min acc)
              . weaklyPositive loc defcount n nn obj_id
              . substBlock obj_id upno Kind
              . instantiateCtor left_params
              . ctorTy
          )
          maxBound
          ctors
    f ctx (DBI m, args)
      | m >= n && m <= nn = checkHomogeneousCall loc defcount n nn args
      | otherwise = do
        undefined --err (show loc ++ "huh?:" ++ show (n, m, nn))
    f ctx t = undefined --err (show loc ++ "Negative recursive occurrence in datatype:")

{-
   why does matita:
   - disallow nesting in mutual types?
   - disallow deeper levels of nesting?
   - add the inspected type to the context?
   => we'll ignore these
-}
weaklyPositive :: Loc -> Int -> Int -> Int -> Int -> Term -> Elab Int
weaklyPositive loc defcount n nn block_no = f n nn
  where
    f :: Int -> Int -> Term -> Elab Int
    f n nn te = do
      te' <- runCore (reduce 0 te)
      case unrollApp te' of
        (Kind, args) -> do
          ctx <- asks EM.context
          assert
            (all (doesNotOccur ctx n nn) args)
            (show loc ++ "Recursive occurrence may only be in uniform parameters of a previously defined inductive type")
          pure maxBound
        (Pi p m name src dst,_) -> do
          local (EM.push (Hyp p m name src Nothing)) (f (n + 1) (nn + 1) dst)
          ctx' <- asks ((Hyp p m name src Nothing :) . EM.context)
          if doesNotOccur ctx' 0 0 dst
            then strictlyPositive loc defcount n nn src
            else do
              ctx <- asks EM.context
              assert
                (doesNotOccur ctx n nn src)
                (show loc ++ "Recursive occurrence in negative position")
              pure maxBound
        (head,args) -> runCore (showTerm (mkApp head args)) >>= traceM >> pure maxBound

-- it does not occur in the parameters or indices,
-- and compute the number of uniformly applied parameters
checkHomogeneousCall :: Loc -> Int -> Int -> Int -> [Term] -> Elab Int
checkHomogeneousCall loc defcount n nn args = do
  ctx <- asks EM.context

  assert (all (doesNotOccur ctx n nn) args) (show loc ++ "a Datatype may not occur in its own indices")

  let depth = length ctx

  pure (f (depth - defcount - 1) args) -- subtract defcount
  where
    f n (DBI m : args)
      | n == m = 1 + f (n - 1) args
    f _ _ = 0

-- compute whether an *inclusive* range of variables occurs in a term 
doesNotOccur :: Context -> Int -> Int -> Term -> Bool
doesNotOccur ctx n nn t = f 0 t True where
  f k (DBI m) acc
    | m >= n + k && m <= nn + k = False
    | m < k && m > nn + k = acc
    | otherwise =
        case nth (m - k) ctx >>= hypDef of
         Just bo -> f 0 (Substitution.lift (m - k) bo) acc
         Nothing -> acc
  f k t acc = Utils.fold (const (+1)) k f t acc