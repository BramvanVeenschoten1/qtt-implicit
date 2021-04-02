module Typecheck where

import Control.Monad.RWS.Lazy
import Core
import Debug.Trace
import Prettyprint
import Reduction
import Substitution
import Utils
import Constructions

import Data.List ( transpose )



emptyUseEnv :: [Mult]
emptyUseEnv = repeat Zero

singleUseEnv :: Int -> [Mult]
singleUseEnv n = replicate n Zero ++ [One] ++ repeat Zero

typeOfRef :: Reference -> Core Term
typeOfRef ref@Def {} = functionType <$> getFunction ref
typeOfRef ref@Ind {} = arity <$> getData ref
typeOfRef ref@(Con block defno ctorno _ _) = do
  ctors <- getData (Ind block defno)
  pure (ctorTy (introRules ctors !! ctorno))

ensureData :: Term -> Core (Int, Int, Datatype, [Term])
ensureData dat = do
  dat' <- reduce 0 dat
  case unrollApp dat' of
    (Top _ ref@(Ind block defno), args) -> do
      dat <- getData ref
      pure (block, defno, dat, args)
    _ -> do
      dat' <- showTerm dat
      error ("expected a datatype in a case expression, but got: " ++ dat')

ensureProduct :: Term -> Core (Plicity, Mult, Name, Term, Term)
ensureProduct t = do
  t' <- reduce 0 t
  case t' of
    Pi p m name src dst -> pure (p, m, name, src, dst)
    _ -> do
      t'' <- showTerm t'
      error ("expected a function type, but got: " ++ t'')

ensureSort :: Term -> Core ()
ensureSort Type = pure ()
ensureSort Kind = pure ()
ensureSort t  = do
  t' <- showTerm t
  error ("expected some type, but got: " ++ t')

assertConvertible :: Term -> Term -> Core ()
assertConvertible t0 t1 = do
  converts <- sub t0 t1
  if converts
  then pure ()
  else do
    t0' <- showTerm t0
    t1' <- showTerm t1
    error ("inconvertible terms:\n" ++ t0' ++ "\n" ++ t1')

check :: Term -> Term -> Core [Mult]
check Kind Kind = pure emptyUseEnv
check Type Kind = pure emptyUseEnv
check (Pi p m n ta tb) l = do
  check ta l
  local (push (Hyp p m n ta Nothing)) (check tb l)
  pure emptyUseEnv
check (Lam p0 m0 n0 ta0 b) (Pi _  m1 n1 ta1 tb) = do
  assertConvertible  ta0 ta1
  ubs <- local (push (Hyp p0 m0 n0 ta0 Nothing)) (check b tb)
  let (u:ub) = ubs

  if multLeq u m0
  then pure ()
  else error "multiplicity mismatch in lambda expression"

  pure ub
check (Let m n ta a b) tb = do
  (ka,_) <- infer ta
  ensureSort ka
  ua <- check a ta
  ub <- local (push (Hyp Explicit m n ta (Just a))) (check b tb)

  let (u:us) = ub

  if u == m
  then pure ()
  else error "multiplicity mismatch in let expression"

  pure (zipWith plus us (fmap (times m) ua))

check term ty = do
  (ty',u) <- infer term
  assertConvertible ty' ty
  pure u

infer :: Term -> Core (Term,[Mult])
infer (DBI n) = do
  ctx <- asks context
  case nth n ctx of
    Just (Hyp _ _ _ _ (Just ty)) -> pure (Substitution.lift (n + 1) ty, singleUseEnv n)
    Nothing -> do
      ctx <- showContext
      error $ "in context:\n" ++ ctx ++ "\nverification failed, DBI out of bounds"
infer (Top _ ref) = do
    ty <- typeOfRef ref
    pure (ty, emptyUseEnv)
infer app@(App fun arg) = do
  (tf,uf) <- infer fun
  (p,m,name,ta,tb) <- ensureProduct tf
  ua <- check arg ta
  pure (psubst [arg] tb, zipWith plus uf (fmap (times m) ua))
infer (Case m scrutinee motive branches) = do
  if m == Zero && length branches > 1
  then error "case expression with more than 1 branch is not erasable"
  else pure ()

  (ty,su) <- infer scrutinee
  (block, defno, dat, args) <- ensureData ty
  let pno = paramno dat
      (params, indices) = splitAt pno args
      motiveTy = motiveType params block defno dat
      branchTys = fmap
        (\ctorno -> branchType (times m) params motive block defno ctorno dat)
        [0 .. length (introRules dat) - 1]
  check motive motiveTy
  branchUses <- zipWithM check branches branchTys
  result <- reduce maxBound (mkApp motive (indices ++ [scrutinee]))
  pure (result, zipWith plus su (fmap splitMult (transpose branchUses)))