module Constructions where

import Control.Monad.RWS
import Core
import Data.List as L
import Reduction
import Substitution
import Utils
import Debug.Trace

{-
hur-dee-dur

The equation compiler will need references to Void, Unit, Eq and DPair

some relaxations:

if a datatype has no constructors, no_conf never applies
if a datatype has one constructor and no subdata, no_conf is trivial
in any case, using injectivity with a nullary constructor is a waste of space
  => is already covered by delete, though

Void => Unit => Eq => DPair

no_conf for DPair may use DPair
other data don't need no_conf
-}

lookupVar :: String -> Core (Term, Term)
lookupVar name = asks context >>= f 0
  where
    f :: Int -> Context -> Core (Term, Term)
    f n [] = error "DBI of undefined name"
    f n (hyp : hyps)
      | hypName hyp == name =
        pure (DBI n, Substitution.lift (n + 1) (hypType hyp))
      | otherwise = f (n + 1) hyps

{-
construct a sequence of k parameters decreasing to 0, lifted by n
example:
mkParams 4 0 = 3,2,1,0
mkParams 3 2 = 4,3,2
-}
mkParams :: Int -> Int -> [Term]
mkParams 0 n = []
mkParams k n = DBI (n + k - 1) : mkParams (k - 1) n

{-
construct a sequence of names
example:
mkNames 5 "x" = x0, x1, x2, x3, x4
-}
mkNames :: Int -> String -> [String]
mkNames n s = f n s 0
  where
    f 0 _ _ = []
    f n s k = (s ++ show k) : f (n - 1) s (k + 1)

-- unroll a type constructor or data constructor with names
unrollParams :: Context -> [String] -> Term -> (Context, Term)
unrollParams acc (name : names) (Pi p m _ src dst) = unrollParams (Hyp p m name src Nothing : acc) names dst
unrollParams acc [] dst = (acc, dst)
unrollParams acc names dst = error (unwords names)

-- roll up a context with binders
rollBinders :: (Plicity -> Mult -> String -> Term -> Term -> Term) -> Context -> Term -> Term
rollBinders f ctx t = L.foldl (\acc (Hyp p m name ty _) -> f p m name ty acc) t ctx

-- get DBI's of a sequence of strings in a context
namesToTerms :: [String] -> Core [Term]
namesToTerms = mapM (fmap fst . lookupVar)

-- get parameters of a datatype as a telescope, with given names
-- parameters are always closed
getParams :: Datatype -> [String] -> Context
getParams dat pnames = fst (unrollParams [] pnames (arity dat))

-- get indices of a datatype as a telescope, with given names
-- indices may depend on parameters, so these are also required
getIndices :: Datatype -> [Term] -> [String] -> Context
getIndices dat params inames = fst
  (unrollParams [] inames
  (instantiateCtor params (arity dat)))

-- get subdata of a constructor as a telescope, with given names
-- data may depend on parameters, so parameters are required
getSubdata :: Datatype -> Int -> [Term] -> [String] -> Context
getSubdata dat ctorno params xnames =
  fst
    ( unrollParams
        []
        xnames
        ( instantiateCtor
            params
            ( ctorTy
                (introRules dat !! ctorno)
            )
        )
    )

{-
given parameters and Datatype info, compute the type of a case motive
example:

data Vec (A : Type): Nat -> Type
  cons : Pi (m : Nat)(x : A)(xs : Vec A m), Vec A (succ m)

P = \(A : Type), Pi n : Nat, Vec A n -> Type
-}
motiveType :: [Term] -> Int -> Int -> Datatype -> Term
motiveType params block defno dat = pis
  where
    name = dataName dat
    pno = paramno dat
    ino = indexno dat

    inames = mkNames ino "i"

    pis = rollBinders Pi (getIndices dat params inames) body

    args = (Substitution.lift ino <$> params) ++ mkParams ino 0

    head = Top name (Ind block defno)

    body = Pi Explicit Many "x" (mkApp head args) Type

{-
given the case multiplicity,
  data parameters,
  motive and
  datatype info,
  compute the type of a match branch,
example:

cons_br =
  \(A : Type)(P : Pi n : Nat, Vec A n -> Type),
    Pi (m : Nat)(x : A)(xs : Vec A m), P (succ m) (cons A m x xs))
-}
branchType :: (Mult -> Mult) -> [Term] -> Term -> Int -> Int -> Int -> Datatype -> Term
branchType f params motive block defno ctorno dat = result
  where
    qname = dataName dat
    pno = paramno dat
    ino = indexno dat

    Constructor ctor_name ctor_arity ctor_ty ctor_pos = introRules dat !! ctorno

    pnames = mkNames pno "p"
    xnames = mkNames ctor_arity "x"

    subdata = getSubdata dat ctorno params xnames

    subdata' = fmap (\hyp -> hyp {hypMult = f (hypMult hyp)}) subdata

    result = rollBinders Pi subdata' returnType

    params' = fmap (Substitution.lift ctor_arity) params

    args = params' ++ mkParams ctor_arity 0
    
    indices = drop pno (reverse (snd (unrollApp (instantiateCtor args ctor_ty))))

    head = Top (qname ++ [ctor_name]) (Con block defno ctorno pno ctor_pos)

    applied_ctor = mkApp head args

    returnType = mkApp (Substitution.lift ctor_arity motive) (indices ++ [applied_ctor])

abstractOver :: (Plicity -> Mult -> String -> Term -> Term -> Term) -> Context -> Core Term -> Core Term
abstractOver f ctx body =
  rollBinders f ctx <$> local (\env -> env {Core.context = ctx ++ Core.context env}) body

-- {-
-- compute a general motive for case distinction, abstracting over target type, data parameters, indices and scrutinee
-- example:

-- P_Vec =
--   \(C A : Type)(n : Nat)(xs : Vec A n)(m : Nat)(ys : Vec A m),
--     Pi (e0 : Eq Nat Nat n m)(e1 : Eq (Vec A n) (Vec A m) xs ys), C
-- -}
-- defaultMotive :: Int -> Int -> Datatype -> Core Term
-- defaultMotive block defno dat = target
--   where
--     name = dataName dat
--     pno = paramno dat
--     ino = indexno dat

--     pnames = mkNames pno "p"
--     ixnames = mkNames ino "ix"
--     iynames = mkNames ino "iy"
--     enames = mkNames ino "e"

--     head = Top name (Ind block defno)

--     target = abstractOver Lam [Hyp "C" (Sort 0)] params

--     params = abstractOver Lam (getParams dat pnames) x_indices

--     x_indices = do
--       params <- namesToTerms pnames
--       abstractOver Lam (getIndices dat params ixnames) x_lam

--     x_lam = do
--       args <- namesToTerms (pnames ++ ixnames)
--       abstractOver Lam [Hyp "x" (mkApp head args)] y_indices

--     y_indices = do
--       params <- namesToTerms pnames
--       abstractOver Lam (getIndices dat params iynames) y_lam

--     y_lam = do
--       args <- namesToTerms (pnames ++ iynames)
--       abstractOver Lam [Hyp "y" (mkApp head args)] equalities

--     equalities = do
--       eqs <- mkEquations ixnames iynames enames
--       abstractOver Pi eqs equality

--     equality = do
--       eq <- mkEquation "x" "y"
--       abstractOver Pi [Hyp "e" eq] (fst <$> lookupCtx "C")

-- {-
-- no-confusion type
-- example:

-- vec_no_conf = \(C A : Type)(n : Nat)(xs ys : Vec A n),
--   case xs _
--     (case ys _
--       (C -> C)
--       (\_ _ _, C) )
--     (\x0 x1 x2, case ys _
--       C
--       (\y0 y1 y2, (x0 == y0 -> x1 == y1 -> x2 == y2 -> C) -> C))
-- -}
-- computeNoConfTy :: Int -> Int -> Datatype -> Core Term
-- computeNoConfTy block defno dat = target
--   where
--     name = dataName dat
--     pno = paramno dat
--     ino = indexno dat

--     ctors = introRules dat

--     pnames = mkNames pno "p"
--     inames = mkNames ino "i"

--     target = abstractOver Lam [Hyp "C" (Sort 0)] params

--     params = abstractOver Lam (getParams dat pnames) indices

--     indices = do
--       params <- namesToTerms pnames
--       abstractOver Lam (getIndices dat params inames) xy

--     xy = do
--       args <- namesToTerms (pnames ++ inames)
--       let x_ty = mkApp (Top name (Ind block defno)) args
--           y_ty = Substitution.lift 1 x_ty
--       abstractOver Lam [Hyp "y" y_ty, Hyp "x" x_ty] outer_case

--     outer_case = do
--       scrut <- fst <$> lookupCtx "x"
--       motiv <- motive
--       brancs <- zipWithM outerBranch [0 ..] ctors
--       pure (Case scrut motiv brancs)

--     motive = do
--       params <- namesToTerms pnames
--       abstractOver Lam (getIndices dat params inames) $ do
--         args <- namesToTerms (pnames ++ inames)
--         abstractOver Lam [Hyp "x" (mkApp (Top name (Ind block defno)) args)] (pure (Sort 0))

--     outerBranch :: Int -> (String, Int, Term) -> Core Term
--     outerBranch ctorno (ctor_name, ctor_arity, ctor_ty) = do
--       let xnames = mkNames ctor_arity "x"
--       params <- namesToTerms pnames
--       abstractOver Lam (getSubdata dat ctorno params xnames) (innerCase ctorno)

--     innerCase :: Int -> Core Term
--     innerCase ctorno = do
--       scrut <- fst <$> lookupCtx "y"
--       motiv <- motive
--       brancs <- zipWithM (innerBranch ctorno) [0 ..] ctors
--       pure (Case scrut motiv brancs)

--     innerBranch :: Int -> Int -> (String, Int, Term) -> Core Term
--     innerBranch ctorno ctorno' (ctor_names, ctor_arity, ctor_ty) = do
--       let enames = mkNames ctor_arity "e"
--           xnames = mkNames ctor_arity "x"
--           ynames = mkNames ctor_arity "y"

--           rhs
--             | ctorno /= ctorno' = fst <$> lookupCtx "C"
--             | otherwise = do
--               eqs <- mkEquations xnames ynames enames
--               eqs <- abstractOver Pi eqs (fst <$> lookupCtx "C")
--               abstractOver Pi [Hyp "" eqs] (fst <$> lookupCtx "C")

--       params <- namesToTerms pnames

--       abstractOver Lam (getSubdata dat ctorno' params ynames) rhs

-- {-
-- example:

-- no_conf_h : Pi (C p : Type)(i : Nat)(xs : Vec p i), no_conf_t C p i xs xs =
--   \(C p : Type)(i : Nat)(xs : Vec p i),
--     case xs return (\(i:Nat)(xs : Vec p i), no_conf_t C p i xs xs) of
--       (\(r : C), r)
--       (\(x0 : Nat)(x1 : p)(x2 : Vec p x0)(r : (Eq Nat Nat x0 x0 -> Eq p p x1 x1 -> Eq (Vec p x0) (Vec p x0) x2 x2 ->  C) -> C),
--         r (refl Nat x0)(refl p x1)(refl (Vec p x0) x2))
-- -}
-- computeNoConfHelp :: Int -> Int -> Datatype -> Core Term
-- computeNoConfHelp block defno dat = result
--   where
--     qname = dataName dat
--     pno = paramno dat
--     ino = indexno dat

--     ctors = introRules dat

--     target_ctx = [Hyp "C" (Sort 0)]

--     pnames = mkNames pno "p"
--     inames = mkNames ino "i"

--     result = abstractOver Lam [Hyp "C" (Sort 0)] params

--     params = abstractOver Lam (getParams dat pnames) indices

--     indices = do
--       params <- namesToTerms pnames
--       abstractOver Lam (getIndices dat params inames) x_lam

--     x_lam = do
--       args <- namesToTerms (pnames ++ inames)
--       abstractOver Lam [Hyp "x" (mkApp (Top qname (Ind block defno)) args)] match

--     match = do
--       motiv <- motive
--       brancs <- zipWithM branch [0 ..] ctors
--       pure (Case (DBI 0) motiv brancs)

--     branch ctorno (_, ctor_arity, ctor_ty) = do
--       let xnames = mkNames ctor_arity "x"
--           enames = mkNames ctor_arity "e"
--       params <- namesToTerms pnames
--       abstractOver Lam (getSubdata dat ctorno params xnames) $ do
--         eqs <- mkEquations xnames xnames enames
--         r_ty <- abstractOver Pi eqs (fst <$> lookupCtx "C")
--         abstractOver Lam [Hyp "r" r_ty] $ do
--           mkApp (DBI 0) <$> mkRefls xnames

--     mkRefls :: [String] -> Core [Term]
--     mkRefls [] = pure []
--     mkRefls (x : xs) = do
--       (x, ty) <- lookupCtx x
--       (App Refl [ty, x] :) <$> mkRefls xs

--     motive = do
--       params <- namesToTerms pnames
--       let indices = getIndices dat params inames
--       abstractOver Lam indices $ do
--         args <- namesToTerms (pnames ++ inames)
--         abstractOver Lam [Hyp "x" (mkApp (Top qname (Ind block defno)) args)] $ do
--           modName <- gets moduleName
--           let nocontyname = qname ++ ["$no_conf_ty"]
--           no_conf_ty <- fst <$> lookupQualified undefined nocontyname

--           args <- namesToTerms ("C" : pnames ++ inames ++ ["x", "x"])
--           pure (App no_conf_ty args)

-- {-
-- example:

-- no_conf : Pi (C p : Type)(i : Nat)(xs ys : Vec p i), Eq (Vec p i) (Vec p i) xs ys -> no_conf_t C p i xs ys =
--   \(C p : Type)(i : Nat)(xs ys : Vec p i)(e, Heq (Vec p i) (Vec p i) xs ys),
--     subst (Vec p i) xs (no_conf_t C p i xs) ys e (no_conf_h C p i xs)
-- -}
-- computeNoConf :: Int -> Int -> Datatype -> Core Term
-- computeNoConf block defno dat = result
--   where
--     qname = dataName dat
--     pno = paramno dat
--     ino = indexno dat

--     ctors = introRules dat

--     target_ctx = [Hyp "C" (Sort 0)]

--     pnames = mkNames pno "p"
--     inames = mkNames ino "i"

--     result = abstractOver Lam [Hyp "C" (Sort 0)] params

--     params = abstractOver Lam (getParams dat pnames) indices

--     indices = do
--       params <- namesToTerms pnames
--       abstractOver Lam (getIndices dat params inames) xy

--     xy = do
--       modName <- gets moduleName
--       args <- namesToTerms (pnames ++ inames)
--       let x_ty = mkApp (Top qname (Ind block defno)) args
--           y_ty = Substitution.lift 1 x_ty
--       abstractOver Lam [Hyp "y" y_ty, Hyp "x" x_ty] $ do
--         eq <- mkEquation "x" "y"
--         abstractOver Lam [Hyp "e" eq] $ do
--           i_args <- namesToTerms (pnames ++ inames)
--           let ty = mkApp (Top qname (Ind block defno)) i_args
--           x <- fst <$> lookupCtx "x"

--           let nocontyname = qname ++ ["$no_conf_ty"]
--           no_conf_ty <- fst <$> lookupQualified undefined nocontyname

--           m_args <- namesToTerms ("C" : pnames ++ inames ++ ["x"])
--           let motive = App no_conf_ty m_args
--           y <- fst <$> lookupCtx "y"
--           e <- fst <$> lookupCtx "e"
--           helper <- computeNoConfHelp block defno dat
--           let body = App helper m_args
--           pure (App Subst [ty, x, y, motive, body, e])

-- -- computeSelector :: Term
-- -- computeSelector = undefined