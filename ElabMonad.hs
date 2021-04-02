module ElabMonad where

import Control.Monad.RWS
import Control.Monad.Reader
import Core
import Data.List as L
import Data.Map as M
import Data.Maybe
import Lexer (Loc)
import Prettyprint
import Utils
import Debug.Trace

type NameSpace = (Map Name [QName], Map QName (Loc, Reference))

data Use
  = None
  | Single Loc
  | Times Mult Use
  | Plus Use Use
  | Split [Use]

type UseEnv = [Use]

{-
justification system may require a bit more thought, if it is to be useable for both
backtracking and error messaging.
error types in the elaborator are:
- ensure function
- ensure sort
- ensure data
- missing branches
- excess branches?
- undefined variable
all but the last one of these are recoverable if due to an ill chosen choice constraint.
solution: throw both justification and violated constraint?
doesnt cover undefined names
-}

data Constraint
  = Convertible Loc Context Term Term -- loc, ctx, expected type, inferred type, constant id, constant value
  | EnsureData Context Int (Elab (Term,Term,UseEnv)) -- context, blocking meta, remainder of elaboration
  | MultUse Loc Mult Use
  | Choice Context Int [Elab (Term,Term,UseEnv)] -- loc, ctx, id, alternatives,

type Error = (String,[Int])

showConstraint :: Constraint -> Core String
showConstraint (Convertible _ ctx l r) =
  local (\env -> env {Core.context = ctx}) $ do
    l' <- showTerm l
    r' <- showTerm r
    pure $ l' ++ " == " ++ r'
showConstraint (MultUse {}) = pure "some usage constraint"

showConstraints :: [Constraint] -> Core String
showConstraints = fmap unlines . mapM showConstraint

{-
  for an elaborator:
  meta env
  meta subst
  mult var subst
  univ constraints

  constraints:
  - convertible (annotated with subtype, pattern, quasipattern, flex-rigid, flex-flex)
  - choice (labeled with on-demand in case of class)
  - multLeq
  - multenv

  guarded constants:
  - a guarded constant depends on a single constraint,
    so this constraint will contain the const id as well as the value
    => a single constraint may yield multiple constraints,
      so constraints must be identified and mapped
    => a single constraint need not yield any constraints at all
  - mult constraints invoke no guardedness issues

  let us not forget universe constraints

  ambiguous names must be distinguishable from either
  argument types or return type, so choice constraints
  can have a set of blocking meta-variables, the typechecker
  will demand the disambiguation is decidable once these
  metas have been solved

  a full elaboration involves constraint simplification as well as
  checking the resulting term for absence of metavariables
  -}

data ElabEnv = ElabEnv
  { moduleName :: Name,
    names :: NameSpace,
    mode :: Mode,
    context :: Context,
    currentBlock :: Int,
    signature :: Signature
  }

type MetaSubst = Map Int (Term,[Int])
type MultSubst = Map Int (Mult,[Int])

data ElabState = ElabState
  { nextVar :: Int,
    metaEnv :: Map Int Term,
    metaSubst :: MetaSubst,
    multSubst :: MultSubst,
    elabConstraints :: [(Constraint,[Int],[Int])], -- constr, choice dependencies, blocking metas
    guardedConstants :: [(Loc,Int,Term,[Int])] -- loc, id, value, blocking metavariables
  }

emptyElabState :: ElabState
emptyElabState = ElabState {
  nextVar = 0,
  metaEnv = mempty,
  metaSubst = mempty,
  multSubst = mempty,
  elabConstraints = [],
  guardedConstants = []}

type Elab = RWST ElabEnv () ElabState (Either Error)

err :: Error -> Elab a
err = lift . Left

push :: Hypothesis -> ElabEnv -> ElabEnv
push hyp env = env {ElabMonad.context = hyp : ElabMonad.context env}

withContext :: Context -> Elab a -> Elab a
withContext ctx e = local (\env -> env {ElabMonad.context = ctx}) e

runCore :: Core a -> Elab a
runCore c = do
  ElabEnv _ _ mod ctx _ sig <- ask
  pure (runReader c (CoreEnv mod ctx sig))

insertConstraint :: Constraint -> [Int] -> [Int] -> Elab ()
insertConstraint constr just metas = do
  modify (\st -> st {
    elabConstraints = (constr,just,metas) : elabConstraints st
  })
  -- (constrs,_,_) <- unzip3 <$> gets elabConstraints
  -- constrs' <- runCore (showConstraints constrs)
  -- traceM constrs'

insertGuard :: Loc -> Int -> Term -> [Int] -> Elab ()
insertGuard loc guard value metas = do
  modify (\st -> st {
    guardedConstants = (loc,guard,value,metas) : guardedConstants st
  })