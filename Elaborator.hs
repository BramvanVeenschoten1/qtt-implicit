module Elaborator where

import Constructions
import Control.Applicative hiding (Const)
import Control.Monad.RWS
import Core
import Data.Functor
import Data.List as L
import Data.Map as M
import Data.Maybe
import Debug.Trace
import ElabMonad as EM
import Lexer ( Loc, emptyLoc )
import Parser
import Prettyprint
import Reduction
import Substitution
import Utils
import Typecheck ( typeOfRef )

{-
novel idea:
in order to have smooth interaction between implicit arguments and type-driven disambiguation,
we might have choice constraints list alternatives between *applications* of constants,
so their implicit arguments may already be filled in. It will require some restructuring of
the elaborator: when inferring the head of an application, a stack of implicit arguments
must be available. This construction might allow a lot of choice constraints to be solved early.

solving a choice constraint may introduce new metavariables that differ with each option taken,
due to introduction of implicit arguments. Care must be taken to ensure the right set of
metavariables are introduced and discarded when a constraint is solved

- any variable or name can be an application
- they are always inferred

We must think of some way to check terms against implicit products
- same checking against implicit products in equations:
    if term is implicit lambda, proceed as usual
    otherwise, do implicit introduction

is there a risk of inferring an implicit product only to immediately instantiate it?
- only when lambda is in app head position, which is dumb anyway

add implicit applications to parser

the procedure:
always begin with check
- when encountering name or variable, infer and fill in implicits
- when encountering app:
  - push args on stack
  - infer head with args, filling in implicits

=> current strategy will result in eta-expansion when functions expect implicit functions as arguments

procedure:
1. preprocess: gather constraints
2. try constraint
  - if solvable:
      instantiate meta's
      remove constraints blocked on instantiated metas from postponed
    else:
      postpone, record blocking meta's
3. goto 2

solving choice constraints:
- try each option
- if any option blocks, postpone
- if all options err, produce error
- if exactly one fits, resolve meta
- if more than one fit, produce error

more notes:
- bidirectionalism might be a good idea
- keep args stack when inferring application
- after inferring var or const, insert implicits
- when checking against implicit products, do implicit introduction
- it might be useful to pass around the universe level to check against,
  even when inferring. This means we don't have to create 2 universe variables
  every time we instantiate Type

perhaps introducing multiplicity variables with metavariables is overengineering.
We can just assert that every variable in scope will be used zero times, and compute
the true multiplicities after the metavariable has been substituted away

for solving of choice constraints we might want to take a cue from Lean.
constraints are annotated with justifications which are used for error messages and backtracking.
justifications come in 3 types:
- asserted: generated during preprocessing, might make use of loc
- assumed: is made every time an attempt at solving a choice constraint is made
- join: conjuction of two justifications
whenever a metavariable is instantiated it is annotated with the justification of the constraint it was instantiated from
when a meta variable substitution is applied to a constraint,
the meta-justification and constraint justification are joined in the new constraint
when trying to solve a choice constraint, create a fresh assumption justification
try each option. if an option errs with a justification dependent on the fresh one, try another constraint.
if the justification does not depend on the assumption, propagate the error

instantiated metavariables are not available to the reductor, but only to the constraint simplifier.
substitution of metavariables happens only at the simplification of constraints, so that the
justification of the substitutions can be added to them. Also, simplify core. Also, core should not
deal with u-constraints, but absolute u-levels

since constraints depend on metavariables, the guarded constants depend on those exact variables as well
as such, constraints don't need to be annotated with identifiers

multiplicity polymorphism does not completely subsume subtyping, consider m-polymorphic composition:

comp : (b ->{p} c) -> (a ->{q} b) -> (a ->{p*q} c)
comp = \f g x. f (g x)

with just polymorphism, the mult of x is only 1 if both p and q are 1. Since extending our calculus
with mult-expressions is complicated, the best type we can infer for comp is:

comp : (b ->{p} c) -> (a -> {p} b) -> (a ->{p} c)

now, if we want to compose a linear and non-linear function to yield a non-linear function, we must
instantiate p to omega, and the linear function will be accepted by subtyping

multiplicity polymorphism is only needed with higher-order functions

how to do a polymorphic mult inference procedure:

forget the multplicities of the function arguments and instantiate them with fresh variables
gather multplicity constraints as usual, but when computing usage environments, do the following:

for each constraint type, we want a function that tries to solve it, with possible results:
- failure, throwing a constraint and a justification
- partial success, with new constraints, each with blocking metas, as well as solved metas
should be callable from both elaborator and solver
-}

emptyUseEnv :: UseEnv
emptyUseEnv = repeat None

singleUseEnv :: Loc -> Int -> UseEnv
singleUseEnv loc n = replicate n None ++ [Single loc] ++ repeat None

-- lookupQName :: QName -> Elab (Maybe (Loc, Reference))
-- lookupQName qname = asks (M.lookup qname . snd . names)

-- lookupName :: Name -> Elab (Maybe [QName])
-- lookupName name = asks (M.lookup name . fst . names)

lookupQualified :: Loc -> QName -> Elab (Term, Term, UseEnv)
lookupQualified loc qname = do
  qname' <- asks (M.lookup qname . snd . names)
  case qname' of
    Nothing -> err (show loc ++ "undefined name: " ++ showQName qname, [])
    Just (_, ref) -> (,,) (Top qname ref) <$> runCore (typeOfRef ref) <*> pure emptyUseEnv

lookupUnQualified :: Loc -> Name -> [(Loc,Plicity,Term,Term,UseEnv)] -> Elab (Term, Term, UseEnv)
lookupUnQualified loc name args = do
  name' <- asks (M.lookup name . fst . names)
  case name' of
    Nothing -> do
      ctx <- runCore showContext
      err (show loc ++ "undefined variable: " ++ name, [])
    Just [qname] -> do
      (t,ty,u) <- lookupQualified loc qname
      checkArgs t ty u args
    Just qnames -> error "disambiguation not yet supported"
      -- todo: make choice constraint here 
      {-
      1. a metavariable as the return type
      2. a metavariable as the value
      3. a choice constraint
      -}
      -- err
      --   ( show loc
      --       ++ "ambiguous name, possibilities are:\n"
      --       ++ intercalate "\n" (fmap showQName qnames)
      --   )

lookupCtx :: Loc -> Name -> Elab (Maybe (Term, Term, UseEnv))
lookupCtx loc name = asks EM.context >>= f 0
  where
    f n [] = pure Nothing
    f n (hyp : hyps)
      | hypName hyp == name =
        pure (Just (DBI n, Substitution.lift (n + 1) (hypType hyp), singleUseEnv loc n))
      | otherwise = f (n + 1) hyps

freshMultVar :: Elab Mult
freshMultVar = do
  m <- gets nextVar
  modify (\st -> st {nextVar = m + 1})
  pure (MVar m)

freshMeta :: Term -> Elab (Term,UseEnv)
freshMeta ty = do
  ctx <- asks EM.context

  -- make fresh multvars
  -- there may be some subtleties concerning let-definitions in the context
  ctx' <- mapM (\hyp ->
    case hypMult hyp of
      Zero -> pure hyp
      Many -> pure hyp
      _ -> do
        m <- freshMultVar
        pure (hyp {hypMult = m})) ctx
  
  -- make fresh metavariable
  mv <- gets nextVar
  modify (\st -> st {nextVar = mv + 1})

  -- abstract type over context
  let ty' = L.foldl (\acc (Hyp p m n ta _) -> (Pi Explicit m n ta acc)) ty ctx

      -- derive multEnv from context
      env = fmap (\hyp -> Times (hypMult hyp) (Single emptyLoc)) ctx

      -- apply fresh var to context
      args = fmap DBI (reverse [0 .. length ctx - 1])
      result = L.foldl App (Meta mv) args

  -- insert meta type in metasenv
  modify (\st -> st {metaEnv = M.insert mv ty' (metaEnv st)})
  
  pure (result,env)

ensureSort :: Loc -> Term -> Elab ()
ensureSort loc t = do
  t' <- runCore (reduce 0 t)
  case unrollApp t of
    (Type,_) -> pure ()
    (Kind,_) -> pure ()
    _ -> do
      t'' <- runCore (showTerm t')
      err (show loc ++ "expected a sort, but got: " ++ t'',[])

ensureProduct :: Loc -> Term -> Elab (Plicity,Mult,String,Term,Term)
ensureProduct loc ty = do
  ty' <- runCore (reduce 0 ty)
  case unrollApp ty' of
    (Pi p m n ta tb,_) -> pure (p, m, n, ta, tb)
    (Meta mv, _) -> do
      m <- freshMultVar
      (ta,_) <- freshMeta Kind
      (tb,_) <- local (EM.push (Hyp Explicit m "" ta Nothing)) (freshMeta Kind)
      ctx <- asks EM.context
      checkConstraint (Convertible loc ctx ty' (Pi Explicit m "" ta tb)) []
      pure (Explicit, m, "", ta, tb)
    _ -> do
      ty'' <- runCore (showTerm ty')
      err (show loc ++ "expected a function type, but got: " ++ show ty'', [])

ensureData :: Term -> Elab (Int, Int, Datatype, [Term])
ensureData ty = do
  (head,args) <- unrollApp <$> runCore (reduce 0 ty)
  case head of
    Top _ ref @ (Ind block defno) -> do
      dat <- runCore (getData ref)
      pure (block,defno,dat,args)
    x -> do
      ctx <- runCore showContext
      x' <- runCore (showTerm x)
      error (
        "in context:\n" ++
        ctx ++
        "expected some datatype in match expression, but got:\n" ++
        x'
        )

elaborate :: Expr -> Term -> Elab (Term, UseEnv)
elaborate expr ty = do
  ty' <- runCore (reduce 0 ty)
  let loc = exprLoc expr
  (term, ty, u) <- inference expr
  ctx <- asks EM.context
  checkConvertible loc [] ty ty'
  
  -- (guard,_) <- freshMeta ty
  -- let (Meta mv, _) = unrollApp guard
  -- ctx' <- zipWithM (\hyp use ->
  --   case hypMult hyp of
  --     Zero -> pure hyp --insertConstraint (MultUse Zero use) [] $> hyp
  --     Many -> pure hyp --insertConstraint (MultUse One use) [] $> hyp
  --     _ -> do
  --       m' <- freshMultVar
  --       --insertConstraint (MultUse m' use) []
  --       pure (hyp {hypMult = m'})
  --   ) ctx u
  -- -- there may be some subtleties concerning let-definitions in the context
  -- let term' = L.foldl (\acc (Hyp p m n ta _) -> Lam p m n ta acc) term ctx'
  -- --insertGuard mv term' []
  -- -- if decidable then use guarded constant, else discard constant

  pure (term,u)

{-
cases:
- implicit product, explicit arg
- implicit product, implicit arg
- implicit product, no arg
- explicit product
-}
checkArgs :: Term -> Term -> UseEnv -> [(Loc,Plicity,Term,Term,UseEnv)] -> Elab (Term, Term, UseEnv)
checkArgs head headTy headUses args = do
  headTy' <- runCore (reduce 0 headTy)
  case (headTy', args) of
    (Pi Implicit m n ta tb, (loc, Implicit, arg, targ, uarg) : args) -> f loc m n ta tb arg targ uarg args
    (Pi Implicit m n ta tb, args) -> do
      (arg,uarg) <- elaborate (EHole emptyLoc) ta
      f emptyLoc m n ta tb arg ta uarg args
    (_, (loc,_,arg,targ,uarg) : args) -> do
      (p,m,n,ta,tb) <- ensureProduct loc headTy'
      f loc m n ta tb arg targ uarg args
    (_, []) -> pure (head, headTy, headUses)
  where
    f loc m n ta tb arg targ uarg args = do
      checkConvertible loc [] ta targ
      let ptb = psubst [arg] tb
      -- head'' <- runCore (showTerm headTy)
      -- ptb' <- runCore (showTerm ptb)

      -- traceM "app ty:"
      -- traceM head''
      -- traceM ptb'

      checkArgs (App head arg) ptb (zipWith Plus headUses (fmap (Times m) uarg)) args

{-
- inference will construct types for (un)qualified names and case-expresssions
- inserts implicit arguments
- constructs choice constraints on ambiguous names

- holes, Type and Pi may not appear in infer (head) position
- let and lambda are allowed but not aesthetic
  => its ok to forbid them because head-lambdas are subsumed by let-expressions
     and head-lets can be altered by pushing the binding outwards
-}
inferHead :: Expr -> [(Loc,Plicity,Term,Term,UseEnv)] -> Elab (Term, Term, UseEnv)
inferHead expr args = case expr of
  EApply loc p fun arg -> do
    (arg,targ,uarg) <- inference arg
    inferHead fun ((loc, p, arg, targ, uarg) : args)
  EVar loc name -> do
    res <- lookupCtx loc name
    case res of
      Nothing -> lookupUnQualified loc name args
      Just (term,ty,u) -> checkArgs term ty u args
  EName loc qname -> do
    (t,ty,u) <- lookupQualified loc qname
    checkArgs t ty u args
  x -> do
    (term,ty,uses) <- inference expr
    checkArgs term ty uses args

inference :: Expr -> Elab (Term,Term,UseEnv)
inference name @ (EName {}) = inferHead name []
inference var  @ (EVar {}) = inferHead var []
inference app  @ (EApply {}) = inferHead app []
inference (EType loc) = pure (Type, Kind, emptyUseEnv)
inference (EHole loc) = do
  (ty,_) <- freshMeta Kind
  (t,u) <- freshMeta ty
  pure (t,ty,u)
inference (ELam loc nloc p _ n ta b) = do
  let la = exprLoc ta
  (ta', ka, _) <- inference ta
  m <- freshMultVar
  (b',tb,ub) <- local (EM.push (Hyp p m n ta' Nothing)) (inference b)
  let (u:us) = ub
  checkUse loc [] m u
  -- let retty = Lam p m n ta' b'
  -- retty' <- runCore (showTerm retty)
  -- traceM "lam:"
  -- traceM retty'
  pure (Lam p m n ta' b', Pi p m n ta' tb, us)
inference (EPi loc nloc p m n ta tb) = do
  let la = exprLoc ta
      lb = exprLoc tb
  (ta',ka,_) <- inference ta
  (tb',kb,_) <- local (EM.push (Hyp p m n ta' Nothing)) (inference tb)
  ensureSort la ka
  ensureSort lb kb
  pure (Pi p m n ta' tb', kb, emptyUseEnv)
inference (ELet loc nloc n a ta b) = do
  let la = exprLoc ta
  (ta',ka,_) <- inference ta
  (a',ua) <- elaborate a ta'
  m <- freshMultVar
  (b',tb,ub) <- local (EM.push (Hyp Explicit m n ta' (Just a'))) (inference b)
  let (u:us) = ub
  checkUse nloc [] m u
  pure (Let m n a' ta' b', psubst [a'] tb, zipWith Plus (fmap (Times m) ua) us)
inference (EMatch loc scrutinee motive branches) = do
  (scrutinee, scrutty, scrutuses) <- inferHead scrutinee []
  (block, defno, dat, args') <- ensureData scrutty
  (f,mult) <- if length branches > 1
    then pure (id,Many)
    else do
      mult <- freshMultVar
      let f Zero = Zero
          f Many = mult
          f _    = error "illegal multiplicity in computed branch"
      pure (f,mult)
  let pno = paramno dat
      (params, indices) = L.splitAt pno (reverse args')
      motiveTy = motiveType params block defno dat

  -- mo' <- runCore (showTerm motiveTy)
  -- traceM "motiveTy:"
  -- traceM mo'

  motive <- fst <$> elaborate motive motiveTy

  -- mo <- runCore (showTerm motive)
  -- traceM "motive:"
  -- traceM mo


  let 
    branchTys =
      fmap
        (\ctorno -> branchType f params motive block defno ctorno dat)
        [0 .. length (introRules dat) - 1]
    ctors = introRules dat
    findBranch branches ctor =
      let name = ctorName ctor in
        L.foldl (\acc (name', args, rhs) ->
          if name' == name
          then
            pure (L.foldl (\acc arg -> ELam loc loc Explicit Many arg (EHole loc) acc) rhs (reverse args))
          else acc)
            (err (show loc ++ "case expression has missing branches: " ++ name, []))
            branches
  
  btys <- runCore (unlines <$> mapM showTerm branchTys)
  traceM "branchTys:"
  traceM btys

  let resultTy = mkApp motive (indices ++ [scrutinee])
  
  resultTy' <- runCore (showTerm resultTy)
  traceM "match ty:"
  traceM resultTy'

  branches <- mapM (findBranch branches) ctors
  branchResults <- zipWithM elaborate branches branchTys
  let (branches, branchUses) = unzip branchResults
      result = Case mult scrutinee motive branches

  pure (result,resultTy,zipWith Plus scrutuses (fmap Split (transpose branchUses)))

applyMultSubst :: Mult -> MultSubst -> (Mult,[Int])
applyMultSubst (MVar m) mus = case M.lookup m mus of
  Just (val,j') ->
    let (r,ms) = applyMultSubst val mus
    in (r, L.union ms j')
  Nothing -> (MVar m, [])
applyMultSubst m mus = (m,[])

instantiateMult :: Int -> Mult -> [Int] -> Elab ()
instantiateMult m v j = do
  modify (\st -> st {
    multSubst = M.insert m (v,j) (multSubst st)
  })

checkMultEq :: [Int] -> Mult -> Mult -> Elab ()
checkMultEq j lhs rhs = do
  mus <- gets multSubst
  let (lhs',lm) = applyMultSubst lhs mus
      (rhs',rm) = applyMultSubst rhs mus

      j' = L.union lm rm

  case (lhs',rhs') of
    (MVar m0,MVar m1) ->
      if m0 == m1 then pure () else instantiateMult m0 (MVar m1) j'
    (MVar m, t) -> instantiateMult m t j'
    (t, MVar m) -> instantiateMult m t j'
    (t0,t1) -> if t0 == t1 then pure () else err ("inconvertible multiplicities", j')

typeOf :: Term -> Elab (Term,UseEnv)
typeOf Type = pure (Kind,emptyUseEnv)
typeOf Kind = pure (Kind,emptyUseEnv)
typeOf (DBI n) = do
  ctx <- asks EM.context
  pure (Substitution.lift (n + 1) (hypType (ctx !! n)), singleUseEnv emptyLoc n)
typeOf (Meta m) = do
  menv <- gets metaEnv
  case M.lookup m menv of
    Just ty -> pure (ty, emptyUseEnv)
    Nothing -> error "meta without type"
typeOf (Top _ r) = do
  ty <- runCore (typeOfRef r)
  pure (ty,emptyUseEnv)
typeOf (App fun arg) = do
  (tf,uf) <- typeOf fun
  (_,ua) <- typeOf arg
  tf' <- runCore (reduce 0 tf)
  let (Pi p m n ta tb) = tf'
  pure (psubst [arg] tb, zipWith Plus uf (fmap (Times m) ua))
typeOf (Lam p m n ta b) = do
  (tb,ub) <- local (EM.push (Hyp p m n ta Nothing)) (typeOf b)
  pure (Pi p m n ta tb, tail ub)
typeOf (Pi p m n ta tb) = do
  (kb,_) <- typeOf tb
  pure (kb, emptyUseEnv)
typeOf (Let m n a ta b) = do
  (_,ua) <- typeOf a
  (tb,ub) <- local (EM.push (Hyp Explicit m n ta (Just a))) (typeOf b)
  let (u:us) = ub
  pure (psubst [a] tb, zipWith Plus us (fmap (Times m) ua))
typeOf (Case m scrutinee motive branches) = do
  (ty,us) <- typeOf scrutinee
  (block,defno,dat,args) <- ensureData ty
  let pno = paramno dat
      (params,indices) = L.splitAt pno args
  ty <- runCore (reduce maxBound (mkApp motive (indices ++ [scrutinee])))
  buses <- mapM (fmap snd . typeOf) branches
  pure (ty, zipWith Plus us (fmap Split (transpose buses)))

instantiate :: Int -> [Int] -> [Int] -> Term -> Elab ()
instantiate m lenv j t = do
  let
    findValue n [] = error "value does not occur after all"
    findValue n (n':ns)
      | n == n' = 0
      | otherwise = 1 + findValue n ns

    relocate t = f 0 t where
      f k t @ (DBI n)
        | n < k = t
        | otherwise = DBI (findValue (n - k) lenv + k)
      f k t = Utils.map (const (+1)) k f t
  
    t' = relocate t

    -- abstracts away the free variables in the relocated term
    -- and checks the usage environment
    check ty [] = do
      (_,uses) <- typeOf t'
      pure (t',uses)
    check (Pi p m n ta tb) (_:lenv) = do
      (t,tu) <- local (EM.push (Hyp p m n ta Nothing)) (check tb lenv)
      let (u:us) = tu
      checkUse emptyLoc j m u
      pure (Lam p m n ta t,us)
    check ty env = do

      when True $ do
        menv <- gets metaEnv
        msub <- gets metaSubst
        menv <- runCore (showMetaEnv menv)
        msub <- runCore (showMetaSubst msub)
        traceM ""
        traceM menv
        traceM ""
        traceM msub
        traceM ""
      ty' <- runCore (showTerm ty)
      error $ 
        "error while instantiating metavariable:\n" ++
        show m ++
        "\nwith type:\n" ++
        ty' ++
        "\nand environment:\n" ++
        show env 

  -- pt <- runCore (showTerm t)
  -- pt' <- runCore (showTerm t')
  -- traceM "relocation:"
  -- traceM (show lenv)
  -- traceM pt
  -- traceM pt'
  
  -- retrieve the type of the metavar, and check it
  -- then add the term to the metaSubst
  mty <- gets metaEnv <&> maybe (error "meta without type") id . M.lookup m
  
  (mval,_) <- check mty lenv

  modify (\st -> st {
    metaSubst = M.insert m (mval,j) (metaSubst st)
  })

  when False $ do
    menv <- gets metaEnv
    msub <- gets metaSubst
    menv <- runCore (showMetaEnv menv)
    msub <- runCore (showMetaSubst msub)
    traceM ""
    traceM menv
    traceM ""
    traceM msub
    traceM ""

pairWiseFreeVars :: [Term] -> [Int] -> Maybe [Int]
pairWiseFreeVars [] acc = Just (reverse acc)
pairWiseFreeVars (DBI m : args) acc
  | not (m `elem` acc) = pairWiseFreeVars args (m : acc)
pairWiseFreeVars _ _ = Nothing

occursCheck :: Int -> [Int] -> Term -> Bool
occursCheck m vars t = f 0 t True where
  f k (DBI n) a
    | n < k = a
    | otherwise = a && (n - k) `elem` vars
  f k (Meta m') a
    | m == m' = False
  f k t a = Utils.fold (const (+1)) k f t a

tryPattern :: [Int] -> Term -> Term -> Elab () -> Elab ()
tryPattern j x y fail =
  case unrollApp x of
    (Meta mv,args) -> 
      case pairWiseFreeVars args [] of
        Just vars ->
          if occursCheck mv vars y
          then instantiate mv vars j y
          else fail
        Nothing -> fail
    _ -> fail
  
applySubst :: MetaSubst -> Term -> (Term,[Int])
applySubst mes = f where
  f t @ (Meta m) = case M.lookup m mes of
    Nothing -> (t,[])
    Just (val,j) -> let (val',j') = applySubst mes val in (val', L.union j j')
  f (App fun arg) = (g fun' arg', L.union j j') where
    (fun',j) = f fun
    (arg',j') = f arg
  f (Pi p m n ta tb) = (Pi p m n ta' tb', L.union j' j'') where
    (ta',j') = f ta
    (tb',j'') = f tb
  f (Lam p m n ta b) = (Lam p m n ta' b', L.union j' j'') where
    (ta',j') = f ta
    (b',j'') = f b
  f (Let m n a ta b) = (Let m n a' ta' b', L.union j (L.union j' j'')) where
    (a',j) = f a
    (ta',j') = f ta
    (b',j'') = f b
  f (Case m scrut mot br) = (Case m scrut' mot' br', L.union j (L.foldr L.union j' js)) where
    (scrut', j) = f scrut
    (mot', j') = f mot
    (br',js) = unzip (fmap f br)
  f t = (t,[])

  g (Lam p m n ta b) arg = psubst [arg] b
  g fun arg = App fun arg

isStuck :: Term -> Bool
isStuck (App t _ ) = isStuck t
isStuck (Meta _) = True
isStuck (Case _ s _ _) = isStuck s
isStuck _ = False

tryStuck :: [Int] -> Term -> Term -> Elab () -> Elab ()
tryStuck j lhs rhs fail
  | isStuck lhs || isStuck rhs = do
    ctx <- asks EM.context
    insertConstraint (Convertible emptyLoc ctx lhs rhs) j []
  | otherwise = fail

isStuckBy :: Term -> Maybe Int
isStuckBy (App t _ ) = isStuckBy t
isStuckBy (Meta m) = Just m
isStuckBy (Case _ s _ _) = isStuckBy s
isStuckBy _ = Nothing

{-
check if two terms convert, with possible outcomes:
- failure
- success
- stuckness
- partial success, where new constraints are generated
-}
checkConvertible :: Loc -> [Int] -> Term -> Term -> Elab ()
checkConvertible loc j lhs rhs = do

  mes <- gets metaSubst

  let (lhs',lm) = applySubst mes lhs
      (rhs',rm) = applySubst mes rhs

      j' = L.union lm rm

  j <- pure j'

  lhs <- runCore (reduce maxBound lhs')
  rhs <- runCore (reduce maxBound rhs')
    
  let
    (lhead,largs) = unrollApp lhs
    (rhead,rargs) = unrollApp rhs
    
    f Type Type = pure ()
    f Kind Kind = pure ()
    f (DBI n0) (DBI n1)
      | n0 == n1 = zipWithM_ (checkConvertible loc j) largs rargs
    f (Top _ r0 @ (Def _ _ h0 True))(Top _ r1 @ (Def _ _ h1 True))
      | h0 > h1 = do
        lhs' <- runCore (reduce h0 lhs)
        checkConvertible loc j lhs' rhs
      | h0 < h1 = do
        rhs' <- runCore (reduce h1 rhs)
        checkConvertible loc j lhs rhs'
      | otherwise = do
        lhs' <- runCore (reduce h0 lhs)
        rhs' <- runCore (reduce h1 rhs)
        checkConvertible loc j lhs' rhs'
    f (Top _ r @ (Def _ _ h True)) _ = do
      lhs' <- runCore (reduce h lhs)
      checkConvertible loc j lhs' rhs
    f _ (Top _ r @ (Def _ _ h True)) = do
      rhs' <- runCore (reduce h rhs)
      checkConvertible loc j lhs rhs'
    f (Top _ r0)(Top _ r1)
      | r0 == r1 = zipWithM_ (checkConvertible loc j) largs rargs
    f (Lam p m0 n ta0 b0)(Lam _ m1 _ ta1 b1) = do
      checkMultEq j m0 m1
      local (EM.push (Hyp p m0 n ta0 Nothing)) (checkConvertible loc j b0 b1)
    f (Pi p m0 n ta0 tb0)(Pi _ m1 _ ta1 tb1) = do
      checkMultEq j m0 m1
      checkConvertible loc j ta1 ta0
      local (EM.push (Hyp p m0 n ta0 Nothing)) (checkConvertible loc j tb0 tb1)
    f (Case m0 s0 mot0 b0)(Case m1 s1 mot1 b1) = do
      checkConvertible loc j s0 s1
      checkConvertible loc j mot0 mot1
      zipWithM_ (checkConvertible loc j) b0 b1
    f t0 t1 = do
      mes   <- gets metaSubst
      menv  <- gets metaEnv
      mes'  <- runCore (showMetaSubst mes)
      menv' <- runCore (showMetaEnv menv)
      lhs2  <- runCore (showTerm lhs)
      rhs2  <- runCore (showTerm rhs)
      ctx   <- runCore showContext
      err (
        show loc ++
        "\nwith meta-environment:\n" ++
        menv' ++
        "\nwith substitution:\n" ++
        mes' ++
        "\nin context:\n" ++
        ctx ++
        "\ninconvertible terms:\n" ++
        lhs2 ++
        "\n" ++
        rhs2 , j)
  
  tryPattern j lhs rhs $ tryPattern j rhs lhs $ tryStuck j lhs rhs $ f lhead rhead

substUse :: MultSubst -> Use -> (Use,[Int])
substUse mus = f where
  f None = (None,[])
  f (Single _) = (None,[])
  f (Plus x y) = (Plus x' y', L.union j j') where
    (x',j) = f x
    (y',j') = f y
  f (Split xs) = (Split xs', L.foldr L.union [] js) where (xs',js) = unzip (fmap f xs)
  f (Times m x) = (Times m' x', L.union j j') where
    (m',j) = applyMultSubst m mus
    (x',j') = f x 

checkUse :: Loc -> [Int] -> Mult -> Use -> Elab ()
checkUse loc j m u = do
  mus <- gets multSubst
  let 
      (m',js) = applyMultSubst m mus
      (u',js') = substUse mus u
      j = L.union js js'
  case m' of
    Zero -> checkZero u'
    One -> checkOne u'
    Many -> pure ()
    MVar m' -> inferUse m' u' u'
    where
      checkZero :: Use -> Elab ()
      checkZero u = case u of
          None -> pure ()
          Single _ -> err (show loc ++ "erased variable used in relevant context", j)
          Plus u0 u1 -> checkZero u0 *> checkZero u1
          Times Zero _ -> pure ()
          Times (MVar mv) (Single _) -> instantiateMult mv Zero j
          Times (MVar mv) _ -> do
            insertConstraint (MultUse loc m u) j [mv]
          Times _ u -> checkZero u
          Split us -> mapM_ checkZero us

      -- instantiate m with many if used, otherwise re-insert constraint
      inferUse :: Int -> Use -> Use -> Elab ()
      inferUse m' u u' = case u' of
          None -> insertConstraint (MultUse loc m u) j [m']
          Single _ -> instantiateMult m' Many j
          Plus u0 u1 -> inferUse m' u u0 *> inferUse m' u u1
          Times Zero _ -> insertConstraint (MultUse loc m u) j [m']
          Times (MVar _) _ -> insertConstraint (MultUse loc m u) j [m']
          Times _ u0 -> inferUse m' u u0
          Split us -> mapM_ (inferUse m' u) us

      checkOne :: Use -> Elab ()
      checkOne u = case u of
          None -> error "linear variable is unused"
          Single _ -> pure ()
          Plus u0 u1 -> do
              used <- checkMaybe u0
              if used
              then checkNone "linear variable is already used" u1
              else checkOne  u1
          Times Zero _ -> error "linear variable is unused"
          Times One u -> checkOne u
          Times Many u -> checkNone "linear variable is used in unrestricted context" u
          Times (MVar _) u -> error "lul"
          Split us -> mapM_ checkOne us

      checkMaybe :: Use -> Elab Bool
      checkMaybe u = case u of
          None -> pure False
          Single _ -> pure True
          Plus u0 u1 -> do
              used <- checkMaybe u0
              if used
              then checkNone "linear variable is already used" u1 $> True
              else checkMaybe u1
          Times Zero _ -> pure False
          Times One u -> checkMaybe u
          Times Many u -> checkNone "linear variable is used in unrestricted context" u $> False
          Times (MVar _) _ -> undefined -- stuck
          Split [] -> pure False
          Split (u:us) -> do
              used <- checkMaybe u
              if used
              then mapM_ checkOne us $> True
              else mapM_ (checkNone "linear variable is not used consistently across case branches") us $> False

      checkNone :: String -> Use -> Elab ()
      checkNone msg u = case u of
          None -> pure ()
          Single loc -> undefined --err (show loc ++ msg)
          Plus u1 u2 -> checkNone msg u1 *> checkNone msg u2
          Times Zero _ -> pure ()
          Times _ u -> checkNone msg u
          Split us -> mapM_ (checkNone msg) us

checkConstraint :: Constraint -> [Int] -> Elab ()
checkConstraint c j = case c of
  Convertible loc ctx lhs rhs -> withContext ctx (checkConvertible loc j lhs rhs)
  MultUse loc m u -> checkUse loc j m u
  EnsureData ctx m e -> error "ensure data constraint not implemented"
  Choice ctx m alts -> error "choice constraint not imlemented"

solveConstraints :: Elab ()
solveConstraints = do
  solvedMetas <- gets (keys . metaSubst)
  solvedMults <- gets (keys . multSubst)
  let solved = L.union solvedMetas solvedMults
  loop solved
  where
    loop solved = do
      constraints <- gets elabConstraints
      modify (\st -> st {elabConstraints = mempty})
      mapM_ (\(c,j,_) -> checkConstraint c j) constraints
      solvedMetas <- gets (keys . metaSubst)
      solvedMults <- gets (keys . multSubst)
      let solved' = L.union solvedMetas solvedMults
      constraints' <- gets elabConstraints
      if L.null constraints'
      then pure ()
      else if L.null (L.deleteFirstsBy (==) solved' solved)
        then do
          let (constrs,_,_) = unzip3 constraints'
          mes <- gets metaSubst
          menv <- gets metaEnv
          mes' <- runCore (showMetaSubst mes)
          menv' <- runCore (showMetaEnv menv)
          constrs' <- runCore (showConstraints constrs)
          err (
            "with meta-environment:\n" ++
            menv' ++
            "\nand meta-substitution:\n" ++
            mes' ++
            "\nunresolved constraints:\n" ++
            constrs', [])
        else loop solved'

checkAllSolved :: Term -> Term -> Elab ()
checkAllSolved t t' = let
  f () (Meta _) _ = False
  f () t acc = Utils.fold (const id) () f t acc
  in
    if f () t' True
    then pure ()
    else do
      t2 <- runCore (showTerm t)
      t3 <- runCore (showTerm t')
      mes <- gets metaSubst
      menv <- gets metaEnv
      mes' <- runCore (showMetaSubst mes)
      menv' <- runCore (showMetaEnv menv)

      err (
        "with meta-environment:\n" ++
        menv' ++
        "\nand meta subst:\n" ++
        mes' ++
        "\nterm has unsolved metas:\n" ++ t3 ++
        "\nbare term\n" ++
        t2
        , [])

finalize :: Term -> Elab Term
finalize t = do
  mes <- gets metaSubst
  let (t',_) = applySubst mes t
  checkAllSolved t t'
  pure t'