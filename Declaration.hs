module Declaration where

import Control.Monad.RWS.Lazy
import Control.Monad.State.Lazy
import Control.Monad.Trans
import Core
import Data.Bifunctor
import Data.Function
import Data.List as L
import Data.Map as M
import Datatype
import Debug.Trace
import ElabMonad as EM
import Elaborator
import Lexer (Loc, emptyLoc)
import Parser
import Prettyprint
import Reduction
import Substitution
import Typecheck
import Utils

type Clause = ([Pattern], Expr)

data Block
  = DataBlock [(Loc, Name, [Param], Expr, [Ctor])]
  | FunBlock [(Loc, Name, Expr, [Clause])]

data DeclState = DeclState
  { moduleName :: Name,
    importedNames :: NameSpace,
    internalNames :: NameSpace,
    nextBlock :: Int,
    signature :: Signature,
    elabState :: ElabState
  }

type DeclElab = StateT DeclState (Either String)

mergeNameSpace :: NameSpace -> NameSpace -> NameSpace
mergeNameSpace (n0, q0) (n1, q1) = (M.unionWith (++) n0 n1, M.union q0 q1)

ensureUnique :: QName -> DeclElab ()
ensureUnique qname = do
  qname' <- gets (M.lookup qname . snd . internalNames)
  case qname' of
    Nothing -> pure ()
    Just (info, _) -> Control.Monad.State.Lazy.lift $ Left (showQName qname ++ " is already defined here:\n" ++ show info)

ensureDistinct :: [String] -> DeclElab ()
ensureDistinct [] = pure ()
ensureDistinct (name : names)
  | name `elem` names = Control.Monad.State.Lazy.lift $ Left "names in a block must be distinct"
  | otherwise = ensureDistinct names

updateNameSpace :: [(QName, Loc, Reference)] -> NameSpace -> NameSpace
updateNameSpace names (shorts, longs) =
  let shorts' = L.foldr (\(qname, _, _) -> insertWith (++) (last qname) [qname]) shorts names
      longs' = L.foldr (\(qname, loc, ref) -> M.insert qname (loc, ref)) longs names
   in (shorts', longs')

runTypechecker :: Elab a -> DeclElab a
runTypechecker x = do
  DeclState modname imported internal nextBlock sig st <- get

  let result =
        runRWST
          x
          (ElabEnv modname (mergeNameSpace imported internal) Safe [] nextBlock sig)
          st

  case result of
    Right (a, st', ()) -> do
      modify (\st -> st {elabState = st'})
      pure a
    Left (msg, j) -> Control.Monad.State.Lazy.lift $ Left $ msg

groupDecls :: [Decl] -> Either String [Block]
groupDecls = coupleGroups . groupBy sameDeclKind
  where
    sameDeclKind DataDecl {} DataDecl {} = True
    sameDeclKind DataDef {} DataDef {} = True
    sameDeclKind FunDecl {} FunDecl {} = True
    sameDeclKind Clause {} Clause {} = True
    sameDeclKind _ _ = False

    declName :: Decl -> String
    declName (DataDecl _ n _ _) = n
    declName (DataDef _ n _) = n
    declName (FunDecl _ n _) = n
    declName (Clause _ n _ _) = n

    declLoc :: Decl -> Loc
    declLoc (DataDecl x _ _ _) = x
    declLoc (DataDef x _ _) = x
    declLoc (FunDecl x _ _) = x
    declLoc (Clause x _ _ _) = x

    findDefs :: [Decl] -> [Decl] -> Either String [(Loc, Name, [Param], Expr, [Ctor])]
    findDefs [] [] = pure []
    findDefs (DataDef loc _ _ : _) [] = Left (show loc ++ "definition was not declared")
    findDefs defs (decl@(DataDecl loc name params arity) : decls) = case find ((name ==) . declName) defs of
      Just (DataDef _ _ ctors) -> do
        block <- findDefs (deleteBy ((==) `on` declName) decl defs) decls
        pure ((loc, name, params, arity, ctors) : block)
      Nothing -> Left (show loc ++ "declaration lacks accompanying definition")

    findClauses :: [[Decl]] -> [Decl] -> Either String [(Loc, Name, Expr, [Clause])]
    findClauses [] [] = pure []
    findClauses ((Clause loc _ _ _ : _) : _) [] = Left (show loc ++ "definition was not declared")
    findClauses clauses (decl@(FunDecl loc name ty) : decls) = case find ((name ==) . declName . head) clauses of
      Just c -> do
        let clauses' = fmap (\(Clause _ _ pats rhs) -> (pats, rhs)) c
        block <- findClauses (deleteBy ((==) `on` (declName . head)) c clauses) decls
        pure ((loc, name, ty, clauses') : block)
      Nothing -> Left (show loc ++ "declaration lacks accompanying definition")

    coupleGroups :: [[Decl]] -> Either String [Block]
    coupleGroups [] = pure []
    coupleGroups (decls : defs : groups) = case (head decls, head defs) of
      (DataDecl {}, DataDef {}) -> do
        block <- findDefs defs decls
        blocks <- coupleGroups groups
        pure (Declaration.DataBlock block : blocks)
      (FunDecl {}, Clause {}) -> do
        block <- findClauses (groupBy ((==) `on` declName) defs) decls
        blocks <- coupleGroups groups
        pure (FunBlock block : blocks)
      (FunDecl loc _ _, _) -> Left (show loc ++ "declarations lacks accompanying definition")
      (DataDecl loc _ _ _, _) -> Left (show loc ++ "declarations lacks accompanying definition")
      (DataDef loc _ _, _) -> Left (show loc ++ "definitions lacks type declaration")
      (Clause loc _ _ _, _) -> Left (show loc ++ "definitions lacks type declaration")

checkBlocks :: [Block] -> DeclElab ()
checkBlocks = mapM_ f
  where
    f (Declaration.DataBlock defs) = checkData defs
    f (FunBlock defs) = checkFunctions defs

checkFunctions :: [(Loc, Name, Expr, [Clause])] -> DeclElab ()
checkFunctions defs = do
  modname <- gets Declaration.moduleName

  block <- gets nextBlock

  let (deflocs, defnames, deftys, clauses) = unzip4 defs

      qnames = fmap (\name -> [modname, name]) defnames

  tys <- runTypechecker $
    flip mapM deftys $ \ty -> do
      (ty, k, _) <- inference ty
      Elaborator.ensureSort emptyLoc k
      solveConstraints
      ty' <- finalize ty
      put emptyElabState
      pure ty'

  traceM "signatures ok"

  let assertOneClause :: [Clause] -> Clause
      assertOneClause [clause] = clause
      assertOneClause xs = error "multiple clauses are not supported yet"

      checkBody :: Term -> Clause -> Elab Term
      checkBody t c = do
        t' <- fst <$> checkClause t c
        t2 <- finalize t'
        put emptyElabState

        t3 <- runCore (showTerm t2)
        traceM t3

        pure t2

      checkClause :: Term -> Clause -> Elab (Term,UseEnv)
      checkClause (Pi Implicit m n ta tb) clause = do
        (rhs,urhs) <- local (EM.push (Hyp Implicit m n ta Nothing)) (checkClause tb clause)
        let (u:us) = urhs
        checkUse emptyLoc [] m u
        pure (Lam Implicit m n ta rhs,us)
      checkClause (Pi Explicit m n ta tb) (PApp l nl n' [] : args, rhs) = do
        (rhs,urhs) <- local (EM.push (Hyp Explicit m n' ta Nothing)) (checkClause tb (args, rhs))
        let (u:us) = urhs
        checkUse emptyLoc [] m u
        pure (Lam Implicit m n' ta rhs, us)
      checkClause _ (_ : _, rhs) = error $ show (exprLoc rhs) ++ "pattern matching clauses not supported yet"
      checkClause ty ([], rhs) = elaborate rhs ty

      firstClauses = fmap assertOneClause clauses

  bodies <- runTypechecker $ zipWithM checkBody tys firstClauses

  let functions = zipWith Function tys bodies

      objects = FunctionBlock 0 True True functions

      refs = fmap (\defno -> Def block defno 0 True) [0 ..]

      name_loc_refs = zip3 qnames deflocs refs

  modify
    ( \st ->
        st
          { nextBlock = block + 1,
            internalNames = updateNameSpace name_loc_refs (internalNames st),
            Declaration.signature = second (M.insert block objects) (Declaration.signature st)
          }
    )

  traceM $ show qnames ++ " defined"

checkData :: [(Loc, Name, [Param], Expr, [Ctor])] -> DeclElab ()
checkData defs = do
  modname <- gets Declaration.moduleName

  block <- gets nextBlock

  let defcount = length defs
      (def_locs, names, paramss, arities, ctorss) = unzip5 defs

      qnames = fmap (\name -> [modname, name]) names

      ctor_names = fmap (fmap (\(_, n, _) -> n)) ctorss

      ctor_qnames = concat (zipWith (\qname ctor_names -> fmap (\name -> qname ++ [name]) ctor_names) qnames ctor_names)

  ensureDistinct names
  mapM_ ensureDistinct ctor_names
  mapM_ ensureUnique qnames
  mapM_ ensureUnique ctor_qnames

  let checkParams :: [Param] -> Expr -> Elab (Context, Term)
      checkParams [] e = do
        (arity, _) <- elaborate e Kind
        solveConstraints
        arity' <- finalize arity
        ctx' <-
          asks EM.context
            >>= mapM
              ( \hyp -> do
                  ty' <- finalize (hypType hyp)
                  pure (hyp {hypType = ty'})
              )
        put emptyElabState
        pure (ctx', arity')
      checkParams ((_, p, m, name, ty) : ctx) e = do
        (ty, _, _) <- inference ty
        local (EM.push (Hyp p m name ty Nothing)) (checkParams ctx e)

  (paramss, arities) <- unzip <$> runTypechecker (zipWithM checkParams paramss arities)

  let unrollPi :: Term -> Int
      unrollPi (Pi _ _ _ _ dst) = 1 + unrollPi dst
      unrollPi _ = 0

      paramnos = fmap length paramss
      indexnos = fmap unrollPi arities

      extendArity :: Term -> Context -> Term
      extendArity = L.foldl (\acc (Hyp p m name ty _) -> Pi p m name ty acc)

      -- arities extended with parameters
      arities_ext = zipWith extendArity arities paramss

      ctx_with_arities = reverse (zipWith (\name ty -> Hyp Explicit Zero name ty Nothing) names arities_ext)

      checkCtor :: Int -> Int -> Ctor -> Elab (Int, Term)
      checkCtor defno pno (loc, name, expr) = do
        (t, _, _) <- inference expr
        solveConstraints
        t' <- finalize t
        put emptyElabState
        -- u <- allOccurrencesPositive loc defcount defno pno pno (pno + defcount) t
        pure (0, t')

      checkCtorBlock :: (Int, Context, [Ctor]) -> Elab (Int, [Term])
      checkCtorBlock (defno, params, ctors) = do
        (us, ctors) <- unzip <$> local (\env -> env {EM.context = params ++ EM.context env}) (mapM (checkCtor defno (length params)) ctors)
        pure (minimum (maxBound : us), ctors)

  --traceM "arities:"

  arities' <- mapM (runTypechecker . runCore . showTerm) arities_ext
  traceM (unlines arities')

  (us, ctor_tys) <-
    runTypechecker $
      unzip
        <$> local
          (\env -> env {EM.context = ctx_with_arities})
          (mapM checkCtorBlock (zip3 [0 ..] paramss ctorss))

  let ctor_arities = fmap (fmap unrollPi) ctor_tys -- compute arities

      -- abstracted ctors explicitly quantify over the datatype parameters
      abstractCtors :: Context -> [Term] -> [Term]
      abstractCtors params ctors =
        fmap
          ( \acc ->
              L.foldl
                ( \acc (Hyp p m name ty _) ->
                    Pi Implicit Zero name ty acc
                )
                acc
                params
          )
          ctors

      abstracted_ctors = zipWith abstractCtors paramss ctor_tys

      upno = minimum us

      def_refs = fmap (Ind block) [0 ..]

      def_consts = zipWith Top qnames def_refs

      def_name_loc_refs = zip3 qnames def_locs def_refs

      ctor_instances = fmap (fmap (psubst (reverse def_consts))) abstracted_ctors

      ctor_refs =
        concat
          ( zipWith3
              ( \ctors params defno ->
                  fmap
                    (\ctorno -> Con block defno ctorno (length params) True)
                    [0 .. length ctors - 1]
              )
              ctor_instances
              paramss
              [0 ..]
          )

      ctor_locs = concatMap (fmap (\(loc, _, _) -> loc)) ctorss

      ctor_ref_name_locs = zip3 ctor_qnames ctor_locs ctor_refs

      name_loc_refs = ctor_ref_name_locs ++ def_name_loc_refs
  --name_names = zip (concat ctor_names) ctor_qnames ++ zip names qnames

  --traceM "ctors:"

  ctors' <- mapM (runTypechecker . runCore . showTerm) (concat ctor_instances)
  traceM (unlines ctors')

  let objects =
        Core.DataBlock
          { dataTotal = True,
            uniparamno = upno,
            dataDefs =
              zipWith7
                ( \name arity ctor_names ctor_arities ctor_tys pno ino ->
                    Datatype
                      { dataName = name,
                        arity = arity,
                        paramno = pno,
                        indexno = ino,
                        introRules = zipWith4 Constructor ctor_names ctor_arities ctor_tys (repeat True)
                      }
                )
                qnames
                arities_ext
                ctor_names
                ctor_arities
                ctor_instances
                paramnos
                indexnos
          }

  modify
    ( \st ->
        st
          { nextBlock = block + 1,
            internalNames = updateNameSpace name_loc_refs (internalNames st),
            Declaration.signature = first (M.insert block objects) (Declaration.signature st)
          }
    )

  let computeAux compute name defno dat = do
        def <- runTypechecker $ compute block defno dat

        runTypechecker $ runCore (showTerm def) >>= traceM >> traceM ""

        ty <- runTypechecker $ fst <$> runCore (infer def)
        block' <- gets nextBlock
        let qname = dataName dat
            ref = Def block' 0 1 True
            name' = qname ++ [name]
            nlr = (name', emptyLoc, ref)
            fun = Function ty def
            obj = FunctionBlock maxBound True True [fun]

        modify
          ( \st ->
              st
                { nextBlock = block' + 1,
                  internalNames = updateNameSpace [nlr] (internalNames st),
                  Declaration.signature = second (M.insert block' obj) (Declaration.signature st)
                }
          )

  traceM $ show qnames ++ " defined"
