module Parser where

import Lexer hiding (keywords, puncts)
import Core

import Control.Applicative ( Alternative(some) )
import Data.List ()
import Data.Function ()
import Data.Array.Unboxed ( listArray )
import Data.Maybe ( isJust )
import Control.Monad.RWS
import Debug.Trace

-- TODO
-- mk fault tolerant parser
-- make mutual blocks indented?

type Param = (Loc, Plicity, Mult, String, Expr)
type Ctor = (Loc, String, Expr)

data Pattern
  = PAbsurd
  | PIgnore
  | PApp Loc Loc String [Pattern]

instance Show Pattern where
  show PIgnore = "_"
  show (PApp _ _ x xs) = x ++ " " ++ unwords (fmap showArg xs) where
    showArg p @ PApp {} = "(" ++ show p ++ ")"
    showArg p = show p

type Module = (String,[String],[Decl])

data Decl 
  = DataDecl Loc String [Param] Expr
  | DataDef  Loc String [Ctor]
  | FunDecl  Loc String Expr
  | Clause   Loc String [Pattern] Expr

data Expr 
  = EType   Loc
  | EName   Loc [String]
  | EVar    Loc String
  | EHole   Loc
  | EApply  Loc Plicity Expr Expr
  | EPi     Loc Loc Plicity Mult String Expr Expr
  | ELam    Loc Loc Plicity Mult String Expr Expr
  | ELet    Loc Loc String Expr Expr Expr
  | EMatch  Loc Expr Expr [(String,[String],Expr)]

exprLoc :: Expr -> Loc
exprLoc (EType s) = s
exprLoc (EName s _) = s
exprLoc (EVar s _) = s
exprLoc (EHole s) = s
exprLoc (ELam s _ _ _ _ _ _) = s
exprLoc (EApply s _ _ _) = s
exprLoc (EPi s _ _ _ _ _ _) = s

declLoc :: Decl -> Loc
declLoc (DataDecl s _ _ _) = s
declLoc (DataDef s _ _) = s
declLoc (FunDecl s _ _) = s
declLoc (Clause s _ _ _) = s

puncts :: [String]
puncts = ["->", "=" , "()", "(" , ")" , "{", "}", "[", "]", "\\" , ".", ":", ","]

keywords :: [String]
keywords = [
  "_",
  "module",
  "import",
  "data",
  "where",
  "match",
  "return",
  "with",
  "let",
  "in",
  "Pi", 
  "Type"]

parseQName :: Cursor -> String -> Parser Expr
parseQName begin x = do
  t <- peekToken
  case t of
    Pct "." -> do
      xs  <- tail
      loc <- endLoc begin
      pure (EName loc (x:xs))
    _ -> do
      loc <- endLoc begin
      pure (EVar loc x)
    where
      tail = do
        token
        x <- expectSymbol "symbol after '.' in qualified name"
        t <- peekToken
        case t of
          Pct "." -> do
            xs <- tail
            pure (x:xs)
          _ -> pure [x]

annot :: Parser Expr
annot = do
  t <- peekToken
  case t of
    Pct ":" -> token *> parseExpr
    _ -> EHole <$> (beginLoc >>= endLoc)

parseMult :: Parser Mult
parseMult = do
  t <- peek token 
  case t of
    Number 0 -> fmap (const Zero) token
    Number 1 -> fmap (const One) token
    _ -> pure Many

annotParam :: Plicity-> Parser [Param]
annotParam p = do
  m  <- parseMult
  bs <- some (withLoc (expectSymbol "name in parameter list"))
  ty <- annot
  pure (fmap (\(nloc,name) -> (nloc,p,m,name,ty)) bs)

param :: Parser [Param]
param = do
  t <- peekToken
  case t of
    Pct "(" -> token *> annotParam Explicit <* f ")"
    Pct "{" -> token *> annotParam Implicit <* f "}"
    Pct "[" -> token *> annotParam Class <* f "]"
    _ -> annotParam Explicit
  where f close = expect close ("closing '" ++ close ++ "' after parameter")

params :: Parser [Param]
params = do
  t <- peekToken
  case t of
    Symbol _ -> someParams
    Pct "("  -> someParams
    Pct "{"  -> someParams
    Pct "["  -> someParams
    _ -> pure []
  
someParams :: Parser [Param]
someParams = (++) <$> param <*> params

-- parse a lambda or dependent product,
-- having already consumed the '\\' or 'Pi' token
parseBinder :: Cursor -> (Loc -> Loc -> Plicity -> Mult -> String -> Expr -> Expr -> Expr) -> Parser Expr
parseBinder begin mk = do
  ps <- someParams
  expect "," "',' after parameters in binder"
  body <- parseExpr
  loc <- endLoc begin
  let f (nloc,p,m,v,ta) = mk loc nloc p m v ta
  pure (foldr f body ps)

parseLet :: Cursor -> Parser Expr
parseLet begin = do
  (nloc,name) <- withLoc (expectSymbol "name after 'let' keyword")
  let f ty = do
        expect "=" "'=' after name in let expression"
        bindee <- parseExpr
        expect "in" "'in' after binding in let expression"
        body <- parseExpr
        loc <- endLoc begin
        pure (ELet loc nloc name ty bindee body)
  t <- peekToken
  case t of
    Pct ":" -> token *> parseExpr >>= f
    _ -> endLoc begin >>= f . EHole

parseMatch :: Cursor -> Parser Expr
parseMatch begin = do
  scrutinee <- parseExpr
  let f motive = do
        expect "with" "'with' after scrutinee in match expression"
        arms <- parseBlock parseArm
        loc <- endLoc begin
        pure (EMatch loc scrutinee motive arms)

      parseArm = do
        x <- expectSymbol "constructor name in match arm"
        (xs,rhs) <- parseSubs
        pure (x,xs,rhs)

      parseSubs = do
        (loc,t) <- withLoc token
        case t of
          Pct "->" -> (,) [] <$> parseExpr
          Symbol x -> do
            (xs,rhs) <- parseSubs
            pure (x:xs,rhs)
          _ -> expected loc "a symbol in match arm" (show loc)

  t <- peek token
  case t of
    Pct "return" -> token *> parseExpr >>= f
    _ -> endLoc begin >>= f . EHole

parsePrimary :: Parser Expr
parsePrimary = do
  begin   <- beginLoc
  (loc,t) <- withLoc token
  case t of
    Pct "(" ->
      parseExpr <* expect ")" "closing ')' after parseExpression"
    Pct "\\" -> parseBinder begin ELam
    Pct "Type" -> pure (EType loc)
    Pct "Pi" -> parseBinder begin EPi
    Pct "let" -> parseLet begin
    Pct "match" -> parseMatch begin
    Pct "_" -> pure (EHole loc)
    Symbol x -> parseQName begin x
    x -> expected loc "some parseExpression" (show loc)


isArg :: Parser Bool
isArg = do
  t <- peekToken
  pure $ case t of
    Symbol _    -> True
    Pct "_"     -> True
    Pct "Type"  -> True
    Pct "\\"    -> True
    Pct "Pi"    -> True
    Pct "let"   -> True
    Pct "match" -> True
    Pct "("     -> True
    Pct "{"     -> True
    _           -> False

parseApp :: Parser Expr
parseApp = do
  begin <- beginLoc 
  head <- parsePrimary
  let
    parseArgs :: Parser [(Plicity,Loc,Expr)]
    parseArgs = do
      blockEnds <- isBlockEnd
      if blockEnds
      then pure []
      else do
        t <- peekToken
        case t of
          Symbol _    -> expArg
          Pct "_"     -> expArg
          Pct "Type"  -> expArg
          Pct "\\"    -> expArg
          Pct "Pi"    -> expArg
          Pct "let"   -> expArg
          Pct "match" -> expArg
          Pct "("     -> expArg
          Pct "{"     -> impArg
          _           -> pure []
    
    expArg = do
      arg <- parsePrimary
      loc <- endLoc begin
      args <- parseArgs
      pure ((Explicit,loc,arg):args)
    
    impArg = do
      token
      arg <- parseExpr
      expect "}" "closing '}' after implicit argument"
      loc <- endLoc begin
      args <- parseArgs
      pure ((Implicit,loc,arg):args)

  args <- parseArgs
  pure (foldl (\fun (p,loc,arg) -> EApply loc p fun arg) head args)
  where


parseArrow :: Parser Expr
parseArrow = do
  begin <- beginLoc
  lhs   <- parseApp
  t     <- peekToken
  case t of
    Pct "->" -> f Many begin lhs
    Pct "=>" -> f Zero begin lhs
    _ -> pure lhs
    where
      f m begin lhs = do
        token
        rhs <- parseArrow
        loc <- endLoc begin
        pure (EPi loc loc Explicit m "" lhs rhs)

parseExpr :: Parser Expr
parseExpr = parseArrow

parseAppPattern :: Parser Pattern
parseAppPattern = do
  begin       <- beginLoc
  (nloc,name) <- withLoc $ expectSymbol "constructor name in application pattern"
  args        <- parsePatterns
  loc         <- endLoc begin
  pure (PApp loc nloc name args)
 
parseClosedPattern :: Parser Pattern
parseClosedPattern = do
  (loc,t) <- withLoc token
  case t of
    Pct "(" -> do
      app <- parseAppPattern
      expect ")" "closing ')' after pattern"
      pure app
    Pct "_" -> pure PIgnore
    Symbol x -> do
      pure (PApp loc loc x [])

parsePatterns :: Parser [Pattern]
parsePatterns = do
  t <- peekToken
  case t of
    Symbol _ -> pat
    Pct "("  -> pat
    Pct "_"  -> pat
    _ -> pure []
  where
    pat = (:) <$> parseClosedPattern <*> parsePatterns

-- parse a function clause, having already consumed the name
parseClause :: Loc -> String -> Parser Decl
parseClause loc name = do
  pats <- parsePatterns
  (loc,t) <- withLoc token
  case t of
    Pct "=" -> parseExpr >>= f pats
    Pct "()" -> f (pats ++ [PAbsurd]) (EHole loc)
    _ -> expected loc "'=' or '()' after patterns in clause" (show loc)
  where
    f pats body = pure (Clause loc name pats body)

parseConstructor :: Parser Ctor
parseConstructor = do
  (nloc,name) <- withLoc $ expectSymbol "name in constructor definition"
  expect ":" "':' after name in constructor definition"
  ty <- parseExpr
  pure (nloc,name,ty)

-- parse a data declaration/definition,
-- having already consumed the 'data' keyword
parseData :: Parser [Decl]
parseData = do
  (loc,name) <- withLoc (expectSymbol "name after 'data' in data declaration")
  ps <- params
  arity <- do
    t <- peekToken
    case t of
      Pct ":" -> token >> fmap Just parseExpr
      _ -> pure Nothing
  ctors <- do
    t <- peekToken
    case t of
      Pct "where" -> token >> fmap Just (parseBlock parseConstructor)
      _ -> pure Nothing

  case (arity,ctors) of
    (Nothing, Nothing) -> errAt loc "data declaration must have a declaration and constructor block"
    (Nothing, Just ctors) -> pure [DataDef loc name ctors]
    (Just arity, Nothing) -> pure [DataDecl loc name ps arity]
    (Just arity, Just ctors) -> pure
      [DataDecl loc name ps arity,
      DataDef loc name ctors]

-- parse a function clause/declaration, having already consumed the symbol
parseFunction :: Loc -> String -> Parser Decl
parseFunction loc name = do
  t <- peekToken
  case t of
    Pct ":" -> token *> (FunDecl loc name <$> parseExpr)
    _ -> parseClause loc name 

-- parse declarations
parseDecl :: Parser [Decl]
parseDecl = do
  (loc,t) <- withLoc token
  case t of
    Pct ""     -> pure []
    Pct "data" -> parseData
    Symbol x   -> (:[]) <$> parseFunction loc x
    x -> err (show loc ++ "expected some declaration")

-- parse module import statements
parseImports :: Parser [String]
parseImports = do
  t <- peekToken
  case t of
    Pct "import" -> do
      token
      parseBlock (expectSymbol "name after 'import'")
    _ -> pure []

parseModule :: Parser Module
parseModule = do
  expect "module" "module name declaration"
  name <- expectSymbol "name after 'module'"
  imports <- parseImports
  decls <- concat <$> parseItems 0 parseDecl
  pure (name,imports,decls)

parse :: Filename -> String -> Either ParseError Module
parse name input = do
  fst <$> evalRWST
            parseModule
            (ParserEnv keywords puncts name (listArray (0, length input - 1) input) [0])
            (Cursor 0 0 0)