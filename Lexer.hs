module Lexer where

import Control.Applicative (Alternative (..))
import Control.Monad (guard, replicateM)
import Control.Monad.RWS
import Data.Array.Unboxed (IArray (bounds), UArray, (!))
import Data.Char
import Data.Either ()
import Data.Foldable (asum)

data Cursor = Cursor
  { cursorIndex :: Int,
    line :: Int,
    col :: Int
  }

data Token
  = Symbol String
  | Number Int
  | Pct String
  | Str [Int]
  deriving (Eq)

type Position = (Int, Int)

type Range = (Position, Position)

data Loc = Loc
  { uri :: String,
    range :: Range
  }

emptyLoc :: Loc
emptyLoc = Loc "" ((0,0),(0,0))

type ParseError = String

type Filename = String

type Charray = UArray Int Char

type Indent = Int

data ParserEnv = ParserEnv
  { keywords :: [String],
    puncts :: [String],
    filename :: Filename,
    source :: Charray,
    indentation :: [Indent]
  }

type Parser a = RWST ParserEnv String Cursor (Either ParseError) a

len :: Charray -> Int
len = (+ 1) . snd . bounds

instance Show Loc where
  show (Loc src ((startLine, startCol), (endLine, endCol))) =
    src ++ ": "
      ++ show startLine
      ++ ":"
      ++ show startCol
      ++ " - "
      ++ show endLine
      ++ ":"
      ++ show endCol

err :: String -> Parser a
err = lift . Left

expected :: Loc -> String -> String -> Parser a
expected span msg e =
  err $
    show span ++ "\nexpected " ++ msg ++ ", but got: \'" ++ e ++ "\'"

errAt :: Loc -> String -> Parser a
errAt span msg = err (show span ++ msg)

isEof :: Parser Bool
isEof = do
  index <- gets cursorIndex
  leng <- asks (len . source)
  pure (index >= leng)

eof :: Parser Token
eof = do
  b <- isEof
  if b then pure (Pct "") else err ""

char :: Parser Char
char = do
  c <- get
  name <- asks filename
  arr <- asks source
  end <- asks (len . source)
  if cursorIndex c >= end
    then err (name ++ ": Unexpected end of input")
    else pure ()
  let x = arr ! cursorIndex c
      c' =
        if x == '\n'
          then
            Cursor
              { cursorIndex = cursorIndex c + 1,
                col = 0,
                line = line c + 1
              }
          else
            Cursor
              { cursorIndex = cursorIndex c + 1,
                col = col c + 1,
                line = line c
              }
  put c'
  pure x

peek :: Parser a -> Parser a
peek p = do
  save <- get
  res <- p
  put save
  pure res

parseIf :: (Char -> Bool) -> Parser Char
parseIf f = do
  x <- char
  guard (f x)
  pure x

beginLoc :: Parser Cursor
beginLoc = ws *> get

endLoc :: Cursor -> Parser Loc
endLoc x = do
  y <- get
  src <- asks filename
  arr <- asks source
  pure $
    Loc src ((line x, col x),(line y, col y))

withLoc :: Parser a -> Parser (Loc, a)
withLoc p = do
  ws
  begin <- get
  item <- p
  loc <- endLoc begin
  pure (loc, item)

string :: String -> Parser String
string = mapM (parseIf . (==))

ws :: Parser ()
ws = blockComment *> ws <|> lineComment *> ws <|> parseIf isSpace *> ws <|> pure ()
  where
    blockComment = string "{-" *> blockRest
    blockRest = string "-}" <|> blockComment *> blockRest <|> char *> blockRest
    lineComment = string "--" *> lineRest
    lineRest = parseIf (== '\n') <|> char *> lineRest

ident :: Parser [Char]
ident =
  (:) <$> parseIf (\x -> x == '_' || isAlpha x)
    <*> many (parseIf (\x -> x == '_' || isAlphaNum x))

number :: Parser Token
number = Number . read <$> some (parseIf isDigit)

symbol :: Parser Token
symbol = do
  kw <- asks keywords
  f kw <$> ident
  where
    f kw s
      | s `elem` kw = Pct s
      | otherwise = Symbol s

punct :: Parser Token
punct = do
  ps <- asks puncts
  Pct <$> asum (string <$> ps)

codepoint :: Int -> Parser Int
codepoint n =
  foldr (\x acc -> 16 * acc + digitToInt x) 0
    <$> replicateM n (parseIf isHexDigit)

charLiteral :: Parser Token
charLiteral = char *> (Number <$> regular) <* (withLoc char >>= quote)
  where
    quote (_, '\'') = pure ()
    quote (span, _) = errAt span "error: expected ' after character literal"

    regular = do
      (span, x) <- withLoc char
      case x of
        '\'' -> errAt span "error: character literals may not be empty"
        '\\' -> do
          (span, x) <- withLoc char
          case x of
            '\\' -> pure $ ord '\\'
            '\'' -> pure $ ord '\''
            'n' -> pure $ ord '\n'
            't' -> pure $ ord '\t'
            'x' -> codepoint 2
            'u' -> codepoint 4
            'U' -> codepoint 8
            _ -> errAt span "invalid escape sequence\n"
        x -> pure $ ord x

stringLiteral :: Parser Token
stringLiteral = char *> (Str <$> elements)
  where
    blockRest x = (:) <$> x <*> elements
    elements = do
      next <- char
      case next of
        '"' -> pure []
        '\\' -> do
          (span, x) <- withLoc char
          case x of
            '\\' -> blockRest $ pure $ ord '\\'
            '"' -> blockRest $ pure $ ord '"'
            'n' -> blockRest $ pure $ ord '\n'
            't' -> blockRest $ pure $ ord '\t'
            'x' -> blockRest $ codepoint 2
            'u' -> blockRest $ codepoint 4
            'U' -> blockRest $ codepoint 8
            _ -> errAt span "invalid escape sequence\n"
        x -> blockRest $ pure $ ord x

-- add col assert
token :: Parser Token
token = ws *> (eof <|> (assertCol *> peek char >>= f))
  where
    f '"' = stringLiteral
    f '\'' = charLiteral
    f _ = number <|> symbol <|> punct <|> badChar

    badChar = withLoc char >>= flip errAt "unexpected character\n" . fst

    assertCol = do
      indent <- asks (head . indentation)
      column <- gets col
      if column >= indent -- must include indent, to accept the first token
        then pure ()
        else do
          (loc, _) <- withLoc char
          errAt loc $ "token is insufficiently indented (" ++ show column ++ ")"

peekToken :: Parser Token
peekToken = do
  c <- get
  t <- local (\env -> env {indentation = 0 : indentation env}) token
  put c
  pure t

expectSymbol :: String -> Parser String
expectSymbol msg = withLoc token >>= f
  where
    f (_, Symbol s) = pure s
    f (loc, e) = expected loc msg (show loc)

expect :: String -> String -> Parser String
expect x msg = withLoc token >>= f
  where
    f (_, Pct y)
      | x == y = pure y
    f (loc, e) = expected loc msg (show loc)

-- parse an indented block of items
-- if the next token is indented further, parse one or more items
-- otherwise, return an empty block
parseBlock :: Parser a -> Parser [a]
parseBlock p = do
  ws
  column <- gets col
  indent <- asks (head . indentation)
  eof <- isEof

  if column <= indent || eof
    then pure []
    else parseItems column p

-- parse one or more items at the current indentation level
parseItems :: Int -> Parser a -> Parser [a]
parseItems column p = do
  item <- local (\env -> env {indentation = column : indentation env}) p
  ws
  column' <- gets col
  eof <- isEof
  if eof
    then pure [item]
    else case compare column column' of
      LT -> do
        (loc, _) <- withLoc char
        errAt loc $ "item is indented too much\nexpected indent: " ++ show column ++ "\nactual indent: " ++ show column'
      EQ -> do
        items <- parseItems column p
        pure (item : items)
      GT -> pure [item]

-- check whether the end of the block is reached
isBlockEnd :: Parser Bool
isBlockEnd = do
  ws
  indent <- asks (head . indentation)
  column <- gets col
  pure (column <= indent) -- must include indent, a token on the indentation level must be a new item