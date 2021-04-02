module Core where

import Control.Monad.Reader
import Data.Map as M
import Data.Maybe

type Name = String

type QName = [Name]

data Mult
  = Zero
  | One
  | Many
  | MVar Int
  deriving (Eq, Ord)

plus :: Mult -> Mult -> Mult
plus Zero m = m
plus One Zero = One
plus One _ = Many
plus Many _ = Many

times :: Mult -> Mult -> Mult
times Zero _ = Zero
times One m = m
times Many Zero = Zero
times Many _ = Many

multLeq :: Mult -> Mult -> Bool
multLeq Zero _ = True
multLeq _ Many = True
multLeq x y = x == y

splitMult :: Foldable t => t Mult -> Mult
splitMult mults
  | all (== Zero) mults = Zero
  | all (== One) mults = One
  | otherwise = Many

data Plicity
  = Explicit
  | Implicit
  | Class
  | Auto
  deriving (Eq, Ord)

data Reference
  = Ind Int Int -- blockno, defno
  | Def Int Int Int Bool -- blockno, defno, height, decreasing
  | Con Int Int Int Int Bool -- blockno, defno, ctorno, paramno, positive
  deriving (Eq, Ord)

{-
We might just delete the 1 multiplicity
The question remains whether to have subtyping for (0,w)

Pros:
- simpler inference without M-variables => is it without m-vars?
  when calling ensure-function on a metavariable, it may not be clear
  at all what multiplicity will be placed there
Cons:
- having subtyping



-}


{-
Q: put plicity in app?
  => this enables:
    recovering elaborated core files with regular parser
Q: put file location in Core?
  => this means a language server can provide type-info
    for snippets without fully elaborating the definition
    or keeping all info in memory
Q: if we do, is it useful to distinguish Term from Expr?
  => 
-}
{-
extend core with primitives (and FFI)
primitives should have
- totality annotations
- variance annotations
- positivity annotations
  => this will guarantee positivity of array-based rosetrees,
     but not termination of recursion based on those trees.
     This might be encoded using an accessibility predicate,
     but further research is needed
- a type
- compiletime behaviour
- runtime behaviour
- in case of a type, it may need a representation (function)

primitives to implement:
- K
- error
- integers
- switch
- strings
- arrays
- IO

notes:
- It might be useful for primitives to have access to their location, in case of error
- It might be useful for primitives to define their behaviour in Core terms
- primitives should specify an arity so Core can deal with partial applications
- primitives may not have to declare their types if we're going to declare them similarly
  to extern functions
- extern functions will need a (partial) type, calling convention and a name
-}

-- add universe levels to let?
data Term
  = Type
  | Kind
  | DBI  Int
  | Meta Int
  | Top  [String] Reference
  | App  Term Term
  | Pi   Plicity Mult String Term Term
  | Lam  Plicity Mult String Term Term
  | Let  Mult String Term Term Term -- mult, name, level, ty, binder, body
  | Case Mult Term Term [Term] -- mult, scrutinee, motive, branches

data DataBlock = DataBlock
  { uniparamno :: Int,
    dataTotal :: Bool,
    dataDefs :: [Datatype]
  }

data Constructor = Constructor {
  ctorName :: String,
  ctorArity :: Int,
  ctorTy :: Term,
  ctorPositive :: Bool}

-- when it comes to universe checking datatypes,
-- parameters must be smaller or equal to return type,
-- constructors must be smaller
data Datatype = Datatype
  { dataName :: [String],
    arity :: Term,
    paramno :: Int,
    indexno :: Int,
    introRules :: [Constructor]
  }

-- add universe level to blocks?
data FunctionBlock = FunctionBlock
  { funparamno :: Int, -- number of uniform parameters, is maxBound if non-recursive
    decreasing :: Bool,
    funTotal :: Bool,
    funBodies :: [Function]
  }

data Function = Function
  { functionType :: Term,
    functionBody :: Term
  }

data Hypothesis = Hyp
  { hypPlicity :: Plicity,
    hypMult :: Mult,
    hypName :: String,
    hypType :: Term,
    hypDef :: Maybe Term
  }

data Mode = Decidable | Safe | Unsafe

type Context = [Hypothesis]

type Signature = (Map Int DataBlock, Map Int FunctionBlock)

emptySignature :: Signature
emptySignature = (M.empty,M.empty)

type UConstraint = ([Int], [Int]) -- lesses, leqs

data CoreEnv = CoreEnv
  { mode :: Mode,
    context :: Context,
    signature :: Signature
  }

type Core = Reader CoreEnv

getFunction :: Reference -> Core Function
getFunction (Def i j _ _) = do
  block <- asks (snd . signature)
  pure (funBodies (block ! i) !! j)

getData :: Reference -> Core Datatype
getData (Ind i j) = do
  block <- asks (fst . signature)
  pure (dataDefs (block ! i) !! j)

{-
The type of axiom K, abstracting over the parameters of the equality,
as well as Eq, refl, and J applied to those parameters.
This is so we can have the axiom with computational behaviour without
depending on yet to be defined datatypes. K abstracts over Eq and Refl
in order to state it, and abstracts over J in order to prove Eq is
an equality relation. The type can be read as:
"Any relation (Eq) that is reflexive (Refl) and satisfies J also satisfies K"

axiomK :: Term
axiomK =
  Pi Explicit Zero "a" (Sort 0) $
    Pi Explicit Zero "x" (DBI 0) $
      Pi Explicit Zero "Eq" (Pi Explicit Many "" (DBI 1) (Sort 0)) $
        Pi Explicit Zero "Refl" (App (DBI 0) (DBI 1)) $
          Pi
            Explicit
            Zero
            "J"
            ( Pi
                Explicit
                Zero
                "P"
                ( Pi Explicit Many "z" (DBI 3) $
                    Pi Explicit Many "" (App (DBI 1) (DBI 0)) (Sort 0)
                )
                $ Pi Explicit Zero "" (App (App (DBI 0) (DBI 3)) (DBI 1)) $
                  Pi Explicit Zero "y" (DBI 5) $
                    Pi Explicit Zero "e" (App (DBI 4) (DBI 0)) $
                      App (DBI 1) (DBI 0)
            )
            $ Pi Explicit Zero "P" (Pi Explicit Many "" (App (DBI 1) (DBI 2)) (Sort 0)) $
              Pi Explicit One "t" (App (DBI 0) (DBI 2)) $
                Pi Explicit Zero "e" (App (DBI 4) (DBI 5)) $
                  App (DBI 2) (DBI 0)
-}