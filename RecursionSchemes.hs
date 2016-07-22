{-# LANGUAGE DeriveFunctor #-}
module RecursionSchemes where

import Control.Arrow
import Text.PrettyPrint (Doc, (<>))
import qualified Text.PrettyPrint as P

data Lit
  = StrLit String
  | IntLit Int
  | IdentLit String
  deriving (Show, Eq)

data Expr a
  = Index   { target :: a, idx :: a }
  | Call    { func :: a, args :: [a] }
  | Unary   { op :: String, target :: a }
  | Binary  { lhs :: a, op :: String, rhs :: a }
  | Paren   { paren :: a }
  | Literal { intVal :: Int }
  | Ident   { name :: String }
  deriving (Show, Eq, Functor)

{-
data Stmt
  = Break
  | Continue
  | Empty
  | IfElse Expr [Stmt] [Stmt]
  | Return (Maybe Expr)
  | While Expr [Stmt]
  | Expression Expr
  deriving (Show, eq)
-}

newtype Term f = In { out :: f (Term f) }

bottomUp :: Functor a => (Term a -> Term a) -> Term a -> Term a
bottomUp f =
  out                    -- 1) unpack a `Term a` into an `a (Term a)`
  >>> fmap (bottomUp f)  -- 2) recurse, with f, into the subterms
  >>> In                 -- 3) repack the `a (Term a)` into a `Term a`
  >>> f                  -- 4) apply f to the packed `Term a`

flattenTerm :: Term Expr -> Term Expr
flattenTerm (In (Paren e)) = e -- remove all Parens
flattenTerm other = other      -- do nothing otherwise

flatten :: Term Expr -> Term Expr
flatten = bottomUp flattenTerm

topDown :: Functor f => (Term f -> Term f) -> Term f -> Term f
topDown f =
  f                    -- 1) apply
  >>> out              -- 2) unpack
  >>> fmap (topDown f) -- 3) recurse
  >>> In               -- 4) repack
-- mira lo que esta esa dualidad papaaaa

ten :: Term Expr
ten = In Literal { intVal = 10 }

add :: Term Expr
add = In Ident { name = "add" }

call :: Term Expr
call = In Call { func = add, args = [ten, ten]} -- add(10,10)

mystery :: Functor f => Algebra f a -> Term f -> a
mystery fn =
  out                   -- 1) unpack the Term
  >>> fmap (mystery fn) -- 2) recursively apply `fn`
  >>> fn                -- 3) apply `fn`

countNodes :: Algebra Expr Int
countNodes (Unary _ arg)    = arg + 1
countNodes (Binary l _ r)   = l + r + 1
countNodes (Call fn args')   = fn + sum args' + 1
countNodes (Index it index) = it + index + 1
countNodes (Paren arg)      = arg + 1
countNodes (Literal _)      = 1
countNodes (Ident _)        = 1

type Algebra f a = f a -> a

-- the mystery function is known as a catamorphism
-- A catamorphism uses an algebra to collapse a container
-- of values into a single value (just like fold)
-- catamorphisms are generalized folds applicable to any functor
cata :: Functor f => Algebra f a -> Term f -> a
cata f = out >>> fmap (cata f) >>> f

prettyPrint :: Algebra Expr Doc
prettyPrint (Literal i) = P.int i
prettyPrint (Ident s) = P.text s
prettyPrint (Call f as) = f <> (P.parens . P.cat) (P.punctuate (P.text ",") as)
prettyPrint (Index it index) = it <> P.brackets index
prettyPrint (Unary op' it) = P.text op' <> it
prettyPrint (Binary l op' r) = l <> P.text op' <> r
prettyPrint (Paren exp') = P.parens exp'

bottomUpCata :: Functor f => (Term f -> Term f) -> Term f -> Term f
bottomUpCata f = cata (In >>> f)

{-
dualidad entre los traversals
bottomUp f = out >>> fmap (bottomUp f) >>> In  >>> f
topDown  f = In  <<< fmap (topDown  f) <<< out <<< f
-}

type Coalgebra f a = a -> f a

ana :: Functor f => Coalgebra f a -> a -> Term f
ana f = In <<< fmap (ana f) <<< f

{-
If we thought about algebras as reunions,
we can think about coalgebras as disassembly or dispersion
-}
topDownAna :: Functor f => (Term f -> Term f) -> Term f -> Term f
topDownAna f = ana (out <<< f)


type RAlgebra f a = f (Term f, a) -> a

{-
 A paramorphism is like a catamorphism except that it
 can view the original structure beside the structure that is being transformed.
-}
 -- fijarse mejor esto
type RAlgebra' f a = Term f -> f a -> a
para' :: Functor f => RAlgebra' f a -> Term f -> a
para' f = out >>> fmap (id &&& para' f) >>> f
