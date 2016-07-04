module Cata where

type Algebra f a = f a -> a

newtype Mu f = InF { outF :: f (Mu f) }

cata :: Functor f => Algebra f a -> Mu f -> a
cata f = f . fmap (cata f) . outF

{-
Alternative Definition
cata f = hylo f outF
cata f = para (f . fmap fst)
-}

{-
Laws:
cata-cancel ~> cata phi . inF = phi . fmap (cata phi)
cata-refl ~> cata inF = id
cata-fusion ~> f . phi = phi . fmap f => f . cata phi = cata phi
cata-compose ~> eps :: f :~> g => cata phi . cata (In . eps) = cata (phi . eps)
-}

-- Examples
data StrF x = Cons Char x | Nil
type Str = Mu StrF

instance Functor StrF where
  fmap f (Cons a as) = Cons a (f as)
  fmap _ Nil = Nil

-- length of a string
length :: Str -> Int
length = cata phi where
  phi (Cons _ b) = 1 + b
  phi Nil = 0


