module OrigamiProgramming where
import           Data.Bifunctor

data List' a = Nil' | Cons' a (List' a)

data Tree a = Leaf a | Node a (Tree a) (Tree a)

-- s represents the shape
-- a represents an instance of the type A
data Fix s a = FixT {getFix :: s a (Fix s a)}

-- rewrite Tree and List in terms of Fix, with an implicit recursion

data List_ a r = Nil_ | Cons_ a r
  deriving Show

data Tree_ a r = Leaf_ a | Node_ a r r
  deriving Show

type ListF a = Fix List_ a

type TreeF a = Fix Tree_ a

aList1 :: List_ Integer (List_ a r)
aList1 = Cons_ 12 Nil_

aList2 :: List_ Integer (List_ Integer (List_ a r))
aList2 = Cons_ 12 (Cons_ 13 Nil_)

aListF :: ListF Integer
aListF = FixT (Cons_ 12 (FixT (Cons_ 13 (FixT Nil_))))

mapL :: (a -> b) -> Fix List_ a -> Fix List_ b
mapL f listF = case list_ of
  (Cons_ x r) -> FixT $ Cons_ (f x) (mapL f r)
  Nil_ -> FixT Nil_
  where list_ = getFix listF

showListF :: (Show a) => ListF a -> String
showListF (FixT (Cons_ x r)) = show x ++ ", " ++ showListF r
showListF (FixT Nil_) = "Nil_"

-- usage: showListF $ mapL (*2) aListF

instance Bifunctor List_ where
  bimap _ _ Nil_ = Nil_
  bimap f g (Cons_ x r) = Cons_ (f x) (g r)

instance Bifunctor Tree_ where
  bimap f _ (Leaf_ x) = Leaf_ (f x)
  bimap f g (Node_ x rl rr) = Node_ (f x) (g rl) (g rr)

gmap :: Bifunctor s => (a -> b) -> Fix s a -> Fix s b
gmap f = FixT . bimap f (gmap f) . getFix

-- usage: showListF $ gmap (*2) aListF

-- Generic Fold

gfold :: Bifunctor s => (s a b -> b) -> Fix s a -> b
gfold f = f . bimap id (gfold f) . getFix

addL :: Num a => List_ a a -> a
addL (Cons_ x r) = x + r
addL Nil_  = 0

-- usage: gfold addL aListF
unfoldL :: (t -> Bool) -> (t -> t) -> t -> [t]
unfoldL stopF nextF val = if stopF val
  then []
  else val : unfoldL stopF nextF (nextF val)

gunfold :: Bifunctor s => (b -> s a b) -> b -> Fix s a
gunfold f = FixT . bimap id (gunfold f) . f

toList :: (Eq r, Num r) => r -> List_ r r
toList 0 = Nil_
toList n = Cons_ n (n - 1)

-- usage: showListF $ gunfold toList 10

-- generic fold and unfold
hylo :: Bifunctor p => (a -> b) 
       -> (((a1 -> b1) -> (c1 -> d) -> p a1 c1 -> p b1 d)
       -> (a2 -> a2) -> (a -> c) -> b -> c)
       -> a
       -> c
hylo f g = g bimap id (hylo f g) . f

-- usage: hylo toList addL 100
