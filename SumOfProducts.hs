{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
module SumOfProducts where
{-
  TL;DR: Pasar la representacion de cada tipo de datos (Tree y List' en este caso) a una de mas bajo nivel
         en la cual ambas puedan ser representadas (suma de productos). Hacer un tipo de datos para esta
         representacion (TypeRep), hacer funciones para convertir entre una representacion y otra.
         Luego para hacer la funcion generica, hacer una funcion que opere bajo la representacion de bajo nivel,
         Pero tomando como argumento valores en la representacion de alto nivel (Tree y List' por ejemplo).
-}

data List' a = Nil' | Cons' a (List' a)
  deriving Show

data Tree a = Node a (Tree a) (Tree a) | Leaf a
  deriving Show

aList :: List' Int
aList = Cons' 2 (Cons' 3 (Cons' 5 Nil'))

intTree :: Tree Int
intTree = Node 2 (Leaf 3) (Node 5 (Leaf 7) (Leaf 11))

sizeT :: Tree a -> Int
sizeT (Leaf _) = 1
sizeT (Node _ lt rt) = 1 + sizeT lt + sizeT rt

sizeL :: List' a -> Int
sizeL Nil' = 0
sizeL (Cons' _ l) = 1 + sizeL l

-- Sum of products type representation

-- Unit (1)
data U = U deriving Show

-- Sum (a + b)
data Choice a b = L a | R b
  deriving Show

-- Product (a * b)
data Combo a b = Combo a b
  deriving Show

-- 1 + a * (List' a)
type RList a = Choice U (Combo a (List' a))

-- (1 * a) + (a * (Tree a * Tree a))
type RTree a = Choice (Combo U a) (Combo a (Combo (Tree a) (Tree a)))

-- Translating between the type and representation

fromL :: List' a -> RList a
fromL Nil' = L U
fromL (Cons' x xs) = R (Combo x xs)

toL :: RList a -> List' a
toL (L U) = Nil'
toL (R (Combo x xs)) = Cons' x xs

data EP d r = EP {from :: d -> r, to :: r -> d}

-- Writing a datatype-generic function

data TypeRep t where
  RUnit   :: TypeRep U
  RChoice :: TypeRep a -> TypeRep b -> TypeRep (Choice a b)
  RCombo  :: TypeRep a -> TypeRep b -> TypeRep (Combo a b)
  RInt    :: TypeRep Int
  RType   :: EP d r -> TypeRep r -> TypeRep d

rList :: TypeRep a -> TypeRep (List' a)
rList tr = RType (EP fromL toL) (RChoice RUnit (RCombo tr (rList tr)))

gSize :: TypeRep a -> a -> Int
gSize RUnit U = 0
gSize (RChoice trA _) (L a) = gSize trA a
gSize (RChoice _ trB) (R b) = gSize trB b
gSize (RCombo trA trB) (Combo a b) = gSize trA a + gSize trB b
gSize RInt _ = 1
gSize (RType ep tr) t = gSize tr (from ep t)

-- usage : gSize (rList RInt) aList

-- Adding a new datatype

fromT :: Tree a -> RTree a
fromT (Leaf x) = L (Combo U x)
fromT (Node x lt rt) = R (Combo x (Combo lt rt))

toT :: RTree a -> Tree a
toT (L (Combo U  x)) = Leaf x
toT (R (Combo x (Combo lt rt))) = Node x lt rt

rTree :: TypeRep a -> TypeRep (Tree a)
rTree tr = RType (EP fromT toT) (RChoice (RCombo RUnit tr) (RCombo tr (RCombo (rTree tr) (rTree tr))))

-- usage: gSize (rTree RInt) intTree

type ForT t1 t2 = (TypeRep t2 -> TypeRep (t1 t2), TypeRep t2)

forTree :: ForT Tree Int
forTree = (rTree, RInt)

forList :: ForT List' Int
forList = (rList, RInt)

genericSize :: (b -> TypeRep a,b) -> a -> Int
genericSize t = gSize (fst t (snd t))

-- further reading: GHC.Generics library
