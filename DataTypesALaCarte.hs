{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators         #-}
module DataTypesALaCarte where
{-
The Expression Problem:
  define a data type by cases, where one can add new cases to the data type
  and new functions over the data type, without recompiling existing code,
  and while retaining static type safety
-}

data Expr f = In (f (Expr f))

data Val e = Val Int
type IntExpr = Expr Val

data Add e = Add e e
type AddExpr = Expr Add

{-
The key idea is to combine expressions by taking the coproduct
of their signatures
It is very similar to the Either data type; the only difference
is that it does not combine two base types, but two type constructors
-}

data (f :+: g) e = Inl (f e) | Inr (g e)

-- example
addExample :: Expr (Val :+: Add)
addExample = In (Inr (Add (In (Inl (Val 118))) (In (Inl (Val 1219)))))

-- Evaluation
instance Functor Val where
  fmap _ (Val x) = Val x

instance Functor Add where
  fmap f (Add e1 e2) = Add (f e1) (f e2)

instance (Functor f, Functor g) => Functor (f :+: g) where
  fmap f (Inl e1) = Inl (fmap f e1)
  fmap f (Inr e2) = Inr (fmap f e2)

foldExpr :: Functor f => (f a -> a) -> Expr f -> a
foldExpr f (In t) = f (fmap (foldExpr f) t)

class Functor f => Eval f where
  evalAlgebra :: f Int -> Int

instance Eval Val where
  evalAlgebra (Val x) = x

instance Eval Add where
  evalAlgebra (Add x y) = x + y

instance (Eval f, Eval g) => Eval (f :+: g) where
  evalAlgebra (Inl x) = evalAlgebra x
  evalAlgebra (Inr y) = evalAlgebra y

eval :: Eval f => Expr f -> Int
eval = foldExpr evalAlgebra

-- 4- Automating injections
{-
val :: Int -> Expr Val
val x = In (Val x)

infix 6 <+>
(<+>) :: Expr Add -> Expr Add -> Expr Add
x <+> y = In (Add x y)
-}

class (Functor sub, Functor sup) => sub :<: sup where
  inj :: sub a -> sup a
  prj :: sup a -> Maybe (sub a)

instance {-# OVERLAPPING #-} Functor f => f :<: f where
  inj = id
  prj = Just

instance {-# OVERLAPPING #-} (Functor f, Functor g) => f :<: (f :+: g) where
  inj = Inl
  prj (Inl x) = Just x
  prj (Inr _) = Nothing

instance {-# OVERLAPPING #-} (Functor f, Functor g, Functor h, f :<: g) => f :<: (h :+: g) where
  inj = Inr . inj
  prj (Inl _) = Nothing
  prj (Inr x) = prj x

inject :: (g :<: f) => g (Expr f) -> Expr f
inject = In . inj

val :: (Val :<: f) => Int -> Expr f
val x = inject (Val x)
-- you may want to read the type constraint Add :<: f as
-- 'any signature f that supports addition'
infix 6 <+>
(<+>) :: (Add :<: f) => Expr f -> Expr f -> Expr f
x <+> y = inject (Add x y)

x1 :: Expr (Add :+: Val)
x1 = val 30 <+> val 30

-- 5 - Examples
data Mul x = Mul x x

instance Functor Mul where
  fmap f (Mul x y) = Mul (f x) (f y)

instance Eval Mul where
  evalAlgebra (Mul x y) = x * y

infix 7 <@>
(<@>) :: (Mul :<: f) => Expr f -> Expr f -> Expr f
x <@> y = inject (Mul x y)

x2 :: Expr (Val :+: (Add :+: Mul))
x2 = val 80 <@> val 5 <+> val 4

x3 :: Expr (Val :+: Mul)
x3 = val 6 <@> val 7

class Render f where
  render :: Render g => f (Expr g) -> String

pretty :: Render f => Expr f -> String
pretty (In t) = render t

instance Render Val where
  render (Val i) = show i

instance Render Add where
  render (Add x y) = "(" ++ pretty x ++ " + " ++ pretty y ++ ")"

instance Render Mul where
  render (Mul x y) = "(" ++ pretty x ++ " * " ++ pretty y ++ ")"

instance (Render f, Render g) => Render (f :+: g) where
  render (Inl x) = render x
  render (Inr y) = render y

match :: (g :<: f) => Expr f -> Maybe (g (Expr f))
match (In t) = prj t

distr :: (Add :<: f, Mul :<: f) => Expr f -> Maybe (Expr f)
distr t = do
  Mul a b <- match t
  Add c d <- match b
  return (a <@> c <+> a <@> d)

-- 6- Monads for free

data Term f a =
  Pure a
  | Impure (f (Term f a))

instance Functor f => Functor (Term f) where
  fmap f (Pure x) = Pure (f x)
  fmap f (Impure t) = Impure $ (f <$>) <$> t

instance Applicative f => Applicative (Term f) where
  pure = Pure
  (Pure f) <*> a = f <$> a
  (Impure f) <*> (Pure a) = Impure $ _
--  (Impure f) <*> (Impure x) = Impure (fmap (fmap f) x)
{-
instance Applicative f => Monad (Term f) where
  return = pure
  (Pure x) >>= f = f x
  (Impure t) >>= f = Impure (fmap (>>= f) t)
-}