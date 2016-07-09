{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DeriveFunctor         #-}

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

data Term f a = Pure a
              | Impure (f (Term f a))

instance Functor f => Functor (Term f) where
  fmap f (Pure x) = Pure (f x)
  fmap f (Impure t) = Impure $ (f <$>) <$> t

instance Functor f => Applicative (Term f) where
  pure = Pure
  Pure f <*> a = f <$> a
  Impure f <*> a  = Impure $ (<*> a) <$> f

instance Functor f => Monad (Term f) where
  return = pure
  (Pure x) >>= f = f x
  (Impure t) >>= f = Impure (fmap (>>= f) t)

data Zero a -- Term Zero is the Identity Monad
data One a = One -- Term One is the Maybe Monad
data Const e a = Const e -- Term (Const e) is the Error Monad

-- In this specific instance, the Term data type is a higher-order functor
-- that maps a functor f to the monad Term f.
-- Computing the Coproduct of two free monads reduces to computing the
-- Coproduct of their underlying functors.
-- Now we can use the Term data type to represent a language of stateful
-- computations.

-- We will consider simple calculators that are equipped with three buttons for
-- modifying the memory:
-- 1- Recall: The memory can be accessed using the recall button. Pressing the
--    recall button returns the current number stored in memory.
-- 2- Increment: You can add an integer to the number currently stored in the
--    memory using the M+ button. To avoid confusion with the coproduct, we will
--    refer to this button as Incr.
-- 3- Clear: Finally, the memory can be reset to zero using a Clear button.

data Incr t = Incr Int t deriving Functor
data Recall t = Recall (Int -> t) deriving Functor

-- smart constructors
injectTerm :: (g :<: f) => g (Term f a) -> Term f a
injectTerm = Impure . inj

incr :: (Incr :<: f) => Int -> Term f ()
incr i = injectTerm (Incr i (Pure ()))

recall :: (Recall :<: f) => Term f Int
recall = injectTerm (Recall Pure)

-- increments the number stored in memory and returns its previous value
tick :: Term (Recall :+: Incr) Int
tick = do
  y <- recall
  incr 1
  return y

-- In order to write functions over terms, we define the following fold:
foldTerm :: Functor f => (a -> b) -> (f b -> b) -> Term f a -> b
foldTerm p _ (Pure x) = p x
foldTerm p imp (Impure t) = imp (foldTerm p imp <$> t)
-- The first arg (p) is applied to pure values and imp for impure values.

-- Represents the contents of a memory cell.
newtype Mem = Mem Int

class Functor f => Run f where
  runAlgebra :: f (Mem -> (a, Mem)) -> (Mem -> (a, Mem))

instance Run Incr where
  runAlgebra (Incr k r) (Mem i) = r (Mem (i + k))

instance Run Recall where
  runAlgebra (Recall r) (Mem i) = r i (Mem i)

instance (Run f, Run g) => Run (f :+: g) where
  runAlgebra (Inl r) = runAlgebra r
  runAlgebra (Inr r) = runAlgebra r

run :: Run f => Term f a -> Mem -> (a, Mem)
run = foldTerm (,) runAlgebra

-- 7 Applications
-- Consider the following two data types, describing two classes of IO
-- operation from the Haskell Prelude:
data Teletype a
  = GetChar (Char -> a)
  | PutChar Char a
  deriving Functor

data FileSystem a
  = ReadFile FilePath (String -> a)
  | WriteFile FilePath String a
  deriving Functor
-- We define a function exec that takes pure terms to their corresponding
-- impure programs:
exec :: Exec f => Term f a -> IO a
exec = foldTerm return execAlgebra

-- The execAlgebra merely gives the correspondence between our constructors
-- and the Prelude.
class Functor f => Exec f where
  execAlgebra :: f (IO a) -> IO a

instance Exec Teletype where
  execAlgebra (GetChar f) = Prelude.getChar >>= f
  execAlgebra (PutChar c io) = Prelude.putChar c >> io

instance Exec FileSystem where
  execAlgebra (ReadFile filepath f) = Prelude.readFile filepath >>= f
  execAlgebra (WriteFile filepath s io) = Prelude.writeFile filepath s >> io

-- smart constructors
-- TODO
{-
cat :: FilePath -> Term (Teletype :+: FileSystem) ()
cat filepath = do
  contents <- readFile filepath
  mapM putChar contents
  return ()
-}
