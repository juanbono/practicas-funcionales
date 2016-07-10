module AlgorithmW where

import qualified Data.Map as Map -- represent contexts (environments) and subs
import qualified Data.Set as Set -- represent sets of type variables.
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import qualified Text.PrettyPrint as PP
import Data.Maybe (fromMaybe)
-- In this paper we develop a complete implementation of the classic algorithm W
-- for Hindley-Milner polymorphic type inference in Haskell.

-- Abstract syntax definition for expressions, types and type schemes.

data Exp = EVar String
         | ELit Lit
         | EApp Exp Exp
         | EAbs String Exp
         | ELet String Exp Exp
         deriving (Eq, Ord)

data Lit = LInt Integer
         | LBool Bool
         deriving (Eq, Ord)

data Type = TVar String
          | TInt
          | TBool
          | TFun Type Type
          deriving (Eq, Ord)

data Scheme = Scheme [String] Type

-- We will need to determine the free type variables of a type.
-- Function ftv implements this operation.
-- Another useful operation is apply a substitution

class Types a where
  ftv   :: a -> Set.Set String
  apply :: Subst -> a -> a

instance Types Type where
  ftv (TVar n) = Set.singleton n
  ftv TInt     = Set.empty
  ftv TBool    = Set.empty
  ftv (TFun t1 t2) = Set.union (ftv t1) (ftv t2)

  apply s (TVar n)     = fromMaybe (TVar n) (Map.lookup n s)
  apply s (TFun t1 t2) = TFun (apply s t1) (apply s t2)
  apply _ t            = t

instance Types Scheme where
  ftv (Scheme vars t) = ftv t Set.\\ Set.fromList vars
  apply s (Scheme vars t) = Scheme vars (apply (foldr Map.delete s vars) t)

instance Types a => Types [a] where
  ftv = foldr (Set.union . ftv) Set.empty
  apply s = map (apply s)

type Subst = Map.Map String Type

nullSubst :: Subst
nullSubst = Map.empty

composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = Map.union (Map.map (apply s1) s2) s1

newtype TypeEnv = TypeEnv (Map.Map String Scheme)

-- The operation remove removes the binding for x from TypeEnv
remove :: TypeEnv -> String -> TypeEnv
remove (TypeEnv env) var = TypeEnv (Map.delete var env)

instance Types TypeEnv where
  ftv (TypeEnv env) = ftv (Map.elems env)
  apply s (TypeEnv env) = TypeEnv (Map.map (apply s) env)

-- abstracts a type over all type variables which are free in the type but
-- not free in the given type environment.
generalize :: TypeEnv -> Type -> Scheme
generalize env t = Scheme vars t
  where vars = Set.toList (ftv t Set.\\ ftv env)

{-
  Several operations, for example type instantiation require fresh names for
  newly introduced type variables. This is implemented by using an appropiated
  monad which takes care of generating fresh names. It is also capable of
  passing a dynamically scoped environment, error handling and performing I/O,
  but will not go into details here.
-}

data TIEnv = TIEnv{}

data TIState = TIState { tiSupply :: Int,
                         tiSubst  :: Subst
                       }

type TI a = ExceptT String (ReaderT TIEnv (StateT TIState IO)) a

runTI :: TI a -> IO (Either String a, TIState)
runTI t = do
  (res, st) <- runStateT (runReaderT (runExceptT t) initTIEnv) initTIState
  return (res, st)
  where initTIEnv = TIEnv{}
        initTIState = TIState { tiSupply = 0, tiSubst = Map.empty}

newTyVar :: String -> TI Type
newTyVar prefix = do
  s <- get
  put s {tiSupply = tiSupply s + 1}
  return (TVar (prefix ++ show (tiSupply s)))

-- The instantiation function replaces all bound type variables in
-- a type scheme with fresh type variables
instantiate :: Scheme -> TI Type
instantiate (Scheme vars t) = do
  nvars <- mapM (\_ -> newTyVar "a") vars
  let s = Map.fromList (zip vars nvars)
  return $ apply s t

-- This is the unification function for types.
-- The function varBind attempts to bind a type variable to a type and return
-- that binding as a substitution, but avoids binding a variable to itself and
-- performs the occurs check.
mgu :: Type -> Type -> TI Subst
mgu (TFun l r) (TFun l' r') = do
  s1 <- mgu l l'
  s2 <- mgu (apply s1 r) (apply s1 r')
  return (s1 `composeSubst` s2)

mgu (TVar u) t  = varBind u t
mgu t (TVar u)  = varBind u t
mgu TInt TInt   = return nullSubst
mgu TBool TBool = return nullSubst
mgu t1 t2       = throwError $ "types do not unify: " ++ show t1 ++ " vs. " ++ show t2

varBind :: String -> Type -> TI Subst
varBind u t | t == TVar u          = return nullSubst
            | u `Set.member` ftv t = throwError $ "occur check fails: " ++ u ++ " vs . " ++ show t
            | otherwise            = return (Map.singleton u t)

-- Pretty-printing functions for the abstract syntax.
instance Show Type where
  showsPrec _ x = shows (prType x)

prType :: Type -> PP.Doc
prType (TVar n) = PP.text n
prType TInt = PP.text "Int"
prType TBool = PP.text "Bool"
prType (TFun t s) = prParenType t PP.<+> PP.text "->" PP.<+> prType s

prParenType :: Type -> PP.Doc
prParenType t = case t of
                     TFun _ _ -> PP.parens (prType t)
                     _        -> prType t

instance Show Exp where
  showsPrec _ x = shows (prExp x)

prExp :: Exp -> PP.Doc
prExp (EVar name) = PP.text name
prExp (ELit lit)  = prLit lit
prExp (ELet x b body) = PP.text "let" PP.<+>
                        PP.text x PP.<+> PP.text "=" PP.<+>
                        prExp b PP.<+> PP.text "in" PP.$$
                        PP.nest 2 (prExp body)
prExp (EApp e1 e2) = prExp e1 PP.<+> prParenExp e2
prExp (EAbs n e) = PP.char '\\' PP.<+> PP.text n PP.<+>
                   PP.text "->" PP.<+>
                   prExp e

prParenExp :: Exp -> PP.Doc
prParenExp t = case t of
                    ELet{} -> PP.parens (prExp t)
                    EApp _ _   -> PP.parens (prExp t)
                    EAbs _ _   -> PP.parens (prExp t)
                    _          -> prExp t

instance Show Lit where
  showsPrec _ x = shows (prLit x)

prLit :: Lit -> PP.Doc
prLit (LInt i) = PP.integer i
prLit (LBool b) = if b then PP.text "True" else PP.text "False"

instance Show Scheme where
  showsPrec _ x = shows (prScheme x)

prScheme :: Scheme -> PP.Doc
prScheme (Scheme vars t) = PP.text "All" PP.<+>
                           PP.hcat
                             (PP.punctuate PP.comma (map PP.text vars))
                           PP.<> PP.text "." PP.<+> prType t
