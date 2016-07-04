{-# LANGUAGE GADTs #-}
module Arith where

data Term where
  TmTrue       :: Term
  TmFalse      :: Term
  TmZero       :: Term
  TmSucc       :: Term -> Term
  TmPred       :: Term -> Term
  TmIsZero     :: Term -> Term
  TmIfThenElse :: Term -> Term -> Term -> Term

instance Show Term where
  show TmTrue  = "true"
  show TmFalse = "false"
  show TmZero  = "zero"
  show (TmSucc t) = "succ (" ++ show t ++ ")"
  show (TmPred t) = "pred (" ++ show t ++ ")"
  show (TmIsZero t) = "isZero (" ++ show t ++ ")"
  show (TmIfThenElse t1 t2 t3) = ifPart ++ thenPart ++ elsePart
    where
      ifPart = "if (" ++ show t1 ++ ")"
      thenPart = " then (" ++ show t2 ++ ")"
      elsePart = " else (" ++ show t3 ++ ")"

