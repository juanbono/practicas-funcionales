{-# LANGUAGE GADTs #-}
module Gadts where

data Binary = Zero | One

data NumberLike a where
  Z :: Int -> NumberLike Int
  R :: Float -> NumberLike Float






