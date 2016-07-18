{-# LANGUAGE TypeFamilies #-}
module TypeFamilies where

type family Rep d
type instance Rep Int = Int
