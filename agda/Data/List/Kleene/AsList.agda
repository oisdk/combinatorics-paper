{-# OPTIONS --cubical --safe #-}

module Data.List.Kleene.AsList where

open import Data.List.Kleene
  using ([])
  renaming (_⋆ to List; foldr⋆ to foldr)
  public

infixr 5 _∷_
pattern _∷_ x xs = Data.List.Kleene.∹ (x Data.List.Kleene.& xs)
