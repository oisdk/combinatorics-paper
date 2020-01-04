{-# OPTIONS --cubical --safe #-}

module Data.List.Sugar where

open import Prelude
open import Data.List
open import Data.List.Syntax

pure : A → List A
pure = [_]

_>>=_ : List A → (A → List B) → List B
_>>=_ = flip concatMap

_>>_ : List A → List B → List B
xs >> ys = xs >>= const ys

_<*>_ : List (A → B) → List A → List B
fs <*> xs = do
  f ← fs
  x ← xs
  [ f x ]

guard : Bool → List ⊤
guard false = []
guard true  = [ tt ]

_⋯_ : ℕ → ℕ → List ℕ
_⋯_ = go 0
  where
  up : ℕ → ℕ → List ℕ
  up a zero    = a ∷ []
  up a (suc m) = a ∷ up (suc a) m

  go : ℕ → ℕ → ℕ → List ℕ
  go a zero    m = up a m
  go a (suc n) zero    = []
  go a (suc n) (suc m) = go (suc a) n m
