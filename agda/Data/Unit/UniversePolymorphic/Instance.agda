{-# OPTIONS --safe --cubical #-}

module Data.Unit.UniversePolymorphic.Instance where

open import Data.Unit.UniversePolymorphic

instance
  poly-unit-inst : ∀ {ℓ} → ⊤ {ℓ}
  poly-unit-inst = tt
