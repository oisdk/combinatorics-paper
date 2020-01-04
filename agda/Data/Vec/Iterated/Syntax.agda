{-# OPTIONS --cubical --safe #-}

module Data.Vec.Iterated.Syntax where

open import Data.Vec.Iterated
open import Prelude

record VecSyntax {a b} (A : Type a) (B : Type b) (n : ℕ) : Type (a ℓ⊔ b) where
  field [_] : B → Vec A n

open VecSyntax ⦃ ... ⦄ public

instance
  cons : ∀ {n} → ⦃ _ : VecSyntax A B n ⦄ →  VecSyntax A (A × B) (suc n)
  [_] ⦃ cons ⦄ (x , xs) = x , [ xs ]

instance
  sing : VecSyntax A A 1
  [_] ⦃ sing ⦄ = _, _
