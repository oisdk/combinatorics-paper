{-# OPTIONS --safe --without-K #-}

module Data.Lift.Instance where

open import Data.Lift
open import Level

instance
  lift-inst : ∀ {ℓ} ⦃ x : A ⦄ → Lift ℓ A
  lift-inst ⦃ x ⦄ .lower = x
