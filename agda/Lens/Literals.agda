{-# OPTIONS --cubical --safe --postfix-projections #-}

module Lens.Literals where

open import Lens
open import Prelude
open import Literals.Number
open import Data.Vec.Iterated hiding (_[_])
open import Data.Nat.Order
open import Data.Nat.Literals

open import Data.Lift.Instance public
open import Data.Unit.Instance public

instance
  numberLens : ∀ {n} → Number (Lens (Vec A n) A)
  numberLens {n = n} .Number.Constraint m = Lift _ (m < n)
  numberLens .Number.fromNat n ⦃ p ⦄ = ⦅ix⦆ n (p .lower)

private
  xs : Vec ℕ 3
  xs = 1 , 2 , 3 , _

  _ : xs [ 0 ] ≡ 1
  _ = refl

  _ : xs [ 1 ] ≡ 2
  _ = refl

  _ : xs [ 2 ]≔ 30 ≡ (1 , 2 , 30 , _)
  _ = refl
