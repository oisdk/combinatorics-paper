{-# OPTIONS --cubical --safe #-}

open import Algebra

module Algebra.SemiringLiterals {ℓ} (srng : NearSemiring ℓ) where

open import Prelude
open import Literals.Number public
import Data.Unit.UniversePolymorphic as Poly
open import Data.Unit.UniversePolymorphic.Instance public

open NearSemiring srng

CarrierFromNat : ℕ → 𝑅
CarrierFromNat zero = 0#
CarrierFromNat (suc zero) = 1#
CarrierFromNat (suc n@(suc _)) = 1# + CarrierFromNat n


instance
  numberCarrier : Number 𝑅
  Number.Constraint numberCarrier _ = Poly.⊤
  Number.fromNat numberCarrier n = CarrierFromNat n
