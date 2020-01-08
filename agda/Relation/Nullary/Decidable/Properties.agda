{-# OPTIONS --cubical --safe #-}

module Relation.Nullary.Decidable.Properties where

open import Relation.Nullary.Decidable.Base
open import Level
open import Relation.Nullary.Stable.Base
open import Data.Empty

Dec→Stable : ∀ {ℓ} (A : Type ℓ) → Dec A → Stable A
Dec→Stable A (yes x) = λ _ → x
Dec→Stable A (no x) = λ f → ⊥-elim (f x)
