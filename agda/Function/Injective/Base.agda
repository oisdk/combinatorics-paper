{-# OPTIONS --cubical --safe #-}

module Function.Injective.Base where

open import Level
open import Path
open import Data.Sigma

Injective : (A → B) → Type _
Injective f = ∀ x y → f x ≡ f y → x ≡ y

infixr 0 _↣_
_↣_ : Set a → Set b → Set (a ℓ⊔ b)
A ↣ B = Σ[ f ⦂ (A → B) ] (Injective f)
