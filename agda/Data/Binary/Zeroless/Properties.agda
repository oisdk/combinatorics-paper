{-# OPTIONS --cubical --safe #-}

module Data.Binary.Zeroless.Properties where

open import Prelude hiding (Bool; true; false)
open import Data.Binary.Zeroless
import Data.Nat as ℕ
import Data.Nat.Properties as ℕ-Prop
open import Data.List as List using (List; _∷_; [])




-- +-homo : ∀ x y → ⟦ x + y ⇓⟧ ≡ ⟦ x ⇓⟧ ℕ.+ ⟦ y ⇓⟧
-- +-homo [] ys = refl
-- +-homo (x ∷ xs) [] = sym (ℕ-Prop.+-idʳ _)
-- +-homo (1ᵇ ∷ xs) (1ᵇ ∷ ys) = cong suc {!!}
-- +-homo (1ᵇ ∷ xs) (2ᵇ ∷ ys) = {!!}
-- +-homo (2ᵇ ∷ xs) (1ᵇ ∷ ys) = {!!}
-- +-homo (2ᵇ ∷ xs) (2ᵇ ∷ ys) = {!!}
