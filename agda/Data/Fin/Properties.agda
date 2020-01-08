{-# OPTIONS --cubical --safe #-}

module Data.Fin.Properties where

open import Prelude
open import Data.Fin.Base
import Data.Nat.Properties as ℕ

private
  variable
    n m : ℕ

FinToℕ : Fin n → ℕ
FinToℕ {n = suc n} f0     = zero
FinToℕ {n = suc n} (fs x)  = suc (FinToℕ x)

FinToℕ-injective : ∀ {k} {m n : Fin k} → FinToℕ m ≡ FinToℕ n → m ≡ n
FinToℕ-injective {suc k} {f0}  {f0}  _ = refl
FinToℕ-injective {suc k} {f0}  {fs x} p = ⊥-elim (ℕ.znots p)
FinToℕ-injective {suc k} {fs m} {f0}  p = ⊥-elim (ℕ.snotz p)
FinToℕ-injective {suc k} {fs m} {fs x} p = cong fs (FinToℕ-injective (ℕ.injSuc p))

pred : Fin (suc n) → Fin (suc (ℕ.pred n))
pred f0 = f0
pred {n = suc n} (fs m) = m

discreteFin : ∀ {k} → Discrete (Fin k)
discreteFin {k = suc _} f0 f0 = yes refl
discreteFin {k = suc _} f0 (fs fk) = no (ℕ.znots ∘ cong FinToℕ)
discreteFin {k = suc _} (fs fj) f0 = no (ℕ.snotz ∘ cong FinToℕ)
discreteFin {k = suc _} (fs fj) (fs fk) =
  ⟦yes cong fs ,no cong (λ { f0 → fk ; (fs x) → x}) ⟧ (discreteFin fj fk)

isSetFin : isSet (Fin n)
isSetFin = Discrete→isSet discreteFin

infix 4 _≢ᶠ_ _≡ᶠ_
_≢ᶠ_ _≡ᶠ_ : Fin n → Fin n → Type _
n ≢ᶠ m = T (not (discreteFin n m .does))
n ≡ᶠ m = T (discreteFin n m .does)
