\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Fin where

open import Prelude
import Data.Nat as ℕ
import Data.Nat.Order as ℕ
open import Data.Bool using (T; not)
open import Relation.Nullary

private
  variable
    n m : ℕ

module Inductive where
\end{code}
%<*def>
\begin{code}
 Fin : ℕ → Type₀
 Fin zero     = ⊥
 Fin (suc n)  = ⊤ ⊎ Fin n
\end{code}
%</def>
\begin{code}
Fin : ℕ → Type₀
Fin zero = ⊥
Fin (suc n) = Maybe (Fin n)

pattern f0 = nothing
pattern fs n = just n

pattern f1 = fs f0
pattern f2 = fs f1
pattern f3 = fs f2
pattern f4 = fs f3
pattern f5 = fs f4
pattern f6 = fs f5
pattern f7 = fs f6
pattern f8 = fs f7
pattern f9 = fs f8


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

ℕToFin : ∀ m {n} → (m ℕ.< n) → Fin n
ℕToFin zero    {suc n} m<n = f0
ℕToFin (suc m) {suc n} m<n = fs (ℕToFin m m<n)

infix 4 _≢ᶠ_ _≡ᶠ_
_≢ᶠ_ _≡ᶠ_ : Fin n → Fin n → Type _
n ≢ᶠ m = T (not (discreteFin n m .does))
n ≡ᶠ m = T (discreteFin n m .does)
\end{code}
