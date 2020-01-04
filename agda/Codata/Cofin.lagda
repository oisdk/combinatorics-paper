\begin{code}
{-# OPTIONS --cubical --safe --sized-types #-}

module Codata.Cofin where

open import Codata.Conat
open import Codata.Thunk
open import Codata.Size
open import Prelude
import Data.Nat as ℕ
open import Data.Fin
\end{code}
%<*def>
\begin{code}
data Cofin : Conat ∞ → Type₀ where
  zero : ∀ {n} → Cofin (suc n)
  suc  : ∀ {n} → Cofin (n .force) → Cofin (suc n)
\end{code}
%</def>
\begin{code}
ℕToCofin : ∀ m {n} → (m ℕ< n) → Cofin n
ℕToCofin zero    {suc n} m<n = zero
ℕToCofin (suc m) {suc n} m<n = suc (ℕToCofin m (p≤p m<n))

CofinToℕ : ∀ {n} → Cofin n → ℕ
CofinToℕ {suc x₁} zero = zero
CofinToℕ {suc x₁} (suc x) = suc (CofinToℕ x)

ℕToCofin∞ : ℕ → Cofin inf
ℕToCofin∞ zero = zero
ℕToCofin∞ (suc n) = suc (ℕToCofin∞ n)

Cofin→ℕ→Cofin : ∀ x → ℕToCofin∞ (CofinToℕ x) ≡ x
Cofin→ℕ→Cofin zero = refl
Cofin→ℕ→Cofin (suc x) i = suc (Cofin→ℕ→Cofin x i)

ℕ→Cofin→ℕ : ∀ x → CofinToℕ (ℕToCofin∞ x) ≡ x
ℕ→Cofin→ℕ zero = refl
ℕ→Cofin→ℕ (suc x) i = suc (ℕ→Cofin→ℕ x i)
\end{code}
%<*cofin-nat>
\begin{code}
Cofin∞⇔ℕ : Cofin inf ⇔ ℕ
\end{code}
%</cofin-nat>
\begin{code}
Cofin∞⇔ℕ .fun = CofinToℕ
Cofin∞⇔ℕ .inv = ℕToCofin∞
Cofin∞⇔ℕ .leftInv  = Cofin→ℕ→Cofin
Cofin∞⇔ℕ .rightInv = ℕ→Cofin→ℕ

cofinToFin : ∀ {n m} → (n ℕ≋ m) → Cofin m → Fin n
cofinToFin {suc n} {suc m} n≋m zero = f0
cofinToFin {suc n} {suc m} n≋m (suc x) = fs (cofinToFin n≋m x)

finToCofin : ∀ {n m} → (n ℕ≋ m) → Fin n → Cofin m
finToCofin {suc n} {suc m} n≋m f0 = zero
finToCofin {suc n} {suc m} n≋m (fs x) = suc (finToCofin n≋m x)

leftInv′ : ∀ {n m} → (n≋m : n ℕ≋ m) → (x : Fin n) → cofinToFin n≋m (finToCofin n≋m x) ≡ x
leftInv′ {suc n} {suc m} n≋m f0 = refl
leftInv′ {suc n} {suc m} n≋m (fs x) i = fs (leftInv′ n≋m x i)

rightInv′ : ∀ {n} {m : Conat ∞} → (n≋m : n ℕ≋ m) → (x : Cofin m) → finToCofin {n} {m} n≋m (cofinToFin {n} {m} n≋m x) ≡ x
rightInv′ {suc n} {suc m} n≋m zero = refl
rightInv′ {suc n} {suc m} n≋m (suc x) i = suc (rightInv′ {n} {m .force} n≋m x i)
\end{code}
%<*cofin-fin>
\begin{code}
Fin⇔Cofin : ∀ {n m} → n ℕ≋ m → Fin n ⇔ Cofin m
\end{code}
%</cofin-fin>
\begin{code}
Fin⇔Cofin n≋m .fun      = finToCofin n≋m
Fin⇔Cofin n≋m .inv      = cofinToFin n≋m
Fin⇔Cofin n≋m .leftInv  = leftInv′ n≋m
Fin⇔Cofin n≋m .rightInv = rightInv′ n≋m

CofinToℕ-injective : ∀ {k} {m n : Cofin k} → CofinToℕ m ≡ CofinToℕ n → m ≡ n
CofinToℕ-injective {suc k} {zero}  {zero}  _ = refl
CofinToℕ-injective {suc k} {zero}  {suc x} p = ⊥-elim (ℕ.znots p)
CofinToℕ-injective {suc k} {suc m} {zero}  p = ⊥-elim (ℕ.snotz p)
CofinToℕ-injective {suc k} {suc m} {suc x} p = cong suc (CofinToℕ-injective (ℕ.injSuc p))

discreteCofin : ∀ {k} → Discrete (Cofin k)
discreteCofin fj fk with ℕ.discreteℕ (CofinToℕ fj) (CofinToℕ fk)
... | yes p = yes (CofinToℕ-injective p)
... | no ¬p = no (¬p ∘ cong CofinToℕ)
\end{code}
