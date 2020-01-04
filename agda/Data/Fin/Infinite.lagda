\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Fin.Infinite where

open import Prelude
open import HITs.InfNat
open import Data.Nat renaming (discreteℕ to _≟_)
open import Relation.Nullary
open import Data.Sigma.Properties
open import Data.Bool.Properties using (isPropT)

private variable n m : ℕ+∞

Fin : ℕ+∞ → Type₀
Fin n = ∃ (_<∞ n)

pattern f0 = zero , tt

fs : Fin n → Fin (suc n)
fs (n , p) = suc n , p

discreteFin : Discrete (Fin n)
discreteFin n m =
  ∣ fst n ≟ fst m
    ∣yes⇒ ΣProp≡ (λ _ → isPropT _)
    ∣no⇒ cong fst
\end{code}
