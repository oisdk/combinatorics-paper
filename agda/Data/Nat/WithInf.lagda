\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Nat.WithInf where

open import Cubical.Data.InfNat hiding (discreteInfNat) public

open import Prelude
import Data.Nat as ℕ
open import Relation.Nullary

discreteInfNat : Discrete ℕ+∞
discreteInfNat ∞ ∞ = yes (λ i → ∞)
discreteInfNat ∞ (fin _) = no λ p → subst (caseInfNat ⊥ ⊤) p tt
discreteInfNat (fin _) ∞ = no λ p → subst (caseInfNat ⊤ ⊥) p tt
discreteInfNat (fin n) (fin m) =
  ∣ ℕ.discreteℕ n m
    ∣yes⇒ cong fin
    ∣no⇒ fin-inj n m
\end{code}
