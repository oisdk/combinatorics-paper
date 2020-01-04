\begin{code}
{-# OPTIONS --cubical --safe #-}

module HITs.InfNat where

open import Prelude

open import Cubical.HITs.InfNat public
import Data.Nat.WithInf as Concrete
open import Data.Bool using (T)

discreteInfNat : Discrete ℕ+∞
discreteInfNat = subst Discrete (sym (isoToPath ℕ+∞⇔Cℕ+∞)) Concrete.discreteInfNat

isSetInfNat : isSet ℕ+∞
isSetInfNat = Discrete→isSet discreteInfNat

infix 4 _<ᵇ∞_ _<∞_
_<ᵇ∞_ : ℕ → ℕ+∞ → Bool
n     <ᵇ∞ zero = false
n     <ᵇ∞ ∞ = true
zero  <ᵇ∞ suc m = true
suc n <ᵇ∞ suc m = n <ᵇ∞ m
zero  <ᵇ∞ suc-inf i = true
suc n <ᵇ∞ suc-inf i = true

_<∞_ : ℕ → ℕ+∞ → Type₀
n <∞ m = T (n <ᵇ∞ m)

_+_ : ℕ+∞ → ℕ+∞ → ℕ+∞
n + m = ℕ+∞⇔Cℕ+∞ .inv (ℕ+∞⇔Cℕ+∞ .fun n Concrete.+ ℕ+∞⇔Cℕ+∞ .fun m)
\end{code}
