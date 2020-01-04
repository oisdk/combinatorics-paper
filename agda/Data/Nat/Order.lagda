\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

module Data.Nat.Order where

open import Prelude
open import Agda.Builtin.Nat using () renaming (_==_ to _≡ᵇ_; _<_ to _<ᵇ_) public
open import Data.Bool
open import Data.Bool.Properties using (T?; isPropT)
open import Data.Nat

infix 4 _≤ᵇ_
_≤ᵇ_ : ℕ → ℕ → Bool
zero  ≤ᵇ m = true
suc n ≤ᵇ m = n <ᵇ m

infix 4 _≡ⁿ_ _≤_ _<_
_≡ⁿ_ _≤_ _<_ : ℕ → ℕ → Type₀
n ≡ⁿ m = T (n ≡ᵇ m)
n ≤  m = T (n ≤ᵇ m)
n <  m = T (n <ᵇ m)

≡ⁿ⇒≡ : ∀ n m → n ≡ⁿ m → n ≡ m
≡ⁿ⇒≡ zero zero p i = zero
≡ⁿ⇒≡ (suc n) (suc m) p i = suc (≡ⁿ⇒≡ n m p i)

≡⇒≡ⁿ : ∀ n m → n ≡ m → n ≡ⁿ m
≡⇒≡ⁿ zero zero n≡m = tt
≡⇒≡ⁿ zero (suc m) n≡m = ⊥-elim (znots n≡m)
≡⇒≡ⁿ (suc n) zero n≡m = ⊥-elim (snotz n≡m)
≡⇒≡ⁿ (suc n) (suc m) n≡m = ≡⇒≡ⁿ n m (cong pred n≡m)

≡ⁿ⇔≡ : ∀ n m → (n ≡ⁿ m) ⇔ (n ≡ m)
≡ⁿ⇔≡ n m .fun = ≡ⁿ⇒≡ n m
≡ⁿ⇔≡ n m .inv = ≡⇒≡ⁿ n m
≡ⁿ⇔≡ n m .rightInv n≡m = isSetℕ n m _ n≡m
≡ⁿ⇔≡ n m .leftInv p = isPropT _ _ p




infix 4 _≡ⁿ?_ _≤?_ _<?_

_≡ⁿ?_ : ∀ n m → Dec (n ≡ⁿ m)
n ≡ⁿ? m = T? (n ≡ᵇ m)

_≤?_ : ∀ n m → Dec (n ≤ m)
n  ≤? m = T? (n ≤ᵇ m)

_<?_ : ∀ n m → Dec (n < m)
n  <? m = T? (n <ᵇ m)

≤⇒<suc : ∀ n m → n ≤ m → n < suc m
≤⇒<suc zero m p = tt
≤⇒<suc (suc n) m p = p

isProp< : ∀ {n m} → isProp (n < m)
isProp< = isPropT _

isProp≤ : ∀ {n m} → isProp (n ≤ m)
isProp≤ = isPropT _
\end{code}
