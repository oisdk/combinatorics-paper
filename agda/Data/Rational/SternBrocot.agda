{-# OPTIONS --cubical --safe #-}

module Data.Rational.SternBrocot where

open import Prelude hiding (I)
open import Data.List as List using (List; _∷_; []; foldr)
open import Data.Nat as ℕ using (pred) renaming (_+_ to _ℕ+_)
open import Data.Nat.Order as ℕ using (≡ⁿ⇔≡) renaming (_≡ⁿ_ to _ℕ≡_)
import Data.Nat.Properties as ℕ
open import Path.Reasoning
open import Data.Rational.Frac using (num; den-1; Frac; _÷suc_)

pattern I = true
pattern O = false

ℚ⁺ : Type₀
ℚ⁺ = List Bool

module TerminationHelpers where
  open import Data.Nat

  lift-ℕ≡ : ∀ {x y} z → (x ≡ y) → suc y ℕ≡ z → suc x ℕ≡ z
  lift-ℕ≡ {x} {y} z x≡y sy≡z = ≡ⁿ⇔≡ (suc x) z .inv (cong suc x≡y ; ≡ⁿ⇔≡ (suc y) z .fun sy≡z)

  lemma₁ : ∀ n m → n + m + zero ≡ n + m
  lemma₁ n m = ℕ.+-idʳ (n + m)

  lemma₂ : ∀ a m → a + m + zero ≡ m + a
  lemma₂ a m =
    a + m + zero ≡⟨ ℕ.+-idʳ (a + m) ⟩
    a + m ≡⟨ ℕ.+-comm a m ⟩
    m + a ∎

  lemma₃ : ∀ a n m → n + m + suc a ≡ n + suc m + a
  lemma₃ a n m =
    n + m + suc a ≡⟨ ℕ.+-assoc n m (suc a) ⟩
    n + (m + suc a) ≡⟨ cong (n +_) (ℕ.+-suc m a) ⟩
    n + (suc m + a) ≡˘⟨ ℕ.+-assoc n (suc m) a ⟩
    n + suc m + a ∎

  lemma₄ : ∀ a n → n + a + zero ≡ n + zero + a
  lemma₄ a n =
    n + a + zero ≡⟨ ℕ.+-idʳ (n + a) ⟩
    n + a ≡˘⟨ cong (_+ a) (ℕ.+-idʳ n) ⟩
    n + zero + a ∎

suc_/suc_ : ℕ → ℕ → ℚ⁺
suc_/suc_ = λ n m → GCD.gcd zero n m (suc n ℕ+ m) (≡ⁿ⇔≡ _ _ .inv (lemma₁ n m))
  module GCD where
  open TerminationHelpers

  gcd : (a n m : ℕ) → ∀ s → suc (n ℕ+ m ℕ+ a) ℕ≡ s → ℚ⁺
  gcd a zero    (suc m) (suc s) p = O ∷ gcd zero a m s (lift-ℕ≡ s (lemma₂ a   m) p)
  gcd a (suc n) (suc m) (suc s) p = gcd (suc a)  n m s (lift-ℕ≡ s (lemma₃ a n m) p)
  gcd a (suc n) zero    (suc s) p = I ∷ gcd zero n a s (lift-ℕ≡ s (lemma₄ a n  ) p)
  gcd a zero    zero    (suc s) p = []

-- mul-distrib-/ : ∀ f n d → suc n /suc d ≡ suc (n ℕ.* suc f ℕ.+ f) /suc (d ℕ.* suc f ℕ.+ f)
-- mul-distrib-/ f n d = go f zero n d (suc n ℕ+ d) (≡ⁿ⇔≡ _ _ .inv (lemma₁ n d)) (≡ⁿ⇔≡ _ _ .inv (lemma₁ (n ℕ.* suc f ℕ.+ f) (d ℕ.* suc f ℕ.+ f)))
--   where
--   open GCD
--   open TerminationHelpers
--   open import Data.Bool.Properties using (isPropT)
--   open import Cubical.Foundations.Prelude hiding (I)

--   _∔_ : ℕ → ℕ → ℕ
--   zero ∔ y = y
--   suc x ∔ y = x ∔ suc y

--   ∔≡+ : ∀ n m → n ∔ m ≡ n ℕ.+ m
--   ∔≡+ zero m = refl
--   ∔≡+ (suc n) m = ∔≡+ n (suc m) ; ℕ.+-suc n m

--   gcd-add : ∀ f a n d s p q → gcd (f ∔ a) n d s q ≡ gcd a (f ℕ.+ n) (f ℕ.+ d) (f ℕ.+ s) p
--   gcd-add zero a n d s p q = cong (gcd a n d s) (isPropT _ q p)
--   gcd-add (suc f) a n d (suc s) p = gcd-add f (suc a) n d (suc s) (lift-ℕ≡ (f ℕ.+ suc s) (lemma₃ a (f ℕ+ n) (f ℕ+ d)) p)

--   gcd-eq : ∀ a n s p → [] ≡ gcd a n n s p
--   gcd-eq a zero    (suc s) p = refl
--   gcd-eq a (suc n) (suc s) p = gcd-eq (suc a) n s (lift-ℕ≡ s (lemma₃ a n n) p)

--   go : ∀ f a n d s → ∀ p q → gcd a n d s p ≡ gcd a (n ℕ.* suc f ℕ.+ f) (d ℕ.* suc f ℕ.+ f) (suc (n ℕ.* suc f ℕ.+ f) ℕ+ (d ℕ.* suc f ℕ.+ f)) q
--   go f a zero    zero    (suc s) p q = gcd-eq a f (suc (f ℕ+ f)) q
--   go f a zero    (suc d) (suc s) p q = {!!} -- cong (O ∷_) (go f zero a d s {!!} {!!} ; {!!})
--   go f a (suc n) zero    (suc s) p q = {!!} -- cong (I ∷_) {!!}
--   go f a (suc n) (suc d) (suc s) p q = {!go (suc f) (suc a) n d {!!} {!!} {!!}!}


ℚ : Type₀
ℚ = ℚ⁺

open import Data.List.Relation.Binary
open import Data.Bool.Properties
open import Relation.Nullary

isSetℚ : isSet ℚ
isSetℚ = isOfHLevelList 0 (Discrete→isSet discreteBool)

open import Data.Integer using (+_; -suc; -_)

fromFrac : Frac → ℚ
fromFrac (+ zero ÷suc d-1) = []
fromFrac (+ suc x ÷suc d-1) = I ∷ (suc x /suc d-1)
fromFrac (-suc  x ÷suc d-1) = O ∷ (suc x /suc d-1)

⟦_⇓⟧ : ℚ⁺ → ℕ × ℕ
⟦_⇓⟧ = foldr f (1 , 1)
  where
  f : Bool → ℕ × ℕ → ℕ × ℕ
  f I (n , d) = (n ℕ+ d) , d
  f O (n , d) = n , (n ℕ+ d)

toFrac : ℚ → Frac
toFrac [] = + zero ÷suc zero
toFrac (x ∷ xs) with ⟦ xs ⇓⟧
toFrac (O ∷ xs) | n , d = - n ÷suc pred d
toFrac (I ∷ xs) | n , d = + n ÷suc pred d



