{-# OPTIONS --cubical --safe #-}

module Data.Rational where

open import Prelude
import Data.Nat as ℕ

data ℚ⁺ : Type₀ where
  _÷_+1 : (n d-1 : ℕ) → ℚ⁺
  reduced : ∀ xⁿ xᵈ yⁿ yᵈ → (xⁿ ℕ.* suc yᵈ) ≡ (yⁿ ℕ.* suc xᵈ) → xⁿ ÷ xᵈ +1 ≡ yⁿ ÷ yᵈ +1
  trunc : isSet ℚ⁺

record ℚ⇘_ {p} (P : ℚ⁺ → Type p) : Type p where
  constructor elim
  field
    ⟦_⟧-set : ∀ {xs} → isSet (P xs)
    ⟦_⟧_÷_+1 : ∀ n d-1 → P (n ÷ d-1 +1)
  private f = ⟦_⟧_÷_+1
  field
    ⟦_⟧-red : ∀ xⁿ xᵈ yⁿ yᵈ p → f xⁿ xᵈ ≡[ i ≔ P (reduced xⁿ xᵈ yⁿ yᵈ p i) ]≡ f yⁿ yᵈ
  ⟦_⟧⇓ : ∀ xs → P xs
  ⟦ n ÷ d-1 +1 ⟧⇓ = f n d-1
  ⟦ reduced xⁿ xᵈ yⁿ yᵈ p i ⟧⇓ = ⟦_⟧-red xⁿ xᵈ yⁿ yᵈ p i
  ⟦ trunc xs ys x y i j ⟧⇓ =
      isOfHLevel→isOfHLevelDep {n = 2}
        (λ xs → ⟦_⟧-set {xs})
        ⟦ xs ⟧⇓ ⟦ ys ⟧⇓
        (cong ⟦_⟧⇓ x) (cong ⟦_⟧⇓ y)
        (trunc xs ys x y)
        i j
open ℚ⇘_ public

infixr 0 ⇘-syntax
⇘-syntax = ℚ⇘_
syntax ⇘-syntax (λ xs → Pxs) = xs ∈ℚ⁺⇒ Pxs

infixr 0 ℚ↘_
record ℚ↘_ {a} (A : Type a) : Type a where
  constructor rec
  field
    [_]-set  : isSet A
    [_]_÷_+1 : ℕ → ℕ → A
  field
    [_]-red : ∀ xⁿ xᵈ yⁿ yᵈ p → [_]_÷_+1 xⁿ xᵈ ≡ [_]_÷_+1 yⁿ yᵈ
  [_]↑ = elim
            [_]-set
            [_]_÷_+1
            [_]-red
  [_]↓ = ⟦ [_]↑ ⟧⇓
open ℚ↘_ public

open import Path.Reasoning
open import Data.Nat.Properties

-- _ℕ*_ : ℕ → ℚ⁺ → ℚ⁺
-- _ℕ*_ = λ x → [ fn x ]↓
--   where
--   fn : ℕ → ℚ↘ ℚ⁺
--   [ fn x ]-set = trunc
--   [ fn x ] n ÷ d-1 +1 = 
--   [ fn x ]-red xⁿ xᵈ yⁿ yᵈ p = reduced (x ℕ.* xⁿ) xᵈ (x ℕ.* yⁿ) yᵈ $
--     x ℕ.* xⁿ ℕ.* suc yᵈ ≡⟨ *-assoc x xⁿ (suc yᵈ)  ⟩
--     x ℕ.* (xⁿ ℕ.* suc yᵈ) ≡⟨ cong (x ℕ.*_)  p ⟩
--     x ℕ.* (yⁿ ℕ.* suc xᵈ) ≡˘⟨  *-assoc x yⁿ (suc xᵈ) ⟩
--     x ℕ.* yⁿ ℕ.* suc xᵈ ∎

_ℕ*_ : ℕ → ℚ⁺ → ℚ⁺
f ℕ* (n ÷ d-1 +1) = (f ℕ.* n) ÷ d-1 +1
f ℕ* trunc xs ys x y i j =
      isOfHLevel→isOfHLevelDep {n = 2}
        (λ xs → trunc)
        (f ℕ* xs) (f ℕ* ys)
        (cong (f ℕ*_) x) (cong (f ℕ*_) y)
        (trunc xs ys x y)
        i j
f ℕ* reduced xⁿ xᵈ yⁿ yᵈ p i = reduced (f ℕ.* xⁿ) xᵈ (f ℕ.* yⁿ) yᵈ (
    f ℕ.* xⁿ ℕ.* suc yᵈ ≡⟨ *-assoc f xⁿ (suc yᵈ)  ⟩
    f ℕ.* (xⁿ ℕ.* suc yᵈ) ≡⟨ cong (f ℕ.*_)  p ⟩
    f ℕ.* (yⁿ ℕ.* suc xᵈ) ≡˘⟨  *-assoc f yⁿ (suc xᵈ) ⟩
    f ℕ.* yⁿ ℕ.* suc xᵈ ∎) i

  -- where
  -- fn : ℕ → ℚ↘ ℚ⁺
  -- [ fn x ]-set = trunc
  -- [ fn x ] n ÷ d-1 +1 = (x ℕ.* n) ÷ d-1 +1
