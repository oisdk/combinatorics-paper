{-# OPTIONS --cubical --safe #-}

module Data.Rational.HIT where

open import Prelude hiding (I)
import Data.Nat as ℕ
import Data.Nat.Properties as ℕ
import Data.Integer as ℤ
open import Data.Integer using (ℤ; +_; -_; -suc)
import Data.Rational.SternBrocot as B
open import Data.Rational.Frac
open import Data.Rational.SternBrocot using (I; O; suc_/suc_)
open import Data.List as List using (_∷_; [])
open import Data.Bool using (bool′)

open import Cubical.HITs.SetQuotients

_≅_ : Frac → Frac → Type₀
(xⁿ ÷suc xᵈ) ≅ (yⁿ ÷suc yᵈ) = xⁿ ℤ.* + suc yᵈ ≡ yⁿ ℤ.* + suc xᵈ

ℚ : Type₀
ℚ = Frac / _≅_

-- toSB-pos : ∀ xⁿ xᵈ yⁿ yᵈ → suc xⁿ ℕ.* suc yᵈ ≡ suc yⁿ ℕ.* suc xᵈ → suc xⁿ /suc xᵈ ≡ suc yⁿ /suc yᵈ
-- toSB-pos xⁿ xᵈ yⁿ yᵈ = {!!}



-- toSB-reduce : ∀ x y → x ≅ y → B.fromFrac x ≡ B.fromFrac y
-- toSB-reduce (-suc  xⁿ ÷suc xᵈ) (+     yⁿ ÷suc yᵈ) p = ⊥-elim (subst (bool′ ⊤ ⊥) (cong ℤ.sign p) tt)
-- toSB-reduce (+     xⁿ ÷suc xᵈ) (-suc  yⁿ ÷suc yᵈ) p = ⊥-elim (subst (bool′ ⊥ ⊤) (cong ℤ.sign p) tt)
-- toSB-reduce (+ zero   ÷suc xᵈ) (+ zero   ÷suc yᵈ) p = refl
-- toSB-reduce (+ zero   ÷suc xᵈ) (+ suc yⁿ ÷suc yᵈ) p = ⊥-elim (ℕ.znots (cong ℤ.offset p))
-- toSB-reduce (+ suc xⁿ ÷suc xᵈ) (+ zero   ÷suc yᵈ) p = ⊥-elim (ℕ.snotz (cong ℤ.offset p))

-- toSB-reduce (+ suc xⁿ ÷suc xᵈ) (+ suc yⁿ ÷suc yᵈ) p = cong (I ∷_) (toSB-pos xⁿ xᵈ yⁿ yᵈ (cong ℤ.offset p))
-- toSB-reduce (-suc  xⁿ ÷suc xᵈ) (-suc  yⁿ ÷suc yᵈ) p = let q = cong ℤ.offset p in cong (O ∷_) (toSB-pos xⁿ xᵈ yⁿ yᵈ {!!})

-- toSB : ℚ → B.ℚ
-- toSB [ xs ] = B.fromFrac xs
-- toSB (eq/ a b r i) = toSB-reduce a b r i
-- toSB (squash/ xs ys x y i j) =
--       isOfHLevel→isOfHLevelDep {n = 2}
--         (λ xs → B.isSetℚ)
--         (toSB xs) (toSB ys)
--         (cong toSB x) (cong toSB y)
--         (squash/ xs ys x y)
--         i j
-- -- toSB ((+ zero) ÷ d-1 +1) = []
-- -- toSB ((+ suc x) ÷ d-1 +1) = I ∷ (x +1/ d-1 +1)
-- -- toSB (ℤ.-suc x ÷ d-1 +1) = O ∷ (x +1/ d-1 +1)
-- -- toSB (reduced nˣ dˣ nʸ dʸ p i) = {!!}



-- -- record ℚ⇘_ {p} (P : ℚ → Type p) : Type p where
-- --   constructor elim
-- --   field
-- --     ⟦_⟧-set : ∀ {xs} → isSet (P xs)
-- --     ⟦_⟧_÷_+1 : ∀ n d-1 → P (n ÷ d-1 +1)
-- --   private f = ⟦_⟧_÷_+1
-- --   field
-- --     ⟦_⟧-red : ∀ nˣ dˣ nʸ dʸ p → f nˣ dˣ ≡[ i ≔ P (reduced nˣ dˣ nʸ dʸ p i) ]≡ f nʸ dʸ
-- --   ⟦_⟧⇓ : ∀ xs → P xs
-- --   ⟦ n ÷ d-1 +1 ⟧⇓ = f n d-1
-- --   ⟦ reduced nˣ dˣ nʸ dʸ p i ⟧⇓ = ⟦_⟧-red nˣ dˣ nʸ dʸ p i
-- --   ⟦ trunc xs ys x y i j ⟧⇓ =
-- -- open ℚ⇘_ public

-- -- infixr 0 ⇘-syntax
-- -- ⇘-syntax = ℚ⇘_
-- -- syntax ⇘-syntax (λ xs → Pxs) = xs ∈ℚ⇒ Pxs

-- -- infixr 0 ℚ↘_
-- -- record ℚ↘_ {a} (A : Type a) : Type a where
-- --   constructor rec
-- --   field
-- --     [_]-set  : isSet A
-- --     [_]_÷_+1 : ℕ → ℕ → A
-- --   field
-- --     [_]-red : ∀ nˣ dˣ nʸ dʸ p → [_]_÷_+1 nˣ dˣ ≡ [_]_÷_+1 nʸ dʸ
-- --   [_]↑ = elim
-- --             [_]-set
-- --             [_]_÷_+1
-- --             [_]-red
-- --   [_]↓ = ⟦ [_]↑ ⟧⇓
-- -- open ℚ↘_ public

-- -- open import Path.Reasoning
-- -- open import Data.Nat.Properties

-- -- -- _ℕ*_ : ℕ → ℚ → ℚ
-- -- -- _ℕ*_ = λ x → [ fn x ]↓
-- -- --   where
-- -- --   fn : ℕ → ℚ↘ ℚ
-- -- --   [ fn x ]-set = trunc
-- -- --   [ fn x ] n ÷ d-1 +1 = 
-- -- --   [ fn x ]-red nˣ dˣ nʸ dʸ p = reduced (x ℕ.* nˣ) dˣ (x ℕ.* nʸ) dʸ $
-- -- --     x ℕ.* nˣ ℕ.* suc dʸ ≡⟨ *-assoc x nˣ (suc dʸ)  ⟩
-- -- --     x ℕ.* (nˣ ℕ.* suc dʸ) ≡⟨ cong (x ℕ.*_)  p ⟩
-- -- --     x ℕ.* (nʸ ℕ.* suc dˣ) ≡˘⟨  *-assoc x nʸ (suc dˣ) ⟩
-- -- --     x ℕ.* nʸ ℕ.* suc dˣ ∎

-- -- _ℕ*_ : ℕ → ℚ → ℚ
-- -- f ℕ* (n ÷ d-1 +1) = (f ℕ.* n) ÷ d-1 +1
-- -- f ℕ* trunc xs ys x y i j =
-- --       isOfHLevel→isOfHLevelDep {n = 2}
-- --         (λ xs → trunc)
-- --         (f ℕ* xs) (f ℕ* ys)
-- --         (cong (f ℕ*_) x) (cong (f ℕ*_) y)
-- --         (trunc xs ys x y)
-- --         i j
-- -- f ℕ* reduced nˣ dˣ nʸ dʸ p i = reduced (f ℕ.* nˣ) dˣ (f ℕ.* nʸ) dʸ (
-- --     f ℕ.* nˣ ℕ.* suc dʸ ≡⟨ *-assoc f nˣ (suc dʸ)  ⟩
-- --     f ℕ.* (nˣ ℕ.* suc dʸ) ≡⟨ cong (f ℕ.*_)  p ⟩
-- --     f ℕ.* (nʸ ℕ.* suc dˣ) ≡˘⟨  *-assoc f nʸ (suc dˣ) ⟩
-- --     f ℕ.* nʸ ℕ.* suc dˣ ∎) i

-- --   -- where
-- --   -- fn : ℕ → ℚ↘ ℚ
-- --   -- [ fn x ]-set = trunc
-- --   -- [ fn x ] n ÷ d-1 +1 = (x ℕ.* n) ÷ d-1 +1
