{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Algebra

module Data.Matrix {r} (rng : Semiring r) where

open import Prelude
open import Data.Fin renaming (discreteFin to _≟_)
open import Relation.Nullary
open import Path.Reasoning

open Semiring rng

private
  variable
    n m p : ℕ

Matrix : ℕ → ℕ → Type r
Matrix n m = Fin n → Fin m → 𝑅

zero-m : Matrix n m
zero-m _ _ = 0#

one-m : Matrix n n
one-m i j = if does (i ≟ j) then 1# else 0#

add : Matrix n m → Matrix n m → Matrix n m
add xs ys i j = xs i j + ys i j

sumOver : (Fin n → 𝑅) → 𝑅
sumOver {zero}  f = 0#
sumOver {suc n} f = f f0 + sumOver (f ∘ fs)

mul : Matrix n m → Matrix m p → Matrix n p
mul xs ys i j = sumOver (λ n → xs i n * ys n j)

sumOver-distribˡ : ∀ x → (y : Fin n → 𝑅) → x * sumOver y ≡ sumOver (λ i → x * y i)
sumOver-distribˡ {zero} x y = Semiring.*0 rng x
sumOver-distribˡ {suc n} x y = *⟨+⟩ x (y f0) (sumOver (y ∘ fs)) ; cong (_ +_) (sumOver-distribˡ x (λ z → y (fs z)))

sumOver-distribʳ : ∀ x → (y : Fin n → 𝑅) → sumOver y * x ≡ sumOver (λ i → y i * x)
sumOver-distribʳ {zero} x y = Semiring.0* rng x
sumOver-distribʳ {suc n} x y = ⟨+⟩* (y f0) (sumOver (y ∘ fs)) x ; cong (_ +_) (sumOver-distribʳ x (λ z → y (fs z)))

-- mul-assoc : (xs ys zs : Matrix n n) → ∀ i j → mul (mul xs ys) zs i j ≡ mul xs (mul ys zs) i j
-- mul-assoc {suc n} xs ys zs i j =
--   mul (mul xs ys) zs i j ≡⟨⟩
--   sumOver (λ k → sumOver (λ p → xs i p * ys p k) * zs k j) ≡⟨ {!!} ⟩
--   sumOver (λ k → sumOver (λ p → xs i p * ys p k * zs k j)) ≡⟨ {!!} ⟩
--   sumOver (λ k → xs i k * sumOver (λ p → ys k p * zs p j)) ≡⟨ {!!} ⟩
--   sumOver (λ k → xs i k * sumOver (λ p → ys k p * zs p j)) ≡⟨⟩
--   mul xs (mul ys zs) i j ∎


-- open NearSemiring

-- mat-nearSemiring : ℕ → NearSemiring r
-- mat-nearSemiring n .𝑅 = Matrix n n
-- mat-nearSemiring n ._+_ = add
-- mat-nearSemiring n ._*_ = mul
-- mat-nearSemiring n .1# = one-m
-- mat-nearSemiring n .0# = zero-m
-- mat-nearSemiring n .+-assoc xs ys zs i j k = +-assoc rng (xs j k) (ys j k) (zs j k) i
-- mat-nearSemiring n .*-assoc xs ys zs = funExt λ i → funExt λ j → mul-assoc xs ys zs i j
-- mat-nearSemiring n .0+ = {!!}
-- mat-nearSemiring n .+0 = {!!}
-- mat-nearSemiring n .1* = {!!}
-- mat-nearSemiring n .*1 = {!!}
-- mat-nearSemiring n .0* = {!!}
-- mat-nearSemiring n .⟨+⟩* = {!!}
