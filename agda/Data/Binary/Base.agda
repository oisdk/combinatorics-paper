{-# OPTIONS --cubical --safe #-}

module Data.Binary.Base where

open import Prelude
import Data.Nat as ℕ

infixr 5 1ᵇ∷_ 2ᵇ∷_
data 𝔹 : Type₀ where
  [] : 𝔹
  1ᵇ∷_ : 𝔹 → 𝔹
  2ᵇ∷_ : 𝔹 → 𝔹

inc : 𝔹 → 𝔹
inc [] = 1ᵇ∷ []
inc (1ᵇ∷ xs) = 2ᵇ∷ xs
inc (2ᵇ∷ xs) = 1ᵇ∷ inc xs

⟦_⇑⟧ : ℕ → 𝔹
⟦ zero  ⇑⟧ = []
⟦ suc n ⇑⟧ = inc ⟦ n ⇑⟧

open import Literals.Number
open import Data.Unit
open import Data.Nat.Literals

instance
  numberBin : Number 𝔹
  Number.Constraint numberBin = λ _ → ⊤
  Number.fromNat numberBin = λ n → ⟦ n ⇑⟧

⟦_⇓⟧ : 𝔹 → ℕ
⟦ [] ⇓⟧ = 0
⟦ 1ᵇ∷ xs ⇓⟧ = 1 ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2
⟦ 2ᵇ∷ xs ⇓⟧ = 2 ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2

add₁ : 𝔹 → 𝔹 → 𝔹
add₂ : 𝔹 → 𝔹 → 𝔹

add₁ [] ys = inc ys
add₁ xs [] = inc xs
add₁ (1ᵇ∷ xs) (1ᵇ∷ ys) = 1ᵇ∷ add₁ xs ys
add₁ (1ᵇ∷ xs) (2ᵇ∷ ys) = 2ᵇ∷ add₁ xs ys
add₁ (2ᵇ∷ xs) (1ᵇ∷ ys) = 2ᵇ∷ add₁ xs ys
add₁ (2ᵇ∷ xs) (2ᵇ∷ ys) = 1ᵇ∷ add₂ xs ys

add₂ [] [] = 2ᵇ∷ []
add₂ [] (1ᵇ∷ ys) = 1ᵇ∷ inc ys
add₂ [] (2ᵇ∷ ys) = 2ᵇ∷ inc ys
add₂ (1ᵇ∷ xs) [] = 1ᵇ∷ inc xs
add₂ (2ᵇ∷ xs) [] = 2ᵇ∷ inc xs
add₂ (1ᵇ∷ xs) (1ᵇ∷ ys) = 2ᵇ∷ add₁ xs ys
add₂ (1ᵇ∷ xs) (2ᵇ∷ ys) = 1ᵇ∷ add₂ xs ys
add₂ (2ᵇ∷ xs) (1ᵇ∷ ys) = 1ᵇ∷ add₂ xs ys
add₂ (2ᵇ∷ xs) (2ᵇ∷ ys) = 2ᵇ∷ add₂ xs ys

infixl 6 _+_
_+_ : 𝔹 → 𝔹 → 𝔹
[] + ys = ys
xs + [] = xs
(1ᵇ∷ xs) + (1ᵇ∷ ys) = 2ᵇ∷ xs + ys
(1ᵇ∷ xs) + (2ᵇ∷ ys) = 1ᵇ∷ add₁ xs ys
(2ᵇ∷ xs) + (1ᵇ∷ ys) = 1ᵇ∷ add₁ xs ys
(2ᵇ∷ xs) + (2ᵇ∷ ys) = 2ᵇ∷ add₁ xs ys

double : 𝔹 → 𝔹
double [] = []
double (1ᵇ∷ xs) = 2ᵇ∷ double xs
double (2ᵇ∷ xs) = 2ᵇ∷ 1ᵇ∷ xs

infixl 7 _*_
_*_ : 𝔹 → 𝔹 → 𝔹
xs * [] = []
xs * (1ᵇ∷ ys) = go xs
  where
  go : 𝔹 → 𝔹
  go [] = []
  go (1ᵇ∷ xs) = 1ᵇ∷ ys + go xs
  go (2ᵇ∷ xs) = 2ᵇ∷ double ys + go xs
xs * (2ᵇ∷ ys) = go xs
  where
  go : 𝔹 → 𝔹
  go [] = []
  go (1ᵇ∷ xs) = 2ᵇ∷ ys + go xs
  go (2ᵇ∷ xs) = 2ᵇ∷ (1ᵇ∷ ys) + go xs

mutual
  dec′ : 𝔹 → 𝔹
  dec′ [] = []
  dec′ (1ᵇ∷ xs) = 2ᵇ∷ dec′ xs
  dec′ (2ᵇ∷ xs) = 2ᵇ∷ 1ᵇ∷ xs

  dec : 𝔹 → 𝔹
  dec [] = []
  dec (2ᵇ∷ xs) = 1ᵇ∷ xs
  dec (1ᵇ∷ xs) = dec′ xs

-- testers : ℕ → ℕ → Type₀
-- testers n m = bins n m ≡ nats n m
--   where
--   open import Data.List
--   open import Data.List.Syntax
--   open import Data.List.Sugar
--   import Agda.Builtin.Nat as Nat

--   upTo : (ℕ → A) → ℕ → List A
--   upTo f zero = []
--   upTo f (suc n) = f zero List.∷ upTo (f ∘ suc) n

--   bins : ℕ → ℕ → List ℕ
--   bins ns ms = do
--     n ← upTo id ns
--     m ← upTo id ms
--     pure ⟦ ⟦ n ⇑⟧ - ⟦ m ⇑⟧ ⇓⟧

--   nats : ℕ → ℕ → List ℕ
--   nats ns ms = do
--     n ← upTo id ns
--     m ← upTo id ms
--     pure (n Nat.- m)

-- ex = ⟦ 4 ⇑⟧

-- -- ex :  ⟦ 5 ⇑⟧ - ⟦ 4 ⇑⟧  ≡ ⟦ 1 ⇑⟧
-- -- ex = refl


-- -- _ : testers 5 5
-- -- _ = refl
