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

by1 : ℕ → 𝔹 → 𝔹
by1 zero    xs = xs
by1 (suc n) xs = 1ᵇ∷ by1 n xs

doublen : ℕ → 𝔹 → 𝔹
doublen _ [] = []
doublen n (1ᵇ∷ xs) = 2ᵇ∷ by1 n (double xs)
doublen n (2ᵇ∷ xs) = 2ᵇ∷ 1ᵇ∷ by1 n xs


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

open import Data.Maybe


sub  : 𝔹 → 𝔹 → Maybe 𝔹
sub′ : ℕ → 𝔹 → 𝔹 → Maybe 𝔹

sub′ n [] [] = just []
sub′ n [] ys = nothing
sub′ n xs [] = just (doublen n xs)
sub′ n (1ᵇ∷ xs) (1ᵇ∷ ys) = sub′ (suc n) xs ys
sub′ n (2ᵇ∷ xs) (2ᵇ∷ ys) = sub′ (suc n) xs ys
sub′ n (2ᵇ∷ xs) (1ᵇ∷ ys) with sub′ zero xs ys
... | nothing = nothing
... | just zs = just (2ᵇ∷ by1 n zs)
sub′ n (1ᵇ∷ xs) (2ᵇ∷ ys) with sub′ zero xs ys
... | nothing = nothing
... | just (2ᵇ∷ zs) = just (2ᵇ∷ by1 n (double zs))
... | just _ = nothing

sub [] [] = just []
sub [] ys = nothing
sub xs [] = just xs
sub (1ᵇ∷ xs) (1ᵇ∷ ys) = sub′ zero xs ys
sub (2ᵇ∷ xs) (2ᵇ∷ ys) = sub′ zero xs ys
sub (2ᵇ∷ xs) (1ᵇ∷ ys) with sub xs ys
... | nothing = nothing
... | just zs = just (1ᵇ∷ zs)
sub (1ᵇ∷ xs) (2ᵇ∷ ys) with sub xs ys
... | nothing = nothing
... | just [] = nothing
... | just zs = just (dec (double zs))

_-_ : 𝔹 → 𝔹 → 𝔹
xs - ys = maybe [] id (sub xs ys)

-- testers : ℕ → Type₀
-- testers n = bins n n ≡ nats n n
--   where
--   open import Data.List
--   open import Data.List.Syntax
--   open import Data.List.Sugar
--   import Agda.Builtin.Nat as Nat

--   upTo : (ℕ → A) → ℕ → List A
--   upTo f zero = []
--   upTo f (suc n) = f zero List.∷ upTo (f ∘ suc) n

--   bins : ℕ → ℕ → List 𝔹
--   bins ns ms = do
--     n ← upTo id ns
--     m ← upTo id ms
--     pure (⟦ n ⇑⟧ - ⟦ m ⇑⟧)

--   nats : ℕ → ℕ → List 𝔹
--   nats ns ms = do
--     n ← upTo id ns
--     m ← upTo id ms
--     pure ⟦ n Nat.- m ⇑⟧

-- _ : testers 30
-- _ = refl
