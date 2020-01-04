\begin{code}
{-# OPTIONS --safe --cubical #-}

module Data.Binary.OneTerminated where

open import Path.Reasoning
import Data.Nat as ℕ
open import Prelude hiding (I)
open import Data.List using (List; _∷_; []; foldr)
open import Data.Nat.Properties using (+-suc)
open import Data.Bool using (not; _∧_; _∨_)
import Data.Maybe as Maybe

Bit : Type₀
Bit = Bool

pattern O = false
pattern I = true

𝔹⁺ : Type₀
𝔹⁺ = List Bit

𝔹 : Type₀
𝔹 = Maybe 𝔹⁺

inc⁺ : 𝔹⁺ → 𝔹⁺
inc⁺ [] = O ∷ []
inc⁺ (O ∷ xs) = I ∷ xs
inc⁺ (I ∷ xs) = O ∷ inc⁺ xs

inc : 𝔹 → 𝔹
inc = just ∘ maybe inc⁺ []

infixr 5 I∷_
I∷_ : 𝔹 → 𝔹⁺
I∷_ = maybe (I ∷_) []

infixr 5 O∷_
O∷_ : 𝔹 → 𝔹
O∷_ = Maybe.map (O ∷_)

module Decrement where
  dec′ : Bit → 𝔹⁺ → 𝔹⁺
  dec : 𝔹⁺ → 𝔹

  dec′ O  xs = I∷ dec xs
  dec′ I xs = O ∷ xs

  dec [] = nothing
  dec (x ∷ xs) = just (dec′ x xs)
open Decrement public using (dec)

2* : ℕ → ℕ
2* zero = zero
2* (suc n) = suc (suc (2* n))

_∷⇓_ : Bit → ℕ → ℕ
O ∷⇓ xs = 2* xs
I ∷⇓ xs = suc (2* xs)

⟦_⇓⟧⁺ : 𝔹⁺ → ℕ
⟦_⇓⟧⁺ = foldr _∷⇓_ 1

⟦_⇓⟧ : 𝔹 → ℕ
⟦ nothing ⇓⟧ = 0
⟦ just xs ⇓⟧ = ⟦ xs ⇓⟧⁺

⟦_⇑⟧ : ℕ → 𝔹
⟦ zero ⇑⟧ = nothing
⟦ suc n ⇑⟧ = inc ⟦ n ⇑⟧

infixl 6 _⊻_
_⊻_ : Bit → Bit → Bit
O ⊻ y = y
I ⊻ y = not y

sumᵇ : Bit → Bit → Bit → Bit
sumᵇ c x y = c ⊻ x ⊻ y

carryᵇ : Bit → Bit → Bit → Bit
carryᵇ O = _∧_
carryᵇ I = _∨_

add : 𝔹⁺ → 𝔹⁺ → Bit → 𝔹⁺
add [] ys O = inc⁺ ys
add [] [] I = I ∷ []
add [] (y ∷ ys) I = y ∷ inc⁺ ys
add (x ∷ xs) [] O = inc⁺ (x ∷ xs)
add (x ∷ xs) [] I = x ∷ inc⁺ xs
add (x ∷ xs) (y ∷ ys) c = sumᵇ c x y ∷ add xs ys (carryᵇ c x y)

_+_ : 𝔹 → 𝔹 → 𝔹
nothing + ys = ys
(just xs) + nothing = just xs
(just xs) + (just ys) = just (add xs ys O)
\end{code}
