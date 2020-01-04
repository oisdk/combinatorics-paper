\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Container.Array where

open import Data.Binary
open import Data.Container
open import Prelude hiding (I)
open import Data.Bool using (Bool; true; false; T; bool′)
open import Data.Vec renaming (_∷_ to _V∷_)
open import Data.List.Kleene.AsList
open import Data.List.Kleene

-- infix 4 _<ᵇ_
-- _<ᵇ_ : 𝔹⁺ → 𝔹⁺ → Type₀
-- I∷[] <ᵇ I∷[] = ⊤
-- I∷[] <ᵇ (O ∷ ys) = ⊥
-- I∷[] <ᵇ (I ∷ ys) = ⊤
-- (x ∷ xs) <ᵇ I∷[] = ⊥
-- (x ∷ xs) <ᵇ (_ ∷ ys) = xs <ᵇ ys

-- Fin𝔹⁺ : 𝔹⁺ → Type₀
-- Fin𝔹⁺ xs = ∃[ ys ] (ys <ᵇ xs)

-- Fin𝔹 : 𝔹 → Type₀
-- Fin𝔹 0𝕓 = ⊥
-- Fin𝔹 (0< xs) = Fin𝔹⁺ xs

-- Array : Container _ _
-- Array = 𝔹 ▷ Fin𝔹

-- Array⁺ : Container _ _
-- Array⁺ = 𝔹⁺ ▷ Fin𝔹⁺

-- module Indexed where
--   cons′ : A → ∀ ns → (∀ is → ⦃ _ : is <ᵇ ns ⦄ → A) → ∀ ms → ⦃ _ : ms <ᵇ ∹ Inc.inc″ ns ⦄ → A
--   cons′ x I∷[] f (i ∷ is) = bool′ x (f is) i
--   cons′ x (O ∷ ns) xs I∷[] = x
--   cons′ x (O ∷ ns) xs (i ∷ is) = xs (i ∷ is)
--   cons′ x (I ∷ ns) xs (i ∷ is) = cons′ (bool′ x (xs I∷[])) ns (λ is i → xs (i ∷ is)) is i

--   cons : A → ∀ ns → (Fin𝔹 ns → A) → Fin𝔹 (inc ns) → A
--   cons x 0𝕓 xs _ = x
--   cons x (0< ns) f (n , p) = cons′ x ns (λ n ⦃ p ⦄ → f (n , p)) n ⦃ p ⦄

-- cons : A → ⟦ Array ⟧ A → ⟦ Array ⟧ A
-- cons x xs .fst = inc (xs .fst)
-- cons x xs .snd = Indexed.cons x (xs .fst) (xs .snd)
\end{code}
