\begin{code}
{-# OPTIONS --cubical --safe --sized-types #-}

module Codata.Conat.Bisimulation where

open import Codata.Conat
open import Codata.Thunk
open import Codata.Size
open import Prelude

mutual
  data ⌈_⌉_≋_ (i : Size) : Conat i → Conat i → Type₀ where
    zero-≋ : ⌈ i ⌉ zero ≋ zero
    suc-≋ : ∀ {x y} → ⌈ i ⌉ x ≋⁺ y → ⌈ i ⌉ suc x ≋ suc y

  record ⌈_⌉_≋⁺_ (i : Size) (x y : Thunk Conat i) : Type₀ where
    coinductive
    field
      force-≋ : ∀ {j : Size< i} → ⌈ j ⌉ x .force ≋ y .force
open ⌈_⌉_≋⁺_ public

mutual
  bisim : ∀ {x y} → ⌈ i ⌉ x ≋ y → x ≡ y
  bisim zero-≋ i = zero
  bisim (suc-≋ x) i = suc (bisim⁺ x i)

  bisim⁺ : ∀ {x y} → ⌈ i ⌉ x ≋⁺ y → x ≡ y
  bisim⁺ x≋y i .force = bisim (x≋y .force-≋) i
\end{code}
