{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Prelude

module Algebra.Construct.Free.Semimodule.Direct.Extensional {s} (rng : Semiring s) (sIsSet : isSet (Semiring.𝑅 rng)) where

open Semiring rng

open import Algebra.Construct.Free.Semimodule.Direct.Definition rng
open import Algebra.Construct.Free.Semimodule.Direct.Eliminators rng

open import Algebra.SemiringLiterals nearSemiring
open import Path.Reasoning


∫ : 𝒱 A → (A → 𝑅) → 𝑅
∫ = λ xs f → [ int f ]↓ xs
  where
  int : (A → 𝑅) → A ↘ 𝑅
  [ int f ]-set = sIsSet
  [ int f ][ x ] = f x
  [ int f ] p ⋊ xs = p * xs
  [ int f ] xs ∪ ys = xs + ys
  [ int f ]∅ = 0
  [ int f ]-com = +-comm
  [ int f ]-assoc = +-assoc
  [ int f ]∅∪ = 0+
  [ int f ]⟨*⟩⋊ = *-assoc
  [ int f ]⟨+⟩⋊ = ⟨+⟩*
  [ int f ]⋊⟨∪⟩ = *⟨+⟩
  [ int f ]1⋊ = 1*
  [ int f ]0⋊ = 0*

collapse : 1 ≡ 0 → (xs : 𝒱 A) → xs ≡ ∅
collapse 1≡0 xs =
  xs ≡˘⟨ 1⋊ xs ⟩
  1 ⋊ xs ≡⟨ cong (_⋊ xs) 1≡0 ⟩
  0 ⋊ xs ≡⟨ 0⋊ xs ⟩
  ∅ ∎
