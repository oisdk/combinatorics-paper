{-# OPTIONS --cubical --safe #-}

open import Algebra

module Algebra.Construct.Free.Semimodule.Direct.Homomorphism {ℓ₁ ℓ₂} (sm : LeftSemimodule ℓ₁ ℓ₂) where

open import Prelude

open LeftSemimodule sm

open import Algebra.Construct.Free.Semimodule.Direct.Definition semiring using (𝒱)
open import Algebra.Construct.Free.Semimodule.Direct.Eliminators semiring

module _ (isSetV : isSet 𝑉) (h : A → 𝑉) where
  ⟦_⟧ : 𝒱 A → 𝑉
  ⟦_⟧ = [ hom ]↓
    where
    hom : A ↘ 𝑉
    [ hom ]-set = isSetV
    [ hom ][ x ] = h x
    [ hom ] x ⋊ xs = x ⋊ xs
    [ hom ] xs ∪ ys = xs ∪ ys
    [ hom ]∅ = ∅
    [ hom ]-com = comm
    [ hom ]-assoc = ∪-assoc
    [ hom ]∅∪ = ∅∪
    [ hom ]⟨*⟩⋊ = ⟨*⟩⋊
    [ hom ]⟨+⟩⋊ = ⟨+⟩⋊
    [ hom ]⋊⟨∪⟩ = ⋊⟨∪⟩
    [ hom ]1⋊ = 1⋊
    [ hom ]0⋊ = 0⋊
