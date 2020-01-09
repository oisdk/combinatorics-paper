{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Free.Semilattice.Relation.Unary.Any.Map where

open import Prelude hiding (⊥; ⊤)
open import Algebra.Construct.Free.Semilattice.Eliminators
open import Algebra.Construct.Free.Semilattice.Definition
open import Cubical.Foundations.HLevels
open import Data.Empty.UniversePolymorphic
open import HITs.PropositionalTruncation.Sugar
open import HITs.PropositionalTruncation.Properties
open import HITs.PropositionalTruncation
open import Data.Unit.UniversePolymorphic
open import Algebra.Construct.Free.Semilattice.Relation.Unary.Any.Def
open import Algebra.Construct.Free.Semilattice.Relation.Unary.Membership

private
  variable p : Level
  variable P : A → Type p

map-◇ : ∀ (x : A) → P x → (xs : 𝒦 A) → x ∈ xs → ◇ P xs
map-◇ x Px = ∥ map-◇′ x Px ∥⇓
  where
  map-◇′ : ∀ x → P x → xs ∈𝒦 A ⇒∥ (x ∈ xs → ◇ P xs) ∥
  ∥ map-◇′ x Px ∥-prop {xs} p q i x∈xs = isProp-◇  {xs = xs} (p x∈xs) (q x∈xs) i
  ∥ map-◇′ x Px ∥[] ()
  ∥ map-◇′ x Px ∥ y ∷ xs ⟨ Pxs ⟩ x∈xs = x∈xs >>= either′ (λ x≡y → ∣ inl (subst _ x≡y Px) ∣ ) (∣_∣ ∘ inr ∘ Pxs)
