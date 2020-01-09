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
map-◇ {A = A} {P = P} x Px =
  𝒦-elim-prop
    (λ {xs} p q i x∈xs → isProp-◇  {xs = xs} (p x∈xs) (q x∈xs) i)
    (λ ())
    λ y xs Pxs x∈xs → x∈xs >>= (fn y xs Pxs)
  where
  fn : ∀ y xs → (x ∈ xs → ◇ P xs) → (y ≡ x) ⊎ (x ∈ xs) → ◇ P (y ∷ xs)
  fn y xs k (inl y≡x) = ∣ inl (subst P (sym y≡x) Px) ∣
  fn y xs k (inr x∈xs) = ∣ inr (k x∈xs) ∣
