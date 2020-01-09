{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Free.Semilattice.Relation.Unary.Any.Dec where

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
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Decidable.Properties
open import Relation.Nullary.Decidable.Logic

private
  variable p : Level

◇′? : ∀ {P : A → Type p} → (∀ x → Dec (P x)) → xs ∈𝒦 A ⇒∥ Dec (◇ P xs) ∥
∥ ◇′? {P = P} P? ∥-prop {xs} = isPropDec (isProp-◇ {P = P} {xs = xs})
∥ ◇′? P? ∥[] = no (Poly⊥⇔Mono⊥ .fun)
∥ ◇′? P? ∥ x ∷ xs ⟨ Pxs ⟩ = map-dec ∣_∣ refute-trunc (P? x || Pxs)

◇? : ∀ {P : A → Type p} → (∀ x → Dec (P x)) → ∀ xs → Dec (◇ P xs)
◇? P? = ∥ ◇′? P? ∥⇓
