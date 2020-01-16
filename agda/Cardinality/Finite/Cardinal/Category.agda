{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Prelude

module Cardinality.Finite.Cardinal.Category {ℓ : Level} where

open import Cardinality.Finite.Cardinal
open import HITs.PropositionalTruncation
open import Data.Sigma.Properties
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Category
open import Category.HSets using (equivSigProp; iso⇔equiv)
open import Cubical.Foundations.Univalence

finSetPreCategory : PreCategory (ℓsuc ℓ) ℓ
finSetPreCategory .PreCategory.Ob = Σ (Type ℓ) 𝒞
finSetPreCategory .PreCategory.Hom (X , _) (Y , _) = X → Y
finSetPreCategory .PreCategory.Id = id
finSetPreCategory .PreCategory.Comp f g = f ∘ g
finSetPreCategory .PreCategory.assoc-Comp _ _ _ = refl
finSetPreCategory .PreCategory.Comp-Id _ = refl
finSetPreCategory .PreCategory.Id-Comp _ = refl
finSetPreCategory .PreCategory.Hom-Set {X} {Y} = hLevelPi 2 λ _ → Discrete→isSet (𝒞⇒Discrete (Y .snd))

open PreCategory finSetPreCategory

iso-iso : (X ≅ Y) ⇔ (fst X ⇔ fst Y)
iso-iso .fun (f , g , f∘g , g∘f) = iso f g (λ x i → g∘f i x) (λ x i → f∘g i x)
iso-iso .inv (iso f g g∘f f∘g) = f , g  , (λ i x → f∘g x i) , (λ i x → g∘f x i)
iso-iso .rightInv _ = refl
iso-iso .leftInv  _ = refl

finSetCategory : Category (ℓsuc ℓ) ℓ
finSetCategory .Category.preCategory = finSetPreCategory
finSetCategory .Category.univalent {X} {Y} =
  isoToEquiv $ equivSigProp (λ _ → squash) ⟨ trans-⇔ ⟩
               equivToIso univalence ⟨ trans-⇔ ⟩
               sym-⇔ (iso⇔equiv (Discrete→isSet (𝒞⇒Discrete (X .snd)))) ⟨ trans-⇔ ⟩
               sym-⇔ (iso-iso {X} {Y})
