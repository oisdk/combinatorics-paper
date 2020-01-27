{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Prelude

module Cardinality.Finite.Cardinal.Category {ℓ : Level} where

open import Cardinality.Finite.Cardinal
open import HITs.PropositionalTruncation
open import Data.Sigma.Properties
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Categories
open import Cubical.Foundations.Univalence
open import Categories.Product
open import Categories.Exponential
open import Data.Fin
open import Cardinality.Finite.ManifestBishop

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
  ≃ΣProp≡ (λ _ → squash) ⟨ trans-≃ ⟩
  univalence ⟨ trans-≃ ⟩
  isoToEquiv (
  sym-⇔ (iso⇔equiv (Discrete→isSet (𝒞⇒Discrete (X .snd)))) ⟨ trans-⇔ ⟩
  sym-⇔ (iso-iso {X} {Y}))

finSetHasProducts : HasProducts finSetCategory
finSetHasProducts .HasProducts.product X Y .Product.obj = X .fst × Y .fst , X .snd ∥×∥ Y .snd
finSetHasProducts .HasProducts.product X Y .Product.proj₁ = fst
finSetHasProducts .HasProducts.product X Y .Product.proj₂ = snd
finSetHasProducts .HasProducts.product X Y .Product.ump f g .fst z = f z , g z
finSetHasProducts .HasProducts.product X Y .Product.ump f g .snd .fst .fst = refl
finSetHasProducts .HasProducts.product X Y .Product.ump f g .snd .fst .snd = refl
finSetHasProducts .HasProducts.product X Y .Product.ump f g .snd .snd (f≡ , g≡) i x = f≡ (~ i) x , g≡ (~ i) x

finSetHasExp : HasExponentials finSetCategory finSetHasProducts
finSetHasExp X Y .Exponential.obj = (X .fst → Y .fst) , (X .snd ∥→∥ Y .snd)
finSetHasExp X Y .Exponential.eval (f , x) = f x
finSetHasExp X Y .Exponential.uniq X₁ f .fst = curry f
finSetHasExp X Y .Exponential.uniq X₁ f .snd .fst = refl
finSetHasExp X Y .Exponential.uniq X₁ f .snd .snd x = cong curry (sym x)
