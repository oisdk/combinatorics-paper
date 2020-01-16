{-# OPTIONS --cubical --safe --postfix-projections #-}

module Category.HSets where

open import Prelude
open import Category
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Data.Sigma.Properties
open import Category.Product

module _ {ℓ : Level} where
  hSetPreCategory : PreCategory (ℓsuc ℓ) ℓ
  hSetPreCategory .PreCategory.Ob = hSet _
  hSetPreCategory .PreCategory.Hom (X , _) (Y , _) = X → Y
  hSetPreCategory .PreCategory.Id = id
  hSetPreCategory .PreCategory.Comp f g = f ∘ g
  hSetPreCategory .PreCategory.assoc-Comp _ _ _ = refl
  hSetPreCategory .PreCategory.Comp-Id _ = refl
  hSetPreCategory .PreCategory.Id-Comp _ = refl
  hSetPreCategory .PreCategory.Hom-Set {X} {Y} = hLevelPi 2 λ _ → Y .snd

  open PreCategory hSetPreCategory

  module _ {X Y : Ob} where
    iso-iso : (X ≅ Y) ⇔ (fst X ⇔ fst Y)
    iso-iso .fun (f , g , f∘g , g∘f) = iso f g (λ x i → g∘f i x) (λ x i → f∘g i x)
    iso-iso .inv (iso f g g∘f f∘g) = f , g  , (λ i x → f∘g x i) , (λ i x → g∘f x i)
    iso-iso .rightInv _ = refl
    iso-iso .leftInv  _ = refl

    univ⇔ : (X ≡ Y) ⇔ (X ≅ Y)
    univ⇔ = equivToIso (≃ΣProp≡ (λ _ → isPropIsSet)) ⟨ trans-⇔ ⟩
            equivToIso univalence ⟨ trans-⇔ ⟩
            sym-⇔ (iso⇔equiv (snd X)) ⟨ trans-⇔ ⟩
            sym-⇔ iso-iso

  hSetCategory : Category (ℓsuc ℓ) ℓ
  hSetCategory .Category.preCategory = hSetPreCategory
  hSetCategory .Category.univalent = isoToEquiv univ⇔

  hSetProd : HasProducts hSetCategory
  hSetProd .HasProducts.product X Y .Product.obj = (X .fst × Y .fst) , isOfHLevelΣ 2 (X .snd) λ _ → Y .snd
  hSetProd .HasProducts.product X Y .Product.fst = fst
  hSetProd .HasProducts.product X Y .Product.snd = snd
  hSetProd .HasProducts.product X Y .Product.ump f g .fst z = f z , g z
  hSetProd .HasProducts.product X Y .Product.ump f g .snd .fst .fst = refl
  hSetProd .HasProducts.product X Y .Product.ump f g .snd .fst .snd = refl
  hSetProd .HasProducts.product X Y .Product.ump f g .snd .snd (f≡ , g≡) i x = f≡ (~ i) x , g≡ (~ i) x
