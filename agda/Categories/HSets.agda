{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Prelude hiding (_×_)

module Categories.HSets {ℓ : Level} where

open import Categories
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Data.Sigma.Properties
open import Categories.Product
open import Categories.Exponential

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
hSetProd .HasProducts.product X Y .Product.obj = (X .fst Prelude.× Y .fst) , isOfHLevelΣ 2 (X .snd) λ _ → Y .snd
hSetProd .HasProducts.product X Y .Product.proj₁ = fst
hSetProd .HasProducts.product X Y .Product.proj₂ = snd
hSetProd .HasProducts.product X Y .Product.ump f g .fst z = f z , g z
hSetProd .HasProducts.product X Y .Product.ump f g .snd .fst .fst = refl
hSetProd .HasProducts.product X Y .Product.ump f g .snd .fst .snd = refl
hSetProd .HasProducts.product X Y .Product.ump f g .snd .snd (f≡ , g≡) i x = f≡ (~ i) x , g≡ (~ i) x

hSetExp : HasExponentials hSetCategory hSetProd
hSetExp .HasExponentials.exponent X Y .Exponential.obj = (X .fst → Y .fst) , hLevelPi 2 λ _ → Y .snd
hSetExp .HasExponentials.exponent X Y .Exponential.eval (f , x) = f x
hSetExp .HasExponentials.exponent X Y .Exponential.uniq X₁ f .fst = curry f
hSetExp .HasExponentials.exponent X Y .Exponential.uniq X₁ f .snd .fst = refl
hSetExp .HasExponentials.exponent X Y .Exponential.uniq X₁ f .snd .snd {y} x = cong curry (sym x)

open import Categories.Pullback

hSetHasPullbacks : HasPullbacks hSetCategory
hSetHasPullbacks .HasPullbacks.pullback {X = X} {Y = Y} {Z = Z} f g .Pullback.P = ∃[ ab ] (f (fst ab) ≡ g (snd ab)) , isOfHLevelΣ 2 (isOfHLevelΣ 2 (X .snd) λ _ → Y .snd) λ xy → isProp→isSet (Z .snd (f (xy .fst)) (g (xy .snd)))
hSetHasPullbacks .HasPullbacks.pullback f g .Pullback.p₁ ((x , _) , _) = x
hSetHasPullbacks .HasPullbacks.pullback f g .Pullback.p₂ ((_ , y) , _) = y
hSetHasPullbacks .HasPullbacks.pullback f g .Pullback.commute = funExt snd
hSetHasPullbacks .HasPullbacks.pullback f g .Pullback.universal {A = A} {h₁} {h₂} p x = (h₁ x , h₂ x) , λ i → p i x
hSetHasPullbacks .HasPullbacks.pullback {Z = Z} f g .Pullback.unique {A = A} {h₁} {h₂} {eq} {i} p₁e p₂e = funExt (λ x → ΣProp≡ (λ _ → Z .snd _ _) λ j → p₁e j x , p₂e j x)
hSetHasPullbacks .HasPullbacks.pullback f g .Pullback.p₁·universal≡h₁ = refl
hSetHasPullbacks .HasPullbacks.pullback f g .Pullback.p₂·universal≡h₂ = refl
