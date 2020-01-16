{-# OPTIONS --cubical --safe --postfix-projections #-}

module Category.HSets where

open import Prelude
open import Category
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

hSet : (ℓ : Level) → Type (ℓsuc ℓ)
hSet ℓ = Σ (Type ℓ) isSet

equivSigProp : ∀ {u} {U : A → Type u} → ((x : A) → isProp (U x)) → {p q : Σ A U} → (p ≡ q) ⇔ (fst p ≡ fst q)
equivSigProp {A = A} {U = U} pA {p} {q} = iso (to p q) (fro p q) ri li
  where
  to : (p q : Σ A U) → p ≡ q → fst p ≡ fst q
  to _ _ = cong fst
  fro : ∀ p q → fst p ≡ fst q → p ≡ q
  fro _ _ = ΣProp≡ pA
  ri : ∀ x → to p q (fro _ _ x) ≡ x
  ri _ = refl
  li : ∀ x → fro _ _ (to _ _ x) ≡ x
  li = J (λ q q≡ → fro p q (to p q q≡) ≡ q≡) λ i j → p .fst , isProp→isSet (pA (p .fst)) (p .snd) (p .snd) (λ k → fro p p (to p p (λ _ → p)) k .snd) (λ _ → p .snd) i j

iso⇔equiv : isSet A → (A ⇔ B) ⇔ (A ≃ B)
iso⇔equiv isSetA .fun = isoToEquiv
iso⇔equiv isSetA .inv = equivToIso
iso⇔equiv isSetA .rightInv x i .fst = x .fst
iso⇔equiv isSetA .rightInv x i .snd = isPropIsEquiv (x .fst) (isoToEquiv (equivToIso x) .snd) (x .snd) i
iso⇔equiv isSetA .leftInv x i .fun = x .fun
iso⇔equiv isSetA .leftInv x i .inv = x .inv
iso⇔equiv isSetA .leftInv x i .rightInv = x .rightInv
iso⇔equiv isSetA .leftInv x i .leftInv y = isSetA _ y (equivToIso (isoToEquiv x) .leftInv y) (x .leftInv y) i

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

  module _ {hA hB : Ob} where
    open Σ hA renaming (fst to A ; snd to sA)
    open Σ hB renaming (fst to B ; snd to sB)

    iso-iso : (hA ≅ hB) ⇔ (fst hA ⇔ fst hB)
    iso-iso .fun (f , g , f∘g , g∘f) = iso f g (λ x i → g∘f i x) (λ x i → f∘g i x)
    iso-iso .inv (iso f g g∘f f∘g) = f , g  , (λ i x → f∘g x i) , (λ i x → g∘f x i)
    iso-iso .rightInv _ = refl
    iso-iso .leftInv  _ = refl

    univ⇔ : (hA ≡ hB) ⇔ (hA ≅ hB)
    univ⇔ = equivSigProp (λ _ → isPropIsSet) ⟨ trans-⇔ ⟩
            equivToIso univalence ⟨ trans-⇔ ⟩
            sym-⇔ (iso⇔equiv (snd hA)) ⟨ trans-⇔ ⟩
            sym-⇔ iso-iso

  hSetCategory : Category (ℓsuc ℓ) ℓ
  hSetCategory .Category.preCategory = hSetPreCategory
  hSetCategory .Category.univalent = isoToEquiv univ⇔
