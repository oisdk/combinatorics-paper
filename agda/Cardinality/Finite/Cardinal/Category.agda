{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Prelude

module Cardinality.Finite.Cardinal.Category {ℓ : Level} where

open import Cardinality.Finite.Cardinal
open import HITs.PropositionalTruncation

open import Data.Sigma.Properties
open import Cubical.Foundations.Equiv

Ob : Type (ℓsuc ℓ)
Ob = ∃ 𝒞

Hom : Ob → Ob → Type ℓ
Hom A B = A .fst → B .fst

Isomorphism : {𝐴 𝐵 : Ob} → Hom 𝐴 𝐵 → Type ℓ
Isomorphism {𝐴} {𝐵} f = Σ[ g ⦂ Hom 𝐵 𝐴 ] ((g ∘ f ≡ id) × (f ∘ g ≡ id))

_≅_ : Ob → Ob → Type ℓ
xs ≅ ys = Σ[ f ⦂ Hom xs ys ] Isomorphism {xs} {ys} f

iso-iso : {xs ys : Ob} → (xs ≅ ys) ⇔ (xs .fst ⇔ ys .fst)
iso-iso {xs} {ys} .fun (f , g , f∘g , g∘f) = iso f g (λ x i → g∘f i x) (λ x i → f∘g i x)
iso-iso {xs} {ys} .inv (iso f g g∘f f∘g) = f , g  , (λ i x → f∘g x i) , (λ i x → g∘f x i)
iso-iso {xs} {ys} .rightInv _ = refl
iso-iso {xs} {ys} .leftInv  _ = refl

iso⇔equiv : isSet A → (A ⇔ B) ⇔ (A ≃ B)
iso⇔equiv isSetA .fun = isoToEquiv
iso⇔equiv isSetA .inv = equivToIso
iso⇔equiv isSetA .rightInv x i .fst = x .fst
iso⇔equiv isSetA .rightInv x i .snd = isPropIsEquiv (x .fst) (isoToEquiv (equivToIso x) .snd) (x .snd) i
iso⇔equiv isSetA .leftInv x i .fun = x .fun
iso⇔equiv isSetA .leftInv x i .inv = x .inv
iso⇔equiv isSetA .leftInv x i .rightInv = x .rightInv
iso⇔equiv isSetA .leftInv x i .leftInv y = isSetA _ y (equivToIso (isoToEquiv x) .leftInv y) (x .leftInv y) i

iso-equiv′ : {xs ys : Ob} → (xs ≅ ys) ⇔ (xs .fst ≃ ys .fst)
iso-equiv′ {xs} {ys} = iso-iso {xs} {ys} ⟨ trans-⇔ ⟩ iso⇔equiv (Discrete→isSet (𝒞⇒Discrete (xs .snd)))

open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma.Properties

-- lemma₂ : (xs ys : Ob) → (xs .fst ≡ ys .fst) ⇔ (xs Σ≡Y ys)
-- lemma₂ xs ys .fun xsf≡ysf = xsf≡ysf , isProp→PathP (λ _ → squash) xsf≡ysf (xs .snd) (ys .snd) i
-- lemma₂ xs ys .inv xs≡ys i = xs≡ys i .fst
-- lemma₂ xs ys .leftInv xsf≡ysf = refl
-- lemma₂ xs ys .rightInv xs≡ys = {!!}

lemma₁ : (xs ys : Ob) → (xs .fst ≡ ys .fst) ≡ (xs ≡ ys)
lemma₁ xs ys = {!!} ; sym (pathSigma≡sigmaPath xs ys)

-- iso-equiv″ : {xs ys : Ob} → (xs .fst ≃ ys .fst) ≃ (xs ≡ ys)
-- iso-equiv″ = sym-≃ univalence ⟨ trans-≃ ⟩ {!!}


-- cat : ∀ x y → x ≅ y → x ≡ y
-- cat x y x⇔y = ΣProp≡ (λ _ → squash) (isoToPath x⇔y)

-- cat⁻¹ : ∀ x y → x ≡ y → x ≅ y
-- cat⁻¹ x y x≡y = subst (Iso _) (cong fst x≡y) refl-⇔

-- cat-cat : ∀ x y → (x ≡ y) ⇔ (x ≅ y)
-- cat-cat x y .fun = cat⁻¹ x y
-- cat-cat x y .inv = cat x y
-- cat-cat x y .rightInv p = {!!}
-- cat-cat x y .leftInv = {!!}

-- -- isSetOb : isSet Ob
-- -- isSetOb x y = isOfHLevelΣ 2 {!!} {!!} x y
