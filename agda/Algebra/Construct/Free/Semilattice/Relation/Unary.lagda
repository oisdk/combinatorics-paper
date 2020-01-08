\begin{code}
{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Free.Semilattice.Relation.Unary where

open import Prelude hiding (⊥; ⊤)
open import Algebra.Construct.Free.Semilattice.Eliminators
open import Algebra.Construct.Free.Semilattice.Definition
open import Cubical.Foundations.HLevels
open import Data.Empty.UniversePolymorphic
open import HITs.PropositionalTruncation.Sugar
open import HITs.PropositionalTruncation.Properties
open import HITs.PropositionalTruncation
open import Data.Unit.UniversePolymorphic

private
  variable p : Level

dup-◇ : (P : A → Type p) → (x : A) (xs : Type p) → ∥ P x ⊎ ∥ P x ⊎ xs ∥ ∥ ⇔ ∥ P x ⊎ xs ∥
dup-◇ P x xs .inv p = ∣ inr p ∣
dup-◇ P x xs .fun ps = ps >>= either (∣_∣ ∘ inl) id
dup-◇ P x xs .leftInv p = squash _ p
dup-◇ P x xs .rightInv p = squash p _

swap-◇ : {x y xs : Type p} → ∥ x ⊎ ∥ y ⊎ xs ∥ ∥ → ∥ y ⊎ ∥ x ⊎ xs ∥ ∥
swap-◇ p = p >>= either′ (∣_∣ ∘ inr ∘ ∣_∣ ∘ inl) (mapʳ (∣_∣ ∘ inr) ∥$∥_)

com-◇ : (P : A → Type p) → (x y : A) (xs : Type p) → ∥ P x ⊎ ∥ P y ⊎ xs ∥ ∥ ⇔ ∥ P y ⊎ ∥ P x ⊎ xs ∥ ∥
com-◇ P y z xs .fun = swap-◇
com-◇ P y z xs .inv = swap-◇
com-◇ P y z xs .leftInv  p = squash _ p
com-◇ P y z xs .rightInv p = squash _ p

◇′ : (P : A → Type p) → A ↘ hProp p
[ ◇′ P ]-set = isSetHProp
[ ◇′ P ] x ∷ (xs , hxs) = ∥ P x ⊎ xs ∥ , squash
[ ◇′ P ][] = ⊥ , λ ()
[ ◇′ P ]-dup x xs = ΣProp≡ (λ _ → isPropIsProp) (isoToPath (dup-◇ P x (xs .fst)))
[ ◇′ P ]-com x y xs = ΣProp≡ (λ _ → isPropIsProp) (isoToPath (com-◇ P x y (xs .fst)))

◇ : (P : A → Type p) → 𝒦 A → Type p
◇ P xs = [ ◇′ P ]↓ xs .fst

isProp-◇ : ∀ {P : A → Type p} {xs} → isProp (◇ P xs)
isProp-◇ {P = P} {xs = xs} = [ ◇′ P ]↓ xs .snd

dup-◻ : (P : A → Type p) → (x : A) (xs : Type p) → (∥ P x ∥ × ∥ P x ∥ × xs) ⇔ (∥ P x ∥ × xs)
dup-◻ P _ _ .fun = snd
dup-◻ P _ _ .inv (x , xs) = x , x , xs
dup-◻ P _ _ .rightInv (x , xs) = refl
dup-◻ P _ _ .leftInv  (x₁ , x₂ , xs) i .fst = squash x₂ x₁ i
dup-◻ P _ _ .leftInv  (x₁ , x₂ , xs) i .snd = (x₂ , xs)

com-◻ : (P : A → Type p) → (x y : A) (xs : Type p) → (∥ P x ∥ × ∥ P y ∥ × xs) ⇔ (∥ P y ∥ × ∥ P x ∥ × xs)
com-◻ P _ _ _ .fun (x , y , xs) = y , x , xs
com-◻ P _ _ _ .inv (y , x , xs) = x , y , xs
com-◻ P _ _ _ .leftInv  (x , y , xs) = refl
com-◻ P _ _ _ .rightInv (x , y , xs) = refl

◻′ : (P : A → Type p) → A ↘ hProp p
[ ◻′ P ]-set = isSetHProp
([ ◻′ P ] x ∷ (xs , hxs)) .fst = ∥ P x ∥ × xs
([ ◻′ P ] x ∷ (xs , hxs)) .snd y z = ΣProp≡ (λ _  → hxs) (squash (fst y) (fst z))
[ ◻′ P ][] = ⊤ , λ x y _ → x
[ ◻′ P ]-dup x xs = ΣProp≡ (λ _ → isPropIsProp) (isoToPath (dup-◻ P x (xs .fst)))
[ ◻′ P ]-com x y xs = ΣProp≡ (λ _ → isPropIsProp) (isoToPath (com-◻ P x y (xs .fst)))

◻ : (P : A → Type p) → 𝒦 A → Type p
◻ P xs = [ ◻′ P ]↓ xs .fst

isProp-◻ : ∀ {P : A → Type p} {xs} → isProp (◻ P xs)
isProp-◻ {P = P} {xs = xs} = [ ◻′ P ]↓ xs .snd

infixr 5 _∈_
_∈_ : {A : Type a} → A → 𝒦 A → Type a
x ∈ xs = ◇ (_≡ x) xs

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Decidable.Properties
open import Relation.Nullary.Decidable.Logic

◻′? : ∀ {P : A → Type p} → (∀ x → Dec (P x)) → xs ∈𝒦 A ⇒∥ Dec (◻ P xs) ∥
∥ ◻′? {P = P} P? ∥-prop {xs} = isPropDec (isProp-◻ {P = P} {xs = xs})
∥ ◻′? P? ∥[] = yes tt
∥ ◻′? P? ∥ x ∷ xs ⟨ Pxs ⟩ = map-dec ∣_∣ refute-trunc (P? x) && Pxs

◻? : ∀ {P : A → Type p} → (∀ x → Dec (P x)) → ∀ xs → Dec (◻ P xs)
◻? P? = ∥ ◻′? P? ∥⇓

P∈◇ : ∀ {p} {P : A → Type p} → ∀ x xs → x ∈ xs → ◻ P xs → ∥ P x ∥
P∈◇ {A = A} {P = P} = λ x → ∥ P∈◇′ x ∥⇓
  where
  P∈◇′ : (x : A) → xs ∈𝒦 A ⇒∥ (x ∈ xs → ◻ P xs → ∥ P x ∥) ∥
  ∥ P∈◇′ x ∥-prop p q i x∈xs ◻Pxs = squash (p x∈xs ◻Pxs) (q x∈xs ◻Pxs) i
  ∥ P∈◇′ x ∥[] ()
  ∥ P∈◇′ x ∥ y ∷ ys ⟨ Pys ⟩ x∈xs ◻Pxs =
    x∈xs >>=
      either′
        (λ y≡x → subst (∥_∥ ∘ P) y≡x (◻Pxs .fst))
        (λ x∈ys → Pys x∈ys (◻Pxs .snd))

map-◻ : ∀ {p} {P : A → Type p} → (∀ x → P x) → ∀ xs → ◻ P xs
map-◻ {A = A} {P = P} = λ f → ∥ map-◻′ f ∥⇓
  where
  map-◻′ : (∀ x → P x) → xs ∈𝒦 A ⇒∥ ◻ P xs ∥
  ∥ map-◻′ f ∥-prop {xs} = isProp-◻ {P = P} {xs = xs}
  ∥ map-◻′ f ∥[] = tt
  ∥ map-◻′ f ∥ x ∷ xs ⟨ Pxs ⟩ = ∣ f x ∣ , Pxs
\end{code}
