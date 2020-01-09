{-# OPTIONS --cubical --safe #-}

module Cardinality.Finite.Kuratowski where

open import Prelude
open import Algebra.Construct.Free.Semilattice
open import Algebra.Construct.Free.Semilattice.Relation.Unary

open import Cardinality.Finite.ManifestEnumerable
open import Cardinality.Finite.ManifestEnumerable.Inductive renaming (_∈_ to _L∈_)

open import HITs.PropositionalTruncation
open import HITs.PropositionalTruncation.Sugar
open import Data.Fin

𝒦ᶠ : Type a → Type a
𝒦ᶠ A = Σ[ xs ⦂ 𝒦 A ] Π[ x ⦂ A ] x ∈ xs

𝒦ᶠ⇒∥ℰ∥ : 𝒦ᶠ A → ∥ ℰ A ∥
𝒦ᶠ⇒∥ℰ∥ K = map₂ (λ p x → p x (K .snd x)) ∥$∥ ∥ enum ∥⇓ (K .fst)
  where
  enum : xs ∈𝒦 A ⇒∥ ∥ Σ[ ys ⦂ List A ] (∀ x → x ∈ xs → ∥ x L∈ ys ∥) ∥ ∥
  ∥ enum ∥-prop = squash
  ∥ enum ∥[] = ∣ [] , (λ _ ()) ∣
  ∥ enum ∥ x ∷ xs ⟨ Pxs ⟩ = cons ∥$∥ Pxs
    where
    cons : _
    cons (ys , p) .fst = x ∷ ys
    cons (ys , p) .snd z zs = zs >>= either′ (∣_∣ ∘ (f0 ,_)) ((push ∥$∥_) ∘ p z)

open import Algebra.Construct.Free.Semilattice.Extensionality
open import Algebra.Construct.Free.Semilattice.FromList
open import Data.Sigma.Properties

isProp𝒦ᶠ : isProp (𝒦ᶠ A)
isProp𝒦ᶠ Kˣ Kʸ =
  ΣProp≡
    (λ K p q i x → isProp-◇ {xs = K} (p x) (q x) i)
    {Kˣ} {Kʸ}
    (extensional (fst Kˣ) (fst Kʸ) λ x → const (Kʸ .snd x) iff const (Kˣ .snd x))

ℰ⇒𝒦 : ℰ A → 𝒦ᶠ A
ℰ⇒𝒦 E .fst = fromList (E .fst)
ℰ⇒𝒦 E .snd x = ∈List⇒∈𝒦 (E .fst) (E .snd x)

∥ℰ∥⇔𝒦 : ∥ ℰ A ∥ ⇔ 𝒦ᶠ A
∥ℰ∥⇔𝒦 .fun = recPropTrunc isProp𝒦ᶠ ℰ⇒𝒦
∥ℰ∥⇔𝒦 .inv = 𝒦ᶠ⇒∥ℰ∥
∥ℰ∥⇔𝒦 .leftInv x = squash _ x
∥ℰ∥⇔𝒦 .rightInv x = isProp𝒦ᶠ _ x

Sub : ∀ p → Type a → Type _
Sub p A = A → hProp p

Subobject : Sub b A → Type _
Subobject s = ∃ (fst ∘ s)

open import Data.List.Filter
open import Cardinality.Finite.SplitEnumerable.Inductive
open import Cardinality.Finite.SplitEnumerable.Isomorphism
open import Cardinality.Finite.SplitEnumerable
open import Data.List.Relation.Unary

to-subobject : (p : A → Bool) → ℰ! A → ℰ! (Σ[ x ⦂ A ] (T (p x)))
to-subobject s xs .fst = filter s (xs .fst)
to-subobject p xs .snd (x , v) = filter-preserves p (xs .fst) x v (xs .snd x)

decide-subobject : (P : A → Type ℓzero) → ℰ! A → (xs : ℰ! (∃ P)) → (x : A) → Dec (P x)
decide-subobject P E xs x =
  ⟦yes (λ { (n , t) → subst P t ((xs .fst ! n) .snd) })
  ,no (λ y → map₂ (cong fst) (xs .snd (x , y)))
  ⟧ (Exists.◇? (λ y → fst y ≡ x) (λ y → ℰ!⇒Discrete (𝕃⇔ℒ⟨ℰ!⟩ .fun E) (y .fst) x) (xs .fst))

dec-refl : ∀ x → (y : Dec (T x)) → does y ≡ x
dec-refl true (yes p) = refl
dec-refl false (no ¬p) = refl
dec-refl true (no ¬p) = ⊥-elim (¬p tt)

dec-un : (x : Dec A) → T (x .does) → A
dec-un (yes x) p = x
dec-un (no ¬x) ()

dec-nu : A → (d : Dec A) → T (d .does)
dec-nu x (true because z) = tt
dec-nu x (no ¬p) = ⊥-elim (¬p x)

open import Data.Bool.Properties
open import Cardinality.Finite.Cardinal
open import Cardinality.Finite.ManifestBishop
open import Relation.Nullary.Decidable.Properties

module _ {a} {A : Type a} (xs : 𝒞 A) where
  to : (A → Bool) → Σ[ sub ⦂ (A → hProp ℓzero) ] (𝒞 (Σ[ x ⦂ A ] (sub x .fst)))
  to p .fst x .fst = T (p x)
  to p .fst x .snd = isPropT _
  to p .snd = ℰ!⇒ℬ ∘ to-subobject p ∘ ℬ⇒ℰ! ∥$∥ xs

  fromDec : (sub : (A → hProp ℓzero)) → 𝒞 (Σ[ x ⦂ A ] (sub x .fst)) → ∀ x → Dec (sub x .fst)
  fromDec sub fin x = recPropTrunc (isPropDec (sub x .snd)) (λ { (xs′ , fin′) → decide-subobject (fst ∘ sub) (ℬ⇒ℰ! xs′) (ℬ⇒ℰ! fin′) x}) ⦇ xs , fin ⦈

  lem : ∀ f x → Dec.does (fromDec (to f .fst) (to f .snd) x) ≡ f x
  lem f x = dec-refl (f x) (fromDec (to f .fst) (to f .snd) x)

  lem3 : (sub : A → hProp ℓzero) → (fin : 𝒞 (∃ (fst ∘ sub))) → ∀ x → T ((does ∘ fromDec sub fin) x) → sub x .fst
  lem3 sub fin x Dx = dec-un ((fromDec sub fin) x) Dx

  lem4 : (sub : A → hProp ℓzero) → (fin : 𝒞 (∃ (fst ∘ sub))) → ∀ x → sub x .fst → T ((does ∘ fromDec sub fin) x)
  lem4 sub fin x Px = dec-nu Px (fromDec sub fin x)

  lem2 : (sub : A → hProp ℓzero) → (fin : 𝒞 (∃ (fst ∘ sub))) → ∀ x → to (does ∘ fromDec sub fin) .fst x ≡ sub x
  lem2 sub fin x = ΣProp≡ (λ _ → isPropIsProp) (isoToPath (iso (lem3 sub fin x) (lem4 sub fin x) (λ y → sub x .snd _ y) (λ x → isPropT _ _ x)  ))

  subobject-classifier : (A → Bool) ⇔ (Σ[ sub ⦂ (A → hProp ℓzero) ] (𝒞 (Σ[ x ⦂ A ] (sub x .fst))))
  subobject-classifier .fun p .fst x .fst = T (p x)
  subobject-classifier .fun p .fst x .snd = isPropT _
  subobject-classifier .fun p .snd = ℰ!⇒ℬ ∘ to-subobject p ∘ ℬ⇒ℰ! ∥$∥ xs
  subobject-classifier .inv (sub , fin) x = does (fromDec sub fin x)
  subobject-classifier .rightInv (sub , fin) = ΣProp≡ (λ _ → squash) (λ i x → lem2 sub fin x i)
  subobject-classifier .leftInv fn i x = lem fn x i
