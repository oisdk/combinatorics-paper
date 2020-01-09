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

filter-subobject : (p : A → Bool) → ℰ! A → ℰ! (Σ[ x ⦂ A ] (T (p x)))
filter-subobject s xs .fst = filter s (xs .fst)
filter-subobject p xs .snd (x , v) = filter-preserves p (xs .fst) x v (xs .snd x)

decide-subobject : (P : A → Type ℓzero) → ℰ! A → (xs : ℰ! (∃ P)) → (x : A) → Dec (P x)
decide-subobject P E xs x =
  ⟦yes (λ { (n , t) → subst P t ((xs .fst ! n) .snd) })
  ,no (λ y → map₂ (cong fst) (xs .snd (x , y)))
  ⟧ (Exists.◇? (λ y → fst y ≡ x) (λ y → ℰ!⇒Discrete (𝕃⇔ℒ⟨ℰ!⟩ .fun E) (y .fst) x) (xs .fst))

it-does : (x : Dec A) → T (x .does) → A
it-does (yes x) p = x
it-does (no ¬x) ()

does-it : (d : Dec A) → A → T (d .does)
does-it (true because z) x = tt
does-it (no ¬p) x = ⊥-elim (¬p x)

open import Data.Bool.Properties
open import Cardinality.Finite.Cardinal
open import Cardinality.Finite.ManifestBishop
open import Relation.Nullary.Decidable.Properties

module _ {a} {A : Type a} (xs : 𝒞 A) where
  to-subobject : (A → Bool) → Σ[ sub ⦂ (A → hProp ℓzero) ] (𝒞 (Σ[ x ⦂ A ] (sub x .fst)))
  to-subobject p .fst x .fst = T (p x)
  to-subobject p .fst x .snd = isPropT _
  to-subobject p .snd = ℰ!⇒ℬ ∘ filter-subobject p ∘ ℬ⇒ℰ! ∥$∥ xs

  fromDec : (sub : (A → hProp ℓzero)) → 𝒞 (Σ[ x ⦂ A ] (sub x .fst)) → ∀ x → Dec (sub x .fst)
  fromDec sub fin x = recPropTrunc (isPropDec (sub x .snd)) id $ do
    c ← xs
    f ← fin
    ∣ decide-subobject (fst ∘ sub) (ℬ⇒ℰ! c) (ℬ⇒ℰ! f) x ∣

  subobject-classifier : (A → Bool) ⇔ (Σ[ sub ⦂ (A → hProp ℓzero) ] (𝒞 (Σ[ x ⦂ A ] (sub x .fst))))
  subobject-classifier .fun = to-subobject
  subobject-classifier .inv (sub , fin) x = does (fromDec sub fin x)
  subobject-classifier .rightInv (sub , fin) = ΣProp≡ (λ _ → squash) (λ i x → lemma sub fin x i)
    where
    lemma : (sub : A → hProp ℓzero) → (fin : 𝒞 (∃ (fst ∘ sub))) → ∀ x → to-subobject (does ∘ fromDec sub fin) .fst x ≡ sub x
    lemma sub fin x = ΣProp≡ (λ _ → isPropIsProp) (isoToPath (iso (it-does (fromDec sub fin x)) (does-it (fromDec sub fin x)) (λ y → sub x .snd _ y) (λ x → isPropT _ _ x)))
  subobject-classifier .leftInv fn i x = lemma fn x i
    where
    dec-refl : ∀ x → (y : Dec (T x)) → does y ≡ x
    dec-refl true (yes p) = refl
    dec-refl false (no ¬p) = refl
    dec-refl true (no ¬p) = ⊥-elim (¬p tt)

    lemma : ∀ f x → Dec.does (fromDec (to-subobject f .fst) (to-subobject f .snd) x) ≡ f x
    lemma f x = dec-refl (f x) (fromDec (to-subobject f .fst) (to-subobject f .snd) x)


open import Relation.Nullary.Decidable.Properties
open import Relation.Nullary.Omniscience
open import HITs.PropositionalTruncation.Properties

𝒦ᶠ⇒Exhaustible : ∀ {p} → 𝒦ᶠ A → Exhaustible p A
𝒦ᶠ⇒Exhaustible K P? =
  ∣ ◻? P? (K .fst)
    ∣yes⇒ (λ ◻Pxs x → recompute (P? x) (P∈◇ x (K .fst) (K .snd x) ◻Pxs))
    ∣no⇒ λ ¬◻Pxs ∀P → ¬◻Pxs (map-◻ ∀P (K .fst))

private variable p : Level

𝒦ᶠ⇒∣Omniscient∣ : {P : A → Type p} → 𝒦ᶠ A → Decidable P → Dec ∥ ∃ P ∥
𝒦ᶠ⇒∣Omniscient∣ K P? =
  recPropTrunc
    (isPropDec squash)
    (map-dec ∣_∣ refute-trunc ∘ λ xs → ℰ⇒Omniscient xs P?)
    (𝒦ᶠ⇒∥ℰ∥ K)
