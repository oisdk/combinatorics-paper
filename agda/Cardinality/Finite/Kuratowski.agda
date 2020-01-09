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
    cons (ys , p) .snd z = _>>= either′ (∣_∣ ∘ (f0 ,_)) ((push ∥$∥_) ∘ p z)

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
