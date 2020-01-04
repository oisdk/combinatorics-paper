\begin{code}
{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Free.Semilattice.Eliminators where

open import Algebra.Construct.Free.Semilattice.Definition
open import Prelude
open import Algebra

record _⇘_ {a p} (A : Type a) (P : 𝒦 A → Type p) : Type (a ℓ⊔ p) where
  constructor elim
  field
    ⟦_⟧-set : ∀ {xs} → isSet (P xs)
    ⟦_⟧[] : P []
    ⟦_⟧_∷_⟨_⟩ : ∀ x xs → P xs → P (x ∷ xs)
  private z = ⟦_⟧[]; f = ⟦_⟧_∷_⟨_⟩
  field
    ⟦_⟧-com : ∀ x y xs pxs →
      f x (y ∷ xs) (f y xs pxs) ≡[ i ≔ P (com x y xs i) ]≡
      f y (x ∷ xs) (f x xs pxs)
    ⟦_⟧-dup : ∀ x xs pxs →
      f x (x ∷ xs) (f x xs pxs) ≡[ i ≔ P (dup x xs i) ]≡
      f x xs pxs
  ⟦_⟧⇓ : ∀ xs → P xs
  ⟦ [] ⟧⇓ = z
  ⟦ x ∷ xs ⟧⇓ = f x xs ⟦ xs ⟧⇓
  ⟦ com x y xs i ⟧⇓ = ⟦_⟧-com x y xs ⟦ xs ⟧⇓  i
  ⟦ dup x xs i ⟧⇓ = ⟦_⟧-dup x xs ⟦ xs ⟧⇓ i
  ⟦ trunc xs ys x y i j ⟧⇓ =
      isOfHLevel→isOfHLevelDep {n = 2}
        (λ xs → ⟦_⟧-set {xs})
        ⟦ xs ⟧⇓ ⟦ ys ⟧⇓
        (cong ⟦_⟧⇓ x) (cong ⟦_⟧⇓ y)
        (trunc xs ys x y)
        i j
open _⇘_ public

infixr 0 ⇘-syntax
⇘-syntax = _⇘_
syntax ⇘-syntax A (λ xs → Pxs) = xs ∈𝒦 A ⇒ Pxs

record _⇲_ {a p} (A : Type a) (P : 𝒦 A  → Type p) : Type (a ℓ⊔ p) where
  constructor elim-prop
  field
    ∥_∥-prop : ∀ {xs} → isProp (P xs)
    ∥_∥[] : P []
    ∥_∥_∷_⟨_⟩ : ∀ x xs → P xs → P (x ∷ xs)
  private z = ∥_∥[]; f = ∥_∥_∷_⟨_⟩
  ∥_∥⇑ = elim
          (λ {xs} → isProp→isSet (∥_∥-prop {xs}))
          z f
          (λ x y xs pxs → toPathP (∥_∥-prop (transp (λ i → P (com x y xs i)) i0 (f x (y ∷ xs) (f y xs pxs))) (f y (x ∷ xs) (f x xs pxs))))
          (λ x xs pxs → toPathP (∥_∥-prop (transp (λ i → P (dup x xs i)) i0 (f x (x ∷ xs) (f x xs pxs))) (f x xs pxs) ))
  ∥_∥⇓ = ⟦ ∥_∥⇑ ⟧⇓

open _⇲_ public
elim-prop-syntax : ∀ {a p} → (A : Type a) → (𝒦 A → Type p) → Type (a ℓ⊔ p)
elim-prop-syntax = _⇲_

syntax elim-prop-syntax A (λ xs → Pxs) = xs ∈𝒦 A ⇒∥ Pxs ∥

record _↘∥_∥ {a p} (A : Type a) (P : 𝒦 A → Type p) : Type (a ℓ⊔ p) where
  constructor elim-to-prop
  field
    ∣_∣[] : P []
    ∣_∣_∷_⟨_⟩ : ∀ x xs → P xs → P (x ∷ xs)
  private z = ∣_∣[]; f = ∣_∣_∷_⟨_⟩
  open import HITs.PropositionalTruncation.Sugar

  ∣_∣⇑ : xs ∈𝒦 A ⇒∥ ∥ P xs ∥ ∥
  ∣_∣⇑ = elim-prop squash ∣ z ∣ λ x xs ∣Pxs∣ → f x xs ∥$∥ ∣Pxs∣
  ∣_∣⇓ = ∥ ∣_∣⇑ ∥⇓


open _↘∥_∥ public
elim-to-prop-syntax : ∀ {a p} → (A : Type a) → (𝒦 A → Type p) → Type (a ℓ⊔ p)
elim-to-prop-syntax = _↘∥_∥

syntax elim-to-prop-syntax A (λ xs → Pxs) = xs ∈𝒦 A ⇒∣ Pxs ∣

infixr 0 _↘_
record _↘_ {a b} (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  constructor rec
  field
    [_]-set  : isSet B
    [_]_∷_   : A → B → B
    [_][]    : B
  private f = [_]_∷_; z = [_][]
  field
    [_]-dup  : ∀ x xs → f x (f x xs) ≡ f x xs
    [_]-com : ∀ x y xs → f x (f y xs) ≡ f y (f x xs)
  [_]↑ = elim
            [_]-set
            z
            (λ x _ xs → f x xs)
            (λ x y xs → [_]-com x y)
            (λ x xs → [_]-dup x)
  [_]↓ = ⟦ [_]↑ ⟧⇓
open _↘_ public
\end{code}
