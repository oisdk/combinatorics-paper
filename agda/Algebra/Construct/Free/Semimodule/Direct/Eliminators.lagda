\begin{code}
{-# OPTIONS --cubical --safe #-}

open import Algebra

module Algebra.Construct.Free.Semimodule.Direct.Eliminators {s} (rng : Semiring s) where

open import Algebra.Construct.Free.Semimodule.Direct.Definition rng

open import Prelude

open Semiring rng

infixr 0 _⇘_
record _⇘_ {a ℓ} (V : Type a) (P : 𝒱 V → Type ℓ) : Type (a ℓ⊔ ℓ ℓ⊔ s) where
  constructor elim
  field
    ⟦_⟧-set : ∀ {xs} → isSet (P xs)
    ⟦_⟧[_] : ∀ x → P [ x ]
    ⟦_⟧_⋊_⟨_⟩ : ∀ p xs → P xs → P (p ⋊ xs)
    ⟦_⟧_∪_⟨_∪_⟩ : ∀ xs ys → P xs → P ys → P (xs ∪ ys)
    ⟦_⟧∅ : P ∅
  private sing = ⟦_⟧[_]; mult = ⟦_⟧_⋊_⟨_⟩; join = ⟦_⟧_∪_⟨_∪_⟩; empt = ⟦_⟧∅
  field
    ⟦_⟧-com : (∀ xs ys pxs pys → PathP (λ i → P (∪-com xs ys i))
              (join xs ys pxs pys) (join ys xs pys pxs))
    ⟦_⟧-assoc : ∀ xs ys zs pxs pys pzs →
      join (xs ∪ ys) zs (join xs ys pxs pys) pzs ≡[ i ≔ P (∪-assoc xs ys zs i ) ]≡
      join xs (ys ∪ zs) pxs (join ys zs pys pzs)
    ⟦_⟧∅∪ : ∀ xs pxs → PathP (λ i → P (∅∪ xs i)) (join ∅ xs empt pxs) pxs
    ⟦_⟧⟨*⟩⋊ : ∀ p q xs pxs →
      PathP
        (λ i → P (⟨*⟩⋊ p q xs i))
        (mult (p * q) xs pxs)
        (mult p (q ⋊ xs) (mult q xs pxs))
    ⟦_⟧⟨+⟩⋊ : ∀ p q xs pxs →
      PathP
        (λ i → P (⟨+⟩⋊ p q xs i))
        (mult (p + q) xs pxs)
        (join (p ⋊ xs) (q ⋊ xs) (mult p xs pxs) (mult q xs pxs))
    ⟦_⟧⋊⟨∪⟩ : ∀ p xs ys pxs pys →
      PathP
        (λ i → P (⋊⟨∪⟩ p xs ys i))
        (mult p (xs ∪ ys) (join xs ys pxs pys))
        (join (p ⋊ xs) (p ⋊ ys) (mult p xs pxs) (mult p ys pys))
    ⟦_⟧1⋊ : ∀ xs pxs →
      PathP
        (λ i → P (1⋊ xs i))
        (mult 1# xs pxs)
        pxs
    ⟦_⟧0⋊ : ∀ xs pxs →
      PathP
        (λ i → P (0⋊ xs i))
        (mult 0# xs pxs)
        empt
  ⟦_⟧⇓ : (xs : 𝒱 V) → P xs
  ⟦ [ x ] ⟧⇓ = sing x
  ⟦ x ⋊ xs ⟧⇓ = mult x xs ⟦ xs ⟧⇓
  ⟦ xs ∪ ys ⟧⇓ = join xs ys ⟦ xs ⟧⇓ ⟦ ys ⟧⇓
  ⟦ ∅ ⟧⇓ = empt
  ⟦ ∪-com xs ys i ⟧⇓ = ⟦_⟧-com xs ys ⟦ xs ⟧⇓ ⟦ ys ⟧⇓ i
  ⟦ ∪-assoc xs ys zs i ⟧⇓ = ⟦_⟧-assoc xs ys zs ⟦ xs ⟧⇓ ⟦ ys ⟧⇓ ⟦ zs ⟧⇓ i
  ⟦ ∅∪ xs i ⟧⇓ = ⟦_⟧∅∪ xs ⟦ xs ⟧⇓ i
  ⟦ ⟨*⟩⋊ x y xs i ⟧⇓ = ⟦_⟧⟨*⟩⋊ x y xs ⟦ xs ⟧⇓ i
  ⟦ ⟨+⟩⋊ x y xs i ⟧⇓ = ⟦_⟧⟨+⟩⋊ x y xs ⟦ xs ⟧⇓ i
  ⟦ ⋊⟨∪⟩ x xs ys i ⟧⇓ = ⟦_⟧⋊⟨∪⟩ x xs ys ⟦ xs ⟧⇓ ⟦ ys ⟧⇓ i
  ⟦ 1⋊ xs i ⟧⇓ = ⟦_⟧1⋊ xs ⟦ xs ⟧⇓ i
  ⟦ 0⋊ xs i ⟧⇓ = ⟦_⟧0⋊ xs ⟦ xs ⟧⇓ i
  ⟦ trunc xs ys p q i j ⟧⇓ =
    isOfHLevel→isOfHLevelDep
      {n = 2}
      (λ xs → ⟦_⟧-set {xs})
      ⟦ xs ⟧⇓
      ⟦ ys ⟧⇓
      (cong ⟦_⟧⇓ p)
      (cong ⟦_⟧⇓ q)
      (trunc xs ys p q) i j
open _⇘_ public

record _⇘∥_∥ {a ℓ} (V : Type a) (P : 𝒱 V → Type ℓ) : Type (a ℓ⊔ ℓ ℓ⊔ s) where
  constructor elim-prop
  field
    ∥_∥-prop : ∀ {xs} → isProp (P xs)
    ∥_∥[_] : ∀ x → P [ x ]
    ∥_∥_⋊_⟨_⟩ : ∀ p xs → P xs → P (p ⋊ xs)
    ∥_∥_∪_⟨_∪_⟩ : ∀ xs ys → P xs → P ys → P (xs ∪ ys)
    ∥_∥∅ : P ∅
  private sing = ∥_∥[_]; mult = ∥_∥_⋊_⟨_⟩; join = ∥_∥_∪_⟨_∪_⟩; empt = ∥_∥∅
  ∥_∥⇑ = elim
          (isProp→isSet ∥_∥-prop)
          sing mult join empt
          (λ xs ys pxs pys → toPathP (∥_∥-prop (transport (λ i → P (∪-com xs ys i)) (join xs ys pxs pys)) (join ys xs pys pxs)))
          (λ xs ys zs pxs pys pzs → toPathP (∥_∥-prop (transport (λ i → P (∪-assoc xs ys zs i)) (join (xs ∪ ys) zs (join xs ys pxs pys) pzs)) (join xs (ys ∪ zs) pxs (join ys zs pys pzs) )))
          (λ xs pxs → toPathP (∥_∥-prop (transport (λ i → P (∅∪ xs i)) (join ∅ xs empt pxs)) pxs))
          (λ p q xs pxs → toPathP (∥_∥-prop (transport (λ i → P (⟨*⟩⋊ p q xs i)) (mult (p * q) xs pxs )) ((mult p (q ⋊ xs) (mult q xs pxs))) ))
          (λ p q xs pxs → toPathP (∥_∥-prop (transport (λ i → P (⟨+⟩⋊ p q xs i)) (mult (p + q) xs pxs)) (join (p ⋊ xs) (q ⋊ xs) (mult p xs pxs) (mult q xs pxs))))
          (λ p xs ys pxs pys → toPathP (∥_∥-prop (transport (λ i → P (⋊⟨∪⟩ p xs ys i)) (mult p (xs ∪ ys) (join xs ys pxs pys))) (join (p ⋊ xs) (p ⋊ ys) (mult p xs pxs) (mult p ys pys))))
          (λ xs pxs → toPathP (∥_∥-prop (transport (λ i → P (1⋊ xs i)) (mult 1# xs pxs)) pxs))
          (λ xs pxs → toPathP (∥_∥-prop (transport (λ i → P (0⋊ xs i)) (mult 0# xs pxs)) empt))
  ∥_∥⇓ = ⟦ ∥_∥⇑ ⟧⇓
open _⇘∥_∥ public

record _↘_ {a b} (V : Type a) (B : Type b) : Type (a ℓ⊔ b ℓ⊔ s) where
  constructor rec
  field
    [_]-set : isSet B
    [_][_] : V → B
    [_]_⋊_ : 𝑅 → B → B
    [_]_∪_ : B → B → B
    [_]∅ : B
  private sing = [_][_]; mult = [_]_⋊_; join = [_]_∪_; empt = [_]∅
  field
    [_]-com : ∀ xs ys → join xs ys ≡ join ys xs
    [_]-assoc  : ∀ xs ys zs → join (join xs ys) zs ≡ join xs (join ys zs)
    [_]∅∪ : ∀ xs → join empt xs ≡ xs
    [_]⟨*⟩⋊ : ∀ x y z → mult (x * y) z ≡ mult x (mult y z)
    [_]⟨+⟩⋊ : ∀ x y z → mult (x + y) z ≡ join (mult x z) (mult y z)
    [_]⋊⟨∪⟩ : ∀ x y z → mult x (join y z) ≡ join (mult x y) (mult x z)
    [_]1⋊ : ∀ xs → mult 1# xs ≡ xs
    [_]0⋊ : ∀ xs → mult 0# xs ≡ empt
  [_]⇑ = elim
            [_]-set
            sing (λ p _ → mult p) (λ _ _ → join) empt
            (λ _ _ → [_]-com)
            (λ _ _ _ → [_]-assoc)
            (λ _ → [_]∅∪)
            (λ p q _ → [_]⟨*⟩⋊ p q)
            (λ p q _ → [_]⟨+⟩⋊ p q)
            (λ p _ _ → [_]⋊⟨∪⟩ p)
            (λ _ → [_]1⋊)
            λ _ → [_]0⋊
  [_]↓ = ⟦ [_]⇑ ⟧⇓
open _↘_ public

infixr 0 ⇘-syntax
⇘-syntax = _⇘_
syntax ⇘-syntax A (λ xs → Pxs) = xs ∈𝒱 A ⇒ Pxs

infixr 0 elim-prop-syntax
elim-prop-syntax : ∀ {a p} → (A : Type a) → (𝒱 A → Type p) → Type (s ℓ⊔ a ℓ⊔ p)
elim-prop-syntax = _⇘∥_∥
syntax elim-prop-syntax A (λ xs → Pxs) = xs ∈𝒱 A ⇒∥ Pxs ∥
\end{code}
