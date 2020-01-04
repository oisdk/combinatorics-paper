\begin{code}
{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Prelude

module Algebra.Construct.Free.Semimodule.Eliminators {s} (rng : Semiring s) where

open Semiring rng
open import Algebra.Construct.Free.Semimodule.Definition rng
\end{code}
\begin{code}
infixr 0 _⇘_
record _⇘_ {a ℓ} (V : Type a) (P : 𝒱 V → Type ℓ) : Type (a ℓ⊔ ℓ ℓ⊔ s) where
  constructor elim
  field
    ⟦_⟧-set : ∀ {xs} → isSet (P xs)
    ⟦_⟧[] : P []
    ⟦_⟧_∶_,_⟨_⟩ : ∀ x p xs → P xs → P (x ∶ p , xs)
  private z = ⟦_⟧[]; f = ⟦_⟧_∶_,_⟨_⟩
  field
    ⟦_⟧-dup : (∀ x p q xs pxs → PathP (λ i → P (dup x p q xs i))
              (f x p (x ∶ q , xs) (f x q xs pxs)) (f x (p + q) xs pxs))
    ⟦_⟧-com : (∀ x p y q xs pxs → PathP (λ i → P (com x p y q xs i))
              (f x p (y ∶ q , xs) (f y q xs pxs)) (f y q (x ∶ p , xs) (f x p xs pxs)))
    ⟦_⟧-del : (∀ x xs pxs → PathP (λ i → P (del x xs i))
              (f x 0# xs pxs) pxs)
  ⟦_⟧⇓ : (xs : 𝒱 V) → P xs
  ⟦ [] ⟧⇓ = z
  ⟦ x ∶ p , xs ⟧⇓ = f x p xs ⟦ xs ⟧⇓
  ⟦ dup x p q xs i ⟧⇓ = ⟦_⟧-dup x p q xs ⟦ xs ⟧⇓ i
  ⟦ com x p y q xs i ⟧⇓ = ⟦_⟧-com x p y q xs ⟦ xs ⟧⇓ i
  ⟦ del x xs i ⟧⇓ = ⟦_⟧-del x xs ⟦ xs ⟧⇓ i
  ⟦ trunc xs ys p q i j ⟧⇓ =
    isOfHLevel→isOfHLevelDep {n = 2} (λ xs → ⟦_⟧-set {xs})  ⟦ xs ⟧⇓ ⟦ ys ⟧⇓ (cong ⟦_⟧⇓ p) (cong ⟦_⟧⇓ q) (trunc xs ys p q) i j
open _⇘_ public

infixr 0 ⇘-syntax
⇘-syntax = _⇘_
syntax ⇘-syntax A (λ xs → Pxs) = xs ∈𝒱 A ⇒ Pxs

record _⇘∥_∥ {a ℓ} (V : Type a) (P : 𝒱 V → Type ℓ) : Type (a ℓ⊔ ℓ ℓ⊔ s) where
  constructor elim-prop
  field
    ∥_∥-prop : ∀ {xs} → isProp (P xs)
    ∥_∥[] : P []
    ∥_∥_∶_,_⟨_⟩ : ∀ x p xs → P xs → P (x ∶ p , xs)
  private z = ∥_∥[]; f = ∥_∥_∶_,_⟨_⟩
  ∥_∥⇑ = elim
          (isProp→isSet ∥_∥-prop)
          z f
          (λ x p q xs pxs →
            toPathP (∥_∥-prop (transp (λ i → P (dup x p q xs i))
            i0
            (f x p (x ∶ q , xs) (f x q xs pxs))) (f x (p + q) xs pxs) ))
          (λ x p y q xs pxs → toPathP (∥_∥-prop (transp (λ i → P (com x p y q xs i)) i0
            (f x p (y ∶ q , xs) (f y q xs pxs))) (f y q (x ∶ p , xs) (f x p xs pxs))))
            λ x xs pxs → toPathP (∥_∥-prop (transp (λ i → P (del x xs i)) i0 ((f x 0# xs pxs))) pxs)
  ∥_∥⇓ = ⟦ ∥_∥⇑ ⟧⇓

open _⇘∥_∥ public
elim-prop-syntax : ∀ {a p} → (A : Type a) → (𝒱 A → Type p) → Type (s ℓ⊔ a ℓ⊔ p)
elim-prop-syntax = _⇘∥_∥

syntax elim-prop-syntax A (λ xs → Pxs) = xs ∈𝒱 A ⇒∥ Pxs ∥

record _⇘∣_∣ {a p} (A : Type a) (P : 𝒱 A → Type p) : Type (s ℓ⊔ a ℓ⊔ p) where
  constructor elim-to-prop
  field
    ∣_∣[] : P []
    ∣_∣_∶_,_⟨_⟩ : ∀ x p xs → P xs → P (x ∶ p , xs)
  private z = ∣_∣[]; f = ∣_∣_∶_,_⟨_⟩
  open import HITs.PropositionalTruncation.Sugar

  ∣_∣⇑ : xs ∈𝒱 A ⇒∥ ∥ P xs ∥ ∥
  ∣_∣⇑ = elim-prop squash ∣ z ∣ λ x p xs ∣Pxs∣ → f x p xs ∥$∥ ∣Pxs∣
  ∣_∣⇓ = ∥ ∣_∣⇑ ∥⇓

open _⇘∣_∣ public
elim-to-prop-syntax : ∀ {a p} → (A : Type a) → (𝒱 A → Type p) → Type (s ℓ⊔ a ℓ⊔ p)
elim-to-prop-syntax = _⇘∣_∣

syntax elim-to-prop-syntax A (λ xs → Pxs) = xs ∈𝒱 A ⇒∣ Pxs ∣

record _↘_ {a b} (V : Type a) (B : Type b) : Type (a ℓ⊔ b ℓ⊔ s) where
  constructor rec
  field
    [_]-set  : isSet B
    [_]_∶_,_ : V → 𝑅 → B → B
    [_][]    : B
  private f = [_]_∶_,_; z = [_][]
  field
    [_]-dup  : ∀ x p q xs → f x p (f x q xs) ≡ f x (p + q) xs
    [_]-com : ∀ x p y q xs → f x p (f y q xs) ≡ f y q (f x p xs)
    [_]-del : ∀ x xs → f x 0# xs ≡ xs
  [_]⇑ = elim
            [_]-set
            z
            (λ x p _ xs → f x p xs)
            (λ x p q xs → [_]-dup x p q)
            (λ x p y q xs → [_]-com x p y q)
            (λ x xs → [_]-del x)
  [_]↓ = ⟦ [_]⇑ ⟧⇓
open _↘_ public

record ⟦_≡_⟧ {a b} {A : Type a} {B : Type b}
            (h : 𝒱 A → B)
            (xf : A ↘ B)
            : Type (a ℓ⊔ b ℓ⊔ s) where
  constructor elim-univ
  field
    ⟦_≡⟧_∶_,_ : ∀ x p xs → h (x ∶ p , xs) ≡ [ xf ] x ∶ p , h xs
    ⟦_≡⟧[] : h [] ≡ [ xf ][]
  ⟦_≡⟧⇓ : ∀ xs → h xs ≡ [ xf ]↓ xs
  ⟦_≡⟧⇓ = ∥ ≡⇓′ ∥⇓
    where
    ≡⇓′ : xs ∈𝒱 A ⇒∥ h xs ≡ [ xf ]↓ xs ∥
    ∥ ≡⇓′ ∥-prop = [ xf ]-set _ _
    ∥ ≡⇓′ ∥[] = ⟦_≡⟧[]
    ∥ ≡⇓′ ∥ x ∶ p , xs ⟨ P ⟩ = ⟦_≡⟧_∶_,_ x p _ ; cong ([ xf ] x ∶ p ,_) P
open ⟦_≡_⟧ public

record ⟦_⊚_≡_⟧ {a b c} {A : Type a} {B : Type b} {C : Type c}
               (h : B → C)
               (xf : A ↘ B)
               (yf : A ↘ C)
               : Type (a ℓ⊔ b ℓ⊔ c ℓ⊔ s)
    where
  constructor elim-fuse
  field
    ⟦_∘≡⟧_∶_,_ : ∀ x p xs → h ([ xf ] x ∶ p , xs) ≡ [ yf ] x ∶ p , h xs
    ⟦_∘≡⟧[] : h [ xf ][] ≡ [ yf ][]
  ⟦_∘≡⟧⇓ : ∀ xs → h ([ xf ]↓ xs) ≡ [ yf ]↓ xs
  ⟦_∘≡⟧⇓ = ∥ ≡⇓′ ∥⇓
    where
    ≡⇓′ : xs ∈𝒱 A ⇒∥ h ([ xf ]↓ xs) ≡ [ yf ]↓ xs ∥
    ∥ ≡⇓′ ∥-prop = [ yf ]-set _ _
    ∥ ≡⇓′ ∥[] = ⟦_∘≡⟧[]
    ∥ ≡⇓′ ∥ x ∶ p , xs ⟨ P ⟩ = ⟦_∘≡⟧_∶_,_ x p _ ; cong ([ yf ] x ∶ p ,_) P
open ⟦_⊚_≡_⟧ public
\end{code}
