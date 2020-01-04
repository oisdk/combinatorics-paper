\begin{code}
{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Prelude
open import Path.Reasoning

module Algebra.Construct.Free.Semimodule.Operations.Condition {s} (rng : Semiring s) where

open Semiring rng
open import Algebra.Construct.Free.Semimodule.Definition rng
open import Algebra.Construct.Free.Semimodule.Eliminators rng
open import Algebra.Construct.Free.Semimodule.Operations.Union rng
open import Algebra.Construct.Free.Semimodule.Operations.Functor rng

_∣_ : 𝒱 A → (A → 𝑅) → 𝒱 A
_∣_ = λ xs f → [ ∣′ f ]↓ xs
  where
  ∣′_ : (A → 𝑅) → A ↘ 𝒱 A
  [ ∣′ f ][] = []
  [ ∣′ f ] x ∶ p , xs = x ∶ f x * p , xs
  [ ∣′ f ]-set = trunc
  [ ∣′ f ]-com x p y q = com x (f x * p) y (f y * q)
  [ ∣′ f ]-dup x p q xs =
    x ∶ f x * p , x ∶ f x * q , xs ≡⟨ dup x _ _ xs ⟩
    x ∶ (f x * p + f x * q) , xs ≡˘⟨ cong (x ∶_, xs) (*⟨+⟩ (f x) p q) ⟩
    x ∶ f x * (p + q) , xs ∎
  [ ∣′ f ]-del x xs =
    x ∶ f x * 0# , xs ≡⟨ cong (x ∶_, xs) (*0 (f x)) ⟩
    x ∶ 0# , xs ≡⟨ del x xs ⟩
    xs ∎

infixl 7 _⋊_
_⋊_ : 𝑅 → 𝒱 A → 𝒱 A
_⋊_ = λ p → [ p ⋊′ ]↓
  where
  _⋊′ : 𝑅 → A ↘ 𝒱 A
  [ p ⋊′ ]-set = trunc
  [ p ⋊′ ][] = []
  [ p ⋊′ ] x ∶ q , xs = x ∶ p * q , xs
  [ p ⋊′ ]-com x q y r xs = com x (p * q) y (p * r) xs
  [ p ⋊′ ]-dup x q r xs =
    x ∶ p * q , x ∶ p * r , xs ≡⟨ dup x (p * q) (p * r) xs ⟩
    x ∶ p * q + p * r , xs     ≡˘⟨ cong (x ∶_, xs) (*⟨+⟩ p q r) ⟩
    x ∶ p * (q + r) , xs       ∎
  [ p ⋊′ ]-del x xs =
    x ∶ p * 0# , xs ≡⟨ cong (x ∶_, xs) (*0 p) ⟩
    x ∶ 0# , xs     ≡⟨ del x xs ⟩
    xs              ∎

⋊-distribʳ : ∀ p q → (xs : 𝒱 A) → p ⋊ xs ∪ q ⋊ xs ≡ (p + q) ⋊ xs
⋊-distribʳ = λ p q → ∥ ⋊-distribʳ′ p q ∥⇓
  module JDistrib where
  ⋊-distribʳ′ : ∀ p q → xs ∈𝒱 A ⇒∥ p ⋊ xs ∪ q ⋊ xs ≡ (p + q) ⋊ xs ∥
  ∥ ⋊-distribʳ′ p q ∥-prop = trunc _ _
  ∥ ⋊-distribʳ′ p q ∥[] = refl
  ∥ ⋊-distribʳ′ p q ∥ x ∶ r , xs ⟨ P ⟩ =
    p ⋊ (x ∶ r , xs) ∪ q ⋊ (x ∶ r , xs)   ≡⟨ ∪-cons (q * r) x (p ⋊ (x ∶ r , xs)) (q ⋊ xs)  ⟩
    x ∶ q * r , p ⋊ (x ∶ r , xs) ∪ q ⋊ xs ≡⟨ cong (_∪ q ⋊ xs) (dup x (q * r) (p * r) (p ⋊ xs)) ⟩
    x ∶ q * r + p * r  , p ⋊ xs ∪ q ⋊ xs   ≡˘⟨ cong (x ∶_, (p ⋊ xs ∪ q ⋊ xs)) (⟨+⟩* q p r) ⟩
    x ∶ (q + p) * r , p ⋊ xs ∪ q ⋊ xs     ≡⟨ cong ( x ∶ (q + p) * r ,_) P ⟩
    x ∶ (q + p) * r , (p + q) ⋊ xs                ≡⟨ cong (λ pq → x ∶ pq * r , (p + q) ⋊ xs) (+-comm q p) ⟩
    x ∶ (p + q) * r , (p + q) ⋊ xs                ≡⟨⟩
    (p + q) ⋊ (x ∶ r , xs) ∎

⋊-distribˡ : ∀ p → (xs ys : 𝒱 A) → p ⋊ xs ∪ p ⋊ ys ≡ p ⋊ (xs ∪ ys)
⋊-distribˡ = λ p xs ys → ∥ ⋊-distribˡ′ p ys ∥⇓ xs
  module JDistribL where
  ⋊-distribˡ′ : ∀ p ys → xs ∈𝒱 A ⇒∥ p ⋊ xs ∪ p ⋊ ys ≡ p ⋊ (xs ∪ ys) ∥
  ∥ ⋊-distribˡ′ p ys ∥-prop = trunc _ _
  ∥ ⋊-distribˡ′ p ys ∥[] = refl
  ∥ ⋊-distribˡ′ p ys ∥ x ∶ q , xs ⟨ P ⟩ =
    p ⋊ (x ∶ q , xs) ∪ p ⋊ ys ≡⟨⟩
    x ∶ p * q , p ⋊ xs ∪ p ⋊ ys ≡⟨ cong (x ∶ p * q ,_) P ⟩
    x ∶ p * q , p ⋊ (xs ∪ ys) ≡⟨⟩
    p ⋊ ((x ∶ q , xs) ∪ ys) ∎

0⋊ : (xs : 𝒱 A) → 0# ⋊ xs ≡ []
0⋊ = ∥ 0⋊′ ∥⇓
  where
  0⋊′ : xs ∈𝒱 A ⇒∥ 0# ⋊ xs ≡ [] ∥
  ∥ 0⋊′ ∥-prop = trunc _ _
  ∥ 0⋊′ ∥[] = refl
  ∥ 0⋊′ ∥ x ∶ p , xs ⟨ P ⟩ =
    0# ⋊ (x ∶ p , xs)    ≡⟨⟩
    x ∶ 0# * p , 0# ⋊ xs ≡⟨ cong (x ∶_, 0# ⋊ xs) (0* p) ⟩
    x ∶ 0# , 0# ⋊ xs     ≡⟨ del x (0# ⋊ xs) ⟩
    0# ⋊ xs              ≡⟨ P ⟩
    [] ∎

1⋊ : (xs : 𝒱 A) → 1# ⋊ xs ≡ xs
1⋊ = ∥ 1⋊′ ∥⇓
  where
  1⋊′ : xs ∈𝒱 A ⇒∥ 1# ⋊ xs ≡ xs ∥
  ∥ 1⋊′ ∥-prop = trunc _ _
  ∥ 1⋊′ ∥[] = refl
  ∥ 1⋊′ ∥ x ∶ p , xs ⟨ P ⟩ =
    1# ⋊ (x ∶ p , xs) ≡⟨⟩
    x ∶ 1# * p , 1# ⋊ xs ≡⟨ cong (x ∶_, 1# ⋊ xs) (1* p) ⟩
    x ∶ p , 1# ⋊ xs ≡⟨ cong (x ∶ p ,_) P ⟩
    x ∶ p , xs ∎

*-assoc-⋊ : ∀ p q (xs : 𝒱 A) → (p * q) ⋊ xs ≡ p ⋊ (q ⋊ xs)
*-assoc-⋊ = λ p q → ∥ *-assoc-⋊′ p q ∥⇓
  where
  *-assoc-⋊′ : ∀ p q → xs ∈𝒱 A ⇒∥ (p * q) ⋊ xs ≡ p ⋊ (q ⋊ xs) ∥
  ∥ *-assoc-⋊′ p q ∥-prop = trunc _ _
  ∥ *-assoc-⋊′ p q ∥[] = refl
  ∥ *-assoc-⋊′ p q ∥ x ∶ r , xs ⟨ P ⟩ =
    p * q ⋊ (x ∶ r , xs) ≡⟨⟩
    x ∶ p * q * r , (p * q ⋊ xs) ≡⟨ cong (x ∶_, (p * q ⋊ xs)) (*-assoc p q r) ⟩
    x ∶ p * (q * r) , (p * q ⋊ xs) ≡⟨ cong (x ∶ p * (q * r) ,_) P ⟩
    x ∶ p * (q * r) , (p ⋊ (q ⋊ xs)) ≡⟨⟩
    p ⋊ (q ⋊ (x ∶ r , xs)) ∎

map-comm-⋊ : ∀ p (f : A → B) (xs : 𝒱 A) → map f (p ⋊ xs) ≡ p ⋊ map f xs
map-comm-⋊ = λ p f → ∥ map-comm-⋊′ p f ∥⇓
  where
  map-comm-⋊′ : ∀ p (f : A → B) → xs ∈𝒱 A ⇒∥ map f (p ⋊ xs) ≡ p ⋊ map f xs ∥
  ∥ map-comm-⋊′ p f ∥-prop = trunc _ _
  ∥ map-comm-⋊′ p f ∥[] = refl
  ∥ map-comm-⋊′ p f ∥ x ∶ q , xs ⟨ P ⟩ =
    map f (p ⋊ (x ∶ q , xs)) ≡⟨⟩
    f x ∶ p * q , map f (p ⋊ xs) ≡⟨ cong (f x ∶ p * q ,_) P ⟩
    f x ∶ p * q , p ⋊ map f xs ≡⟨⟩
    p ⋊ map f (x ∶ q , xs) ∎

leftSemimodule : ∀ {a} → Type a → LeftSemimodule _ _
leftSemimodule A = record
  { semiring = rng
  ; semimodule = ∪-commutativeMonoid A
  ; _⋊_ = _⋊_
  ; ⟨*⟩⋊ = *-assoc-⋊
  ; ⟨+⟩⋊ = λ x y z →  sym (⋊-distribʳ x y z)
  ; ⋊⟨∪⟩ = λ x y z → sym (⋊-distribˡ x y z)
  ; 1⋊ = 1⋊
  ; 0⋊ = 0⋊
  }
\end{code}
