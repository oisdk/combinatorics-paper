\begin{code}
{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Prelude

module Algebra.Construct.Free.Semimodule.Operations.Union {s} (rng : Semiring s) where

open Semiring rng
open import Algebra.Construct.Free.Semimodule.Definition rng
open import Algebra.Construct.Free.Semimodule.Eliminators rng

∪′_ : 𝒱 A → A ↘ 𝒱 A
[ ∪′ ys ] x ∶ p , xs  = x ∶ p , xs
[ ∪′ ys ][]           = ys
[ ∪′ ys ]-set  = trunc
[ ∪′ ys ]-dup  = dup
[ ∪′ ys ]-com  = com
[ ∪′ ys ]-del  = del

infixr 5 _∪_
_∪_ : 𝒱 A  → 𝒱 A  → 𝒱 A
xs ∪ ys = [ ∪′ ys ]↓ xs

∪-assoc  : (xs ys zs : 𝒱 A )
  → xs ∪ (ys ∪ zs) ≡ (xs ∪ ys) ∪ zs
∪-assoc = λ xs ys zs → ∥ ∪-assoc′ ys zs ∥⇓ xs
  where
  ∪-assoc′ : ∀ ys zs →
    xs ∈𝒱 A ⇒∥ xs ∪ (ys ∪ zs) ≡ (xs ∪ ys) ∪ zs ∥
  ∥ ∪-assoc′ ys zs ∥-prop = trunc _ _
  ∥ ∪-assoc′ ys zs ∥[] = refl
  ∥ ∪-assoc′ ys zs ∥ x ∶ p , xs ⟨ P ⟩ =
    cong (x ∶ p ,_) P

∪-cons : ∀ p (x : A) xs ys → xs ∪ x ∶ p , ys ≡ x ∶ p , xs ∪ ys
∪-cons = λ p x xs ys → ∥ ∪-cons′ p x ys ∥⇓ xs
  where
  ∪-cons′ : ∀ p x ys → xs ∈𝒱 A ⇒∥ xs ∪ x ∶ p , ys ≡ x ∶ p , xs ∪ ys ∥
  ∥ ∪-cons′ p x ys ∥-prop = trunc _ _
  ∥ ∪-cons′ p x ys ∥[] = refl
  ∥ ∪-cons′ p x ys ∥ y ∶ r , xs ⟨ P ⟩ = cong (y ∶ r ,_) P ; com y r x p (xs ∪ ys)

∪-idʳ : (xs : 𝒱 A ) → xs ∪ [] ≡ xs
∪-idʳ = ∥ ∪-idʳ′ ∥⇓
  where
  ∪-idʳ′ : xs ∈𝒱 A ⇒∥ xs ∪ [] ≡ xs ∥
  ∥ ∪-idʳ′ ∥-prop = trunc _ _
  ∥ ∪-idʳ′ ∥[] = refl
  ∥ ∪-idʳ′ ∥ x ∶ p , xs ⟨ P ⟩ = cong (x ∶ p ,_) P

∪-comm : (xs ys : 𝒱 A ) → xs ∪ ys ≡ ys ∪ xs
∪-comm = λ xs ys → ∥ ∪-comm′ ys ∥⇓ xs
  where
  ∪-comm′ : ∀ ys → xs ∈𝒱 A ⇒∥ xs ∪ ys ≡ ys ∪ xs ∥
  ∥ ∪-comm′ ys ∥-prop = trunc _ _
  ∥ ∪-comm′ ys ∥[] = sym (∪-idʳ ys)
  ∥ ∪-comm′ ys ∥ x ∶ p , xs ⟨ P ⟩ = cong (x ∶ p ,_) P ; sym (∪-cons p x ys xs)

∪-commutativeMonoid : ∀ {a} → Type a → CommutativeMonoid _
∪-commutativeMonoid A = record
  { monoid = record
    { _∙_ = _∪_ {A = A}
    ; assoc = λ xs ys zs → sym (∪-assoc xs ys zs)
    ; ε = []
    ; ε∙ = λ xs → refl
    ; ∙ε = ∪-idʳ
    }
  ; comm = ∪-comm
  }
\end{code}
