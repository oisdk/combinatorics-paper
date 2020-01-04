\begin{code}
{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Prelude
open import Path.Reasoning

module Algebra.Construct.Free.Semimodule.Operations.Functor {s} (rng : Semiring s) where

open Semiring rng
open import Algebra.Construct.Free.Semimodule.Definition rng
open import Algebra.Construct.Free.Semimodule.Eliminators rng
open import Algebra.Construct.Free.Semimodule.Operations.Union rng

map′ : ∀ {a b} {A : Type a} {B : Type b} → (A → B) → A ↘ 𝒱 B
[ map′ f ] x ∶ p , xs = f x ∶ p , xs
[ map′ f ][] = []
[ map′ f ]-set = trunc
[ map′ f ]-dup x = dup (f x)
[ map′ f ]-com x p y = com (f x) p (f y)
[ map′ f ]-del x = del (f x)

map : (A → B) → 𝒱 A → 𝒱 B
map f = [ map′ f ]↓

map-id : (xs : 𝒱 A) → map id xs ≡ xs
map-id = ∥ map-id′ ∥⇓
  where
  map-id′ : xs ∈𝒱 A ⇒∥ map id xs ≡ xs ∥
  ∥ map-id′ ∥-prop = trunc _ _
  ∥ map-id′ ∥[] = refl
  ∥ map-id′ ∥ x ∶ p , xs ⟨ P ⟩ = cong (x ∶ p ,_) P

map-distrib : (f : A → B) (xs ys : 𝒱 A) → map f (xs ∪ ys) ≡ map f xs ∪ map f ys
map-distrib = λ f xs ys → ∥ map-distrib′ f ys ∥⇓ xs
  where
  map-distrib′ : (f : A → B) (ys : 𝒱 A) → xs ∈𝒱 A ⇒∥ map f (xs ∪ ys) ≡ map f xs ∪ map f ys ∥
  ∥ map-distrib′ f ys ∥-prop = trunc _ _
  ∥ map-distrib′ f ys ∥[] = refl
  ∥ map-distrib′ f ys ∥ x ∶ p , xs ⟨ P ⟩ =
    map f ((x ∶ p , xs) ∪ ys) ≡⟨⟩
    map f (x ∶ p , (xs ∪ ys)) ≡⟨⟩
    f x ∶ p , map f (xs ∪ ys) ≡⟨ cong (f x ∶ p ,_) P ⟩
    map f (x ∶ p , xs) ∪ map f ys ∎

map-comp : (f : B → C) (g : A → B) (xs : 𝒱 A) → map f (map g xs) ≡ map (f ∘′ g) xs
map-comp = λ f g → ⟦ map-comp′ f g ∘≡⟧⇓
  where
  map-comp′ : (f : B → C) (g : A → B) → ⟦ (map f) ⊚ (map′ g) ≡ map′ (f ∘′ g) ⟧
  ⟦ map-comp′ f g ∘≡⟧[] = refl
  ⟦ map-comp′ f g ∘≡⟧ x ∶ p , xs = refl

functor : ∀ {ℓ} → Functor ℓ (s ℓ⊔ ℓ)
functor = record
  { 𝐹 = 𝒱
  ; map = map
  ; map-id = funExt map-id
  ; map-comp = λ f g → sym (funExt (map-comp f g))
  }
\end{code}
