{-# OPTIONS --cubical --safe #-}

module Data.Product where

open import Agda.Builtin.Sigma
  using (Σ; _,_; fst; snd)
  public
open import Level

∃ : ∀ {a b} {A : Type a} (B : A → Type b) → Type (a ℓ⊔ b)
∃ {A = A} = Σ A

infixr 3 ∃-syntax
∃-syntax : ∀ {a b} {A : Type a} (B : A → Type b) → Type (a ℓ⊔ b)
∃-syntax = ∃

syntax ∃-syntax (λ x → e) = ∃[ x ] e

infixr 3 Σ∈-syntax
Σ∈-syntax : (A : Type a) (B : A → Type b) → Type (a ℓ⊔ b)
Σ∈-syntax = Σ

syntax Σ∈-syntax t (λ x → e) = Σ[ x ∈ t ] e

infixr 4 _×_
_×_ : (A : Type a) → (B : Type b) → Type (a ℓ⊔ b)
A × B = Σ A λ _ → B

curry : ∀ {A : Type a} {B : A → Type b} {C : Σ A B → Type c} →
          ((p : Σ A B) → C p) →
          ((x : A) → (y : B x) → C (x , y))
curry f x y = f (x , y)

uncurry : ∀ {A : Type a} {B : A → Type b} {C : Σ A B → Type c} →
            ((x : A) → (y : B x) → C (x , y)) →
            ((p : Σ A B) → C p)
uncurry f (x , y) = f x y

-- curried : ∀ {A : Type a} {B : A → Type b} {C : Σ A B → Type c}
--         → ((p : Σ A B) → C p) ⇔ ((x : A) → (y : B x) → C (x , y))
-- curried .fun = curry
-- curried .inv = uncurry
-- curried .leftInv  f i (x , y) = f (x , y)
-- curried .rightInv f i x y = f x y

swap : A × B → B × A
swap (x , y) = y , x

curry′ : (A × B → C) → (A → B → C)
curry′ = curry

uncurry′ : (A → B → C) → (A × B → C)
uncurry′ = uncurry

map-Σ : ∀ {p q} {P : A → Set p} {Q : B → Set q} →
        (f : A → B) → (∀ {x} → P x → Q (f x)) →
        Σ A P → Σ B Q
map-Σ f g (x , y) = (f x , g y)

map₁ : (A → B) → A × C → B × C
map₁ f = map-Σ f (λ x → x)

map₁-Σ : ∀ {A : Set a} {B : Set b} {C : B → Set b}
       → (f : A → B) → Σ A (λ x → C (f x)) → Σ B C
map₁-Σ f (x , y) = f x , y

map₂ : ∀ {A : Set a} {B : A → Set b} {C : A → Set c} →
        (∀ {x} → B x → C x) → Σ A B → Σ A C
map₂ f = map-Σ (λ x → x) f

zip-Σ : ∀ {p} {q} {r} {P : A → Set p} {Q : B → Set q} {R : C → Set r} →
        (_∙_ : A → B → C) →
        (∀ {x y} → P x → Q y → R (x ∙ y)) →
        Σ A P → Σ B Q → Σ C R
zip-Σ _∙_ _∘_ (a , p) (b , q) = ((a ∙ b) , (p ∘ q))
