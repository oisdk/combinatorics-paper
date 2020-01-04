{-# OPTIONS --cubical --safe #-}

open import Algebra

module Algebra.Construct.Applicative.Monoid {ℓ₁ ℓ₂} (app : Applicative ℓ₁ ℓ₂) (mon : Monoid ℓ₁) where

open import Prelude

open Applicative app
open Monoid mon

open import Path.Reasoning

_⊙_ : 𝐹 𝑆 → 𝐹 𝑆 → 𝐹 𝑆
xs ⊙ ys = map _∙_ xs <*> ys

ε⊙ : ∀ xs → pure ε ⊙ xs ≡ xs
ε⊙ xs =
  pure ε ⊙ xs ≡⟨⟩
  map _∙_ (pure ε) <*> xs ≡⟨ cong (_<*> xs) (pure-homo _∙_ ε) ⟩
  pure (ε ∙_) <*> xs ≡⟨ cong (λ e → pure e <*> xs) (funExt ε∙) ⟩
  pure id <*> xs ≡˘⟨ (λ i → map-ap id i xs) ⟩
  map id xs ≡⟨ (λ i → map-id i xs) ⟩
  xs ∎

⊙ε : ∀ xs → xs ⊙ pure ε ≡ xs
⊙ε xs =
  xs ⊙ pure ε ≡⟨⟩
  (map _∙_ xs) <*> pure ε ≡⟨ <*>-interchange (map _∙_ xs) ε ⟩
  map (_$ ε) (map _∙_ xs) ≡˘⟨ (λ i → map-comp (_$ ε) _∙_ i xs) ⟩
  map (_∙ ε) xs ≡⟨ cong (flip map xs) (funExt ∙ε) ⟩
  map id xs ≡⟨ (λ i → map-id i xs) ⟩
  xs ∎

<*>-comp-map : (u : 𝐹 (B → C)) →
               (v : 𝐹 (A → B)) →
               (w : 𝐹 A) →
               map _∘′_ u <*> v <*> w ≡ u <*> (v <*> w)
<*>-comp-map u v w = cong (λ cu → cu <*> v <*> w) (λ i → map-ap _∘′_ i u) ;
                     <*>-comp u v w

⊙-assoc : ∀ xs ys zs → (xs ⊙ ys) ⊙ zs ≡ xs ⊙ (ys ⊙ zs)
⊙-assoc xs ys zs =
  (xs ⊙ ys) ⊙ zs ≡⟨⟩
  map _∙_ (map _∙_ xs <*> ys) <*> zs ≡⟨ cong (_<*> zs) (λ i → map-ap _∙_ i (map _∙_ xs <*> ys)) ⟩
  pure _∙_ <*> (map _∙_ xs <*> ys) <*> zs ≡˘⟨ cong (_<*> zs) (<*>-comp-map (pure _∙_) (map _∙_ xs) ys ) ⟩
  map _∘′_ (pure _∙_) <*> map _∙_ xs <*> ys <*> zs ≡⟨ cong (λ c → c <*> map _∙_ xs <*> ys <*> zs) (pure-homo _∘′_ _∙_) ⟩
  pure (_∘′_ _∙_) <*> map _∙_ xs <*> ys <*> zs ≡˘⟨ (λ i → map-ap (_∘′_ _∙_) i (map _∙_ xs) <*> ys <*> zs ) ⟩
  map (_∘′_ _∙_) (map _∙_ xs) <*> ys <*> zs ≡˘⟨ (λ i → map-comp (_∘′_ _∙_) _∙_ i xs <*> ys <*> zs) ⟩
  map (λ x y z → (x ∙ y) ∙ z) xs <*> ys <*> zs ≡⟨ (λ i → map (λ x y z → assoc x y z i) xs <*> ys <*> zs ) ⟩
  map (λ x y z → x ∙ (y ∙ z)) xs <*> ys <*> zs ≡⟨⟩
  map ((_$ _∙_) ∘ _∘′_ ∘ _∘′_ ∘ _∙_) xs <*> ys <*> zs ≡⟨ (λ i → map-comp ((_$ _∙_) ∘ _∘′_ ∘ _∘′_) _∙_ i xs <*> ys <*> zs ) ⟩
  map ((_$ _∙_) ∘ _∘′_ ∘ _∘′_) (map _∙_ xs) <*> ys <*> zs ≡⟨ (λ i → map-comp ((_$ _∙_) ∘ _∘′_) _∘′_ i (map _∙_ xs) <*> ys <*> zs ) ⟩
  map ((_$ _∙_) ∘ _∘′_) (map _∘′_ (map _∙_ xs)) <*> ys <*> zs ≡⟨ (λ i → map-comp (_$ _∙_) _∘′_ i (map _∘′_ (map _∙_ xs)) <*> ys <*> zs ) ⟩
  map (_$ _∙_) (map _∘′_ (map _∘′_ (map _∙_ xs))) <*> ys <*> zs ≡˘⟨ cong (λ c → c <*> ys <*> zs) (<*>-interchange (map _∘′_ (map _∘′_ (map _∙_ xs))) _∙_) ⟩
  map _∘′_ (map _∘′_ (map _∙_ xs)) <*> pure _∙_ <*> ys <*> zs ≡⟨ cong (_<*> zs) (<*>-comp-map (map _∘′_ (map _∙_ xs)) (pure _∙_) ys ) ⟩
  map _∘′_ (map _∙_ xs) <*> (pure _∙_ <*> ys) <*> zs ≡˘⟨ (λ i → map _∘′_ (map _∙_ xs) <*> map-ap _∙_ i ys <*> zs ) ⟩
  map _∘′_ (map _∙_ xs) <*> map _∙_ ys <*> zs ≡⟨ <*>-comp-map (map _∙_ xs) (map _∙_ ys) zs ⟩
  (map _∙_ xs) <*> (map _∙_ ys <*> zs) ≡⟨⟩
  xs ⊙ (ys ⊙ zs) ∎
