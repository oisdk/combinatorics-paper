\begin{code}
{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Prelude
open import Path.Reasoning

module Algebra.Construct.Free.Semimodule.Operations.Applicative {s} (rng : Semiring s) where

open Semiring rng
open import Algebra.Construct.Free.Semimodule.Definition rng
open import Algebra.Construct.Free.Semimodule.Eliminators rng
open import Algebra.Construct.Free.Semimodule.Operations.Functor rng
open import Algebra.Construct.Free.Semimodule.Operations.Condition rng
open import Algebra.Construct.Free.Semimodule.Operations.Union rng

pure : A → 𝒱 A
infixl 5 _<*>_
_<*>_ : 𝒱 (A → B) → 𝒱 A → 𝒱 B
pure-map : ∀ (f : A → B) (xs : 𝒱 A) → (pure f <*> xs) ≡ map f xs
<*>-idˡ : ∀ (x : 𝒱 A) → (pure id <*> x) ≡ x
<*>-homo : ∀ (f : A → B) (x : A) → (pure f <*> pure x) ≡ pure (f x)
<*>-interchange : (fs : 𝒱 (A → B)) (x : A) → (fs <*> pure x) ≡ (pure (_$ x) <*> fs)
<*>-distribʳ : (xs ys : 𝒱 (A → B)) (zs : 𝒱 A) → ((xs ∪ ys) <*> zs) ≡ (xs <*> zs) ∪ (ys <*> zs)
<*>-distribˡ : (xs : 𝒱 (A → B)) (ys zs : 𝒱 A) → (xs <*> (ys ∪ zs)) ≡ (xs <*> ys) ∪ (xs <*> zs)
⋊-distrib-<*> : ∀ p (xs : 𝒱 (A → B)) (ys : 𝒱 A) → p ⋊ xs <*> ys ≡ p ⋊ (xs <*> ys)
map-<*> : ∀ (f : B → C) (xs : 𝒱 (A → B)) (ys : 𝒱 A) → map f (xs <*> ys) ≡ map (f ∘′_) xs <*> ys
<*>-comp : (xs : 𝒱 (B → C)) (ys : 𝒱 (A → B)) (zs : 𝒱 A)
         → (pure _∘′_ <*> xs <*> ys <*> zs) ≡ xs <*> (ys <*> zs)

pure x = x ∶ 1# , []

_<*>_ = λ fs xs → [ <*>′ xs ]↓ fs
  where
  <*>′_ : (xs : 𝒱 A) → (A → B) ↘ 𝒱 B
  [ <*>′ xs ][] = []
  [ <*>′ xs ] f ∶ p , fs = p ⋊ map f xs ∪ fs
  [ <*>′ xs ]-set = trunc
  [ <*>′ xs ]-del f fs = cong (_∪ fs) (0⋊ (map f xs))
  [ <*>′ xs ]-dup f p q fs =
    p ⋊ map f xs ∪ q ⋊ map f xs ∪ fs ≡⟨ ∪-assoc (p ⋊ map f xs) (q ⋊ map f xs) fs ⟩
    (p ⋊ map f xs ∪ q ⋊ map f xs) ∪ fs ≡⟨ cong (_∪ fs) (⋊-distribʳ p q (map f xs)) ⟩
    (p + q) ⋊ map f xs ∪ fs ∎
  [ <*>′ xs ]-com f p g q fs =
    p ⋊ (map f xs) ∪ q ⋊ (map g xs) ∪ fs   ≡⟨ ∪-assoc (p ⋊ map f xs) (q ⋊ map g xs) fs ⟩
    (p ⋊ (map f xs) ∪ q ⋊ (map g xs)) ∪ fs ≡⟨ cong (_∪ fs) (∪-comm (p ⋊ map f xs) (q ⋊ map g xs)) ⟩
    (q ⋊ (map g xs) ∪ p ⋊ (map f xs)) ∪ fs ≡˘⟨ ∪-assoc (q ⋊ map g xs) (p ⋊ map f xs) fs ⟩
    q ⋊ (map g xs) ∪ p ⋊ (map f xs) ∪ fs ∎

pure-map = λ f xs → ⟦ pure-map′ f ≡⟧⇓ xs
  where
  pure-map′ : (f : A → B) → ⟦ (pure f <*>_) ≡ map′ f ⟧
  ⟦ pure-map′ f ≡⟧[] = refl
  ⟦ pure-map′ f ≡⟧ x ∶ p , xs =
    pure f <*> (x ∶ p , xs) ≡⟨⟩
    1# ⋊ map f (x ∶ p , xs) ∪ [] ≡⟨⟩
    f x ∶ 1# * p , (pure f <*> xs) ≡⟨ cong (λ p′ → f x ∶ p′ , (pure f <*> xs)) (1* p) ⟩
    f x ∶ p , (pure f <*> xs) ≡⟨⟩
    [ map′ f ] x ∶ p , (pure f <*> xs) ∎

<*>-idˡ x = pure-map id x ; map-id x

<*>-homo f x =
  pure f <*> pure x ≡⟨ pure-map f (pure x) ⟩
  map f (pure x) ≡⟨⟩
  pure (f x) ∎

<*>-interchange = λ fs x → ∥ <*>-interchange′ x ∥⇓ fs
  where
  <*>-interchange′ : (x : A) → fs ∈𝒱 (A → B) ⇒∥ fs <*> pure x ≡ pure (_$ x) <*> fs ∥
  ∥ <*>-interchange′ x ∥-prop = trunc _ _
  ∥ <*>-interchange′ x ∥[] = refl
  ∥ <*>-interchange′ x ∥ f ∶ p , fs ⟨ P ⟩ =
    ((f ∶ p , fs) <*> pure x) ≡⟨⟩
    f x ∶ p * 1# , (fs <*> pure x) ≡⟨ cong (f x ∶_, (fs <*> pure x)) (*1 p) ⟩
    f x ∶ p , (fs <*> pure x) ≡˘⟨ cong (f x ∶_, (fs <*> pure x)) (1* p) ⟩
    f x ∶ 1# * p , (fs <*> pure x) ≡⟨  cong (f x ∶ 1# * p ,_) P ⟩
    f x ∶ 1# * p , (pure (_$ x) <*> fs) ≡⟨⟩
    (pure (_$ x) <*> (f ∶ p , fs)) ∎

<*>-distribʳ = λ xs ys zs → ∥ <*>-distribʳ′ ys zs ∥⇓ xs
  where
  <*>-distribʳ′ : ∀ ys zs → xs ∈𝒱 (A → B) ⇒∥ ((xs ∪ ys) <*> zs) ≡ (xs <*> zs) ∪ (ys <*> zs) ∥
  ∥ <*>-distribʳ′ ys zs ∥-prop = trunc _ _
  ∥ <*>-distribʳ′ ys zs ∥[] = refl
  ∥ <*>-distribʳ′ ys zs ∥ x ∶ p , xs ⟨ P ⟩ =
    ((x ∶ p , xs) ∪ ys) <*> zs ≡⟨⟩
    (x ∶ p , (xs ∪ ys)) <*> zs ≡⟨⟩
    p ⋊ map x zs ∪ ((xs ∪ ys) <*> zs) ≡⟨ cong (p ⋊ map x zs ∪_) P ⟩
    p ⋊ map x zs ∪ ((xs <*> zs) ∪ (ys <*> zs)) ≡⟨ ∪-assoc (p ⋊ map x zs) (xs <*> zs) (ys <*> zs) ⟩
    (p ⋊ map x zs ∪ (xs <*> zs)) ∪ (ys <*> zs) ≡⟨⟩
    ((x ∶ p , xs) <*> zs) ∪ (ys <*> zs) ∎

    -- ((x ∶ p , xs) ∪ ys) <*> zs ≡⟨⟩
    -- (x ∶ p , (xs ∪ ys)) <*> zs ≡⟨⟩
    -- p ⋊ map x zs ∪ ((xs ∪ ys) <*> zs) ≡⟨ cong (p ⋊ map x zs ∪_) P ⟩
    -- p ⋊ map x zs ∪ ((xs <*> zs) ∪ (ys <*> zs)) ≡⟨ ∪-assoc (p ⋊ map x zs) (xs <*> zs) (ys <*> zs) ⟩
    -- (p ⋊ map x zs ∪ (xs <*> zs)) ∪ (ys <*> zs) ≡⟨⟩
    -- ((x ∶ p , xs) <*> zs) ∪ (ys <*> zs) ∎

⋊-distrib-<*> = λ p xs ys → ∥ ⋊-distrib-<*>′ p ys ∥⇓ xs
  where
  ⋊-distrib-<*>′ : ∀ p (ys : 𝒱 A) → xs ∈𝒱 (A → B) ⇒∥ p ⋊ xs <*> ys ≡ p ⋊ (xs <*> ys) ∥
  ∥ ⋊-distrib-<*>′ p ys ∥-prop = trunc _ _
  ∥ ⋊-distrib-<*>′ p ys ∥[] = refl
  ∥ ⋊-distrib-<*>′ p ys ∥ x ∶ q , xs ⟨ P ⟩ =
    p ⋊ (x ∶ q , xs) <*> ys ≡⟨⟩
    p * q ⋊ map x ys ∪ (p ⋊ xs <*> ys) ≡⟨ cong (p * q ⋊ (map x ys) ∪_) P ⟩
    p * q ⋊ map x ys ∪ (p ⋊ (xs <*> ys)) ≡⟨ cong (_∪ p ⋊ (xs <*> ys)) (*-assoc-⋊ p q (map x ys)) ⟩
    p ⋊ (q ⋊ map x ys) ∪ p ⋊ (xs <*> ys) ≡⟨ ⋊-distribˡ p (q ⋊ map x ys) (xs <*> ys)  ⟩
    p ⋊ (q ⋊ map x ys ∪ (xs <*> ys)) ≡⟨⟩
    p ⋊ ((x ∶ q , xs) <*> ys) ≡⟨⟩
    p ⋊ (q ⋊ map x ys ∪ (xs <*> ys)) ∎

map-<*> = λ f xs ys → ∥ map-<*>′ f ys ∥⇓ xs
  where
  map-<*>′ : ∀ (f : B → C)  (ys : 𝒱 A) → xs ∈𝒱 (A → B) ⇒∥ map f (xs <*> ys) ≡ map (f ∘′_) xs <*> ys ∥
  ∥ map-<*>′ f ys ∥-prop = trunc _ _
  ∥ map-<*>′ f ys ∥[] = refl
  ∥ map-<*>′ f ys ∥ x ∶ p , xs ⟨ P ⟩ =
    map f ((x ∶ p , xs) <*> ys) ≡⟨⟩
    map f (p ⋊ map x ys ∪ (xs <*> ys)) ≡⟨ map-distrib f (p ⋊ map x ys) (xs <*> ys) ⟩
    map f (p ⋊ map x ys) ∪ map f (xs <*> ys) ≡⟨ cong (_∪ map f (xs <*> ys)) (map-comm-⋊ p f (map x ys)) ⟩
    p ⋊ map f (map x ys) ∪ map f (xs <*> ys) ≡⟨ cong (λ fg → p ⋊ fg ∪ map f (xs <*> ys)) (map-comp f x ys) ⟩
    p ⋊ map (f ∘′ x) ys ∪ map f (xs <*> ys) ≡⟨ cong (p ⋊ map (f ∘′ x) ys ∪_) P ⟩
    p ⋊ map (f ∘′ x) ys ∪ (map (f ∘′_) xs <*> ys) ≡⟨⟩
    ((f ∘′ x) ∶ p , map (f ∘′_) xs) <*> ys ≡⟨⟩
    map (f ∘′_) (x ∶ p , xs) <*> ys ∎

<*>-comp = λ xs ys zs →  ∥ <*>-comp′ ys zs ∥⇓ xs
  where
  <*>-comp′ : (ys : 𝒱 (A → B)) (zs : 𝒱 A) → xs ∈𝒱 (B → C) ⇒∥ (pure _∘′_ <*> xs <*> ys <*> zs) ≡ xs <*> (ys <*> zs) ∥
  ∥ <*>-comp′ ys zs ∥-prop = trunc _ _
  ∥ <*>-comp′ ys zs ∥[] = refl
  ∥ <*>-comp′ ys zs ∥ x ∶ p , xs ⟨ P ⟩ =
    pure _∘′_ <*> (x ∶ p , xs) <*> ys <*> zs ≡⟨ cong (λ xs′ → xs′ <*> ys <*> zs) (pure-map _∘′_ (x ∶ p , xs)) ⟩
    map _∘′_ (x ∶ p , xs) <*> ys <*> zs ≡⟨⟩
    (p ⋊ map (x ∘′_ ) ys ∪ (map _∘′_ xs <*> ys)) <*> zs ≡⟨ <*>-distribʳ (p ⋊ map (x ∘′_) ys) (map _∘′_ xs <*> ys) zs ⟩
    (p ⋊ map (x ∘′_ ) ys <*> zs) ∪ (map _∘′_ xs <*> ys <*> zs) ≡˘⟨ cong (λ xs′ → (p ⋊ map (x ∘′_ ) ys <*> zs) ∪ (xs′ <*> ys <*> zs)) (pure-map _∘′_ xs)  ⟩
    (p ⋊ map (x ∘′_ ) ys <*> zs) ∪ (pure _∘′_ <*> xs <*> ys <*> zs) ≡⟨ cong ((p ⋊ map (x ∘′_) ys <*> zs) ∪_) P ⟩
    (p ⋊ map (x ∘′_ ) ys <*> zs) ∪ (xs <*> (ys <*> zs)) ≡⟨ cong (_∪ (xs <*> (ys <*> zs))) (⋊-distrib-<*> p (map (x ∘′_) ys) zs) ⟩
    (p ⋊ (map (x ∘′_ ) ys <*> zs)) ∪ (xs <*> (ys <*> zs)) ≡˘⟨ cong (λ fs → (p ⋊ fs) ∪ (xs <*> (ys <*> zs))) (map-<*> x ys zs) ⟩
    (p ⋊ map x (ys <*> zs)) ∪ (xs <*> (ys <*> zs)) ≡⟨⟩
    (x ∶ p , xs) <*> (ys <*> zs) ∎

applicative : ∀ {ℓ} → Applicative ℓ (s ℓ⊔ ℓ)
applicative = record
  { functor = functor
  ; pure = pure
  ; _<*>_ = _<*>_
  ; map-ap = λ f → sym (funExt (pure-map f))
  ; pure-homo = λ f x → refl
  ; <*>-interchange = λ f x → <*>-interchange f x ; pure-map _ f
  ; <*>-comp = <*>-comp
  }

<*>-distribˡ xs ys zs = ∥ <*>-distribˡ′ ys zs ∥⇓ xs
  where
  <*>-distribˡ′ : ∀ ys zs → xs ∈𝒱 (A → B) ⇒∥ (xs <*> (ys ∪ zs)) ≡ (xs <*> ys) ∪ (xs <*> zs) ∥
  ∥ <*>-distribˡ′ ys zs ∥-prop = trunc _ _
  ∥ <*>-distribˡ′ ys zs ∥[] = refl
  ∥ <*>-distribˡ′ ys zs ∥ x ∶ p , xs ⟨ P ⟩ =
    (x ∶ p , xs) <*> (ys ∪ zs) ≡⟨⟩
    (p ⋊ (map x (ys ∪ zs))) ∪ (xs <*> (ys ∪ zs)) ≡⟨ cong ((p ⋊ (map x (ys ∪ zs))) ∪_) P ⟩
    (p ⋊ (map x (ys ∪ zs))) ∪ ((xs <*> ys) ∪ (xs <*> zs)) ≡⟨ cong (_∪ ((xs <*> ys) ∪ (xs <*> zs))) (cong (p ⋊_) (map-distrib x ys zs)) ⟩
    (p ⋊ (map x ys ∪ map x zs)) ∪ ((xs <*> ys) ∪ (xs <*> zs)) ≡˘⟨ cong (_∪ ((xs <*> ys) ∪ (xs <*> zs))) (⋊-distribˡ p (map x ys) (map x zs)) ⟩
    ((p ⋊ map x ys) ∪ (p ⋊ map x zs)) ∪ ((xs <*> ys) ∪ (xs <*> zs)) ≡⟨ ∪-assoc ((p ⋊ map x ys) ∪ (p ⋊ map x zs)) (xs <*> ys) (xs <*> zs) ⟩
    (((p ⋊ map x ys) ∪ (p ⋊ map x zs)) ∪ (xs <*> ys)) ∪ (xs <*> zs) ≡⟨ cong (_∪ (xs <*> zs)) (∪-comm ((p ⋊ map x ys) ∪ (p ⋊ map x zs)) (xs <*> ys)) ⟩
    ((xs <*> ys) ∪ ((p ⋊ map x ys) ∪ (p ⋊ map x zs))) ∪ (xs <*> zs) ≡⟨ cong (_∪ (xs <*> zs)) (∪-assoc (xs <*> ys) (p ⋊ map x ys) (p ⋊ map x zs)) ⟩
    (((xs <*> ys) ∪ (p ⋊ map x ys)) ∪ (p ⋊ map x zs)) ∪ (xs <*> zs) ≡˘⟨ ∪-assoc ((xs <*> ys) ∪ (p ⋊ map x ys)) (p ⋊ map x zs) (xs <*> zs) ⟩
    ((xs <*> ys) ∪ (p ⋊ map x ys)) ∪ ((p ⋊ map x zs) ∪ (xs <*> zs)) ≡⟨ cong (_∪ (((p ⋊ map x zs) ∪ (xs <*> zs)))) (∪-comm (xs <*> ys) (p ⋊ map x ys)) ⟩
    ((p ⋊ map x ys) ∪ (xs <*> ys)) ∪ ((p ⋊ map x zs) ∪ (xs <*> zs)) ≡⟨⟩
    ((x ∶ p , xs) <*> ys) ∪ ((x ∶ p , xs) <*> zs) ∎
\end{code}
