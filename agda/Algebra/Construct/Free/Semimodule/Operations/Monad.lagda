\begin{code}
{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Prelude
open import Path.Reasoning

module Algebra.Construct.Free.Semimodule.Operations.Monad {s} (rng : Semiring s)  where

open Semiring rng
open import Algebra.Construct.Free.Semimodule.Definition rng
open import Algebra.Construct.Free.Semimodule.Eliminators rng
open import Algebra.Construct.Free.Semimodule.Operations.Condition rng
open import Algebra.Construct.Free.Semimodule.Operations.Union rng
open import Algebra.Construct.Free.Semimodule.Operations.Functor rng
open import Algebra.Construct.Free.Semimodule.Operations.Applicative rng
\end{code}
%<*impl>
\begin{code}
_>>=_ : 𝒱 A → (A → 𝒱 B) → 𝒱 B
xs >>= f = [ f =<< ]↓ xs
  where
  _=<< : (A → 𝒱 B) → A ↘ 𝒱 B
  [ f =<< ] x ∶ p , xs = p ⋊ (f x) ∪ xs
  [ f =<< ][] = []
\end{code}
%</impl>
\begin{code}
  [ f =<< ]-set = trunc
  [ f =<< ]-del x xs = cong (_∪ xs) (0⋊ (f x))
  [ f =<< ]-dup x p q xs =
    p ⋊ (f x) ∪ q ⋊ (f x) ∪ xs   ≡⟨ ∪-assoc (p ⋊ f x) (q ⋊ f x) xs ⟩
    (p ⋊ (f x) ∪ q ⋊ (f x)) ∪ xs ≡⟨ cong (_∪ xs) (⋊-distribʳ p q (f x) ) ⟩
    (p + q) ⋊ (f x) ∪ xs ∎
  [ f =<< ]-com x p y q xs =
    p ⋊ (f x) ∪ q ⋊ (f y) ∪ xs   ≡⟨ ∪-assoc (p ⋊ f x) (q ⋊ f y) xs ⟩
    (p ⋊ (f x) ∪ q ⋊ (f y)) ∪ xs ≡⟨ cong (_∪ xs) (∪-comm (p ⋊ f x) (q ⋊ f y)) ⟩
    (q ⋊ (f y) ∪ p ⋊ (f x)) ∪ xs ≡˘⟨ ∪-assoc (q ⋊ f y) (p ⋊ f x) xs ⟩
    q ⋊ (f y) ∪ p ⋊ (f x) ∪ xs ∎

>>=-distrib : (xs ys : 𝒱 A) (g : A → 𝒱 B) → ((xs ∪ ys) >>= g) ≡ (xs >>= g) ∪ (ys >>= g)
>>=-distrib = λ xs ys g → ∥ >>=-distrib′ ys g ∥⇓ xs
  where
  >>=-distrib′ : (ys : 𝒱 A) (g : A → 𝒱 B) → xs ∈𝒱 A ⇒∥ ((xs ∪ ys) >>= g) ≡ (xs >>= g) ∪ (ys >>= g) ∥
  ∥ >>=-distrib′ ys g ∥-prop = trunc _ _
  ∥ >>=-distrib′ ys g ∥[] = refl
  ∥ >>=-distrib′ ys g ∥ x ∶ p , xs ⟨ P ⟩ =
    (((x ∶ p , xs) ∪ ys) >>= g) ≡⟨⟩
    ((x ∶ p , xs ∪ ys) >>= g) ≡⟨⟩
    p ⋊ g x ∪ ((xs ∪ ys) >>= g) ≡⟨ cong (p ⋊ g x ∪_) P ⟩
    p ⋊ g x ∪ ((xs >>= g) ∪ (ys >>= g)) ≡⟨ ∪-assoc (p ⋊ g x) (xs >>= g) (ys >>= g) ⟩
    (p ⋊ g x ∪ (xs >>= g)) ∪ (ys >>= g) ≡⟨⟩
    ((x ∶ p , xs) >>= g) ∪ (ys >>= g) ∎

⋊-assoc->>= : ∀ p (xs : 𝒱 A) (f : A → 𝒱 B) → ((p ⋊ xs) >>= f) ≡ p ⋊ (xs >>= f)
⋊-assoc->>= = λ p xs f → ∥ ⋊-assoc->>=′ p f ∥⇓ xs
  module JDistribB where
  ⋊-assoc->>=′ : ∀ p (f : A → 𝒱 B) → xs ∈𝒱 A ⇒∥ ((p ⋊ xs) >>= f) ≡ p ⋊ (xs >>= f) ∥
  ∥ ⋊-assoc->>=′ p f ∥-prop = trunc _ _
  ∥ ⋊-assoc->>=′ p f ∥[] = refl
  ∥ ⋊-assoc->>=′ p f ∥ x ∶ q , xs ⟨ P ⟩ =
    ((p ⋊ (x ∶ q , xs)) >>= f) ≡⟨⟩
    ((x ∶ p * q , p ⋊ xs) >>= f) ≡⟨⟩
    ((p * q) ⋊ f x) ∪ ((p ⋊ xs) >>= f) ≡⟨ cong (((p * q) ⋊ f x) ∪_) P ⟩
    ((p * q) ⋊ f x) ∪ (p ⋊ (xs >>= f)) ≡⟨ cong (_∪ (p ⋊ (xs >>= f))) (*-assoc-⋊ p q (f x)) ⟩
    (p ⋊ (q ⋊ f x)) ∪ (p ⋊ (xs >>= f)) ≡⟨ ⋊-distribˡ p (q ⋊ f x) (xs >>= f) ⟩
    p ⋊ ((x ∶ q , xs) >>= f) ∎


>>=-idˡ : (x : A) → (f : A → 𝒱 B)
      → (pure x >>= f) ≡ f x
>>=-idˡ x f =
  (pure x >>= f) ≡⟨⟩
  ((x ∶ 1# , []) >>= f) ≡⟨⟩
  1# ⋊ f x ∪ ([] >>= f) ≡⟨⟩
  1# ⋊ f x ∪ [] ≡⟨ ∪-idʳ (1# ⋊ f x) ⟩
  1# ⋊ f x ≡⟨ 1⋊ (f x) ⟩
  f x ∎

>>=-idʳ : (xs : 𝒱 A) → (xs >>= pure) ≡ xs
>>=-idʳ = ∥ >>=-idʳ′ ∥⇓
  module Law1 where
  >>=-idʳ′ : xs ∈𝒱 A ⇒∥ (xs >>= pure) ≡ xs ∥
  ∥ >>=-idʳ′ ∥-prop = trunc _ _
  ∥ >>=-idʳ′ ∥[] = refl
  ∥ >>=-idʳ′ ∥ x ∶ p , xs ⟨ P ⟩ =
    ((x ∶ p , xs) >>= pure) ≡⟨⟩
    p ⋊ (pure x) ∪ (xs >>= pure) ≡⟨⟩
    p ⋊ (x ∶ 1# , []) ∪ (xs >>= pure) ≡⟨⟩
    x ∶ p * 1# , [] ∪ (xs >>= pure) ≡⟨⟩
    x ∶ p * 1# , (xs >>= pure) ≡⟨ cong (x ∶_, (xs >>= pure)) (*1 p) ⟩
    x ∶ p , (xs >>= pure) ≡⟨ cong (x ∶ p ,_) P ⟩
    x ∶ p , xs ∎

>>=-assoc : (xs : 𝒱 A) → (f : A → 𝒱 B) → (g : B → 𝒱 C)
      → ((xs >>= f) >>= g) ≡ (xs >>= (λ x → f x >>= g))
>>=-assoc = λ xs f g → ∥ >>=-assoc′ f g ∥⇓ xs
  module Law3 where
  >>=-assoc′ : (f : A → 𝒱 B) → (g : B → 𝒱 C) → xs ∈𝒱 A ⇒∥ ((xs >>= f) >>= g) ≡ (xs >>= (λ x → f x >>= g)) ∥
  ∥ >>=-assoc′ f g ∥-prop = trunc _ _
  ∥ >>=-assoc′ f g ∥[] = refl
  ∥ >>=-assoc′ f g ∥ x ∶ p , xs ⟨ P ⟩ =
    (((x ∶ p , xs) >>= f) >>= g) ≡⟨⟩
    ((p ⋊ f x ∪ (xs >>= f)) >>= g) ≡⟨ >>=-distrib (p ⋊ f x) (xs >>= f) g ⟩
    ((p ⋊ f x) >>= g) ∪ ((xs >>= f) >>= g) ≡⟨ cong (((p ⋊ f x) >>= g) ∪_) P ⟩
    ((p ⋊ f x) >>= g) ∪ (xs >>= (λ y → f y >>= g)) ≡⟨ cong (_∪ (xs >>= (λ y → f y >>= g))) (⋊-assoc->>= p (f x) g) ⟩
    p ⋊ (f x >>= g) ∪ (xs >>= (λ y → f y >>= g)) ≡⟨⟩
    ((x ∶ p , xs) >>= (λ y → f y >>= g)) ∎

>>=-map : ∀ (xs : 𝒱 A) (f : A → B) → xs >>= (pure ∘ f) ≡ map f xs
>>=-map = λ xs f → ∥ >>=-map′ f ∥⇓ xs
  where
  >>=-map′ : (f : A → B) → xs ∈𝒱 A ⇒∥ xs >>= (pure ∘ f) ≡ map f xs ∥
  ∥ >>=-map′ f ∥-prop = trunc _ _
  ∥ >>=-map′ f ∥[] = refl
  ∥ >>=-map′ f ∥ x ∶ p , xs ⟨ P ⟩ =
    (x ∶ p , xs) >>= (pure ∘ f) ≡⟨⟩
    p ⋊ pure (f x) ∪ (xs >>= (pure ∘ f)) ≡⟨ cong (p ⋊ pure (f x) ∪_) P ⟩
    p ⋊ pure (f x) ∪ (map f xs) ≡⟨⟩
    f x ∶ p * 1# , map f xs ≡⟨ cong (f x ∶_, map f xs) (*1 p) ⟩
    map f (x ∶ p , xs) ∎

ap : 𝒱 (A → B) → 𝒱 A → 𝒱 B
ap fs xs = do
  f ← fs
  x ← xs
  pure (f x)

ap-<*> : (fs : 𝒱 (A → B)) (xs : 𝒱 A) → (fs <*> xs) ≡ ap fs xs
ap-<*> fs xs = ∥ ap-<*>′ xs ∥⇓ fs
  where
  ap-<*>′ : (xs : 𝒱 A) → fs ∈𝒱 (A → B) ⇒∥ (fs <*> xs) ≡ ap fs xs ∥
  ∥ ap-<*>′ xs ∥-prop = trunc _ _
  ∥ ap-<*>′ xs ∥[] = refl
  ∥ ap-<*>′ xs ∥ f ∶ p , fs ⟨ P ⟩ =
    (f ∶ p , fs) <*> xs ≡⟨⟩
    p ⋊ map f xs ∪ (fs <*> xs) ≡⟨ cong (p ⋊ map f xs ∪_) P ⟩
    p ⋊ map f xs ∪ ap fs xs ≡˘⟨ cong (λ fxs → p ⋊ fxs ∪ ap fs xs) (>>=-map xs f) ⟩
    p ⋊ (xs >>= (pure ∘′ f)) ∪ ap fs xs ≡⟨⟩
    ap (f ∶ p , fs) xs ∎

monad : ∀ {ℓ} → Monad ℓ (ℓ ℓ⊔ s)
monad = record
  { applicative = applicative
  ; _>>=_ = _>>=_
  ; >>=-idˡ = flip >>=-idˡ
  ; >>=-idʳ = >>=-idʳ
  ; >>=-assoc = >>=-assoc
  }
\end{code}
