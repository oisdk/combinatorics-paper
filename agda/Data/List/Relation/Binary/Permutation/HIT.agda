{-# OPTIONS --cubical --safe #-}

module Data.List.Relation.Binary.Permutation.HIT where

open import Prelude
open import Cubical.Foundations.Prelude using (isGroupoid)
open import Data.List using (List; _∷_; []; foldr)
import Data.Empty.UniversePolymorphic as Poly
import Data.Unit.UniversePolymorphic as Poly

infixr 5 _∷_
data Perm (A : Type a) : Type a where
  [] : Perm A
  _∷_ : A → Perm A → Perm A

  com : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  trunc : isGroupoid (Perm A)

jumble : List A → Perm A
jumble = foldr _∷_ []

infix 4 _↭_
_↭_ : (xs ys : List A) → Type _
xs ↭ ys = jumble xs ≡ jumble ys


-- code : {A : Type a} → Perm A → Perm A → Σ[ t ∈ Type a ] (isSet t)
-- code [] [] = Poly.⊤ , isProp→isSet (λ _ _ → refl)
-- code [] (x ∷ ys) = Poly.⊥ , λ ()
-- code [] (com x y ys i) = Poly.⊥ 
-- code [] (trunc ys ys₁ x y x₁ y₁ i i₁ x₂) = {!!}
-- code (x ∷ xs) ys = {!!}
-- code (com x y xs i) ys = {!!}
-- code (trunc xs xs₁ x y x₁ y₁ i i₁ x₂) ys = {!!}

-- cong-cons : ∀ (x : A) xs ys → xs ↭ ys → x ∷ xs ↭ x ∷ ys
-- cong-cons x xs ys xs↭ys i = x ∷ xs↭ys i


-- hSet : (a : Level) → Type (ℓ-suc a)
-- hSet a = Σ[ A ∈ Type a ] isSet A

-- isGroupoidhSet : ∀ {a} → isGroupoid (hSet a)
-- isGroupoidhSet a b x y x₁ y₁ = {!!}


-- com-in : ∀ {a} (x y z : Type a) → x ⊎ (y ⊎ z) ⇔ y ⊎ (x ⊎ z)
-- com-in = {!!}

-- infixr 5 _∈_
-- _∈_ : {A : Type a} (x : A) (xs : Perm A) → Type a
-- x ∈ (y ∷ xs) = (x ≡ y) ⊎ (x ∈ xs)
-- x ∈ [] = Poly.⊥
-- x ∈ com y z xs i = isoToPath (com-in (x ≡ y) (x ≡ z) (x ∈ xs)) i
-- t ∈ trunc xs ys x y x′ y′ i j z =
--   isOfHLevel→isOfHLevelDep {n = 3}
--     {!!}
--     (t ∈ xs) (t ∈ ys)
--     (cong (t ∈_) x) (cong (t ∈_) y)
--     (λ k → cong (t ∈_) (x′ k)) (λ k → cong (t ∈_) (y′ k))
--     (trunc xs ys x y x′ y′)
--     i j z
