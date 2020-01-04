{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Relation.Binary
open import Prelude

module Algebra.Construct.Free.Semimodule.Operations.ToList
  {s} (rng : Semiring s)
  {ℓ₁} {S : Type ℓ₁} ℓ₂ (ord : TotalOrder S ℓ₂)
  (_≟_ : Discrete (Semiring.𝑅 rng)) where

open Semiring rng
open TotalOrder ord renaming (refl to refl-≤)
open import Path.Reasoning
open import Relation.Nullary

open import Algebra.Construct.Free.Semimodule.Definition rng
open import Algebra.Construct.Free.Semimodule.Eliminators rng

open import Data.List using (List; _∷_; [])
open import Data.List.Relation.Binary using (isOfHLevelList)

infixr 5 _∷↓_
_∷↓_ : S × 𝑅 → List (S × 𝑅) → List (S × 𝑅)
(x , p) ∷↓ xs with does (p ≟ 0#)
(x , p) ∷↓ xs | false = (x , p) ∷ xs
(x , p) ∷↓ xs | true  = xs

insert : S → 𝑅 → List (S × 𝑅) → List (S × 𝑅)
insert x p [] = (x , p) ∷↓ []
insert x p ((y , q) ∷ xs) with compare x y
... | lt x<y = (x , p) ∷↓ (y , q) ∷ xs
... | eq x≡y = (y , p + q) ∷↓ xs
... | gt x>y = (y , q) ∷ insert x p xs

-- cons-del : ∀ x xs → (x , 0#) ∷↓ xs ≡ xs
-- cons-del x xs with (0# ≟ 0#)
-- cons-del x xs | yes p = refl
-- cons-del x xs | no ¬p = ⊥-elim (¬p refl)

-- insert-dup : (x : S) (p q : 𝑅) (xs : List (S × 𝑅)) →
--       insert x p (insert x q xs) ≡ insert x (p + q) xs
-- insert-dup x p q [] = {!!}
-- insert-dup x p q (x₁ ∷ xs) = {!!}

-- insert-com : (x : S) (p : 𝑅) (y : S) (q : 𝑅) (xs : List (S × 𝑅)) →
--       insert x p (insert y q xs) ≡ insert y q (insert x p xs)
-- insert-com = {!!}


-- insert-del : (x : S) (xs : List (S × 𝑅)) → insert x 0# xs ≡ xs
-- insert-del x [] = cons-del x []
-- insert-del x ((y , q) ∷ xs) with compare x y
-- insert-del x ((y , q) ∷ xs) | lt x<y = cons-del x ((y , q) ∷ xs)
-- insert-del x ((y , q) ∷ xs) | eq x≡y = {!!}
-- insert-del x ((y , q) ∷ xs) | gt x>y = {!!}

-- open import Cubical.Foundations.HLevels using (isOfHLevelΣ)

-- toList : 𝒱 S → List (S × 𝑅)
-- toList = [ list ]↓
--   where
--   list : S ↘ List (S × 𝑅)
--   [ list ]-set = isOfHLevelList 0 (isOfHLevelΣ 2 (Discrete→isSet total⇒discrete) λ _ → Discrete→isSet _≟_)
--   [ list ] x ∶ p , xs = insert x p xs
--   [ list ][] = []
--   [ list ]-dup = insert-dup
--   [ list ]-com = insert-com
--   [ list ]-del = insert-del
