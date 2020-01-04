{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Free.CommutativeMonoid.Permutation where

open import Prelude
open import Algebra.Construct.Free.CommutativeMonoid
open import Data.List using (List; _∷_; []; foldr)
open import Cubical.Foundations.HLevels

import Data.Unit.UniversePolymorphic as Poly
import Data.Empty.UniversePolymorphic as Poly

open import HITs.PropositionalTruncation.Sugar

jumble : List A → ⟅ A ⟆
jumble = foldr _∷_ []

-- infix 4 _↭_
-- _↭_ : List A → List A → Type _
-- xs ↭ ys = jumble xs ≡ jumble ys

-- -- tailₚ : ∀ (x : A) xs ys →
-- --       x ∷ xs ↭ x ∷ ys →
-- --       xs ↭ ys
-- -- tailₚ x xs ys x∷xs↭x∷ys = {!!}
-- --   where
-- --   p : x ∷ jumble xs ≡ x ∷ jumble ys
-- --   p = x∷xs↭x∷ys

swap-◇ : {x y xs : Type a} → ∥ x ⊎ ∥ y ⊎ xs ∥ ∥ → ∥ y ⊎ ∥ x ⊎ xs ∥ ∥
swap-◇ p = p >>= either′ (∣_∣ ∘ inr ∘ ∣_∣ ∘ inl) (mapʳ (∣_∣ ∘ inr) ∥$∥_)

com-◇ : ∀ {p} (P : A → Type p) → (x y : A) (xs : Type p) → ∥ P x ⊎ ∥ P y ⊎ xs ∥ ∥ ⇔ ∥ P y ⊎ ∥ P x ⊎ xs ∥ ∥
com-◇ P y z xs .fun = swap-◇
com-◇ P y z xs .inv = swap-◇
com-◇ P y z xs .leftInv  p = squash _ p
com-◇ P y z xs .rightInv p = squash _ p

_∈′ : {A : Type a} (x : A) → [⟅ A ⟆→ hProp a ]
[ x ∈′ ]-set = isSetHProp
[ x ∈′ ] y ∷ ys = ∥ (x ≡ y) ⊎ fst ys ∥ , squash
[ x ∈′ ][] = Poly.⊥  , λ ()
[ x ∈′ ]-com y z xs =
  ΣProp≡ (λ _ → isPropIsProp) (isoToPath (com-◇ (x ≡_) y z (xs .fst)))

_∈_ : {A : Type a} (x : A) (xs : ⟅ A ⟆) → Type a
x ∈ xs = [ x ∈′ ]↓ xs .fst

