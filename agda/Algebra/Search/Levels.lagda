\begin{code}
{-# OPTIONS --cubical --safe #-}

module Algebra.Search.Levels where

open import Algebra
open import Algebra.Construct.Free.CommutativeMonoid hiding (⟦_⇒_⟧; ⟦_⟧⇓)
open import Prelude
open import Path.Reasoning
open import Data.List
open import Data.List.Relation.Binary using (isOfHLevelList)
\end{code}
%<*definition>
\begin{code}
Levels : (A : Type a) → Type a
Levels A = List ⟅ A ⟆
\end{code}
%</definition>
\begin{code}
_+_ : Levels A → Levels A → Levels A
[] + ys = ys
(x ∷ xs) + [] = x ∷ xs
(x ∷ xs) + (y ∷ ys) = (x ∪ y) ∷ (xs + ys)

+-assoc : (xs ys zs : Levels A) → (xs + ys) + zs ≡ xs + (ys + zs)
+-assoc [] ys zs = refl
+-assoc (x ∷ xs) [] zs = refl
+-assoc (x ∷ xs) (y ∷ ys) [] = refl
+-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) = cong₂ _∷_ (∪-assoc x y z) (+-assoc xs ys zs)

+-idʳ : (xs : Levels A) → xs + [] ≡ xs
+-idʳ (x ∷ xs) = refl
+-idʳ [] = refl

+-comm : (xs ys : Levels A) → (xs + ys) ≡ (ys + xs)
+-comm [] ys = sym (+-idʳ ys)
+-comm (x ∷ xs) [] = refl
+-comm (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (∪-comm x y) (+-comm xs ys)

+-commutativeMonoid : Type a → CommutativeMonoid a
+-commutativeMonoid A = record
  { monoid = record
    { 𝑆 = Levels A
    ; _∙_ = _+_
    ; ε = []
    ; assoc = +-assoc
    ; ε∙    = λ _ → refl
    ; ∙ε    = +-idʳ
    }
  ; comm = +-comm
  }

_=<<ᵇ_ : (A → Levels B) → ⟅ A ⟆ → Levels B
_=<<ᵇ_ {B = B} = ⟦ +-commutativeMonoid B ⟧ (isOfHLevelList 0 trunc)

wrap : Levels A → Levels A
wrap (x ∷ xs) = [] ∷ x ∷ xs
wrap [] = []

_>>=_ : Levels A → (A → Levels B) → Levels B
_>>=_ {A = A} {B = B} xs k = foldr f [] xs
  where
  f : ⟅ A ⟆ → Levels B → Levels B
  f x ys = (k =<<ᵇ x) + wrap ys

pure : A → Levels A
pure x = (x ∷ []) ∷ []

>>=-idˡ : (f : A → Levels B) (x : A) → (pure x >>= f) ≡ f x
>>=-idˡ f x =
  (pure x >>= f) ≡⟨⟩
  (((x ∷ []) ∷ []) >>= f) ≡⟨⟩
  ((f =<<ᵇ (x ∷ [])) + (wrap [])) ≡⟨⟩
  ((f =<<ᵇ (x ∷ [])) + []) ≡⟨⟩
  (f x + []) + [] ≡⟨ cong (_+ []) (+-idʳ (f x)) ⟩
  f x + [] ≡⟨ +-idʳ (f x) ⟩
  f x ∎

-- open ⟦_⇒_⟧
-- >>=-idʳ : (xs : Levels A) → (xs >>= pure) ≡ xs
-- >>=-idʳ = ⟦ >>=-idʳ′ ⟧⇓
--   where
--   >>=-idʳ′ : ⟦ xs ∶[ (⟅ A ⟆) ]⇒ ((xs >>= pure) ≡ xs) ⟧
--   ⟦ >>=-idʳ′ ⟧[] = refl
--   ⟦ >>=-idʳ′ ⟧ x ∷ xs ⟨ P ⟩ = {!!}
\end{code}
