\begin{code}
{-# OPTIONS --cubical --safe #-}
module Algebra.Construct.Free.NearSemiring where

open import Prelude
open import Data.List
open import Algebra
\end{code}
%<*definition>
\begin{code}
mutual
  Forest : Type a → Type a
  Forest A = List (Tree A)

  infixr 5 _◂_
  data Tree (A : Type a) : Type a where
    leaf : Tree A
    _◂_ : A → Forest A → Tree A
\end{code}
%</definition>
\begin{code}
module _ {a} {A : Type a} where
  _⊗_ : Forest A → Forest A → Forest A
  [] ⊗ ys = []
  (leaf ∷ xs) ⊗ ys = ys ++ (xs ⊗ ys)
  ((x ◂ zs) ∷ xs) ⊗ ys = (x ◂ (zs ⊗ ys)) ∷ (xs ⊗ ys)

  ⊗1 : (xs : Forest A) → (xs ⊗ (leaf ∷ [])) ≡ xs
  ⊗1 [] = refl
  ⊗1 (leaf ∷ xs) = cong (leaf ∷_) (⊗1 xs)
  ⊗1 ((x ◂ ys) ∷ xs) = cong₂ _∷_ (cong (x ◂_) (⊗1 ys)) (⊗1 xs)

  ⊗-distrib : _⊗_ Distributesˡ _++_
  ⊗-distrib [] ys zs = refl
  ⊗-distrib (leaf ∷ xs) ys zs = cong (zs ++_) (⊗-distrib xs ys zs) ; sym (++-assoc zs (xs ⊗ zs) (ys ⊗ zs))
  ⊗-distrib ((x ◂ xs′) ∷ xs) ys zs = cong ((x ◂ (xs′ ⊗ zs)) ∷_) (⊗-distrib xs ys zs)

  ⊗-assoc : Associative _⊗_
  ⊗-assoc [] ys zs = refl
  ⊗-assoc (leaf ∷ xs) ys zs = ⊗-distrib ys (xs ⊗ ys) zs ; cong ((ys ⊗ zs) ++_) (⊗-assoc xs ys zs)
  ⊗-assoc ((x ◂ xxs) ∷ xs) ys zs = cong₂ _∷_ (cong (x ◂_) (⊗-assoc xxs ys zs)) (⊗-assoc xs ys zs)

freeNearSemiring : ∀ {a} → Type a → NearSemiring a
freeNearSemiring A = record
  { 𝑅 = Forest A
  ; _+_ = _++_
  ; _*_ = _⊗_
  ; 1# = leaf ∷ []
  ; 0# = []
  ; +-assoc = ++-assoc
  ; *-assoc = ⊗-assoc
  ; 0+ = λ _ → refl
  ; +0 = ++[]
  ; 1* = λ xs → ++[] xs
  ; *1 = ⊗1
  ; 0* = λ _ → refl
  ; ⟨+⟩* = ⊗-distrib
  }
\end{code}
