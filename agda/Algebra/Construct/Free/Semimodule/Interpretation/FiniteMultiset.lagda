\begin{code}
{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Free.Semimodule.Interpretation.FiniteMultiset where

open import Prelude
open import Path.Reasoning
open import Algebra.Nat using (ℕ-semiring)
open import Data.Nat using (isSetℕ)
open import Algebra.Construct.Free.Semimodule.Definition ℕ-semiring as V
open import Algebra.Construct.Free.Semimodule.Operations ℕ-semiring isSetℕ
open import Algebra.Construct.Free.Semimodule.Eliminators ℕ-semiring
open import Algebra

open Semiring ℕ-semiring

⟅_⟆* : Type a → Type a
⟅ A ⟆* = 𝒱 A

module _ {a} {A : Type a} (_≟_ : Discrete A) where
\end{code}
%<*count>
\begin{code}
 count : (x : A) → ⟅ A ⟆* → ℕ
 count x xs =
   ∫[ xs ]
    (case x ≟ y of λ { (yes _) → 1; (no _) → 0 })
    𝑑 y
\end{code}
%</count>
\begin{code}
open import Algebra.Construct.Free.CommutativeMonoid as Mon
  using (⟅_⟆; []; _∷_; trunc; com; elim-prop-syntax; ⟦_⟧-prop; ⟦_⟧_∷_⟨_⟩; ⟦_⟧[])

mul : A → ℕ → ⟅ A ⟆ → ⟅ A ⟆
mul x zero xs = xs
mul x (suc n) xs = x ∷ mul x n xs

mul-cons : ∀ (x : A) y p xs → x ∷ mul y p xs ≡ mul y p (x ∷ xs)
mul-cons x y zero xs = refl
mul-cons x y (suc p) xs = Mon.com x y (mul y p xs) ; cong (y ∷_) (mul-cons x y p xs)

mul-comm : ∀ (x : A) p y q xs → mul x p (mul y q xs) ≡ mul y q (mul x p xs)
mul-comm x zero y q xs = refl
mul-comm x (suc p) y q xs = cong (x ∷_) (mul-comm x p y q xs) ; mul-cons x y q (mul x p xs)

mul-add : ∀ (x : A) p q xs → mul x p (mul x q xs) ≡ mul x (p + q) xs
mul-add x zero q xs = refl
mul-add x (suc p) q xs = cong (x ∷_) (mul-add x p q xs)

*⇒⟅⟆ : ⟅ A ⟆* → ⟅ A ⟆
*⇒⟅⟆ = [ *⇒⟅⟆′ ]↓
  where
  *⇒⟅⟆′ : A ↘ ⟅ A ⟆
  [ *⇒⟅⟆′ ][] = []
  [ *⇒⟅⟆′ ] x ∶ p , xs = mul x p xs
  [ *⇒⟅⟆′ ]-set = Mon.trunc
  [ *⇒⟅⟆′ ]-com x p y q xs = mul-comm x p y q xs
  [ *⇒⟅⟆′ ]-del x xs = refl
  [ *⇒⟅⟆′ ]-dup x p q xs = mul-add x p q xs

⟅⟆⇒* : ⟅ A ⟆ → ⟅ A ⟆*
⟅⟆⇒* {A = A}= Mon.⟦_⟧ (∪-commutativeMonoid A) V.trunc pure

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

mul-rev : ∀ (x : A) p xs → ⟅⟆⇒* (mul x p xs) ≡ x ∶ p , ⟅⟆⇒* xs
mul-rev x zero xs = sym (del x (⟅⟆⇒* xs))
mul-rev x (suc p) xs =
  ⟅⟆⇒* (x ∷ mul x p xs) ≡⟨⟩
  pure x ∪ (⟅⟆⇒* (mul x p xs)) ≡⟨⟩
  x ∶ 1 , (⟅⟆⇒* (mul x p xs)) ≡⟨ cong (x ∶ 1 ,_) (mul-rev x p xs) ⟩
  x ∶ 1 , (x ∶ p , ⟅⟆⇒* xs) ≡⟨ dup x 1 p (⟅⟆⇒* xs) ⟩
  x ∶ suc p , ⟅⟆⇒* xs ∎

*→⟅⟆→* : (n : ⟅ A ⟆*) → ⟅⟆⇒* (*⇒⟅⟆ n) ≡ n
*→⟅⟆→* = ∥ prf ∥⇓
  where
  prf : xs ∈𝒱 A ⇒∥ ⟅⟆⇒* (*⇒⟅⟆ xs) ≡ xs ∥
  ∥ prf ∥-prop = V.trunc _ _
  ∥ prf ∥[] = refl
  ∥ prf ∥ x ∶ p , xs ⟨ P ⟩ =
    (⟅⟆⇒* (*⇒⟅⟆ (x ∶ p , xs))) ≡⟨⟩
    (⟅⟆⇒* (mul x p (*⇒⟅⟆ xs))) ≡⟨ mul-rev x p (*⇒⟅⟆ xs) ⟩
    x ∶ p , (⟅⟆⇒* (*⇒⟅⟆ xs)) ≡⟨ cong (x ∶ p ,_) P ⟩
    (x ∶ p , xs) ∎

⟅⟆→*→⟅⟆ : (n : ⟅ A ⟆) → *⇒⟅⟆ (⟅⟆⇒* n) ≡ n
⟅⟆→*→⟅⟆ = Mon.⟦ prf ⟧⇓
  where
  prf : ⟦ xs ∶⟅ A ⟆⇒ *⇒⟅⟆ (⟅⟆⇒* xs) ≡ xs ⟧
  ⟦ prf ⟧[] = refl
  ⟦ prf ⟧-prop = Mon.trunc _ _
  ⟦ prf ⟧ x ∷ xs ⟨ P ⟩ =
    *⇒⟅⟆ (⟅⟆⇒* (x ∷ xs)) ≡⟨⟩
    *⇒⟅⟆ (x ∶ 1 , ⟅⟆⇒* xs) ≡⟨⟩
    mul x 1 (*⇒⟅⟆ (⟅⟆⇒* xs)) ≡⟨⟩
    x ∷ (*⇒⟅⟆ (⟅⟆⇒* xs)) ≡⟨ cong (x ∷_) P ⟩
    x ∷ xs ∎

*≡⟅⟆ : ⟅ A ⟆* ≡ ⟅ A ⟆
*≡⟅⟆ = isoToPath (iso *⇒⟅⟆ ⟅⟆⇒* ⟅⟆→*→⟅⟆ *→⟅⟆→*)
\end{code}
