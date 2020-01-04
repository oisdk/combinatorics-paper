\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

open import Algebra
open import Prelude

module Algebra.Construct.Free.Semimodule.Extensionality {s} (rng : Semiring s) (sIsSet : isSet (Semiring.𝑅 rng)) where

open import Algebra.Construct.Free.Semimodule.Definition rng
open import Algebra.Construct.Free.Semimodule.Eliminators rng
open import Algebra.Construct.Free.Semimodule.Operations.Functor rng
open import Algebra.Construct.Free.Semimodule.Operations.Expect rng sIsSet
open import Algebra.Construct.Free.Semimodule.Operations.Union rng
open import Algebra.Construct.Free.Semimodule.Operations.Condition rng

open Semiring rng

open import Algebra.SemiringLiterals nearSemiring

open import Path.Reasoning

sum : 𝒱 A → 𝑅
sum xs = ∫[ xs ] 1 𝑑 x

sum-map : (xs : 𝒱 A) → (tt ∶ sum xs , []) ≡ map (const tt) xs
sum-map = ∥ sum-map′ ∥⇓
  where
  sum-map′ : xs ∈𝒱 A ⇒∥ (tt ∶ sum xs , []) ≡ map (const tt) xs ∥
  ∥ sum-map′ ∥-prop = trunc _ _
  ∥ sum-map′ ∥[] = del tt []
  ∥ sum-map′ ∥ x ∶ p , xs ⟨ Pxs ⟩ =
    tt ∶ sum (x ∶ p , xs) , [] ≡⟨⟩
    tt ∶ 1 * p + sum xs , [] ≡⟨ cong (tt ∶_, []) (cong (_+ sum xs) (1* p)) ⟩
    tt ∶ p + sum xs , [] ≡˘⟨ dup tt p (sum xs) [] ⟩
    tt ∶ p , tt ∶ sum xs , [] ≡⟨ cong (tt ∶ p ,_) Pxs ⟩
    tt ∶ p , map (const tt) xs ≡⟨⟩
    map (const tt) (x ∶ p , xs) ∎

fill-empt : (xs : 𝒱 A) → (sum xs ≡ 0) → map (const tt) xs ≡ []
fill-empt xs ∫xs≡0 =
  map (const tt) xs ≡˘⟨ sum-map xs ⟩
  tt ∶ sum xs , [] ≡⟨ cong (tt ∶_, []) ∫xs≡0 ⟩
  tt ∶ 0 , [] ≡⟨ del tt [] ⟩
  [] ∎

-- module DecidableEvents (_≟_ : Discrete A) where
--   pull : ∀ x (xs : 𝒱 A) → ∃[ p ] ∃[ ys ] x ∶ p , ys ≡ xs
--   pull = λ x → ⟦ pull′ x ⟧⇓
--     where
--     pull′ : ∀ x → xs ∈𝒱 A ⇒ ∃[ p ] ∃[ ys ] (x ∶ p , ys ≡ xs)
--     ⟦ pull′ t ⟧-set = {!!}
--     ⟦ pull′ t ⟧[] = 0 , [] , del t []
--     ⟦ pull′ t ⟧ x ∶ p , xs ⟨ q , ys , Pxs ⟩ with t ≟ x
--     ⟦ pull′ t ⟧ x ∶ p , xs ⟨ q , ys , Pxs ⟩ | yes prf = p + q , ys , (sym (dup t p q ys) ; cong (_∶ p , t ∶ q , ys) prf) ; cong (x ∶ p ,_) Pxs
--     ⟦ pull′ t ⟧ x ∶ p , xs ⟨ q , ys , Pxs ⟩ | no ¬prf = q , (x ∶ p , ys) , com t q x p ys ; cong (x ∶ p ,_) Pxs
--     ⟦ pull′ t ⟧-com x p y q xs Pxs i .fst = {!!}
--     ⟦ pull′ t ⟧-com x p y q xs Pxs i .snd .fst = {!!}
--     ⟦ pull′ t ⟧-com x p y q xs Pxs i .snd .snd = {!!}
--     ⟦ pull′ t ⟧-dup x p q xs Pxs i .fst = {!!}
--     ⟦ pull′ t ⟧-dup x p q xs Pxs i .snd .fst = {!!}
--     ⟦ pull′ t ⟧-dup x p q xs Pxs i .snd .snd = {!!}
--     ⟦ pull′ t ⟧-del x xs Pxs i .fst = {!0!}
--     ⟦ pull′ t ⟧-del x xs Pxs i .snd .fst = {!!}
--     ⟦ pull′ t ⟧-del x xs Pxs i .snd .snd = {!!}

--   extensional : (xs ys : 𝒱 A) → (∀ f → ∫ xs f ≡ ∫ ys f) → xs ≡ ys
--   extensional = {!!}


-- module DecidableMeas (_≟_ : Discrete 𝑅) where
--   empty-ext : (xs : 𝒱 A) → (∀ f → ∫ xs f ≡ 0) → xs ≡ []
--   empty-ext = ∥ empty-ext′ ∥⇓
--     where
--     empty-ext′ : xs ∈𝒱 A ⇒∥ ((∀ f → ∫ xs f ≡ 0) → xs ≡ []) ∥
--     ∥ empty-ext′ ∥-prop = {!!}
--     ∥ empty-ext′ ∥[] _ = refl
--     ∥ empty-ext′ ∥ x ∶ p , xs ⟨ Pxs ⟩ xs↭[] = {!!}

--   subset-ext : (xs ys : 𝒱 A) → (∀ f → ∫ xs f ≡ ∫ ys f) → xs ∪ ys ≡ 2 ⋊ ys
--   subset-ext = λ xs ys → ∥ subset-ext′ ys ∥⇓ xs
--     where
--     subset-ext′ : (ys : 𝒱 A) →  xs ∈𝒱 A ⇒∥ ((∀ f → ∫ xs f ≡ ∫ ys f) → xs ∪ ys ≡ 2 ⋊ ys) ∥
--     ∥ subset-ext′ ys ∥-prop = {!!}
--     ∥ subset-ext′ ys ∥[] xs↭ys = {!!}
--     ∥ subset-ext′ ys ∥ x ∶ p , xs ⟨ Pxs ⟩ = {!!}

--   extensional : (xs ys : 𝒱 A) → (∀ f → ∫ xs f ≡ ∫ ys f) → xs ≡ ys
--   extensional = {!!}

\end{code}
