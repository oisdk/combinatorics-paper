\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

module Data.Container.List.Membership where

open import Data.Container
open import Data.Container.List
open import Data.Container.Relation.Unary ℒ
open import Prelude
open import Relation.Nullary
open import Data.Fin

push : ∀ (x : A) l xs → x ∈ (l , xs ∘ fs) → x ∈ (suc l , xs)
push x l xs (n , p) = fs n , p

-- cong-∈ : ∀ (f : A → B) {x : A} xs → x ∈ xs → f x ∈ map f xs
-- cong-∈ f {x} _ = Congruence.cong-◇ (_≡ x) (_≡ (f x)) (cong f)


-- module _ {a} {A : Set a} (_≟_ : Discrete A) where
--   isSet⟨A⟩ : isSet A
--   isSet⟨A⟩ = Discrete→isSet _≟_

--   infixl 6 _\\_
--   _\\_ : ⟦ ℒ ⟧ A → A → ⟦ ℒ ⟧ A
--   xs \\ x = foldr f [] xs
--     where
--     f : A → ⟦ ℒ ⟧ A → ⟦ ℒ ⟧ A
--     f y xs =
--       if does (x ≟ y)
--         then xs
--         else y ∷ xs

--   uniques : ⟦ ℒ ⟧ A → ⟦ ℒ ⟧ A
--   uniques = foldr f []
--     where
--     f : _
--     f x xs = x ∷ (xs \\ x)

--   x∉xs\\x : ∀ x xs → x ∉ xs \\ x
--   x∉xs\\x x xs x∈xs = foldrP (λ xs → x ∉ xs \\ x) f (λ ()) xs x∈xs
--     where
--     f : ∀ n xs → x ∉ (n , xs ∘ fs) \\ x → x ∉ (suc n , xs) \\ x
--     f n xs Pxs x∈xs with x ≟ xs f0
--     f n xs Pxs x∈xs | yes p = Pxs x∈xs
--     f n xs Pxs (f0 , x∈xs) | no ¬p = ¬p (sym x∈xs)
--     f n xs Pxs (fs x , x∈xs) | no ¬p = Pxs (x , x∈xs)
\end{code}
