\begin{code}
{-# OPTIONS --cubical --safe --sized-types --postfix-projections #-}

module Codata.Covec where

open import HITs.InfNat
open import Prelude
open import Codata.Size as Size
open import Data.Fin.Infinite

private
  variable n m : ℕ+∞

mutual
  infixr 5 _&_ ∹_
  data Covec (A : Type a) (i : Size) : ℕ+∞ → Type a where
    [] : Covec A i zero
    ∹_ : Covec⁺ A i n → Covec A i (suc n)

  record Covec⁺ (A : Type a) (i : Size) (n : ℕ+∞) : Type a where
    coinductive
    constructor _&_
    field
      head : A
      tail : ∀ {j : Size< i} → Covec A j n
open Covec⁺ public

infixl 6 _!_ _!⁺_
mutual
  _!_ : (xs : Covec A Size.∞ n) → Fin n → A
  (∹ xs) ! n = xs !⁺ n

  _!⁺_ : (xs : Covec⁺ A Size.∞ n) → Fin (suc n) → A
  xs !⁺ f0  = head xs
  xs !⁺ (suc n , p) = xs .tail ! (n , p)

◇ : ∀ {p} (P : A → Type p) → Covec A Size.∞ n → Type p
◇ P xs = ∃[ i ] (P (xs ! i))

infixr 5 _∈_
_∈_ : A → Covec A Size.∞ n → Type _
x ∈ xs = ◇ (_≡ x) xs

mutual
  map : (A → B) → Covec A i n → Covec B i n
  map f [] = []
  map f (∹ xs) = ∹ map⁺ f xs

  map⁺ : (A → B) → Covec⁺ A i n → Covec⁺ B i n
  map⁺ f xs .head = f (xs .head)
  map⁺ f xs .tail = map f (xs .tail)


push : ∀ {x} {xs : Covec⁺ A Size.∞ n} → x ∈ (xs .tail) → x ∈ ∹ xs
push ((n , p) , x∈xs)= (suc n , p) , x∈xs


cong-∈ : ∀ {x : A} → (f : A → B) → (xs : Covec A Size.∞ n) → x ∈ xs → f x ∈ map f xs
cong-∈ f (∹ xs) ((zero  , p) , x∈xs) = (zero , p) , cong f x∈xs
cong-∈ f (∹ xs) ((suc n , p) , x∈xs) = push (cong-∈ f (xs .tail) ((n , p) , x∈xs))
\end{code}
