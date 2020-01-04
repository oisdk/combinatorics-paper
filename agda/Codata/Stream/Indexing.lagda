\begin{code}
{-# OPTIONS --sized-types --cubical --safe #-}

module Codata.Stream.Indexing where

open import Codata.Size
open import Codata.Stream
open import Prelude

infixr 5 _∈_ _∉_ _∈!_
_∈_ : A → Stream A ∞ → Type _
x ∈ xs = ∃[ i ] xs ! i ≡ x

_∉_ : A → Stream A ∞ → Type _
x ∉ xs = ¬ (x ∈ xs)

_∈!_ : A → Stream A ∞ → Type _
x ∈! xs = isContr (x ∈ xs)

push : ∀ {x : A} {xs} → x ∈ xs .tail → x ∈ xs
push  (n , x∈xs) = (suc n , x∈xs)

pull : ∀ {x : A} {xs} → xs .head ≢ x → x ∈ xs → x ∈ xs .tail
pull y≢x (zero   , y≡x)     = ⊥-elim (y≢x y≡x)
pull y≢x (suc n  , x∈y∷xs)  = n , x∈y∷xs

cong-∈ : ∀ (f : A → B) {x : A} xs → x ∈ xs → f x ∈ map f xs
cong-∈ f xs (zero  , x∈xs) = zero , cong f x∈xs
cong-∈ f xs (suc n , x∈xs) = push (cong-∈ f (xs .tail) (n , x∈xs))
\end{code}
