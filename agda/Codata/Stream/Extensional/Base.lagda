\begin{code}
{-# OPTIONS --cubical --safe #-}

module Codata.Stream.Extensional.Base where

open import Prelude
open import Data.List using (List; _∷_; [])
open import Data.List.Kleene
\end{code}
%<*def>
\begin{code}
Stream : Type a → Type a
Stream A = (i : ℕ) → A
\end{code}
%</def>
\begin{code}
infixr 5 _◂_
_◂_ : A → Stream A → Stream A
(x ◂ xs) zero = x
(x ◂ xs) (suc i) = xs i

toList : ℕ → Stream A → List A
toList zero xs = []
toList (suc n) xs = xs zero ∷ toList n (xs ∘ suc)

mutual
  concat⋆ : A ⋆ → Stream (A ⁺) → Stream A
  concat⋆ []    xs = concat⁺ (xs zero) (xs ∘ suc)
  concat⋆ (∹ x) xs = concat⁺ x xs

  concat⁺ : A ⁺ → Stream (A ⁺) → Stream A
  concat⁺ x xs zero    = x .head
  concat⁺ x xs (suc n) = concat⋆ (x .tail) xs n

concat : Stream (A ⁺) → Stream A
concat xs = concat⁺ (xs zero) (xs ∘ suc)
\end{code}
