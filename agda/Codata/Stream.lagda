\begin{code}
{-# OPTIONS --cubical --sized-types --safe --postfix-projections #-}
module Codata.Stream where

open import Codata.Thunk
open import Codata.Size
open import Prelude
open import Data.List.Kleene using (_⋆; _⁺; []; _&_; ∹_; head; tail)

\end{code}
%<*definition>
\begin{code}
infixr 5 _◂_
record Stream (A : Set a) (i : Size) : Set a where
  coinductive
  constructor _◂_
  field
    head : A
    tail : ∀ {j : Size< i} → Stream A j
\end{code}
%</definition>
\begin{code}
open Stream public

module _ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : Size → Set ℓ₂) where
  foldr : ∀ {i}
        → (∀ {j : Size≤ i} → A → Thunk B j → B j)
        → Stream A i
        → B i
  foldr f xs = f (xs .head) λ where .force → foldr f (xs .tail)

_!_ : Stream A _ → ℕ → A
xs ! zero  = xs .head
xs ! suc i = xs .tail ! i

map : (A → B) → Stream A i → Stream B i
map f xs .head = f (xs .head)
map f xs .tail = map f (xs .tail)

tabulate : (ℕ → A) → Stream A i
tabulate f .head = f zero
tabulate f .tail = tabulate (f ∘ suc)

infixr 5 _⁺++_ _⋆++_
mutual
  _⁺++_ : A ⁺ → Thunk (Stream A) i → Stream A i
  (xs ⁺++ ys) .head = xs .head
  (xs ⁺++ ys) .tail = xs .tail ⋆++ ys .force

  _⋆++_ : A ⋆ → Stream A i → Stream A i
  []     ⋆++ ys = ys
  (∹ xs) ⋆++ ys = xs ⁺++ λ where .force → ys

concat : Stream (A ⁺) i → Stream A i
concat = foldr (Stream _) _⁺++_

interleaving : (A → C) → (B → C) → Stream A i → Stream B i → Stream C i
interleaving f g xs ys .head = f (xs .head)
interleaving f g xs ys .tail = interleaving g f ys (xs .tail)

zipWith : (A → B → C) → Stream A i → Stream B i → Stream C i
zipWith f xs ys .head = f (xs .head) (ys .head)
zipWith f xs ys .tail = zipWith f (xs .tail) (ys .tail)

repeat : A → Stream A i
repeat x .head = x
repeat x .tail = repeat x

\end{code}
