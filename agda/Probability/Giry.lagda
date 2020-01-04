\begin{code}
{-# OPTIONS --cubical --safe #-}
open import Algebra

module Probability.Giry {s} (rng : Semiring s) where

open Semiring rng
open import Prelude
\end{code}
%<*definition>
\begin{code}
𝒢 : Type a → Type (s ℓ⊔ a)
𝒢 A = (A → 𝑅) → 𝑅
\end{code}
%</definition>
%<*int>
\begin{code}
∫-syntax : 𝒢 A → (A → 𝑅) → 𝑅
∫-syntax = id
syntax ∫-syntax xs (λ x → e) = ∫[ xs ] e 𝑑 x

probOf : (A → Bool) → 𝒢 A → 𝑅
probOf f xs = ∫[ xs ] if f x then 1# else 0# 𝑑 x
\end{code}
%</int>
\begin{code}
pure : A → 𝒢 A
pure x f = f x

map : (A → B) → 𝒢 A → 𝒢 B
map f xs g = xs (g ∘ f)

_<*>_ : 𝒢 (A → B) → 𝒢 A → 𝒢 B
(fs <*> xs) k = ∫[ fs ] (∫[ xs ] k (f x) 𝑑 x) 𝑑 f
\end{code}
%<*monad>
\begin{code}
_>>=_ : 𝒢 A → (A → 𝒢 B) → 𝒢 B
(xs >>= f) k = ∫[ xs ] (∫[ f x ] k y 𝑑 y) 𝑑 x
\end{code}
%</monad>
\begin{code}
_⋊_ : 𝑅 → 𝒢 A → 𝒢 A
(p ⋊ xs) k = ∫[ xs ] p * k x 𝑑 x

functor : ∀ {ℓ} → Functor ℓ (s ℓ⊔ ℓ)
functor = record
  { 𝐹 = 𝒢
  ; map = map
  ; map-id = refl
  ; map-comp = λ f g → refl
  }

applicative : ∀ {ℓ} → Applicative ℓ (s ℓ⊔ ℓ)
applicative = record
  { functor = functor
  ; pure = pure
  ; _<*>_ = _<*>_
  ; map-ap = λ f → refl
  ; pure-homo = λ f x → refl
  ; <*>-interchange = λ u y → refl
  ; <*>-comp = λ u v w → refl
  }

monad : ∀ {ℓ} → Monad ℓ (s ℓ⊔ ℓ)
monad = record
  { applicative = applicative
  ; _>>=_ = _>>=_
  ; >>=-idˡ = λ f x → refl
  ; >>=-idʳ = λ x → refl
  ; >>=-assoc = λ xs f g → refl
  }

open import Data.List

fromDist : List (A × 𝑅) → 𝒢 A
fromDist xs k = foldr (λ { (x , p) xs → k x * p + xs }) 0# xs
\end{code}
