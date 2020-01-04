\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Vec where

open import Prelude
import Data.Nat as ℕ

infixr 5 _∷_
\end{code}
%<*def>
\begin{code}
data Vec (A : Type a) : ℕ → Type a where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)
\end{code}
%</def>
\begin{code}
replicate : ∀ {n} → A → Vec A n
replicate {n = zero} x = []
replicate {n = suc n} x = x ∷ replicate x

module _ (B : ℕ → Type b) where
  foldr : (∀ {n} → A → B n → B (suc n))
        → B zero
        → ∀ {n} → Vec A n → B n
  foldr f b [] = b
  foldr f b (x ∷ xs) = f x (foldr f b xs)

_++_ : ∀ {n m} → Vec A n → Vec A m → Vec A (n ℕ.+ m)
xs ++ ys = foldr (λ n → Vec _ (n ℕ.+ _)) _∷_ ys xs
\end{code}
