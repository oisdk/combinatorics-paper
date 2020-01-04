\begin{code}
{-# OPTIONS --cubical --safe #-}
module Snippets.List where

open import Prelude
open import Data.List
open import Data.Nat
open import Data.List.Syntax

_>>=_ : List A → (A → List B) → List B
xs >>= f = foldr (λ x xs → f x ++ xs) [] xs

_>>_ : List A → List B → List B
xs >> ys = xs >>= const ys

open import Data.Bool

guard : Bool → List ⊤
guard = bool′ [] [ tt ]

_⋯_ : ℕ → ℕ → List ℕ
_⋯_ = go 0
  where
  go′ : ℕ → ℕ → List ℕ
  go′ i zero = []
  go′ i (suc m) = i ∷ go′ (suc i) m

  go : ℕ → ℕ → ℕ → List ℕ
  go i zero m = i ∷ go′ (suc i) m
  go i (suc n) zero = []
  go i (suc n) (suc m) = go (suc i) n m

infix 4 _==_
_==_ : ℕ → ℕ → Bool
zero  == zero  = true
zero  == suc m = false
suc n == zero  = false
suc n == suc m = n == m
\end{code}
%<*pyth>
\begin{code}
pyth : List (ℕ × ℕ × ℕ)
pyth = do
  x ← 1 ⋯ 10
  y ← 1 ⋯ 10
  z ← 1 ⋯ 10
  guard (x * x + y * y == z * z)
  [ (x , y , z) ]

_ : pyth ≡  [  (3  , 4  , 5   )
            ,  (4  , 3  , 5   )
            ,  (6  , 8  , 10  )
            ,  (8  , 6  , 10  ) ]
_ = refl
\end{code}
%</pyth>
