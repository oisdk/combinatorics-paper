{-# OPTIONS --cubical --safe #-}

module Data.List.Filter where

open import Prelude
open import Data.List
open import Data.List.Membership
open import Data.Sigma.Properties
open import Data.Bool.Properties
open import Data.Fin

filter : (p : A → Bool) → List A → List (∃ (T ∘ p))
filter p = foldr f []
  where
  f : _ → List (∃ (T ∘ p)) → List (∃ (T ∘ p))
  f y ys with T? (p y)
  ... | yes t = (y , t) ∷ ys
  ... | no _  = ys

filter-preserves : (p : A → Bool) (xs : List A) →
                   (x : A) →
                   (v : T (p x)) →
                   (x ∈ xs) →
                   ((x , v) ∈ filter p xs)
filter-preserves p (x ∷ xs) y v (n , y∈xs) with T? (p x)
filter-preserves p (x ∷ xs) y v (f0   , y∈xs) | yes t = f0 , ΣProp≡ (isPropT ∘ p) y∈xs
filter-preserves p (x ∷ xs) y v (fs n , y∈xs) | yes t = let m , q = filter-preserves p xs y v (n , y∈xs) in fs m , q
filter-preserves p (x ∷ xs) y v (f0   , y∈xs) | no ¬t = ⊥-elim (¬t (subst (T ∘ p) (sym y∈xs) v))
filter-preserves p (x ∷ xs) y v (fs n , y∈xs) | no ¬t = filter-preserves p xs y v (n , y∈xs)
