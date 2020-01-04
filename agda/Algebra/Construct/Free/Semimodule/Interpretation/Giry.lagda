\begin{code}
{-# OPTIONS --cubical --safe #-}

open import Algebra
open import Prelude

module Algebra.Construct.Free.Semimodule.Interpretation.Giry {s} (rng : Semiring s) (sIsSet : isSet (Semiring.𝑅 rng)) where

open Semiring rng
open import Algebra.Construct.Free.Semimodule.Definition rng
-- open import Algebra.Construct.Free.Semimodule.Eliminators rng
open import Algebra.Construct.Free.Semimodule.Operations rng sIsSet
open import Probability.Giry rng
open import Cardinality.Finite
open import Data.List
open import Relation.Nullary
open import Data.Bool using (bool)

open _↘_ renaming ([_]↓ to List[_]↓)

𝒢⇒* : ℰ A → 𝒢 A → 𝒱 A
𝒢⇒* = λ fa g → List[ 𝒢⇒*′ (ℰ⇒Discrete fa) g  ]↓ (fst (ℰ⇒ℬ fa))
  where
  𝒢⇒*′ : Discrete A → 𝒢 A → (A ↘ 𝒱 A)
  [ 𝒢⇒*′ _≟_ g ][] = []
  [ 𝒢⇒*′ _≟_ g ] x ∷ xs = x ∶ g (bool 0# 1# ∘ does ∘ _≟_ x) , xs

-- *⇔𝒢 : 𝒦 A → (A *) ⇔ 𝒢 A
-- *⇔𝒢 {A = A} fa = iso ∫ (𝒢⇒* fa) 𝒢⇒*⇒𝒢 *⇒𝒢⇒*
--   where
--   *⇒𝒢⇒* : (x : A *) → 𝒢⇒* fa (∫ x) ≡ x
--   *⇒𝒢⇒* = {!!}
--   𝒢⇒*⇒𝒢 : (x : 𝒢 A) → ∫ (𝒢⇒* fa x) ≡ x
--   𝒢⇒*⇒𝒢 = {!!}

\end{code}
