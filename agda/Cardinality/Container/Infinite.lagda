\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections --sized-types #-}

module Cardinality.Container.Infinite where

open import Prelude
open import Data.List.Kleene
open import Data.Fin
import Data.Nat as ℕ
open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.Prelude using (J)
import Data.List.Kleene.Membership as Kleene
open import Codata.Stream.Extensional.Base
open import Codata.Stream.Extensional.Membership
open import Codata.Stream.Extensional.Iso

private
  variable
    u : Level
    U : A → Type u
    s : Level
    S : ℕ → Type s

ℰ! : Type a → Type a
ℰ! A = Σ[ support ∈ Stream A ] ∀ x → x ∈ support

mutual
\end{code}
%<*conv>
\begin{code}
  convΣ⋆ : Stream A → (∀ x → Stream (U x)) → Stream (Σ A U ⋆)
  convΣ⋆ xs ys zero     = []
  convΣ⋆ xs ys (suc n)  = ∹ convΣ xs ys n

  convΣ : Stream A → (∀ x → Stream (U x)) → Stream (Σ A U ⁺)
  convΣ xs ys n .head  = x , ys x n where x = xs zero
  convΣ xs ys n .tail  = convΣ⋆ (xs ∘ suc) ys n
\end{code}
%</conv>
\begin{code}
cantor : Stream A → (∀ x → Stream (U x)) → Stream (Σ A U)
cantor xs ys = concat (convΣ xs ys)

convΣ-cover : ∀ (x : A) xs (y : U x) (ys : ∀ x → Stream (U x)) → x ∈ xs → y ∈ ys x → (x , y) ∈² convΣ xs ys
convΣ-cover {U = U} x xs y ys (n , x∈xs) (m , y∈ys) = (n ℕ.+ m) , lemma xs n x∈xs
  where
  lemma : ∀ xs n → xs n ≡ x → (x , y) Kleene.∈⁺ convΣ xs ys (n ℕ.+ m)
  lemma xs zero    x∈xs .fst = f0
  lemma xs zero    x∈xs .snd i .fst = x∈xs i
  lemma xs zero    x∈xs .snd i .snd = J (λ z z≡ → PathP (λ j → U (sym z≡ j)) (ys z m) y) y∈ys (sym x∈xs) i
  lemma xs (suc n) x∈xs = let i , p = lemma (xs ∘ suc) n x∈xs in fs i , p

_|Σ|_ : ℰ! A → (∀ x → ℰ! (U x)) → ℰ! (Σ A U)
(xs |Σ| ys) .fst = cantor (xs .fst) (fst ∘ ys)
(xs |Σ| ys) .snd (x , y) =
  concat-∈
    (x , y)
    (convΣ (xs .fst) (fst ∘ ys))
    (convΣ-cover x (xs .fst) y (fst ∘ ys) (xs .snd x) (ys x .snd y))

-- module _ (xs : Stream A) where
--   mutual
--     star⁺ : (A ⋆ → B) → B ⋆ → Stream (B ⁺)
--     star⁺ k ks zero    = k [] & ks
--     star⁺ k ks (suc i) = plus⁺ zero (k ∘ ∹_) ks i

--     plus⋆ : ℕ → (A ⁺ → B) → B ⋆ → Stream (B ⋆)
--     plus⋆ n k ks zero    = ks
--     plus⋆ n k ks (suc i) = ∹ plus⁺ n k ks i

--     plus⁺ : ℕ → (A ⁺ → B) → B ⋆ → Stream (B ⁺)
--     plus⁺ n k ks i = star⁺ (k ∘ (xs n &_)) (plus⋆ (suc n) k ks i) i

--   star : Stream (A ⋆)
--   star = concat (star⁺ id [])

--   plus : Stream (A ⁺)
--   plus = concat (plus⁺ zero id [])

--   -- module _ (cover : ∀ x → x ∈ xs) where
--   --   mutual
--   --     star⁺-cover : (k : A ⋆ → B) → (ks : B ⋆) → ∀ x → k x ∈² star⁺ k ks
--   --     star⁺-cover k ks [] = zero , f0 , refl
--   --     star⁺-cover k ks (∹ x) = let n , p = plus⁺-cover zero (k ∘ ∹_) ks x in suc n , p

--   --     plus⁺-cover : ∀ n (k : A ⁺ → B) (ks : B ⋆) → ∀ x → k x ∈² plus⁺ n k ks
--   --     plus⁺-cover n k ks (x & xxs) = let m , p = cover x in {!!}
