{-# OPTIONS --cubical --safe #-}

module Dyck where

open import Prelude
open import Data.List
open import Cardinality.Finite.SplitEnumerable
open import Cardinality.Finite.SplitEnumerable.Inductive
open import Data.Fin
open import Data.List.Membership

private
  variable
    n m : ℕ

infixr 5 ⟨_ ⟩_
data Dyck : ℕ → ℕ → Type₀ where
  done : Dyck 0 0
  ⟨_ : Dyck (suc n) m → Dyck n (suc m)
  ⟩_ : Dyck n m → Dyck (suc n) m

Bal : ℕ → Type₀
Bal = Dyck 0

support-dyck : ∀ n m → List (Dyck n m)
support-dyck = λ n m → end n m ++ ( lefts n m ++ rights n m )
  module ListDyck where
  lefts : ∀ n m → List (Dyck n m)
  lefts n zero    = []
  lefts n (suc m) = map ⟨_ (support-dyck (suc n) m)

  rights : ∀ n m → List (Dyck n m)
  rights (suc n) m = map ⟩_ (support-dyck n m)
  rights zero    m = []

  end : ∀ n m → List (Dyck n m)
  end (suc _) _ = []
  end zero (suc _) = []
  end zero zero = done ∷ []


cover-dyck : (x : Dyck n m) → x ∈ support-dyck n m
cover-dyck {.0} {.0} done = f0 , refl
cover-dyck {n} {suc m} (⟨ x) =
  ListDyck.end n (suc m) ++◇ ListDyck.lefts n (suc m) ◇++ cong-∈ ⟨_ (support-dyck (suc n) m) (cover-dyck x)
cover-dyck {suc n} {m} (⟩ x) =
  ListDyck.lefts (suc n) m ++◇ cong-∈ ⟩_ (support-dyck n m) (cover-dyck x)

ℰ!⟨Dyck⟩ : ℰ! (Dyck n m)
ℰ!⟨Dyck⟩ .fst = support-dyck _ _
ℰ!⟨Dyck⟩ .snd = cover-dyck
