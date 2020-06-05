{-# OPTIONS --cubical --safe #-}

module Dyck where

open import Prelude
open import Data.List
open import Cardinality.Finite.SplitEnumerable
open import Cardinality.Finite.SplitEnumerable.Inductive
open import Data.Fin
open import Data.List.Membership
import Data.Nat as ℕ
open import Agda.Builtin.Nat using (_-_)
open import Data.Nat.Properties using (pred)

private
  variable
    n m k : ℕ

infixr 6 ⟨_ ⟩_
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

data Tree : Type₀ where
  leaf : Tree
  _*_ : Tree → Tree → Tree

sz : Tree → ℕ → ℕ
sz leaf     = id
sz (xs * ys) = sz xs ∘ suc ∘ sz ys

size : Tree → ℕ
size t = sz t 0

toDyck′ : (t : Tree) → Dyck n m → Dyck n (sz t m)
toDyck′ leaf = id
toDyck′ (xs * ys) = toDyck′ xs ∘ ⟨_ ∘ toDyck′ ys ∘ ⟩_

toDyck : (t : Tree) → Bal (size t)
toDyck t = toDyck′ t done

infixr 5 _∷_
data Vec (A : Type a) : ℕ → Type a where
  [] : Vec A 0
  _∷_ : A → Vec A n → Vec A (suc n)

fromDyck′ : Dyck n m → Vec Tree (suc n) → Tree
fromDyck′ done   (x ∷ [])    = x
fromDyck′ (⟨ xs) s           = fromDyck′ xs (leaf ∷ s)
fromDyck′ (⟩ xs) (x ∷ y ∷ s) = fromDyck′ xs ((y * x) ∷ s)

fromDyck : Dyck 0 n → Tree
fromDyck xs = fromDyck′ xs (leaf ∷ [])

fromDyck-size : (xs : Dyck 0 n) → size (fromDyck xs) ≡ n
fromDyck-size d = go d (leaf ∷ [])
  where
  sizes : Vec Tree (suc n) → ℕ → ℕ
  sizes (x ∷ []) = sz x
  sizes (x ∷ y ∷ ys) = sizes (y ∷ ys) ∘ suc ∘ sz x

  go : (d : Dyck n m) → (st : Vec Tree (suc n)) → sz (fromDyck′ d st) 0 ≡ sizes st m
  go done (x ∷ []) = refl
  go (⟨ d) (x ∷ st) = go d (leaf ∷ x ∷ st)
  go (⟩ d) (x ∷ y ∷ []) = go d ((y * x) ∷ [])
  go (⟩ d) (x ∷ y ∷ (x₁ ∷ st)) = go d ((y * x) ∷ (x₁ ∷ st))
