\begin{code}
{-# OPTIONS --cubical --safe #-}

module Dyck where

open import Prelude hiding (_⟨_⟩_)
open import Data.List
open import Cardinality.Finite.SplitEnumerable
open import Cardinality.Finite.SplitEnumerable.Inductive
open import Data.Fin
open import Data.List.Membership
import Data.Nat as ℕ
open import Agda.Builtin.Nat using (_-_; _+_)
open import Data.Nat.Properties using (pred)
open import Data.Vec.Iterated

private
  variable
    n m k : ℕ
infixr 6 ⟨_ ⟩_
\end{code}
%<*dyck-def>
\begin{code}
data Dyck : ℕ → ℕ → Type₀ where
  done : Dyck zero zero
  ⟨_ : Dyck (suc n) m → Dyck n (suc m)
  ⟩_ : Dyck n m → Dyck (suc n) m
\end{code}
%</dyck-def>
\begin{code}
private
  module DyckExamples where
\end{code}
%<*dyck-0-2>
\begin{code}
    _ : Dyck 0 2
    _ = ⟨ ⟩ ⟨ ⟩ done
\end{code}
%</dyck-0-2>
%<*dyck-0-3>
\begin{code}
    _ : Dyck 0 3
    _ = ⟨ ⟩ ⟨ ⟨ ⟩ ⟩ done
\end{code}
%</dyck-0-3>
%<*dyck-1-2>
\begin{code}
    _ : Dyck 1 2
    _ = ⟩ ⟨ ⟩ ⟨ ⟩ done
\end{code}
%</dyck-1-2>
\begin{code}
-- module _ {p} (P : ℕ → ℕ → Type p)
--              (lbrack : ∀ {n m} → P (suc n) m → P n (suc m))
--              (rbrack : ∀ {n m} → P n m → P (suc n) m)
--              (base : P 0 0)
--              where
--   foldrDyck : Dyck n m → P n m
--   foldrDyck done = base
--   foldrDyck (⟨ x) = lbrack (foldrDyck x)
--   foldrDyck (⟩ x) = rbrack (foldrDyck x)

Bal : ℕ → Type₀
Bal = Dyck 0

Diff : Type₀ → Type₁
Diff A = ∀ {B : Type₀} → (A → B) → List B → List B

support-dyck : ∀ n m → List (Dyck n m)
support-dyck = λ n m → sup-k n m id []
  module ListDyck where
  mutual
    sup-k : ∀ n m → Diff (Dyck n m)
    sup-k n m k = end n m k ∘ lefts n m k ∘ rights n m k

    lefts : ∀ n m → Diff (Dyck n m)
    lefts n zero    k = id
    lefts n (suc m) k = sup-k (suc n) m (k ∘ ⟨_)

    rights : ∀ n m → Diff (Dyck n m)
    rights (suc n) m k = sup-k n m (k ∘ ⟩_)
    rights zero    m k = id

    end : ∀ n m → Diff (Dyck n m)
    end (suc _) _    k = id
    end zero (suc _) k = id
    end zero zero    k xs = k done ∷ xs

cover-dyck : (x : Dyck n m) → x ∈ support-dyck n m
cover-dyck x = go _ _ x id []
  where
  open ListDyck

  mutual
    pushLefts : ∀ n m (k : Dyck n m → B) x xs → x ∈ xs → x ∈ lefts n m k xs
    pushLefts n (suc m) k = pushSup (suc n) m (λ z → k (⟨ z))
    pushLefts _ zero    k x xs p = p

    pushEnd : ∀ n m (k : Dyck n m → B) x xs → x ∈ xs → x ∈ end n m k xs
    pushEnd (suc _) _ k x xs p = p
    pushEnd zero (suc _) k x xs p = p
    pushEnd zero zero k x xs (i , p) = fs i , p

    pushRights : ∀ n m (k : Dyck n m → B) x xs → x ∈ xs → x ∈ rights n m k xs
    pushRights (suc n) m k = pushSup n m (λ z → k (⟩ z))
    pushRights zero _ k x xs p = p

    pushSup : ∀ n m (k : Dyck n m → B) x xs → x ∈ xs → x ∈ sup-k n m k xs
    pushSup n m k x xs p = pushEnd n m k x (lefts n m k (rights n m k xs)) (pushLefts n m k x (rights n m k xs) (pushRights n m k x xs p))

  go : ∀ n m → (x : Dyck n m) → (k : Dyck n m → A) → (xs : List A) → k x ∈ sup-k n m k xs
  go zero zero done k xs = f0 , refl
  go zero    (suc m) (⟨ x) k xs = go (suc zero) m x (k ∘ ⟨_) (rights (zero) (suc m) k xs)
  go (suc n) (suc m) (⟨ x) k xs = go (suc (suc n)) m x (k ∘ ⟨_) (rights (suc n) (suc m) k xs)
  go (suc n) m (⟩ x) k xs =
    let p = go n m x (k ∘ ⟩_) xs
    in pushEnd (suc n) m k (k (⟩ x)) (lefts (suc n) m k _) (pushLefts (suc n) m k (k (⟩ x)) (rights (suc n) m k xs) p)

ℰ!⟨Dyck⟩ : ℰ! (Dyck n m)
ℰ!⟨Dyck⟩ .fst = support-dyck _ _
ℰ!⟨Dyck⟩ .snd = cover-dyck

private
  module NonParamTree where
\end{code}
%<*tree-simpl-def>
\begin{code}
    data Tree : Type₀ where
      leaf : Tree
      _*_ : Tree → Tree → Tree
\end{code}
%</tree-simpl-def>
%<*from-dyck>
\begin{code}
    dyck→tree : Dyck zero n → Tree
    dyck→tree d = go d (leaf , _)
      where
      go : Dyck n m → Vec Tree (suc n) → Tree
      go (⟨ d)  ts              = go d (leaf , ts)
      go (⟩ d)  (t₁ , t₂ , ts)  = go d (t₂ * t₁ , ts)
      go done   (t , _)         = t
\end{code}
%</from-dyck>
\begin{code}
data Tree (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  leaf : B → Tree A B
  node : A → Tree A B → Tree A B → Tree A B

fromDyck′ : Dyck n m → Tree A B → Vec (Tree A B) n → Vec B m → Vec A m → Vec A n → Tree A B
fromDyck′ done   t _       vls        ops₁ ops₂ = t
fromDyck′ (⟩ xs) x (y , s) vls        ops₁ (op , ops₂) = fromDyck′ xs (node op y x) s vls ops₁ ops₂
fromDyck′ (⟨ xs) t s       (vl , vls) (op , ops₁) ops₂ = fromDyck′ xs (leaf vl) (t , s) vls ops₁ (op , ops₂)

fromDyck : Dyck 0 n → Vec A n → Vec B (suc n) → Tree A B
fromDyck xs ops (val , vals) = fromDyck′ xs (leaf val) _ vals ops _

-- data Tree : Type₀ where
--   leaf : Tree
--   _*_ : Tree → Tree → Tree

-- sz : Tree → ℕ → ℕ
-- sz leaf     = id
-- sz (xs * ys) = sz xs ∘ suc ∘ sz ys

-- size : Tree → ℕ
-- size t = sz t 0

-- toDyck′ : (t : Tree) → Dyck n m → Dyck n (sz t m)
-- toDyck′ leaf = id
-- toDyck′ (xs * ys) = toDyck′ xs ∘ ⟨_ ∘ toDyck′ ys ∘ ⟩_

-- toDyck : (t : Tree) → Bal (size t)
-- toDyck t = toDyck′ t done

-- fromDyck-size : (xs : Dyck 0 n) → size (fromDyck xs) ≡ n
-- fromDyck-size d = go d leaf []
--   where
--   sizes : Vec Tree n → ℕ → ℕ
--   sizes = foldr′ (λ x xs → xs ∘ sz x ∘ suc) id

--   go : (d : Dyck n m) → (t : Tree) → (st : Vec Tree n) → sz (fromDyck′ d t st) 0 ≡ sizes st (sz t m)
--   go done  t []       = refl
--   go (⟨ d) t st       = go d leaf (t ∷ st)
--   go (⟩ d) x (y ∷ st) = go d (y * x) st

-- Sized : ℕ → Type₀
-- Sized n = Σ[ t ⦂ Tree ] (size t ≡ n)

-- fromDyck-sized : Dyck 0 n → Sized n
-- fromDyck-sized d = fromDyck d , fromDyck-size d

-- toDyck-sized : Sized n → Dyck 0 n
-- toDyck-sized (xs , p) = subst (Dyck 0) p (toDyck xs)
\end{code}
