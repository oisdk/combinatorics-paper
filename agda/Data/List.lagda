\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.List where

open import Prelude
open import Algebra
private
 module ShowDef where
\end{code}
%<*definition>
\begin{code}
  data List {a} (A : Type a) : Type a where
    [] : List A
    _∷_ : A → List A → List A
\end{code}
%</definition>
\begin{code}
open import Agda.Builtin.List using (List; _∷_; []) public

module _ {a} {A : Type a} {p} (P : List A → Type p) where
  foldrP : (∀ x xs → P xs → P (x ∷ xs))
         → P []
         → ∀ xs → P xs
  foldrP f b [] = b
  foldrP f b (x ∷ xs) = f x xs (foldrP f b xs)

foldr : (A → B → B) → B → List A → B
foldr f b [] = b
foldr f b (x ∷ xs) = f x (foldr f b xs)

foldl : (B → A → B) → B → List A → B
foldl f b [] = b
foldl f b (x ∷ xs) = foldl f (f b x) xs

map : (A → B) → List A → List B
map f = foldr (λ x xs → f x ∷ xs) []

length : List A → ℕ
length = foldr (const suc) 0

infixr 0 _⇘_
record _⇘_ {a ℓ} (A : Type a) (P : List A → Type ℓ) : Type (a ℓ⊔ ℓ) where
  constructor elim
  field
    ⟦_⟧[] : P []
    ⟦_⟧_∷_⟨_⟩ : ∀ x xs → P xs → P (x ∷ xs)
  ⟦_⟧⇓ : ∀ xs → P xs
  ⟦_⟧⇓ = foldrP P ⟦_⟧_∷_⟨_⟩ ⟦_⟧[]
open _⇘_

⇘-syntax : ∀ {a ℓ} (A : Type a) (P : List A → Type ℓ) → Type (a ℓ⊔ ℓ)
⇘-syntax = _⇘_
infixr 0 ⇘-syntax

syntax ⇘-syntax A (λ xs → e) = xs ⦂List A ⇘ e

record _↘_ (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  constructor alg
  field
    [_]_∷_ : A → B → B
    [_][] : B
  [_]↓ : List A → B
  [_]↓ = foldr [_]_∷_ [_][]
open _↘_

infixr 0 _↘_

unfoldr : (P : ℕ → Type b)
        → (∀ {n} → P (suc n) → A × P n)
        → ∀ n
        → P n → List A
unfoldr P f zero b = []
unfoldr P f (suc n) b = let (x , xs) = f b in x ∷ unfoldr P f n xs

open import Data.Fin

infixl 6 _!_
\end{code}
%<*indexing>
\begin{code}
_!_ : (xs : List A) → Fin (length xs) → A
(x ∷ xs) ! f0 = x
(x ∷ xs) ! fs i = xs ! i
\end{code}
%</indexing>
%<*concatenation>
\begin{code}
infixr 5 _++_
_++_ : List A → List A → List A
xs ++ ys = foldr _∷_ ys xs
\end{code}
%</concatenation>
\begin{code}

open import Data.Nat
\end{code}
%<*tabulate>
\begin{code}
tabulate : ∀ n → (Fin n → A) → List A
tabulate zero f = []
tabulate (suc n) f = f f0 ∷ tabulate n (f ∘ fs)
\end{code}
%</tabulate>
%<*list-elim>
\begin{code}

-- sum-alg : List⟨ ℕ ⟩→ ℕ
-- [ sum-alg ][] = 0
-- [ sum-alg ] x ∷ xs = x + xs

-- sum : List ℕ → ℕ
-- sum = [ sum-alg ]↓
\end{code}
%</list-elim>
%<*conc-assoc>
\begin{code}
++-assoc : Associative {A = List A} _++_
++-assoc []        ys zs = refl
++-assoc (x ∷ xs)  ys zs =
  cong (x ∷_) (++-assoc xs ys zs)
\end{code}
%</conc-assoc>
\begin{code}
++[] : Identityʳ {A = List A} _++_ []
++[] [] = refl
++[] (x ∷ xs) = cong (x ∷_) (++[] xs)

concat : List (List A) → List A
concat = foldr _++_ []

concatMap : (A → List B) → List A → List B
concatMap f = foldr (λ x ys → f x ++ ys) []
\end{code}
