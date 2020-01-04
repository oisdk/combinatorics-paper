\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Container.List where

open import Prelude
open import Data.Container
open import Data.Fin
open import Data.List.Properties
open import Data.List using (List; tabulate; length ; _!_) renaming (_∷_ to _L∷_; [] to L[])
open import Data.Maybe using (maybe′)
\end{code}
%<*def>
\begin{code}
ℒ : Container ℓ-zero ℓ-zero
ℒ = ℕ ▷ Fin
\end{code}
%</def>
\begin{code}

ℒ→List : ⟦ ℒ ⟧ A → List A
ℒ→List = uncurry tabulate

List→ℒ : List A → ⟦ ℒ ⟧ A
List→ℒ xs .fst = length xs
List→ℒ xs .snd i = xs ! i

ℒ→List→ℒ : ∀ n (xs : Fin n → A) → List→ℒ (ℒ→List (n , xs)) ≡ (n , xs)
ℒ→List→ℒ n xs i .fst = tab-length n xs i
ℒ→List→ℒ n xs i .snd = tab-id n xs i

List→ℒ→List : ∀ (xs : List A) → ℒ→List (List→ℒ xs) ≡ xs
List→ℒ→List L[] _ = L[]
List→ℒ→List (x L∷ xs) i = x L∷ List→ℒ→List xs i

List⇔ℒ : List A ⇔ ⟦ ℒ ⟧ A
List⇔ℒ .fun = List→ℒ
List⇔ℒ .inv = ℒ→List
List⇔ℒ .rightInv  = uncurry ℒ→List→ℒ
List⇔ℒ .leftInv = List→ℒ→List
\end{code}
%<*foldr>
\begin{code}
foldr : (A → B → B) → B → ⟦ ℒ ⟧ A → B
foldr f b = uncurry go
  where
  go : _
  go zero     _  = b
  go (suc n)  k  = f (k f0) (go n (k ∘ fs))
\end{code}
%</foldr>
