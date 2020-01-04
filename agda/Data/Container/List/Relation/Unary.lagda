\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Container.List.Relation.Unary where

open import Data.Container.List
open import Data.Container.Relation.Unary ℒ public
open import Prelude
open import Data.Fin

-- module Exists {a} {A : Type a} {p} (P : A → Type p) where
--   int⇔ext : ∀ {x xs} → P x ⊎ ◇ P xs ⇔ ◇ P (x ∷ xs)
--   int⇔ext .fun  (inl     Px)       = f0 ,  Px
--   int⇔ext .inv  (f0 ,  Px)       = inl     Px
--   int⇔ext .fun  (inr (  n , Pxs))  = fs    n , Pxs
--   int⇔ext .inv  (fs    n , Pxs)   = inr (  n , Pxs)

--   int⇔ext .leftInv   (inl  Px)       i = inl  Px
--   int⇔ext .leftInv   (inr  Pxs)      i = inr  Pxs
--   int⇔ext .rightInv  (f0   , Px)   i = f0   , Px
--   int⇔ext .rightInv  (fs n  , Pxs)  i = fs n  , Pxs

--   push! : ∀ {x xs} → ¬ P x → ◇! P xs → ◇! P (x ∷ xs)
--   push! ¬Px x∈!xs .fst = int⇔ext .fun (inr (x∈!xs .fst))
--   push! ¬Px x∈!xs .snd (f0   , px) = ⊥-elim (¬Px px)
--   push! ¬Px x∈!xs .snd (fs n  , y∈xs) i = int⇔ext .fun (inr (x∈!xs .snd (n , y∈xs) i))

--   pull! : ∀ {x xs} → ¬ P x → ◇! P (x ∷ xs) → ◇! P xs
--   pull! ¬Px ((f0   , px    ) , uniq) = ⊥-elim (¬Px px)
--   pull! ¬Px ((fs n  , x∈xs  ) , uniq) .fst = (n , x∈xs)
--   pull! ¬Px ((fs n  , x∈xs  ) , uniq) .snd (m , x∈xs′) i =
--     ⟦l ⊥-elim ∘ ¬Px ,r id ⟧ (int⇔ext .inv (uniq (fs m , x∈xs′ ) i))
\end{code}
