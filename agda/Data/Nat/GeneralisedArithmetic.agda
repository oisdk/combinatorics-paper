{-# OPTIONS --cubical --safe #-}

module Data.Nat.GeneralisedArithmetic where

open import Data.Nat
open import Prelude

fold : ℕ → (A → A) → A → A
fold zero f x = x
fold (suc n) f x = f (fold n f x)

+-distrib : ∀ n m (f : A → A) → fold n f ∘ fold m f ≡ fold (n + m) f
+-distrib zero m _ = refl
+-distrib (suc n) m f = cong (f ∘_) (+-distrib n m f)

*-distrib : ∀ n m → fold {a} {A} n ∘ fold m ≡ fold (n * m)
*-distrib zero m = refl
*-distrib (suc n) m =  funExt (λ f → cong (fold m f ∘_) (cong (_$ f) (*-distrib n m)) ; +-distrib m (n * m) f)
