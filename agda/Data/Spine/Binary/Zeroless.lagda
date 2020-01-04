\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Spine.Binary.Zeroless where

open import Prelude hiding (b; true; false)
open import Data.Binary.Zeroless
open import Data.Binary.Zeroless.Order
open import Data.List.Kleene.AsList as List using (List; []) renaming (_∷_ to _∶_)
open import Data.Bool using (not; bool′)
open import Data.Nest

private
  variable
    t : Level
    T : ℕ → Type t
    n m : ℕ
    b : Bit
    bs : 𝔹
    F : Type a → Type t

------------------------------------------------------------------------
-- Definition
------------------------------------------------------------------------

infixr 5 _1∷_ _2∷_ _∷_
data Spine (T : ℕ → Type a) : 𝔹 → Type a where
  []  : Spine T []
  _∷_ : T (bool′ 0 1 b) → Spine (T ∘ suc) bs → Spine T (b ∶ bs)

pattern _1∷_ x xs = _∷_ {b = 1ᵇ} x xs
pattern _2∷_ x xs = _∷_ {b = 2ᵇ} x xs

------------------------------------------------------------------------
-- Construction
------------------------------------------------------------------------

cons : (_∙_ : ∀ {n} → T n → T n → T (suc n))
     → T 0 → Spine T bs → Spine T (inc bs)
cons _∙_ x [] = x 1∷ []
cons _∙_ x (y 1∷ ys) = (x ∙ y) 2∷ ys
cons _∙_ x (y 2∷ ys) = x 1∷ cons _∙_ y ys

cons^ : (∀ {A} → A → A → F A) → A → Spine (Nest F A) bs → Spine (Nest F A) (inc bs)
cons^ _∙_ x [] = x ∷ []
cons^ _∙_ x (y 1∷ ys) = (x ∙ y) 2∷ ys
cons^ _∙_ x (y 2∷ ys) = x ∷ cons^ _∙_ y ys

------------------------------------------------------------------------
-- Folds
------------------------------------------------------------------------

2^_*_ : ℕ → ℕ → ℕ
2^ zero  * n = n
2^ suc m * n = 2* (2^ m * n)

foldr^ : (A : ℕ → Type a)
       → (∀ n {m} → T n → A (2^ n * m) → A (2^ n * suc m))
       → A 0 → Spine T bs → A ⟦ bs ⇓⟧
foldr^ A c b []        = b
foldr^ A c b (x 1∷ xs) = c 0 x (foldr^ (A ∘ 2*) (c ∘ suc) b xs)
foldr^ {bs = 2ᵇ ∶ bs} A c b (x 2∷ xs) = c 1 {m = ⟦ bs ⇓⟧} x (foldr^ (A ∘ 2*) (c ∘ suc) b xs)
\end{code}
