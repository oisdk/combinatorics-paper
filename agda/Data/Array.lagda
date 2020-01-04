\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Array where

open import Prelude hiding (b; true; false)
open import Data.Binary.Zeroless
open import Data.Binary.Zeroless.Order
open import Data.List.Kleene.AsList as List using (List; _∷_; [])
open import Data.Bool using (not; bool)

open import Data.Spine.Binary.Zeroless as Spine hiding (cons; _∷_)
open import Data.Nest
open import Data.Tree.Perfect

private
  variable
    t : Level
    T : ℕ → Type t
    n m : ℕ
    b : Bit
    bs : 𝔹
    F : Type a → Type t

Array : Set a → 𝔹 → Set a
Array A = Spine (Perfect A)

cons : A → Array A bs → Array A (inc bs)
cons = cons^ _,_

foldrP : (B : ℕ → Type c)
       → (∀ {n} → A → B n → B (suc n))
       → ∀ n {m}
       → Perfect A n
       → B (2^ n * m)
       → B (2^ n * suc m)
foldrP B f zero = f
foldrP B f (suc n) =
  foldrP (B ∘ 2*) (λ { (x , y) → f x ∘ f y }) n

foldr : (B : ℕ → Type c)
      → (∀ {n} → A → B n → B (suc n))
      → B 0
      → Array A bs
      → B ⟦ bs ⇓⟧
foldr B f = foldr^ B (foldrP B f)

mutual
  lookup″ : (xs : Array A bs) → ∀ i is → i ∷ is ≤ bs → A
  lookup″ (x 1∷ xs) 2ᵇ is       p = fst (lookup  xs is p)
  lookup″ (x 2∷ xs) 2ᵇ is       p = snd (lookup′ x xs is p)
  lookup″ (x 1∷ xs) 1ᵇ (i ∷ is) p = snd (lookup″ xs i is p)
  lookup″ (x 2∷ xs) 1ᵇ (i ∷ is) p = fst (lookup″ xs i is p)
  lookup″ (x 1∷ xs) 1ᵇ []       p = x
  lookup″ (x 2∷ xs) 1ᵇ []       p = fst x

  lookup′ : (x : A) → (xs : Array A bs) → ∀ is → is ≤ bs → A
  lookup′ x xs []       p = x
  lookup′ x xs (i ∷ is) p = lookup″ xs i is p

  lookup : (xs : Array A bs) → ∀ is → is < bs → A
  lookup (x 1∷ xs) (1ᵇ ∷ is) p = fst (lookup xs is p)
  lookup (x 2∷ xs) (1ᵇ ∷ is) p = snd (lookup′ x xs is p)
  lookup (x 1∷ xs) (2ᵇ ∷ is) p = snd (lookup xs is p)
  lookup (x 2∷ xs) (2ᵇ ∷ is) p = fst (lookup xs is p)
  lookup (x 1∷ xs) []        p = x
  lookup (x 2∷ xs) []        p = fst x

lookup-may : Array A bs → 𝔹 → Maybe A
lookup-may {bs = bs} xs is with is <? bs
... | no ¬p = nothing
... | yes p = just (lookup xs is p)

open import Data.Vec as Vec using (Vec)

toVec : Array A bs → Vec A ⟦ bs ⇓⟧
toVec = foldr (Vec _) Vec._∷_ Vec.[]

fromVec : Vec A n → Array A ⟦ n ⇑⟧
fromVec = Vec.foldr (Array _ ∘ ⟦_⇑⟧) (cons^ _,_) []
\end{code}
