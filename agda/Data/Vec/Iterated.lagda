\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Vec.Iterated where

open import Prelude hiding (⊤; tt)
open import Data.Fin
open import Data.Unit.UniversePolymorphic

private
  variable
    n : ℕ

module _ (B : Type b) where
\end{code}
%<*def>
\begin{code}
 Vec : ℕ → Type b
 Vec zero     = ⊤
 Vec (suc n)  = B × Vec n
\end{code}
%</def>
\begin{code}
_[_] : Vec A n → Fin n → A
_[_] {n = suc _} xs f0 = fst xs
_[_] {n = suc _} xs (fs i) = snd xs [ i ]

tabulate : (Fin n → A) → Vec A n
tabulate {n = zero} f = tt
tabulate {n = suc n} f = f f0 , tabulate (f ∘ fs)

map : ∀ {n} → (A → B) → Vec A n → Vec B n
map {n = zero} f xs = tt
map {n = suc n} f (fst₁ , snd₁) = f fst₁ , map f snd₁

module _ {a} {A : Type a} {b} (B : ℕ → Type b) where
  foldr : (∀ {n} → A → B n → B (suc n))
        → B zero
        → ∀ {n} → Vec A n → B n
  foldr f b {zero} xs = b
  foldr f b {suc n} (x , xs) = f x (foldr f b xs)

foldr′ : (A → B → B) → B → ∀ {n} → Vec A n → B
foldr′ f b = foldr (const _) f b
\end{code}
%<*iso>
\begin{code}
Vec⇔Fin→ : Vec A n ⇔ (Fin n → A)
\end{code}
%</iso>
\begin{code}
Vec⇔Fin→ = iso _[_] tabulate Ind⇒Vec⇒Ind Vec⇒Ind⇒Vec
  where
  Ind⇒Vec⇒Ind′ : (xs : Fin n → A) → ∀ i → tabulate xs [ i ] ≡ xs i
  Ind⇒Vec⇒Ind′ {n = suc _} f f0 = refl
  Ind⇒Vec⇒Ind′ {n = suc _} f (fs i) = Ind⇒Vec⇒Ind′ (f ∘ fs) i

  Ind⇒Vec⇒Ind : (xs : Fin n → A) → tabulate xs [_] ≡ xs
  Ind⇒Vec⇒Ind f = funExt (Ind⇒Vec⇒Ind′ f)

  Vec⇒Ind⇒Vec : ∀ {n a} {A : Type a} → (xs : Vec A n) → tabulate (xs [_]) ≡ xs
  Vec⇒Ind⇒Vec {n = zero} tt = refl
  Vec⇒Ind⇒Vec {n = suc n} (x , xs) = cong (x ,_) (Vec⇒Ind⇒Vec xs)
\end{code}
