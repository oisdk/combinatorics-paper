\begin{code}
{-# OPTIONS --without-K #-}
module Snippets.NonCubical where

open import Agda.Primitive using (Level)

Type = λ x → Set x

variable
  a b c : Level
  A : Type a
  B : Type b
  C : Type c
\end{code}
%<*eq-def>
\begin{code}
data _≡_ {A : Type a} (x : A) : A → Type a where
  refl : x ≡ x
\end{code}
%</eq-def>
%<*comb>
\begin{code}
sym : {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong _ refl = refl
\end{code}
%</comb>
\begin{code}
postulate
\end{code}
%<*fun-ext>
\begin{code}
 fun-ext  : {f g : A → B}
          → (∀ x → f x ≡ g x)
          → f ≡ g
\end{code}
%</fun-ext>
%<*j>
\begin{code}
J : (A : Set a) (C : (x y : A) → x ≡ y → Set c)
  → ((x : A) → C x x refl)
  → (m n : A) (P : m ≡ n) → C m n P
J A C b m .m refl = b m
\end{code}
%</j>
%<*k>
\begin{code}
postulate
 K : (A : Set a) (m : A) (C : m ≡ m → Set c)
   → C refl
   → (loop : m ≡ m) → C loop
\end{code}
%</k>
