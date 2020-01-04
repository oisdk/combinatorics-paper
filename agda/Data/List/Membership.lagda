\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.List.Membership where

open import Data.List
open import Data.Fin
open import Data.Fin.Properties
open import Prelude
open import Relation.Nullary
open import Path.Reasoning
open import Data.List.Relation.Unary as Relation using (module Exists; module Congruence; ◇; ◇!)
import Data.Nat as ℕ
open import Data.List.Properties

module _ {a} {A : Type a} {x : A} where
  open Exists (_≡ x)
    using (push; pull; push!; pull!; here!; _◇++_; _++◇_)
    renaming (◇? to _∈?_)
    public

infixr 5 _∈_ _∈!_ _∉_
\end{code}
%<*in-def>
\begin{code}
_∈_ : A → List A → Type _
x ∈ xs = ◇ (_≡ x) xs
\end{code}
%</in-def>
\begin{code}
module Preliminary where
\end{code}
%<*in-uniq>
\begin{code}
 _∈!_ : A → List A → Type _
 x ∈! xs = isContr (x ∈ xs)
\end{code}
%</in-uniq>
\begin{code}
_∉_ : {A : Type a} → A → List A → Type a
x ∉ xs = ¬ (x ∈ xs)
\end{code}
\begin{code}
_∈!_ : A → List A → Type _
x ∈! xs = ◇! (_≡ x) xs
\end{code}
%<*cong-in>
\begin{code}
cong-∈ : ∀ (f : A → B) {x : A} xs → x ∈ xs → f x ∈ map f xs
cong-∈ f {x} = Congruence.cong-◇ (_≡ x) (_≡ (f x)) (cong f)
\end{code}
%</cong-in>
%<*fin-in-tabulate>
\begin{code}
fin∈tabulate :  ∀ {n}
                (f : Fin n → A)
                (i : Fin n) →
                f i ∈ tabulate n f
fin∈tabulate {n = suc _} f f0     = f0 , refl
fin∈tabulate {n = suc _} f (fs i)  =
  push (fin∈tabulate (f ∘ fs) i)
\end{code}
%</fin-in-tabulate>
\begin{code}
open import Function.Injective

f⟨i⟩∈!tab⟨f⟩ : ∀ {n} → isSet A → (f : Fin n ↣ A) → {x : A} (i : Fin n) → (f .fst i ≡ x) → x ∈! tabulate n (f .fst)
f⟨i⟩∈!tab⟨f⟩ {n = suc _} isSetA f (fs i) p = push! (λ q → ℕ.znots (cong FinToℕ (f .snd _ _ (q ; sym p)))) (f⟨i⟩∈!tab⟨f⟩ isSetA (fin-inj-suc f) i p)
f⟨i⟩∈!tab⟨f⟩ {n = suc _}isSetA f f0 p .fst = f0 , p
f⟨i⟩∈!tab⟨f⟩ {n = suc _}isSetA f f0 p .snd (f0  , q) = cong (f0 ,_) (isSetA (f .fst f0) _ p q)
f⟨i⟩∈!tab⟨f⟩ {n = suc _}isSetA f f0 p .snd (fs n , q) =
  let (i , r) = tab-distrib _ (f .fst ∘ fs) n
  in ⊥-elim (ℕ.snotz (cong FinToℕ (f .snd _ _ (r ; q ; sym p))))
\end{code}
%<*at>
\begin{code}
at : ∀ {xs : List A} (n : Fin (length xs)) → (xs ! n) ∈ xs
at n = n , refl
\end{code}
%</at>
\begin{code}
module _ {a} {A : Set a} (_≟_ : Discrete A) where
  isSet⟨A⟩ : isSet A
  isSet⟨A⟩ = Discrete→isSet _≟_

  infixl 6 _\\_
\end{code}
%<*uniques>
\begin{code}
  _\\_ : List A → A → List A
  xs \\ x = foldr f [] xs
    where
    f : A → List A → List A
    f y xs with x ≟ y
    ... | yes p = xs
    ... | no  p = y ∷ xs

  uniques : List A → List A
  uniques = foldr f []
    where
    f : A → List A → List A
    f x xs = x ∷ (xs \\ x)
\end{code}
%</uniques>
%<*not-in-removed>
\begin{code}
  x∉xs\\x : ∀ x xs → x ∉ xs \\ x
  x∉xs\\x x (y ∷ xs) (n , x∈xs) with x ≟ y
  x∉xs\\x x (y ∷ xs) (n      , x∈xs)  | yes p = x∉xs\\x x xs (n , x∈xs)
  x∉xs\\x x (y ∷ xs) (f0   , y≡x)   | no ¬p = ¬p (sym y≡x)
  x∉xs\\x x (y ∷ xs) (fs n  , x∈xs)  | no ¬p = x∉xs\\x x xs (n , x∈xs)
\end{code}
%</not-in-removed>
%<*cons-remove>
\begin{code}
  x∈!x∷xs\\x : ∀ x xs → x ∈! x ∷ xs \\ x
  x∈!x∷xs\\x x xs = here! (refl , isSet⟨A⟩ _ _ refl) (x∉xs\\x x xs)
\end{code}
%</cons-remove>
%<*remove-other>
\begin{code}
  x∉xs⇒x∉xs\\y : ∀ (x : A) y xs → x ∉ xs → x ∉ xs \\ y
  x∉xs⇒x∉xs\\y x y (z ∷ xs) x∉xs x∈xs\\y with y ≟ z
  x∉xs⇒x∉xs\\y x y (z ∷ xs) x∉xs x∈xs\\y | yes p =
    x∉xs⇒x∉xs\\y x y xs (x∉xs ∘ push) x∈xs\\y
  x∉xs⇒x∉xs\\y x y (z ∷ xs) x∉xs (f0  , x∈xs\\y) | no ¬p =
    x∉xs (f0 , x∈xs\\y)
  x∉xs⇒x∉xs\\y x y (z ∷ xs) x∉xs (fs n , x∈xs\\y) | no ¬p =
    x∉xs⇒x∉xs\\y x y xs (x∉xs ∘ push) (n , x∈xs\\y)
\end{code}
%</remove-other>
%<*unique-remove-other>
\begin{code}
  x∈!xs⇒x∈!xs\\y : ∀ (x : A) y xs → y ≢ x → x ∈! xs → x ∈! xs \\ y
  x∈!xs⇒x∈!xs\\y x y (z ∷ xs) y≢x x∈!xs with y ≟ z
  x∈!xs⇒x∈!xs\\y x y (z ∷ xs) y≢x x∈!xs | yes p =
    x∈!xs⇒x∈!xs\\y x y xs y≢x (pull! (y≢x ∘ p ;_) x∈!xs)
  x∈!xs⇒x∈!xs\\y x y (z ∷ xs) y≢x ((f0  , x∈xs) , uniq) | no ¬p =
    here! (x∈xs , isSet⟨A⟩ _ _ _) (x∉xs⇒x∉xs\\y x y xs (ℕ.znots ∘ cong FinToℕ ∘ cong fst ∘ uniq ∘ push))
  x∈!xs⇒x∈!xs\\y x y (z ∷ xs) y≢x ((fs n , x∈xs) , uniq) | no ¬p =
    push! z≢x (x∈!xs⇒x∈!xs\\y x y xs y≢x (pull! z≢x ((fs n , x∈xs) , uniq)))
    where z≢x = ℕ.snotz ∘ cong FinToℕ ∘ cong fst ∘ uniq ∘ (f0 ,_)
\end{code}
%</unique-remove-other>
%<*unique-preserves>
\begin{code}
  ∈⇒∈! : (x : A) (xs : List A) → x ∈ xs → x ∈! uniques xs
  ∈⇒∈! x (y ∷ xs) (f0  , x∈xs) =
    subst (_∈! (y ∷ uniques xs \\ y)) x∈xs (x∈!x∷xs\\x y (uniques xs))
  ∈⇒∈! x (y ∷ xs) (fs n , x∈xs) with y ≟ x
  ... | yes p = subst (_∈! (y ∷ uniques xs \\ y)) p (x∈!x∷xs\\x y (uniques xs))
  ... | no ¬p = push! ¬p (x∈!xs⇒x∈!xs\\y x y (uniques xs) ¬p (∈⇒∈! x xs (n , x∈xs)))
\end{code}
%</unique-preserves>
\begin{code}
infixr 5 _∈²_
_∈²_ : A → List (List A) → Type _
x ∈² xs = ◇ (x ∈_) xs

∈²→∈ : ∀ {x : A} xs → x ∈² xs → x ∈ concat xs
∈²→∈ = Relation.◇-concat (_≡ _)
\end{code}
