\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

module HITs.Logic where

open import Prelude hiding (⊤; ⊥)
open import Data.Unit.UniversePolymorphic
open import Data.Empty.UniversePolymorphic
open import Cubical.Foundations.HLevels
open import Algebra
open import HITs.PropositionalTruncation.Sugar

infixl 7 _∧_
_∧_ : Type a → Type b → Type (a ℓ⊔ b)
x ∧ y = x × y

infixl 6 _∨_
_∨_ : Type a → Type b → Type (a ℓ⊔ b)
x ∨ y = x ⊎ y

True : Type a
True = ⊤

False : Type a
False = ⊥

∨-assoc : ∀ {xs ys zs : Type a} → ((xs ∨ ys) ∨ zs) ⇔ (xs ∨ (ys ∨ zs))
∨-assoc .fun (inl (inl x)) = inl x
∨-assoc .fun (inl (inr x)) = inr (inl x)
∨-assoc .fun (inr x) = inr (inr x)
∨-assoc .inv (inl x) = inl (inl x)
∨-assoc .inv (inr (inl x)) = inl (inr x)
∨-assoc .inv (inr (inr x)) = inr x
∨-assoc .rightInv (inl x) i = inl x
∨-assoc .rightInv (inr (inl x)) i = inr (inl x)
∨-assoc .rightInv (inr (inr x)) i = inr (inr x)
∨-assoc .leftInv (inl (inl x)) i = inl (inl x)
∨-assoc .leftInv (inl (inr x)) i = inl (inr x)
∨-assoc .leftInv (inr x) i = inr x

∧-assoc : ∀ {xs ys zs : Type a} → ((xs ∧ ys) ∧ zs) ⇔ (xs ∧ (ys ∧ zs))
∧-assoc .fun ((x , y) , z) = x , (y , z)
∧-assoc .inv (x , (y , z)) = (x , y) , z
∧-assoc .rightInv x i = x
∧-assoc .leftInv x i = x

False∨ : ∀ {x : Type a} → False {a} ∨ x ⇔ x
False∨ .fun (inr x) = x
False∨ .inv = inr
False∨ .rightInv x i = x
False∨ .leftInv (inr x) i = inr x

∨False : ∀ {x : Type a} → x ∨ False {a} ⇔ x
∨False .fun (inl x) = x
∨False .inv = inl
∨False .rightInv x i = x
∨False .leftInv (inl x) i = inl x

True∧ : ∀ {x : Type a} → True {a} ∧ x ⇔ x
True∧ .fun = snd
True∧ .inv = tt ,_
True∧ .rightInv x _ = x
True∧ .leftInv x _ = x

∧True : ∀ {x : Type a} → x ∧ True {a} ⇔ x
∧True .fun = fst
∧True .inv = _, tt
∧True .rightInv x _ = x
∧True .leftInv x _ = x

False∧ : ∀ {x : Type a} → False {a} ∧ x ⇔ False {a}
False∧ .fun ()
False∧ .inv ()
False∧ .rightInv ()
False∧ .leftInv ()

∨∧ : ∀ {x y z : Type a} → (x ∨ y) ∧ z ⇔ x ∧ z ∨ y ∧ z
∨∧ .fun (inl x , z) = inl (x , z)
∨∧ .fun (inr y , z) = inr (y , z)
∨∧ .inv (inl (x , z)) = inl x , z
∨∧ .inv (inr (y , z)) = inr y , z
∨∧ .rightInv (inl x) = refl
∨∧ .rightInv (inr x) = refl
∨∧ .leftInv (inl x , z) = refl
∨∧ .leftInv (inr x , z) = refl

∨-comm : ∀ {x y : Type a} → x ∨ y ⇔ y ∨ x
∨-comm .fun (inl x) = inr x
∨-comm .fun (inr x) = inl x
∨-comm .inv (inl x) = inr x
∨-comm .inv (inr x) = inl x
∨-comm .rightInv (inl x) = refl
∨-comm .rightInv (inr x) = refl
∨-comm .leftInv (inl x) = refl
∨-comm .leftInv (inr x) = refl

∧False : ∀ {x : Type a} → x ∧ False {a} ⇔ False {a}
∧False .fun ()
∧False .inv ()
∧False .rightInv ()
∧False .leftInv ()

∧∨ : ∀ {x y z : Type a} → x ∧ (y ∨ z) ⇔ x ∧ y ∨ x ∧ z
∧∨ .fun (x , inl y) = inl (x , y)
∧∨ .fun (x , inr z) = inr (x , z)
∧∨ .inv (inl (x , y)) = x , inl y
∧∨ .inv (inr (x , z)) = x , inr z
∧∨ .rightInv (inl x) = refl
∧∨ .rightInv (inr x) = refl
∧∨ .leftInv (fst₁ , inl x) = refl
∧∨ .leftInv (fst₁ , inr x) = refl

∧-comm : ∀ {x y : Type a} → x ∧ y ⇔ y ∧ x
∧-comm .fun (x , y) = (y , x)
∧-comm .inv (y , x) = (x , y)
∧-comm .rightInv _ = refl
∧-comm .leftInv _ = refl

open CommutativeSemiring
open Semiring
open NearSemiring

tySemiring : CommutativeSemiring (ℓ-suc a)
tySemiring {a} .semiring .nearSemiring .𝑅 = Type a
tySemiring {a} .semiring .nearSemiring ._+_ = _∨_
tySemiring {a} .semiring .nearSemiring ._*_ = _∧_
tySemiring {a} .semiring .nearSemiring .1# = True
tySemiring {a} .semiring .nearSemiring .0# = False
tySemiring {a} .semiring .nearSemiring .+-assoc _ _ _ = isoToPath ∨-assoc
tySemiring {a} .semiring .nearSemiring .*-assoc _ _ _ = isoToPath ∧-assoc
tySemiring {a} .semiring .nearSemiring .0+ _ = isoToPath False∨
tySemiring {a} .semiring .nearSemiring .+0 _ = isoToPath ∨False
tySemiring {a} .semiring .nearSemiring .1* _ = isoToPath True∧
tySemiring {a} .semiring .nearSemiring .*1 _ = isoToPath ∧True
tySemiring {a} .semiring .nearSemiring .0* _ = isoToPath False∧
tySemiring {a} .semiring .nearSemiring .⟨+⟩* _ _ _ = isoToPath ∨∧
tySemiring {a} .semiring .+-comm _ _ = isoToPath ∨-comm
tySemiring {a} .semiring .*0 _ = isoToPath ∧False
tySemiring {a} .semiring .*⟨+⟩ _ _ _ = isoToPath ∧∨
tySemiring {a} .*-comm _ _ = isoToPath ∧-comm

open StarSemiring
open import Data.List using (List; _∷_; [])

list-iterʳ : ∀ {x : Type a} → List x ⇔ True {a} ∨ x ∧ List x
list-iterʳ .fun [] = inl tt
list-iterʳ .fun (x ∷ xs) = inr (x , xs)
list-iterʳ .inv (inl x) = []
list-iterʳ .inv (inr (x , xs)) = x ∷ xs
list-iterʳ .rightInv (inl x) = refl
list-iterʳ .rightInv (inr x) = refl
list-iterʳ .leftInv [] = refl
list-iterʳ .leftInv (x ∷ x₁) = refl

list-iterˡ : ∀ {x : Type a} → List x ⇔ True {a} ∨ List x ∧ x
list-iterˡ .fun [] = inl tt
list-iterˡ .fun (x ∷ xs) = inr (xs , x)
list-iterˡ .inv (inl x) = []
list-iterˡ .inv (inr (xs , x)) = x ∷ xs
list-iterˡ .rightInv (inl x) = refl
list-iterˡ .rightInv (inr x) = refl
list-iterˡ .leftInv [] = refl
list-iterˡ .leftInv (x ∷ x₁) = refl

tyStar : StarSemiring (ℓ-suc a)
tyStar .semiring = tySemiring .semiring
tyStar ⋆ = List
tyStar .star-iterʳ _ = isoToPath list-iterʳ
tyStar .star-iterˡ _ = isoToPath list-iterˡ
\end{code}
