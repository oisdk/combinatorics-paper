{-# OPTIONS --cubical --safe #-}

module Function.Isomorphism where

open import Cubical.Foundations.Equiv using (isoToEquiv) public
open import Cubical.Foundations.Isomorphism using (Iso; section; retract; isoToPath; iso) public
open import Level
open import Path
open import Function

open Iso public

infix 4 _⇔_
_⇔_ = Iso

sym-⇔ : (A ⇔ B) → (B ⇔ A)
fun (sym-⇔ A⇔B) = inv A⇔B
inv (sym-⇔ A⇔B) = fun A⇔B
leftInv (sym-⇔ A⇔B) = rightInv A⇔B
rightInv (sym-⇔ A⇔B) = leftInv A⇔B

refl-⇔ : A ⇔ A
fun refl-⇔ x = x
inv refl-⇔ x = x
leftInv refl-⇔ x = refl
rightInv refl-⇔  x = refl

trans-⇔ : A ⇔ B → B ⇔ C → A ⇔ C
fun      (trans-⇔ A⇔B B⇔C) = fun B⇔C ∘ fun A⇔B
inv      (trans-⇔ A⇔B B⇔C) = inv A⇔B ∘ inv B⇔C
leftInv  (trans-⇔ A⇔B B⇔C) x = cong (inv A⇔B) (leftInv B⇔C _) ; leftInv A⇔B _
rightInv (trans-⇔ A⇔B B⇔C) x = cong (fun B⇔C) (rightInv A⇔B _) ; rightInv B⇔C _
