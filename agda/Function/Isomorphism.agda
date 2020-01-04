{-# OPTIONS --cubical --safe #-}

module Function.Isomorphism where

open import Cubical.Foundations.Isomorphism using (Iso; section; retract; isoToPath; iso) public
open import Relation.Binary
open import Level
open import Path as ≡ using (_;_; cong)
open import Function
open import Agda.Builtin.Sigma

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
leftInv refl-⇔ x = ≡.refl
rightInv refl-⇔  x = ≡.refl

trans-⇔ : A ⇔ B → B ⇔ C → A ⇔ C
fun      (trans-⇔ A⇔B B⇔C) = fun B⇔C ∘ fun A⇔B
inv      (trans-⇔ A⇔B B⇔C) = inv A⇔B ∘ inv B⇔C
leftInv  (trans-⇔ A⇔B B⇔C) x = cong (inv A⇔B) (leftInv B⇔C _) ; leftInv A⇔B _
rightInv (trans-⇔ A⇔B B⇔C) x = cong (fun B⇔C) (rightInv A⇔B _) ; rightInv B⇔C _

equivIso : Equivalence (Type a) a
equivIso = record
  { _≋_ = _⇔_
  ; sym = sym-⇔
  ; refl = refl-⇔
  ; trans = trans-⇔
  }

iso-arg : A ⇔ B → (A → C) ⇔ (B → C)
iso-arg A⇔B .fun f x = f (A⇔B .inv x)
iso-arg A⇔B .inv f x = f (A⇔B .fun x)
iso-arg A⇔B .leftInv f i x = f (A⇔B .leftInv x i)
iso-arg A⇔B .rightInv f i x = f (A⇔B .rightInv x i)

iso-Σ : {B : A → Type b} {C : A → Type c} → (∀ x → B x ⇔ C x) → Σ A B ⇔ Σ A C
iso-Σ B⇔C .fun (x , xs) = x , B⇔C x .fun xs
iso-Σ B⇔C .inv (x , xs) = x , B⇔C x .inv xs
iso-Σ B⇔C .rightInv (x , xs) i .fst = x
iso-Σ B⇔C .rightInv (x , xs) i .snd = B⇔C x .rightInv xs i
iso-Σ B⇔C .leftInv (x , xs) i .fst = x
iso-Σ B⇔C .leftInv (x , xs) i .snd = B⇔C x .leftInv xs i
