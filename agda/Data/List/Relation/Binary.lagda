\begin{code}
{-# OPTIONS --cubical --safe #-}


module Data.List.Relation.Binary where

open import Prelude hiding (Lift; _×_; _,_)
open import Cubical.Foundations.Prelude using (J; JRefl; Lift; lift)
open import Cubical.Foundations.HLevels
open import Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Unit using (isPropUnit)
open import Cubical.Data.Empty using (isProp⊥)
open import Cubical.Data.Prod using (hLevelProd; _×_; _,_)

module ListPath {ℓ} {A : Type ℓ} where

  Cover : List A → List A → Type ℓ
  Cover [] [] = Lift ⊤
  Cover [] (_ ∷ _) = Lift ⊥
  Cover (_ ∷ _) [] = Lift ⊥
  Cover (x ∷ xs) (y ∷ ys) = (x ≡ y) × Cover xs ys

  reflCode : ∀ xs → Cover xs xs
  reflCode [] = lift tt
  reflCode (_ ∷ xs) = refl , reflCode xs

  encode : ∀ xs ys → (p : xs ≡ ys) → Cover xs ys
  encode xs _ = J (λ ys _ → Cover xs ys) (reflCode xs)

  encodeRefl : ∀ xs → encode xs xs refl ≡ reflCode xs
  encodeRefl xs = JRefl (λ ys _ → Cover xs ys) (reflCode xs)

  decode : ∀ xs ys → Cover xs ys → xs ≡ ys
  decode [] [] _ = refl
  decode [] (_ ∷ _) (lift ())
  decode (x ∷ xs) [] (lift ())
  decode (x ∷ xs) (y ∷ ys) (p , c) = cong₂ _∷_ p (decode xs ys c)

  decodeRefl : ∀ xs → decode xs xs (reflCode xs) ≡ refl
  decodeRefl [] = refl
  decodeRefl (x ∷ xs) = cong (cong₂ _∷_ refl) (decodeRefl xs)

  decodeEncode : ∀ xs ys → (p : xs ≡ ys) → decode xs ys (encode xs ys p) ≡ p
  decodeEncode xs _ =
    J (λ ys p → decode xs ys (encode xs ys p) ≡ p)
      (cong (decode xs xs) (encodeRefl xs) ; decodeRefl xs)

  isOfHLevelCover : (n : ℕ) (p : isOfHLevel (suc (suc n)) A)
    (xs ys : List A) → isOfHLevel (suc n) (Cover xs ys)
  isOfHLevelCover n p [] [] =
    isOfHLevelLift (suc n)
      (subst (λ m → isOfHLevel m ⊤) (+-comm n 1)
        (hLevelLift n isPropUnit))
  isOfHLevelCover n p [] (y ∷ ys) =
    isOfHLevelLift (suc n)
      (subst (λ m → isOfHLevel m ⊥) (+-comm n 1)
        (hLevelLift n isProp⊥))
  isOfHLevelCover n p (x ∷ xs) [] =
    isOfHLevelLift (suc n)
      (subst (λ m → isOfHLevel m ⊥) (+-comm n 1)
        (hLevelLift n isProp⊥))
  isOfHLevelCover n p (x ∷ xs) (y ∷ ys) =
    hLevelProd (suc n) (p x y) (isOfHLevelCover n p xs ys)

isOfHLevelList : ∀ {ℓ} (n : ℕ) {A : Type ℓ}
  → isOfHLevel (suc (suc n)) A → isOfHLevel (suc (suc n)) (List A)
isOfHLevelList n ofLevel xs ys =
  retractIsOfHLevel (suc n)
    (ListPath.encode xs ys)
    (ListPath.decode xs ys)
    (ListPath.decodeEncode xs ys)
    (ListPath.isOfHLevelCover n ofLevel xs ys)
\end{code}
