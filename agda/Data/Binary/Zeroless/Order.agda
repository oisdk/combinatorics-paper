{-# OPTIONS --cubical --safe --postfix-projections #-}

module Data.Binary.Zeroless.Order where

open import Prelude
open import Data.Binary.Zeroless
open import Data.List.Kleene.AsList using (List; _∷_; [])
open import Data.Bool using (T; _∨_; _∧_; not)
open import Data.Bool.Properties using (T?; _&_≲ᵇ_; isPropT)
open import Relation.Nullary

infix 4 _≤ᴮ_ _<ᴮ_ _≤_ _<_ _≤?_ _<?_ _&_≲ᴮ_ _&_≲_

_&_≲ᴮ_ : Bool → 𝔹 → 𝔹 → Bool
s & []       ≲ᴮ []       = s
s & []       ≲ᴮ (y ∷ ys) = true
s & (x ∷ xs) ≲ᴮ []       = false
s & (x ∷ xs) ≲ᴮ (y ∷ ys) = (s & x ≲ᵇ y) & xs ≲ᴮ ys

_<ᴮ_ _≤ᴮ_ : 𝔹 → 𝔹 → Bool
_<ᴮ_ = false &_≲ᴮ_
_≤ᴮ_ = true  &_≲ᴮ_

_<_ _≤_ : 𝔹 → 𝔹 → Type₀
xs < ys = T (xs <ᴮ ys)
xs ≤ ys = T (xs ≤ᴮ ys)

_&_≲_ : Bool → 𝔹 → 𝔹 → Type₀
s & xs ≲ ys = T (s & xs ≲ᴮ ys)

_<?_ : ∀ xs ys → Dec (xs < ys)
(xs <? ys) = T? (xs <ᴮ ys)

_≤?_ : ∀ xs ys → Dec (xs ≤ ys)
(xs ≤? ys) = T? (xs ≤ᴮ ys)

≲-trans : ∀ s xs ys zs i j → i & xs ≲ ys → j & ys ≲ zs → (s ∨ (i ∧ j)) & xs ≲ zs
≲-trans s     []        _         (z  ∷ zs) i     j     xs≲ys ys≲zs = tt
≲-trans true  []        []        []        true  j     xs≲ys ys≲zs = tt
≲-trans false []        []        []        true  j     xs≲ys ys≲zs = ys≲zs
≲-trans s     (1ᵇ ∷ xs) (1ᵇ ∷ ys) (1ᵇ ∷ zs) i     j     = ≲-trans s     xs ys zs i     j
≲-trans s     (2ᵇ ∷ xs) (2ᵇ ∷ ys) (2ᵇ ∷ zs) i     j     = ≲-trans s     xs ys zs i     j
≲-trans s     (1ᵇ ∷ xs) (1ᵇ ∷ ys) (2ᵇ ∷ zs) i     j     = ≲-trans true  xs ys zs i     true
≲-trans s     (1ᵇ ∷ xs) (2ᵇ ∷ ys) (2ᵇ ∷ zs) i     j     = ≲-trans true  xs ys zs true  j
≲-trans s     (1ᵇ ∷ xs) (2ᵇ ∷ ys) (1ᵇ ∷ zs) false j     = ≲-trans s     xs ys zs true  false
≲-trans s     (1ᵇ ∷ xs) (2ᵇ ∷ ys) (1ᵇ ∷ zs) true  false = ≲-trans s     xs ys zs true  false
≲-trans false (1ᵇ ∷ xs) (2ᵇ ∷ ys) (1ᵇ ∷ zs) true  true  = ≲-trans true  xs ys zs true  false
≲-trans true  (1ᵇ ∷ xs) (2ᵇ ∷ ys) (1ᵇ ∷ zs) true  true  = ≲-trans true  xs ys zs true  false
≲-trans s     (2ᵇ ∷ xs) (1ᵇ ∷ ys) (1ᵇ ∷ zs) i     j     = ≲-trans false xs ys zs false j
≲-trans s     (2ᵇ ∷ xs) (1ᵇ ∷ ys) (2ᵇ ∷ zs) false j     = ≲-trans s     xs ys zs false true
≲-trans s     (2ᵇ ∷ xs) (1ᵇ ∷ ys) (2ᵇ ∷ zs) true  false = ≲-trans s     xs ys zs false true
≲-trans false (2ᵇ ∷ xs) (1ᵇ ∷ ys) (2ᵇ ∷ zs) true  true  = ≲-trans true  xs ys zs false true
≲-trans true  (2ᵇ ∷ xs) (1ᵇ ∷ ys) (2ᵇ ∷ zs) true  true  = ≲-trans true  xs ys zs false true
≲-trans s     (2ᵇ ∷ xs) (2ᵇ ∷ ys) (1ᵇ ∷ zs) false j     = ≲-trans false xs ys zs false false
≲-trans s     (2ᵇ ∷ xs) (2ᵇ ∷ ys) (1ᵇ ∷ zs) true  j     = ≲-trans false xs ys zs true  false

<⇒≤ : ∀ xs ys → xs < ys → xs ≤ ys
<⇒≤ []        (y  ∷ ys) xs≲ys = tt
<⇒≤ (1ᵇ ∷ xs) (1ᵇ ∷ ys) xs≲ys = <⇒≤ xs ys xs≲ys
<⇒≤ (1ᵇ ∷ xs) (2ᵇ ∷ ys) xs≲ys = xs≲ys
<⇒≤ (2ᵇ ∷ xs) (1ᵇ ∷ ys) xs≲ys = xs≲ys
<⇒≤ (2ᵇ ∷ xs) (2ᵇ ∷ ys) xs≲ys = <⇒≤ xs ys xs≲ys

≤-refl : ∀ xs → xs ≤ xs
≤-refl [] = tt
≤-refl (1ᵇ ∷ xs) = ≤-refl xs
≤-refl (2ᵇ ∷ xs) = ≤-refl xs

<-inc : ∀ xs → xs < inc xs
<-inc [] = tt
<-inc (1ᵇ ∷ xs) = ≤-refl xs
<-inc (2ᵇ ∷ xs) = <-inc xs

0≤xs : ∀ xs → [] ≤ xs
0≤xs [] = tt
0≤xs (x ∷ xs) = tt

0<sxs : ∀ xs → [] < inc xs
0<sxs [] = tt
0<sxs (1ᵇ ∷ xs) = tt
0<sxs (2ᵇ ∷ xs) = tt

≤⇒< : ∀ xs ys → xs ≤ ys → xs < inc ys
≤⇒< [] ys p = tt
≤⇒< (1ᵇ ∷ xs) (1ᵇ ∷ ys) p = p
≤⇒< (2ᵇ ∷ xs) (1ᵇ ∷ ys) p = p
≤⇒< (1ᵇ ∷ xs) (2ᵇ ∷ ys) p = ≤⇒< xs ys p
≤⇒< (2ᵇ ∷ xs) (2ᵇ ∷ ys) p = ≤⇒< xs ys p

<⇒≤-1 : ∀ xs ys → xs < ys → inc xs ≤ ys
<⇒≤-1 []        (1ᵇ ∷ ys) p = 0≤xs ys
<⇒≤-1 []        (2ᵇ ∷ ys) p = 0≤xs ys
<⇒≤-1 (1ᵇ ∷ xs) (1ᵇ ∷ ys) p = p
<⇒≤-1 (1ᵇ ∷ xs) (2ᵇ ∷ ys) p = p
<⇒≤-1 (2ᵇ ∷ xs) (1ᵇ ∷ ys) p = <⇒≤-1 xs ys p
<⇒≤-1 (2ᵇ ∷ xs) (2ᵇ ∷ ys) p = <⇒≤-1 xs ys p

cong-inc : ∀ xs ys → xs < ys → inc xs < inc ys
cong-inc []        (1ᵇ ∷ ys) p = 0≤xs ys
cong-inc []        (2ᵇ ∷ ys) p = 0<sxs ys
cong-inc (1ᵇ ∷ xs) (1ᵇ ∷ ys) p = p
cong-inc (1ᵇ ∷ xs) (2ᵇ ∷ ys) p = ≤⇒< xs ys p
cong-inc (2ᵇ ∷ xs) (1ᵇ ∷ ys) p = <⇒≤-1 xs ys p
cong-inc (2ᵇ ∷ xs) (2ᵇ ∷ ys) p = cong-inc xs ys p

import Data.Nat.Order as ℕ

ℕ<⇒< : ∀ n m → n ℕ.< m → ⟦ n ⇑⟧ < ⟦ m ⇑⟧
ℕ<⇒< zero    (suc m) p = 0<sxs ⟦ m ⇑⟧
ℕ<⇒< (suc n) (suc m) p = cong-inc ⟦ n ⇑⟧ ⟦ m ⇑⟧ (ℕ<⇒< n m p)

cong-<-2* : ∀ n m → n ℕ.< m → 2* n ℕ.< 2* m
cong-<-2* zero (suc m) p = tt
cong-<-2* (suc n) (suc m) p = cong-<-2* n m p

cong-≤-2* : ∀ n m → n ℕ.≤ m → suc (suc (2* n)) ℕ.≤ suc (suc (2* m))
cong-≤-2* zero m p = tt
cong-≤-2* (suc n) zero p = p
cong-≤-2* (suc zero) (suc n) p = tt
cong-≤-2* (suc (suc n₁)) (suc n) p = cong-≤-2* (suc n₁) n p

+2<*2 : ∀ n m → n ℕ.< m → suc (suc (2* n)) ℕ.< suc (2* m)
+2<*2 n zero p = p
+2<*2 zero (suc n) p = tt
+2<*2 (suc n₁) (suc n) p = +2<*2 n₁ n p

*2<+2 : ∀ n m → n ℕ.≤ m → suc (2* n) ℕ.< suc (suc (2* m))
*2<+2 zero m p = tt
*2<+2 (suc n) zero p = p
*2<+2 (suc zero) (suc n) p = tt
*2<+2 (suc (suc n₁)) (suc n) p = *2<+2 (suc n₁) n p

≤-s-r : ∀ n m → n ℕ.≤ m → suc (2* n) ℕ.≤ suc (suc (2* m))
≤-s-r zero m p = tt
≤-s-r (suc n) zero p = p
≤-s-r (suc zero) (suc n) p = tt
≤-s-r (suc (suc n₁)) (suc n) p = ≤-s-r (suc n₁) n p

≤⇒ℕ≤ : ∀ xs ys → xs ≤ ys → ⟦ xs ⇓⟧ ℕ.≤ ⟦ ys ⇓⟧
<⇒ℕ< : ∀ xs ys → xs < ys → ⟦ xs ⇓⟧ ℕ.< ⟦ ys ⇓⟧

≤⇒ℕ≤ [] [] p = tt
≤⇒ℕ≤ [] (x ∷ ys) p = tt
≤⇒ℕ≤ (false ∷ xs) (false ∷ ys) p = cong-≤-2* ⟦ xs ⇓⟧ ⟦ ys ⇓⟧ (≤⇒ℕ≤ xs ys p)
≤⇒ℕ≤ (false ∷ xs) (true ∷ ys) p = ≤-s-r ⟦ xs ⇓⟧ ⟦ ys ⇓⟧ (≤⇒ℕ≤ xs ys p)
≤⇒ℕ≤ (true ∷ xs) (false ∷ ys) p = cong-<-2* ⟦ xs ⇓⟧ ⟦ ys ⇓⟧ (<⇒ℕ< xs ys p)
≤⇒ℕ≤ (true ∷ xs) (true ∷ ys) p = cong-≤-2* ⟦ xs ⇓⟧ ⟦ ys ⇓⟧ (≤⇒ℕ≤ xs ys p)

<⇒ℕ< [] (false ∷ ys) p = tt
<⇒ℕ< [] (true ∷ ys) p = tt
<⇒ℕ< (false ∷ xs) (false ∷ ys) p = cong-<-2* ⟦ xs ⇓⟧ ⟦ ys ⇓⟧ (<⇒ℕ< xs ys p)
<⇒ℕ< (false ∷ xs) (true ∷ ys) p = *2<+2 ⟦ xs ⇓⟧ ⟦ ys ⇓⟧ (≤⇒ℕ≤ xs ys p)
<⇒ℕ< (true ∷ xs) (false ∷ ys) p = +2<*2 ⟦ xs ⇓⟧ ⟦ ys ⇓⟧ (<⇒ℕ< xs ys p)
<⇒ℕ< (true ∷ xs) (true ∷ ys) p = cong-<-2* ⟦ xs ⇓⟧ ⟦ ys ⇓⟧ (<⇒ℕ< xs ys p)

-- open import Cubical.Foundations.Everything using (J)

-- module _ (P : ∀ y → x ≡ y → Type ℓ') (d : P x refl) where
--   J : (p : x ≡ y) → P y p

-- lemma : ∀ xs ys p → subst (⟦ ⟦ ys ⇓⟧ ⇑⟧ <_) (𝔹⇔ℕ .leftInv xs) (ℕ<⇒< ⟦ ys ⇓⟧ ⟦ xs ⇓⟧ (<⇒ℕ< ys xs p)) ≡[ i ≔ 𝔹⇔ℕ .leftInv ys i < xs ]≡ p
-- lemma xs ys = J (λ xs′ xs′≡ → ∀ (p : ys < xs′) → subst (_<_ ⟦ ⟦ ys ⇓⟧ ⇑⟧) xs′≡ (ℕ<⇒< ⟦ ys ⇓⟧ ⟦ xs′ ⇓⟧ (<⇒ℕ< ys xs′ p)) ≡[ i ≔ 𝔹⇔ℕ .leftInv ys i < xs′ ]≡ p) {!!} {!!}

-- Fin𝔹⇔Finℕ : ∀ xs → ∃ (_< xs) ⇔ ∃ (ℕ._< ⟦ xs ⇓⟧)
-- Fin𝔹⇔Finℕ xs .fun (ys , p) = ⟦ ys ⇓⟧ , <⇒ℕ< ys xs p
-- Fin𝔹⇔Finℕ xs .inv (ys , p) = ⟦ ys ⇑⟧ , subst (⟦ ys ⇑⟧ <_) (𝔹⇔ℕ .leftInv xs) (ℕ<⇒< ys ⟦ xs ⇓⟧ p)
-- Fin𝔹⇔Finℕ xs .leftInv    (ys , p) i .fst = 𝔹⇔ℕ .leftInv ys i
-- Fin𝔹⇔Finℕ xs .leftInv    (ys , p) i .snd = {!!}
-- Fin𝔹⇔Finℕ xs .rightInv   (ys , p) = {!!}

-- -- ℕ<⇒< : ∀ n m → n ℕ.< m → ⟦ n ⇑⟧ < ⟦ m ⇑⟧
