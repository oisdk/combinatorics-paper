{-# OPTIONS --cubical --safe #-}

module Algebra.Construct.Dyck where

open import Prelude
open import Algebra
open import Data.Nat using (_+_)
import Data.Nat.Properties as ℕ
open import Agda.Builtin.Nat using (_-_)

record Bal : Type₀ where
  constructor _⟩⟨_
  field
    left  : ℕ
    right : ℕ
open Bal public

infix 4.5 _⟩-⟨_ _⟩⟨_ _+⟨_⟩+_ _+⟨⟩+_

_⟩-⟨_ : ℕ → ℕ → Bal
zero  ⟩-⟨ m     = zero  ⟩⟨ m
suc n ⟩-⟨ zero  = suc n ⟩⟨ zero
suc n ⟩-⟨ suc m = n ⟩-⟨ m

_+⟨_⟩+_ : ℕ → Bal → ℕ → Bal
left  (x +⟨ z ⟩+ y) = right z + x
right (x +⟨ z ⟩+ y) = left z  + y

_+⟨⟩+_ : Bal → Bal → Bal
x +⟨⟩+ y = left x +⟨ right x ⟩-⟨ left y ⟩+ right y

mempty : Bal
left  mempty = 0
right mempty = 0

diff-zeroʳ : ∀ n → n ⟩-⟨ zero ≡ n ⟩⟨ zero
diff-zeroʳ zero    = refl
diff-zeroʳ (suc n) = refl

invert : Bal → Bal
left  (invert x) = right x
right (invert x) = left  x

neg-inv : ∀ x y → invert (x ⟩-⟨ y) ≡ y ⟩-⟨ x
neg-inv zero  zero = refl
neg-inv zero (suc y) = refl
neg-inv (suc x) zero = refl
neg-inv (suc x) (suc y) = neg-inv x y

open import Path.Reasoning

add-inv : ∀ x y → (x +⟨⟩+ y) ≡ invert (invert y +⟨⟩+ invert x)
add-inv (xl ⟩⟨ xr) (yl ⟩⟨ yr) = cong₂ _⟩⟨_ (cong (_+ xl) (cong left (neg-inv xr yl))) (cong (_+ yr) (cong right (neg-inv xr yl)))

0+⟨⟩ : ∀ x → mempty +⟨⟩+ x ≡ x
0+⟨⟩ (zero   ⟩⟨ xr) i = zero ⟩⟨ xr
0+⟨⟩ (suc xl ⟩⟨ xr) i = suc (ℕ.+-idʳ xl i) ⟩⟨ xr

⟨⟩+0 : ∀ x → x +⟨⟩+ mempty ≡ x
⟨⟩+0 (xl ⟩⟨ zero  ) i = xl ⟩⟨ zero
⟨⟩+0 (xl ⟩⟨ suc xr) i = xl ⟩⟨ suc (ℕ.+-idʳ xr i)


⟨⟩-assoc : Associative _+⟨⟩+_
⟨⟩-assoc (xl ⟩⟨ xr    ) (zero   ⟩⟨ zero  ) (zl     ⟩⟨ zr) = cong₂ _+⟨⟩+_ (⟨⟩+0 (xl ⟩⟨ xr)) (sym (0+⟨⟩ (zl ⟩⟨ zr)))
⟨⟩-assoc (xl ⟩⟨ zero  ) (yl     ⟩⟨ yr    ) (zl     ⟩⟨ zr) = cong (_⟩⟨ (left (yr ⟩-⟨ zl) + zr)) (sym (ℕ.+-assoc (right (yr ⟩-⟨ zl)) yl xl))
⟨⟩-assoc (xl ⟩⟨ suc xr) (yl     ⟩⟨ yr    ) (zl     ⟩⟨ zr) = {!!}

-- ⟨⟩-assoc (xl ⟩⟨ suc xr) (zero   ⟩⟨ suc yr) (zero   ⟩⟨ zr) = cong (xl ⟩⟨_) (cong suc (ℕ.+-assoc xr (suc yr) zr))
-- ⟨⟩-assoc (xl ⟩⟨ suc xr) (zero   ⟩⟨ suc yr) (suc zl ⟩⟨ zr) = cong₂ _⟩⟨_ lhs rhs
--   where
--   lhs : right (xr + suc yr ⟩-⟨ zl) + xl ≡ right (suc xr ⟩-⟨ right (yr ⟩-⟨ zl) + 0) + xl
--   lhs =
--     right (xr + suc yr ⟩-⟨ zl) + xl ≡⟨ {!!} ⟩
--     right (suc xr ⟩-⟨ right (yr ⟩-⟨ zl)) + xl ≡˘⟨ cong (λ pz → right (suc xr ⟩-⟨ pz) + xl) (ℕ.+-idʳ (right (yr ⟩-⟨ zl))) ⟩
--     right (suc xr ⟩-⟨ right (yr ⟩-⟨ zl) + 0) + xl ∎

--   rhs : left (xr + suc yr ⟩-⟨ zl) + zr ≡ left (suc xr ⟩-⟨ right (yr ⟩-⟨ zl) + 0) + (left (yr ⟩-⟨ zl) + zr)
--   rhs =
--     left (xr + suc yr ⟩-⟨ zl) + zr ≡⟨ {!!} ⟩
--     left (suc xr ⟩-⟨ right (yr ⟩-⟨ zl)) + (left (yr ⟩-⟨ zl) + zr) ≡˘⟨ cong (λ pz → left (suc xr ⟩-⟨ pz) + (left (yr ⟩-⟨ zl) + zr)) (ℕ.+-idʳ (right (yr ⟩-⟨ zl))) ⟩
--     left (suc xr ⟩-⟨ right (yr ⟩-⟨ zl) + 0) + (left (yr ⟩-⟨ zl) + zr) ∎

-- ⟨⟩-assoc (xl ⟩⟨ suc xr) (suc yl ⟩⟨ zero  ) (zero   ⟩⟨ zr) = cong₂ _⟩⟨_ lhs rhs
--   where
--   lhs : right (left (xr ⟩-⟨ yl) + 0 ⟩-⟨ 0) + (right (xr ⟩-⟨ yl) + xl) ≡ right (xr ⟩-⟨ yl) + xl
--   lhs = cong (_+ (right (xr ⟩-⟨ yl) + xl)) (cong right (diff-zeroʳ (left (xr ⟩-⟨ yl) + 0)))

--   rhs : left (left (xr ⟩-⟨ yl) + 0 ⟩-⟨ 0) + zr ≡ left (xr ⟩-⟨ yl) + zr
--   rhs = cong (_+ zr) (cong left (diff-zeroʳ (left (xr ⟩-⟨ yl) + 0)) ; ℕ.+-idʳ (left (xr ⟩-⟨ yl)))

-- ⟨⟩-assoc (xl ⟩⟨ suc xr) (suc yl ⟩⟨ zero  ) (suc zl ⟩⟨ zr) = cong₂ _⟩⟨_ lhs rhs
--   where
--   lhs : right (left (xr ⟩-⟨ yl) + 0 ⟩-⟨ suc zl) + (right (xr ⟩-⟨ yl) + xl) ≡ right (xr ⟩-⟨ zl + suc yl) + xl
--   lhs = {!!}

--   rhs : left (left (xr ⟩-⟨ yl) + 0 ⟩-⟨ suc zl) + zr ≡ left (xr ⟩-⟨ zl + suc yl) + zr
--   rhs = {!!}

-- ⟨⟩-assoc (xl ⟩⟨ suc xr) (suc yl ⟩⟨ suc yr) (zero   ⟩⟨ zr) = cong₂ _⟩⟨_ lhs rhs
--   where
--   lhs : right (left (xr ⟩-⟨ yl) + suc yr ⟩-⟨ 0) + (right (xr ⟩-⟨ yl) + xl) ≡ right (xr ⟩-⟨ yl) + xl
--   lhs = {!!}

--   rhs : left (left (xr ⟩-⟨ yl) + suc yr ⟩-⟨ 0) + zr ≡ left (xr ⟩-⟨ yl) + suc (yr + zr)
--   rhs = {!!}

-- ⟨⟩-assoc (xl ⟩⟨ suc xr) (suc yl ⟩⟨ suc yr) (suc zl ⟩⟨ zr) = cong₂ _⟩⟨_ lhs rhs
--   where
--   lhs : right (left (xr ⟩-⟨ yl) + suc yr ⟩-⟨ suc zl) + (right (xr ⟩-⟨ yl) + xl) ≡ right (suc xr ⟩-⟨ right (yr ⟩-⟨ zl) + suc yl) + xl
--   lhs = {!!}

--   rhs : left (left (xr ⟩-⟨ yl) + suc yr ⟩-⟨ suc zl) + zr ≡ left (suc xr ⟩-⟨ right (yr ⟩-⟨ zl) + suc yl) + (left (yr ⟩-⟨ zl) + zr)
--   rhs = {!!}

-- semigroupBal : Semigroup _
-- semigroupBal .Semigroup.𝑆 = Bal
-- semigroupBal .Semigroup._∙_ = _+⟨⟩+_
-- semigroupBal .Semigroup.assoc = {!!}
