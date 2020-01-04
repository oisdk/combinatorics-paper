{-# OPTIONS --cubical --safe #-}

module Data.Integer where

open import Prelude
import Data.Nat as ℕ

record ℤ : Type₀ where
  constructor int
  field
    sign : Bool
    offset : ℕ
open ℤ public

pattern +_ n = int true n
pattern -suc n = int false n

sub⁻¹ : ℕ → ℕ → ℤ
sub⁻¹ zero    y       = -suc y
sub⁻¹ (suc x) zero    = + x
sub⁻¹ (suc x) (suc y) = sub⁻¹ x y

sub : ℕ → ℕ → ℤ
sub n zero = + n
sub n (suc m) = sub⁻¹ n m

infixl 6 _+_
_+_ : ℤ → ℤ → ℤ
+ x    + + y    = + (x ℕ.+ y)
+ x    + -suc y = sub⁻¹ x y
-suc x + + y    = sub⁻¹ y x
-suc x + -suc y = -suc (suc (x ℕ.+ y))

infixl 6 _-_
_-_ : ℤ → ℤ → ℤ
-suc x  - + y       = -suc (x ℕ.+ y)
+ x     - + y       = sub x y
+ x     - -suc y    = + (suc (x ℕ.+ y))
-suc x  - -suc y    = sub⁻¹ (suc y) x

-_ : ℕ → ℤ
- zero = + zero
- suc n = -suc n

infixl 7 _*_
_*_ : ℤ → ℤ → ℤ
+ x     * + y     = + (x ℕ.* y)
+ zero  * -suc y  = + zero
+ suc x * -suc y  = -suc (x ℕ.+ y ℕ.+ x ℕ.* y)
-suc x  * + zero  = + zero
-suc x  * + suc y = -suc (x ℕ.+ y ℕ.+ x ℕ.* y)
-suc x  * -suc y  = + (suc (x ℕ.+ y ℕ.+ x ℕ.* y))

