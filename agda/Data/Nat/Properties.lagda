\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Nat.Properties where

open import Algebra
open import Data.Nat
open import Prelude
open import Path.Reasoning

+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
+-assoc zero     y z = refl
+-assoc (suc x)  y z = cong suc (+-assoc x y z)

+-idʳ : ∀ x → x + 0 ≡ x
+-idʳ zero     = refl
+-idʳ (suc x)  = cong suc (+-idʳ x)

+-idˡ : ∀ x → 0 + x ≡ x
+-idˡ _ = refl

+-suc : ∀ x y → x + suc y ≡ suc (x + y)
+-suc zero y = refl
+-suc (suc x) y = cong suc (+-suc x y)

+-comm : ∀ x y → x + y ≡ y + x
+-comm x zero = +-idʳ x
+-comm x (suc y) = +-suc x y ; cong suc (+-comm x y)

*0 : ∀ x → x * 0 ≡ 0
*0 zero = refl
*0 (suc x) = *0 x

⟨+⟩* : ∀ x y z → (x + y) * z ≡ x * z + y * z
⟨+⟩* zero y z = refl
⟨+⟩* (suc x) y z = cong (z +_) (⟨+⟩* x y z) ; sym (+-assoc z (x * z) (y * z))

*-assoc : Associative _*_
*-assoc zero y z = refl
*-assoc (suc x) y z = ⟨+⟩* y (x * y) z ; cong (y * z +_) (*-assoc x y z)

1* : ∀ x → 1 * x ≡ x
1* zero = refl
1* (suc x) = cong suc (+-idʳ x)

*1 : ∀ x → x * 1 ≡ x
*1 zero = refl
*1 (suc x) = cong suc (*1 x)

*⟨+⟩ : ∀ x y z → x * (y + z) ≡ x * y + x * z
*⟨+⟩ zero y z = refl
*⟨+⟩ (suc x) y z =
  y + z + x * (y + z)       ≡⟨ cong (y + z +_) (*⟨+⟩ x y z) ⟩
  y + z + (x * y + x * z)   ≡˘⟨ +-assoc (y + z) (x * y) (x * z) ⟩
  (y + z + x * y) + x * z   ≡⟨ cong (_+ x * z) (+-assoc y z (x * y)) ⟩
  (y + (z + x * y)) + x * z ≡⟨ cong (λ zxy → (y + zxy) + x * z) (+-comm z (x * y)) ⟩
  (y + (x * y + z)) + x * z ≡˘⟨ cong (_+ x * z) (+-assoc y (x * y) z) ⟩
  (y + x * y + z) + x * z   ≡⟨ +-assoc (y + x * y) z (x * z) ⟩
  y + x * y + (z + x * z) ∎
\end{code}
