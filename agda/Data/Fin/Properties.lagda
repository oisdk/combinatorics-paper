\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

module Data.Fin.Properties where

open import Prelude
open import Data.Fin renaming (discreteFin to _≟_)
open import Data.Nat hiding (pred)
open import Data.Nat.Properties using (+-comm)
open import Function.Injective
open import Data.Maybe.Properties

private
  variable
    n m : ℕ

fin-inj-suc : ∀ {n} → (Fin (suc n) ↣ A) → Fin n ↣ A
fin-inj-suc fn .fst = fn .fst ∘ fs
fin-inj-suc fn .snd x y = cong (λ { f0 → y ; (fs x) → x}) ∘ fn .snd (fs x) (fs y)
\end{code}

%<*fin-inj>
\begin{code}
_F↣_ : ℕ → ℕ → Type₀
n F↣ m = Σ[ f ∈ (Fin n → Fin m) ] ∀ {x y} → x ≢ᶠ y → f x ≢ᶠ f y

shift : (x y : Fin (suc n)) → x ≢ᶠ y → Fin n
shift          f0     (fs y)  x≢y = y
shift {suc _}  (fs x)  f0     x≢y = f0
shift {suc _}  (fs x)  (fs y)  x≢y = fs (shift x y x≢y)

shift-inj : ∀ (x y z : Fin (suc n)) x≢y x≢z → y ≢ᶠ z → shift x y x≢y ≢ᶠ shift x z x≢z
shift-inj          f0     (fs y)  (fs z)  x≢y x≢z x+y≢x+z = x+y≢x+z
shift-inj {suc _}  (fs x)  f0     (fs z)  x≢y x≢z x+y≢x+z = tt
shift-inj {suc _}  (fs x)  (fs y)  f0     x≢y x≢z x+y≢x+z = tt
shift-inj {suc _}  (fs x)  (fs y)  (fs z)  x≢y x≢z x+y≢x+z = shift-inj x y z x≢y x≢z x+y≢x+z

shrink : suc n F↣ suc m → n F↣ m
shrink (f , inj) .fst  x  = shift (f f0) (f (fs x)) (inj tt)
shrink (f , inj) .snd  p  = shift-inj (f f0) (f (fs _)) (f (fs _)) (inj tt) (inj tt) (inj p)

¬plus-inj : ∀ n m → ¬ (suc (n + m) F↣ m)
¬plus-inj zero     zero     (f , _)  = f f0
¬plus-inj zero     (suc m)  inj      = ¬plus-inj zero m (shrink inj)
¬plus-inj (suc n)  m        (f , p)  = ¬plus-inj n m (f ∘ fs , p)

toFin-inj : (Fin n ↣ Fin m) → n F↣ m
toFin-inj f .fst = f .fst
toFin-inj (f , inj) .snd {x} {y} x≢ᶠy with x ≟ y | f x ≟ f y
... | no ¬p  | yes p  = ¬p (inj _ _ p)
... | no _   | no _   = tt

n≢sn+m : ∀ n m → Fin n ≢ Fin (suc (n + m))
n≢sn+m n m n≡m =
  ¬plus-inj m n
    (toFin-inj
      (subst
        (_↣ Fin n)
        (n≡m ; cong (Fin ∘ suc) (+-comm n m))
        refl-↣))

Fin-inj : Injective Fin
Fin-inj n m eq with compare n m
... | equal _        = refl
... | less     n  k  = ⊥-elim (n≢sn+m n k eq)
... | greater  m  k  = ⊥-elim (n≢sn+m m k (sym eq))
\end{code}
%</fin-inj>
