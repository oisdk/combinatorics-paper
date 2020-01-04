\begin{code}
{-# OPTIONS --cubical --safe #-}

module Data.Pauli where

open import Prelude hiding (I)
open import Cardinality.Finite
open import Data.List.Syntax
open import Data.List.Membership
open import Literals.Number
open import Data.Fin.Literals
open import Data.Nat.Literals
\end{code}
%<*def>
\begin{code}
data Pauli : Type₀ where X Y Z I : Pauli
\end{code}
%</def>
\begin{code}
module BadEq where
\end{code}
%<*bad-eq>
\begin{code}
  ⟦X→_Y→_Z→_I→_⟧ : A → A → A → A → Pauli → A
  ⟦X→ x  Y→ _  Z→ _  I→ _  ⟧ X  = x
  ⟦X→ _  Y→ y  Z→ _  I→ _  ⟧ Y  = y
  ⟦X→ _  Y→ _  Z→ z  I→ _  ⟧ Z  = z
  ⟦X→ _  Y→ _  Z→ _  I→ i  ⟧ I  = i

  _≟_ : (x y : Pauli) → Dec (x ≡ y)
  X  ≟ X   = yes refl
  Y  ≟ Y   = yes refl
  Z  ≟ Z   = yes refl
  I  ≟ I   = yes refl
  X  ≟ Y   = no λ p → subst ⟦X→ ⊤   Y→ ⊥  Z→ ⊥  I→ ⊥  ⟧ p tt
  X  ≟ Z   = no λ p → subst ⟦X→ ⊤   Y→ ⊥  Z→ ⊥  I→ ⊥  ⟧ p tt
  X  ≟ I   = no λ p → subst ⟦X→ ⊤   Y→ ⊥  Z→ ⊥  I→ ⊥  ⟧ p tt
  Y  ≟ X   = no λ p → subst ⟦X→ ⊥   Y→ ⊤  Z→ ⊥  I→ ⊥  ⟧ p tt
  Y  ≟ Z   = no λ p → subst ⟦X→ ⊥   Y→ ⊤  Z→ ⊥  I→ ⊥  ⟧ p tt
  Y  ≟ I   = no λ p → subst ⟦X→ ⊥   Y→ ⊤  Z→ ⊥  I→ ⊥  ⟧ p tt
  Z  ≟ X   = no λ p → subst ⟦X→ ⊥   Y→ ⊥  Z→ ⊤  I→ ⊥  ⟧ p tt
  Z  ≟ Y   = no λ p → subst ⟦X→ ⊥   Y→ ⊥  Z→ ⊤  I→ ⊥  ⟧ p tt
  Z  ≟ I   = no λ p → subst ⟦X→ ⊥   Y→ ⊥  Z→ ⊤  I→ ⊥  ⟧ p tt
  I  ≟ X   = no λ p → subst ⟦X→ ⊥   Y→ ⊥  Z→ ⊥  I→ ⊤  ⟧ p tt
  I  ≟ Y   = no λ p → subst ⟦X→ ⊥   Y→ ⊥  Z→ ⊥  I→ ⊤  ⟧ p tt
  I  ≟ Z   = no λ p → subst ⟦X→ ⊥   Y→ ⊥  Z→ ⊥  I→ ⊤  ⟧ p tt
\end{code}
%</bad-eq>
\begin{code}
open BadEq using (⟦X→_Y→_Z→_I→_⟧)
instance
\end{code}
%<*inst>
\begin{code}
  ℰ⟨Pauli⟩ : ℰ Pauli
  ℰ⟨Pauli⟩ .fst  = [ X , Y , Z , I ]
  ℰ⟨Pauli⟩ .snd X  = at 0
  ℰ⟨Pauli⟩ .snd Y  = at 1
  ℰ⟨Pauli⟩ .snd Z  = at 2
  ℰ⟨Pauli⟩ .snd I  = at 3
\end{code}
%</inst>
\begin{code}

infix 4 _≟_
\end{code}
%<*good-eq>
\begin{code}
_≟_ : (x y : Pauli) → Dec (x ≡ y)
_≟_ = ℰ⇒Discrete ℰ⟨Pauli⟩
\end{code}
%</good-eq>
\begin{code}
infixl 6 _·_
\end{code}
%<*group-op>
\begin{code}
_·_ : Pauli → Pauli → Pauli
I  · x  = x
X  · X  = I
X  · Y  = Z
X  · Z  = Y
X  · I  = X
Y  · X  = Z
Y  · Y  = I
Y  · Z  = X
Y  · I  = Y
Z  · X  = Y
Z  · Y  = X
Z  · Z  = I
Z  · I  = Z
\end{code}
%</group-op>
\begin{code}
module NonInstPrf where
  open import Cardinality.Finite.Search using (module NonInst)
  open NonInst using (∀↯)
\end{code}
%<*noninst-prf>
\begin{code}
  cancel-· : ∀ x → x · x ≡ I
  cancel-· = ∀↯ ℰ⟨Pauli⟩ λ x → x · x ≟ I
\end{code}
%</noninst-prf>
\begin{code}
  contra : ¬ (
\end{code}
%<*contra>
\begin{code}
    ∀ x → x · x ≡ x
\end{code}
%</contra>
\begin{code}
    )
  contra p = subst ⟦X→ ⊥ Y→ ⊤ Z→ ⊤ I→ ⊤ ⟧ (p X) tt
\end{code}
\begin{code}
module Manual where
\end{code}
%<*cancel>
\begin{code}
 cancel-· : ∀ x → x · x ≡ I
 cancel-· X  = refl
 cancel-· Y  = refl
 cancel-· Z  = refl
 cancel-· I  = refl
\end{code}
%</cancel>
\begin{code}
open import Cardinality.Finite.Instances
open import Cardinality.Finite.Search
\end{code}
%<*cancel-auto>
\begin{code}
cancel-· : ∀ x → x · x ≡ I
cancel-· = ∀↯ λ x → x · x ≟ I
\end{code}
%</cancel-auto>
\begin{code}
module Uncurried where
\end{code}
%<*comm-uncurried>
\begin{code}
 comm-· : ∀ x y → x · y ≡ y · x
 comm-· = curry (∀↯ (uncurry (λ x y → x · y ≟ y · x)))
\end{code}
%</comm-uncurried>
%<*prf-curried>
\begin{code}
comm-· : ∀ x y → x · y ≡ y · x
comm-· = ∀↯ⁿ 2 λ x y → x · y ≟ y · x

assoc-· : ∀ x y z → (x · y) · z ≡ x · (y · z)
assoc-· = ∀↯ⁿ 3 λ x y z → (x · y) · z ≟ x · (y · z)
\end{code}
%</prf-curried>
\begin{code}
open import Data.Bool.Properties renaming (discreteBool to _B≟_)

not₁ : Bool → Bool
not₁ false = true
not₁ true  = false

not₂ : Bool → Bool
not₂ false = true
not₂ true  = false

it : ∀ {a} {A : Type a} ⦃ _ : A ⦄ → A
it ⦃ x ⦄ = x

eqFun : Discrete (Bool → Bool)
eqFun = ℰ⇒Discrete it

open import Relation.Nullary

-- prf : not₁ ≡ not₂
-- prf = toWitness {decision = eqFun not₁ not₂} tt
\end{code}
