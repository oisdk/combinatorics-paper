\begin{code}
{-# OPTIONS --cubical --safe #-}

module Relation.Nullary where

open import Data.Bool using (Bool; true; false; T)
open import Cubical.Relation.Nullary public
  using (¬_; isProp¬; Stable; Stable¬)
open import Level
open import Cubical.Core.Everything hiding (Type; Type₀)
open import Data.Empty
open import Cubical.Foundations.Prelude hiding (Type; Type₀)
open import Data.Unit
\end{code}
%<*dec-def>
\begin{code}
data Reflects {a} (A : Type a) : Bool → Type a where
  ofʸ  : (p   :    A) → Reflects A true
  ofⁿ  : (¬p  : ¬  A) → Reflects A false

record Dec {a} (A : Type a) : Type a where
  constructor _because_
  field
    does  : Bool
    why   : Reflects A does
open Dec public

pattern yes p  = true   because ofʸ p
pattern no ¬p  = false  because ofⁿ ¬p
\end{code}
%</dec-def>
\begin{code}

fromReflection : ∀ {a} {A : Type a} → ∀ {b} → Reflects A b → T b → A
fromReflection (ofʸ x) tt = x

Discrete : Type a → Type a
Discrete A = (x y : A) → Dec (x ≡ y)

fromYes : A → Dec A → A
fromYes _ (yes a) = a
fromYes a (no _) = a

discreteDec : (Adis : Discrete A) → Discrete (Dec A)
discreteDec Adis (yes p) (yes p') = decideYes (Adis p p')
  where
  decideYes : Dec (p ≡ p') → Dec (yes p ≡ yes p')
  decideYes (yes eq) = yes (λ i → yes (eq i))
  decideYes (no ¬eq) = no λ eq → ¬eq (λ i → (fromYes p) (eq i))
discreteDec Adis (yes p) (no ¬p) = ⊥-elim (¬p p)
discreteDec Adis (no ¬p) (yes p) = ⊥-elim (¬p p)
discreteDec {A = A} Adis (no ¬p) (no ¬p') = yes (λ i → no (isProp¬ A ¬p ¬p' i))

isPropDec : (Aprop : isProp A) → isProp (Dec A)
isPropDec Aprop (yes a) (yes a') i = yes (Aprop a a' i)
isPropDec Aprop (yes a) (no ¬a) = ⊥-elim (¬a a)
isPropDec Aprop (no ¬a) (yes a) = ⊥-elim (¬a a)
isPropDec {A = A} Aprop (no ¬a) (no ¬a') i = no (isProp¬ A ¬a ¬a' i)
\end{code}
%<*true-def>
\begin{code}
True : ∀  {a} {A : Type a} → Dec A → Type₀
True (yes  _) = ⊤
True (no   _) = ⊥
\end{code}
%</true-def>
\begin{code}

toWitness : {decision : Dec A} → True decision → A
toWitness {decision = yes x} p = x

Dec→Stable : ∀ {ℓ} (A : Type ℓ) → Dec A → Stable A
Dec→Stable A (yes x) = λ _ → x
Dec→Stable A (no x) = λ f → ⊥-elim (f x)

Stable≡→isSet : ∀ {ℓ} {A : Type ℓ} → (st : ∀ (a b : A) → Stable (a ≡ b)) → isSet A
Stable≡→isSet {A = A} st a b p q j i =
  let f : (x : A) → a ≡ x → a ≡ x
      f x p = st a x (λ h → h p)
      fIsConst : (x : A) → (p q : a ≡ x) → f x p ≡ f x q
      fIsConst = λ x p q i → st a x (isProp¬ _ (λ h → h p) (λ h → h q) i)
      rem : (p : a ≡ b) → PathP (λ i → a ≡ p i) (f a refl) (f b p)
      rem p j = f (p j) (λ i → p (i ∧ j))
  in hcomp (λ k → λ { (i = i0) → f a refl k
                    ; (i = i1) → fIsConst b p q j k
                    ; (j = i0) → rem p i k
                    ; (j = i1) → rem q i k }) a

-- Hedberg's theorem
Discrete→isSet : ∀ {ℓ} {A : Type ℓ} → Discrete A → isSet A
Discrete→isSet d = Stable≡→isSet (λ x y → Dec→Stable (x ≡ y) (d x y))

map-refl : ∀ {d} → (A → B) → (¬ A → ¬ B) → Reflects A d → Reflects B d
map-refl to fro (ofʸ p) = ofʸ (to p)
map-refl to fro (ofⁿ ¬p) = ofⁿ (fro ¬p)

⟦y_,n_⟧ : ∀ {d} → (A → B) → (B → A) → Reflects A d → Reflects B d
⟦y to ,n fro ⟧ = map-refl to λ ¬A ¬B → ¬A (fro ¬B)

map-dec : (A → B) → (¬ A → ¬ B) → Dec A → Dec B
map-dec to fro dec .does = dec .does
map-dec to fro dec .why = map-refl to fro (dec .why)

⟦yes_,no_⟧ : (A → B) → (B → A) → Dec A → Dec B
⟦yes to ,no fro ⟧ = map-dec to λ ¬A ¬B → ¬A (fro ¬B)

∣_∣yes⇒_∣no⇒_ : Dec A → (A → B) → (B → A) → Dec B
∣ d ∣yes⇒ y ∣no⇒ n = ⟦yes y ,no n ⟧ d

open import Cubical.HITs.PropositionalTruncation

recompute : Dec A → ∥ A ∥ → A
recompute (yes p) _ = p
recompute (no ¬p) p = ⊥-elim (recPropTrunc (λ ()) ¬p p)

refute-trunc : ¬ A → ¬ ∥ A ∥
refute-trunc = recPropTrunc isProp⊥

∀[_] : ∀ {a p} {A : Type a} (P : A → Type p) → Type (a ℓ⊔ p)
∀[ P ] = ∀ x → P x

\end{code}
