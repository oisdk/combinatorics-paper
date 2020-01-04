\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

module Cardinality.Finite.ManifestEnumerable where

open import Data.List hiding (alg)
open import Prelude
open import Data.List.Membership
open import Data.Fin
open import Cubical.HITs.S1 hiding (inv)
open import Cardinality.Finite.SplitEnumerable
open import Data.List.Relation.Unary
open import Relation.Nullary
open import HITs.PropositionalTruncation.Sugar
open import Function.Surjective
\end{code}
%<*def>
\begin{code}
ℰ : Type a → Type a
ℰ A = Σ[ support ∈ List A ] ∀ x → ∥ x ∈ support ∥
\end{code}
%</def>
\begin{code}

module _ where
 open import Literals.Number
 open import Data.Fin.Literals
\end{code}
%<*circ-inst>
\begin{code}
 ℰ⟨S¹⟩ : ℰ S¹
 ℰ⟨S¹⟩ .fst           = base ∷ []
 ℰ⟨S¹⟩ .snd base      = ∣ 0 , loop ∣
 ℰ⟨S¹⟩ .snd (loop i)  =
   isPropFamS¹ (λ x → ∥ x ∈ base ∷ [] ∥) (λ _ → squash) ∣ 0 , loop ∣ i
\end{code}
%</circ-inst>
%<*to-split-enum>
\begin{code}
ℰ⇒ℰ! : Discrete A → ℰ A → ℰ! A
ℰ⇒ℰ! _≟_ E .fst = E .fst
ℰ⇒ℰ! _≟_ E .snd x = recompute ((_≟ x) ∈? E .fst) (E .snd x)
\end{code}
%</to-split-enum>
\begin{code}
module ManifestQuant {a} {A : Type a} {p} {P : A → Type p} where
  open Forall P
  open Exists P
  open Quantifications {A = A} {P = P} using (for-some; for-each)

  ∀? : ℰ A
    → (∀ x → Dec (P x))
    → Dec (∀ x → P x)
  ∀? E P? =
    ∣ ◻? P? (E .fst)
      ∣yes⇒  (λ ◻Pxs x → recompute (P? x) (for-each (E .fst) ◻Pxs x ∥$∥ E .snd x))
      ∣no⇒   λ ∀Px i → ∀Px _

  ∃? : ℰ A
    → (∀ x → Dec (P x))
    → Dec (∃[ x ] P x)
  ∃? E P? with ◇? P? (E .fst)
  ... | yes (i , p) = yes (_ , p)
  ... | no ¬p = no (refute-trunc ¬p ∘ λ { (x , Px) → map₂ (flip (subst P) Px ∘ sym) ∥$∥ E .snd x })
\end{code}
%<*from-surj>
\begin{code}
map-ℰ : (A ↠ B) → ℰ A → ℰ B
map-ℰ (f , surj) (sup , cov) =
  map f sup , λ x → do
    y  , p  ← surj x
    z  , q  ← cong-∈ f sup ∥$∥ cov y
    ∣ z , q ; p ∣
\end{code}
%</from-surj>
\begin{code}

to-surj : (E : ℰ A) → Fin (length (E .fst)) ↠ A
to-surj E .fst = E .fst !_
to-surj E .snd = E .snd

_∥×∥_ : ℰ A → ℰ B → ℰ (A × B)
(xs ∥×∥ ys) .fst = cart (xs .fst) (ys .fst)
(xs ∥×∥ ys) .snd (x , y) = ⦇ (cart-cover x y (xs .fst) (ys .fst)) (xs .snd x) (ys .snd y) ⦈

enum-Σ-cover′ : {B : A → Type b}
              → (x : A)
              → (y : B x)
              → (xs : List A)
              → (ys : ∀ x → ℰ (B x))
              → ∥ x ∈ xs ∥
              → ∥ (x , y) ∈ enum-Σ xs (fst ∘ ys) ∥
enum-Σ-cover′ xᵢ yᵢ [] ys x∈xs = ⊥-elim (recPropTrunc (λ ()) fst x∈xs)
enum-Σ-cover′ xᵢ yᵢ (x ∷ xs) ys x∈xs = do
  fs n , xᵢ∈xs ← x∈xs
    where
    f0 , x≡xᵢ → do
      y∈ys ← ys xᵢ .snd yᵢ
      ∣ subst (λ x′ → (xᵢ , yᵢ) ∈ enum-Σ (x′ ∷ xs) (fst ∘ ys)) (sym x≡xᵢ) (map (xᵢ ,_) (ys xᵢ .fst) ◇++ cong-∈ (xᵢ ,_) (ys xᵢ .fst) y∈ys) ∣
  zs ← enum-Σ-cover′ xᵢ yᵢ xs ys ∣ n , xᵢ∈xs ∣
  ∣ map (x ,_) (ys x .fst) ++◇ zs ∣

_∥Σ∥_ : {B : A → Type b} → ℰ A → ((x : A) → ℰ (B x)) → ℰ (Σ A B)
(xs ∥Σ∥ ys) .fst = enum-Σ (xs .fst) (fst ∘ ys)
(xs ∥Σ∥ ys) .snd (x , y) = enum-Σ-cover′ x y (xs .fst) ys (xs .snd x)

_∥⊎∥_ : ℰ A → ℰ B → ℰ (A ⊎ B)
(xs ∥⊎∥ ys) .fst = map inl (fst xs) ++ map inr (fst ys)
(xs ∥⊎∥ ys) .snd (inl x) = do x∈xs ← xs .snd x ; ∣ map inl (xs .fst) ◇++ cong-∈ inl (xs .fst) x∈xs ∣
(xs ∥⊎∥ ys) .snd (inr y) = do y∈ys ← ys .snd y ; ∣ map inl (xs .fst) ++◇ cong-∈ inr (ys .fst) y∈ys ∣

ℰ⟨⊤⟩ : ℰ ⊤
ℰ⟨⊤⟩ .fst = tt ∷ []
ℰ⟨⊤⟩ .snd _ = ∣ f0 , refl ∣

ℰ⟨⊥⟩ : ℰ ⊥
ℰ⟨⊥⟩ .fst = []
ℰ⟨⊥⟩ .snd ()

ℰ!⇒ℰ : ℰ! A → ℰ A
ℰ!⇒ℰ E .fst = E .fst
ℰ!⇒ℰ E .snd x = ∣ E .snd x ∣

open import Cubical.Foundations.HLevels using (isOfHLevelΣ; hLevelPi)
open import Data.List.Relation.Binary using (isOfHLevelList)

isSet⟨ℰ⟩ : isSet A → isSet (ℰ A)
isSet⟨ℰ⟩ isSetA = isOfHLevelΣ 2 (isOfHLevelList 0 isSetA) λ _ → isProp→isSet (hLevelPi 1 λ _ → squash)
\end{code}
