\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

module Cardinality.Finite.ManifestBishop where

open import Prelude
open import Data.List
open import Data.List.Membership
open import Data.Fin as Fin using (Fin; fs; f0)
open import Cardinality.Finite.SplitEnumerable
open import Data.Vec.Iterated as Vec using (Vec; Vec⇔Fin→)
open import Path.Reasoning
import Data.Unit.UniversePolymorphic as Poly-⊤
\end{code}
%<*def>
\begin{code}
ℬ : Type a → Type a
ℬ A = Σ[ support ∈ List A ] (∀ x → x ∈! support)
\end{code}
%</def>
%<*equiv>
\begin{code}
ℬ⇒Fin≃ : (ba : ℬ A) → Fin (length (fst ba)) ≃ A
ℬ⇒Fin≃ ba .fst i = ba .fst ! i
ℬ⇒Fin≃ ba .snd .equiv-proof = ba .snd
\end{code}
%</equiv>
%<*bishop-to-split-enum>
\begin{code}
ℬ⇒ℰ! : ℬ A → ℰ! A
ℬ⇒ℰ! xs .fst    = xs .fst
ℬ⇒ℰ! xs .snd x  = xs .snd x .fst
\end{code}
%</bishop-to-split-enum>
%<*split-enum-to-bishop>
\begin{code}
ℰ!⇒ℬ : ℰ! A → ℬ A
ℰ!⇒ℬ xs .fst    = uniques (ℰ!⇒Discrete xs) (xs .fst)
ℰ!⇒ℬ xs .snd x  = ∈⇒∈! (ℰ!⇒Discrete xs) x (xs .fst) (xs .snd x)
\end{code}
%</split-enum-to-bishop>
\begin{code}
# : ℰ! A → ℕ
# = length ∘ fst ∘ ℰ!⇒ℬ

module Monomorphic where
 _|→|_ : {A B : Type₀} → ℰ! A → ℰ! B → ℰ! (A → B)
\end{code}
%<*fun-prf>
\begin{code}
 _|→|_ {A = A} {B = B} xs ys = subst ℰ! Vec⇔→ (ℰ!⟨Vec⟩ ys)
   where
   Vec⇔→ : Vec B (# xs) ≡ (A → B)
   Vec⇔→ =
     Vec B (# xs)      ≡⟨ isoToPath Vec⇔Fin→ ⟩
     (Fin (# xs) → B)  ≡⟨ (λ i → (ua (ℬ⇒Fin≃ (ℰ!⇒ℬ xs)) i → B)) ⟩
     (A → B) ∎
\end{code}
%</fun-prf>
\begin{code}
lift⇔ : ∀ {ℓ} → Lift ℓ A ⇔ A
lift⇔ .fun = lower
lift⇔ .inv = lift
lift⇔ .leftInv _ = refl
lift⇔ .rightInv _ = refl

Lift⟨Vec⇔Fin→⟩ : ∀ {ℓ n} → Lift ℓ (Vec A n) ⇔ (Lift ℓ (Fin n) → A)
Lift⟨Vec⇔Fin→⟩ = trans-⇔ lift⇔ (trans-⇔ Vec⇔Fin→ (sym-⇔ (iso-arg lift⇔)))

ℬ⇒Lift⟨Fin⟩≃ : {A : Type a} → (ba : ℬ A) → Lift a (Fin (length (fst ba))) ≃ A
ℬ⇒Lift⟨Fin⟩≃ xs .fst (lift n) = fst xs ! n
ℬ⇒Lift⟨Fin⟩≃ xs .snd .equiv-proof x = prf (xs .snd x)
  where
  prf : isContr (fiber (xs .fst !_) x) → isContr (fiber _ x)
  prf xc .fst .fst = lift (xc .fst .fst)
  prf xc .fst .snd = xc .fst .snd
  prf xc .snd (lift y , z) i .fst = lift (xc .snd (y , z) i .fst)
  prf xc .snd (lift y , z) i .snd = xc .snd (y , z) i .snd
\end{code}
%<*fun-sig>
\begin{code}
_|→|_ : ∀ {A : Type a} {B : Type b} → ℰ! A → ℰ! B → ℰ! (A → B)
\end{code}
%</fun-sig>
\begin{code}
_|→|_ {a} {b} {A = A} {B = B} xs ys = subst ℰ! Vec≡→ (ℰ!⟨Lift⟩ (ℰ!⟨Vec⟩ ys))
  where
  Vec≡→ : Lift a (Vec B (# xs)) ≡ (A → B)
  Vec≡→ =
    Lift a (Vec B (# xs)) ≡⟨ isoToPath Lift⟨Vec⇔Fin→⟩ ⟩
    (Lift a (Fin (# xs)) → B)  ≡⟨ (λ i → (ua (ℬ⇒Lift⟨Fin⟩≃ (ℰ!⇒ℬ xs)) i → B)) ⟩
    (A → B) ∎
\end{code}
\begin{code}
Tuple : ∀ n → (Fin n → Type b) → Type b
Tuple zero    _ = Poly-⊤.⊤
Tuple (suc n) B = B f0 × Tuple n (B ∘ fs)

depInd : ∀ {n} {B : Fin n → Type b} → Tuple n B → (i : Fin n) → B i
depInd {n = suc n} (x , xs) f0 = x
depInd {n = suc n} (x , xs) (fs i) = depInd xs i

depTab : ∀ {n} {B : Fin n → Type b} → ((i : Fin n ) → B i) → Tuple n B
depTab {n = zero} f = Poly-⊤.tt
depTab {n = suc n} f = f f0 , depTab (f ∘ fs)

ΠFin→Vec→ΠFin : ∀ {n} {B : Fin n → Type b} → (xs : (i : Fin n) → B i) → (i : Fin n) → depInd (depTab xs) i ≡ xs i
ΠFin→Vec→ΠFin {n = suc n} f f0 = refl
ΠFin→Vec→ΠFin {n = suc n} f (fs i) = ΠFin→Vec→ΠFin (f ∘ fs) i

Vec→ΠFin→Vec : ∀ {n} {B : Fin n → Type b} → (xs : Tuple n B) → depTab (depInd xs) ≡ xs
Vec→ΠFin→Vec {n = zero} Poly-⊤.tt = refl
Vec→ΠFin→Vec {n = suc n} (x , xs) i .fst = x
Vec→ΠFin→Vec {n = suc n} (x , xs) i .snd = Vec→ΠFin→Vec {n = n} xs i

Tuple⇔ΠFin : ∀ {n} {B : Fin n → Type b} → Tuple n B ⇔ ((i : Fin n) → B i)
Tuple⇔ΠFin .fun = depInd
Tuple⇔ΠFin .inv = depTab
Tuple⇔ΠFin .leftInv = Vec→ΠFin→Vec
Tuple⇔ΠFin .rightInv x = funExt (ΠFin→Vec→ΠFin x)

ℰ!⟨Tuple⟩ : ∀ {n} {B : Fin n → Type b} → ((i : Fin n) → ℰ! (B i)) → ℰ! (Tuple n B)
ℰ!⟨Tuple⟩ {n = zero} f = ℰ!⟨⊤⟩-poly
ℰ!⟨Tuple⟩ {n = suc n} f = f f0 |×| ℰ!⟨Tuple⟩ (f ∘ fs)

ℬ⇒Discrete : ℬ A → Discrete A
ℬ⇒Discrete = ℰ!⇒Discrete ∘ ℬ⇒ℰ!
\end{code}
%<*pi-clos>
\begin{code}
_|Π|_ :  ∀ {A : Type₀} {B : A → Type b} →
         ℰ! A →
         ((x : A) → ℰ! (B x)) →
         ℰ! ((x : A) → B x)
_|Π|_ xs =
  subst
    (λ t → {A : t → Type _} → ((x : t) → ℰ! (A x)) → ℰ! ((x : t) → (A x)))
    (ua (ℬ⇒Fin≃ (ℰ!⇒ℬ xs)))
    (subst ℰ! (isoToPath Tuple⇔ΠFin) ∘ ℰ!⟨Tuple⟩)
\end{code}
%</pi-clos>
