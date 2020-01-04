\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

module Cardinality.Finite.Kuratowski where

open import Prelude
open import Algebra.Construct.Free.Semilattice
open import Cardinality.Finite.ManifestEnumerable
open import Data.List as List using (List; foldr; _∷_; [])
import Data.List.Membership as ℰ
open import Algebra.Construct.Free.Semilattice.Relation.Unary
open import Relation.Nullary
open import Relation.Nullary.Omniscience
open import HITs.PropositionalTruncation.Sugar
open import Data.Fin using (f0)
\end{code}
%<*def>
\begin{code}
𝒦ᶠ : Type a → Type a
𝒦ᶠ A = Σ[ support ∈ 𝒦 A ] (∀ x → x ∈ support)
\end{code}
%</def>
%<*exhaustible>
\begin{code}
𝒦ᶠ⇒Exhaustible : ∀ {p} → 𝒦ᶠ A → Exhaustible p A
𝒦ᶠ⇒Exhaustible K P? =
  map-dec
    (λ ◻Pxs x → recompute (P? x) (P∈◇ x (K .fst) (K .snd x) ◻Pxs) )
    (λ ¬◻Pxs ∀P → ¬◻Pxs (map-◻ ∀P (K .fst)))
    (◻? P? (K .fst))
\end{code}
%</exhaustible>
%<*to-enum>
\begin{code}
𝒦ᶠ⇒∥ℰ∥ : 𝒦ᶠ A → ∥ ℰ A ∥
𝒦ᶠ⇒∥ℰ∥ K = map₂ (λ p x → p x (K .snd x)) ∥$∥ ∥ enum ∥⇓ (K .fst)
  where
  enum : xs ∈𝒦 A ⇒∥ ∥ Σ[ ys ∈ List A ] (∀ x → x ∈ xs → ∥ x ℰ.∈ ys ∥) ∥ ∥
  ∥ enum ∥-prop = squash
  ∥ enum ∥[] = ∣ [] , (λ _ ()) ∣
  ∥ enum ∥ x ∷ xs ⟨ Pxs ⟩ = cons ∥$∥ Pxs
    where
    cons : _
    cons (ys , p) .fst = x ∷ ys
    cons (ys , p) .snd z = _>>= either′ (∣_∣ ∘ (f0 ,_)) ((ℰ.push ∥$∥_) ∘ p z)
\end{code}
%</to-enum>
%<*from-enum>
\begin{code}
open import Algebra.Construct.Free.Semilattice.Extensionality
open import Algebra.Construct.Free.Semilattice.FromList
open import Data.Sigma.Properties

isProp𝒦ᶠ : isProp (𝒦ᶠ A)
isProp𝒦ᶠ Kˣ Kʸ =
  ΣProp≡
    (λ K p q i x → isProp-◇ {xs = K} (p x) (q x) i)
    {Kˣ} {Kʸ}
    (extensional (fst Kˣ) (fst Kʸ) λ x → const (Kʸ .snd x) iff const (Kˣ .snd x))

ℰ⇒𝒦 : ℰ A → 𝒦ᶠ A
ℰ⇒𝒦 E .fst = fromList (E .fst)
ℰ⇒𝒦 E .snd x = ∈List⇒∈𝒦 (E .fst) (E .snd x)

∥ℰ∥⇒𝒦 : ∥ ℰ A ∥ → 𝒦ᶠ A
∥ℰ∥⇒𝒦 = recPropTrunc isProp𝒦ᶠ ℰ⇒𝒦

∥ℰ∥⇔𝒦 : ∥ ℰ A ∥ ⇔ 𝒦ᶠ A
∥ℰ∥⇔𝒦 .fun = ∥ℰ∥⇒𝒦
∥ℰ∥⇔𝒦 .inv = 𝒦ᶠ⇒∥ℰ∥
∥ℰ∥⇔𝒦 .leftInv x = squash _ x
∥ℰ∥⇔𝒦 .rightInv x = isProp𝒦ᶠ _ x
\end{code}
%</from-enum>
