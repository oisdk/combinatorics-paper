\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

module Cardinality.Container.Finite where

open import Prelude

open import Data.Container
open import Data.Container.List
open import Data.Container.List.Membership
open import Data.Container.Relation.Unary ℒ
import Data.List.Membership as List
open import Data.List as List using (List; _∷_; [])
import Cardinality.Finite.SplitEnumerable as List
import Cardinality.Finite.ManifestEnumerable as List
import Cardinality.Finite.ManifestBishop as List
open import Data.Fin
open import Data.List.Properties
open import Data.Nat using (znots; snotz)
open import Cubical.Foundations.Everything using (J)
open import HITs.PropositionalTruncation.Sugar
\end{code}
%<*split-enum>
\begin{code}
ℰ! : Type a → Type a
ℰ! A = Σ[ support ∈ ⟦ ℒ ⟧ A ] ∀ x → x ∈ support
\end{code}
%</split-enum>
%<*bishop>
\begin{code}
ℬ : Type a → Type a
ℬ A = Σ[ support ∈ ⟦ ℒ ⟧ A ] ∀ x → x ∈! support
\end{code}
%</bishop>
%<*enum>
\begin{code}
ℰ : Type a → Type a
ℰ A = Σ[ support ∈ ⟦ ℒ ⟧ A ] ∀ x → ∥ x ∈ support ∥
\end{code}
%</enum>
\begin{code}
∈ℒ⇒∈List : ∀ (x : A) (xs : ⟦ ℒ ⟧ A) → x ∈ xs → x List.∈ ℒ→List xs
∈ℒ⇒∈List x (suc l , xs) (f0   , p) = f0 , p
∈ℒ⇒∈List x (suc l , xs) (fs n , p) = List.push (∈ℒ⇒∈List x (l , xs ∘ fs) (n , p))

Int⇔Ext⟨ℰ!⟩ : List.ℰ! A ⇔ ℰ! A
Int⇔Ext⟨ℰ!⟩ .fun (sup , cov) = List→ℒ sup , cov
Int⇔Ext⟨ℰ!⟩ .inv (sup , cov) = ℒ→List sup , λ x → ∈ℒ⇒∈List x sup (cov x)
Int⇔Ext⟨ℰ!⟩ .rightInv (sup , cov) i .fst = List⇔ℒ .rightInv sup i
Int⇔Ext⟨ℰ!⟩ .rightInv (sup , cov) i .snd x = ∈ℒ⇒∈List-rightInv sup (cov x) i
  where
  ∈ℒ⇒∈List-rightInv : ∀ xs x∈xs →
    ∈ℒ⇒∈List x xs x∈xs ≡[ i ≔ x ∈ List⇔ℒ .rightInv xs i ]≡ x∈xs
  ∈ℒ⇒∈List-rightInv (suc l , xs) (f0   , x∈xs) i = f0 , x∈xs
  ∈ℒ⇒∈List-rightInv (suc l , xs) (fs n , x∈xs) i =
    let m , q = ∈ℒ⇒∈List-rightInv (l , xs ∘ fs) (n , x∈xs) i
    in fs m , q
Int⇔Ext⟨ℰ!⟩ .leftInv (sup , cov) i .fst = List⇔ℒ .leftInv sup i
Int⇔Ext⟨ℰ!⟩ .leftInv (sup , cov) i .snd x = ∈ℒ⇒∈List-leftInv sup (cov x) i
  where
  ∈ℒ⇒∈List-leftInv : ∀ xs x∈xs →
    ∈ℒ⇒∈List x (List→ℒ xs) x∈xs ≡[ i ≔ x List.∈ List→ℒ→List xs i ]≡ x∈xs
  ∈ℒ⇒∈List-leftInv (_ ∷ xs) (f0   , x∈xs) i = f0 , x∈xs
  ∈ℒ⇒∈List-leftInv (_ ∷ xs) (fs n , x∈xs) i =
    let m , p = ∈ℒ⇒∈List-leftInv xs (n , x∈xs) i
    in fs m , p

Int⇔Ext⟨ℰ⟩ : List.ℰ A ⇔ ℰ A
Int⇔Ext⟨ℰ⟩ .fun (sup , cov) = List→ℒ sup , cov
Int⇔Ext⟨ℰ⟩ .inv (sup , cov) = ℒ→List sup , λ x → ∈ℒ⇒∈List x sup ∥$∥ cov x
Int⇔Ext⟨ℰ⟩ .rightInv (sup , cov) i .fst = List⇔ℒ .rightInv sup i
Int⇔Ext⟨ℰ⟩ .rightInv (sup , cov) i .snd x =
  J
    (λ ys ys≡ → (x∈ys : ∥ x ∈ ys ∥) → PathP (λ i → ∥ x ∈ sym ys≡ i ∥ ) x∈ys (cov x))
    (λ z → squash z _)
    (sym (uncurry ℒ→List→ℒ sup))
    (∈ℒ⇒∈List x sup ∥$∥ cov x)
    i
Int⇔Ext⟨ℰ⟩ .leftInv (sup , cov) i .fst = List⇔ℒ .leftInv sup i
Int⇔Ext⟨ℰ⟩ .leftInv (sup , cov) i .snd x =
  J
    (λ ys ys≡ → (x∈ys : ∥ x List.∈ ys ∥) → PathP (λ i → ∥ x List.∈ sym ys≡ i ∥ ) x∈ys (cov x))
    (λ z → squash z _)
    (sym (List→ℒ→List sup))
    (∈ℒ⇒∈List x (List→ℒ sup) ∥$∥ cov x)
    i

∈!ℒ⇒∈!List : ∀ (x : A) l (xs : Fin l → A) → x ∈! (l , xs) → x List.∈! ℒ→List (l , xs)
∈!ℒ⇒∈!List x (suc l) xs ((f0   , p) , u) = (f0 , p) , lemma
  where
  lemma : (y : x List.∈ ℒ→List (suc l , xs)) → (f0 , p) ≡ y
  lemma (f0   , q) = cong (∈ℒ⇒∈List x (suc l , xs)) (u (f0 , q))
  lemma (fs m , q) =
    let o , r = subst (x ∈_) (ℒ→List→ℒ l (xs ∘ fs)) (m , q)
    in ⊥-elim (znots (cong (FinToℕ ∘ fst) (u (fs o , r))))
∈!ℒ⇒∈!List x (suc l) xs ((fs n , p) , u) = List.push! xs0≢x (∈!ℒ⇒∈!List x l (xs ∘ fs) ((n , p) , uxss))
  where
  xs0≢x : xs f0 ≢ x
  xs0≢x xs0≡x = snotz (cong (FinToℕ ∘ fst) (u (f0 , xs0≡x)))

  uxss : (y : x ∈ (l , xs ∘ fs)) → (n , p) ≡ y
  uxss (m , q) = cong (λ { (f0 , q) → ⊥-elim (xs0≢x q) ; (fs m , q) → m , q}) (u (fs m , q))

Int⇔Ext⟨ℬ⟩ : List.ℬ A ⇔ ℬ A
Int⇔Ext⟨ℬ⟩ .fun (sup , cov) = List→ℒ sup , cov
Int⇔Ext⟨ℬ⟩ .inv ((l , xs) , cov) = ℒ→List (l , xs) , λ x → ∈!ℒ⇒∈!List x l xs (cov x)
Int⇔Ext⟨ℬ⟩ .rightInv (sup , cov) i .fst = List⇔ℒ .rightInv sup i
Int⇔Ext⟨ℬ⟩ .rightInv ((l , xs) , cov) i .snd x =
  J
    (λ ys ys≡ → (zs : x ∈! ys) → zs ≡[ i ≔ x ∈! sym ys≡ i ]≡ cov x)
    (λ _ → isPropIsContr _ _)
    (sym (ℒ→List→ℒ l xs))
    (∈!ℒ⇒∈!List x l xs (cov x))
    i
Int⇔Ext⟨ℬ⟩ .leftInv  (sup , cov) i .fst = List⇔ℒ .leftInv sup i
Int⇔Ext⟨ℬ⟩ .leftInv  (sup , cov) i .snd x =
  J
    (λ ys ys≡ → (zs : x List.∈! ys) → zs ≡[ i ≔ x List.∈! sym ys≡ i ]≡ cov x)
    (λ zs → isPropIsContr _ _)
    (sym (List→ℒ→List sup))
    (∈!ℒ⇒∈!List x (List.length sup) (sup List.!_) (cov x))
    i

open import Function.Surjective

ℰ!⇔Fin↠! : ℰ! A ⇔ (∃[ n ] (Fin n ↠! A))
ℰ!⇔Fin↠! .fun ((n , xs) , cov) = (n , (xs , cov))
ℰ!⇔Fin↠! .inv (n , (xs , cov)) = ((n , xs) , cov)
ℰ!⇔Fin↠! .rightInv _ = refl
ℰ!⇔Fin↠! .leftInv _ = refl

ℬ⇔Fin≃ : ℬ A ⇔ (∃[ n ] (Fin n ≃ A))
ℬ⇔Fin≃ .fun ((n , xs) , cov) .fst = n
ℬ⇔Fin≃ .fun ((n , xs) , cov) .snd .fst = xs
ℬ⇔Fin≃ .fun ((n , xs) , cov) .snd .snd .equiv-proof = cov
ℬ⇔Fin≃ .inv (n , (xs , cov)) = ((n , xs) , cov .equiv-proof)
ℬ⇔Fin≃ .rightInv (n , (xs , cov)) i .fst = n
ℬ⇔Fin≃ .rightInv (n , (xs , cov)) i .snd .fst = xs
ℬ⇔Fin≃ .rightInv (n , (xs , cov)) i .snd .snd .equiv-proof = cov .equiv-proof
ℬ⇔Fin≃ .leftInv _ = refl
\end{code}
