\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

module Cardinality.Finite.SplitEnumerable where

open import Prelude
open import Container
open import Data.Fin
open import Data.Sigma.Properties
open import Function.Surjective.Properties
open import Data.Fin.Properties

import Cardinality.Finite.SplitEnumerable.Container as ℒ
import Cardinality.Finite.SplitEnumerable.Inductive as 𝕃
open import Cardinality.Finite.SplitEnumerable.Isomorphism

open import Data.Nat.Literals
open import Data.Fin.Literals
open import Literals.Number

private
  variable
    u : Level
    U : A → Type u

module _ {a} {A : Type a} where
 open ℒ
 open import Container.List
 open import Container.Membership (ℕ ▷ Fin)
 open import Relation.Binary.Equivalence.Reasoning (⇔-equiv {a})
\end{code}
%<*split-surj>
\begin{code}
 ℰ!⇔Fin↠! : ℰ! A ⇔ Σ[ n ⦂ ℕ ] (Fin n ↠! A)
 ℰ!⇔Fin↠! =
   ℰ! A                                                  ≋⟨⟩ -- ℰ!
   Σ[ xs ⦂ List A ] Π[ x ⦂ A ] x ∈ xs                    ≋⟨⟩ -- ∈
   Σ[ xs ⦂ List A ] Π[ x ⦂ A ] fiber (xs .snd) x         ≋⟨ reassoc ⟩
   Σ[ n ⦂ ℕ ] Σ[ f ⦂ (Fin n → A) ] Π[ x ⦂ A ] fiber f x  ≋⟨⟩ -- ↠!
   Σ[ n ⦂ ℕ ] (Fin n ↠! A) ∎
\end{code}
%</split-surj>
\begin{code}
 ℰ!⇒Discrete : ℰ! A → Discrete A
 ℰ!⇒Discrete = flip Discrete↠!A⇒Discrete⟨A⟩ discreteFin
             ∘ snd
             ∘ ℰ!⇔Fin↠! .fun

module _ where
 open 𝕃
 open import Data.List.Sugar hiding ([_])
 open import Data.List.Syntax
 open import Data.List.Membership
\end{code}
%<*bool>
\begin{code}
 ℰ!⟨2⟩ : ℰ! Bool
 ℰ!⟨2⟩ .fst = [ false , true ]
 ℰ!⟨2⟩ .snd false  = 0  , refl
 ℰ!⟨2⟩ .snd true   = 1  , refl
\end{code}
%</bool>
%<*top>
\begin{code}
 ℰ!⟨⊤⟩ : ℰ! ⊤
 ℰ!⟨⊤⟩ .fst = [ tt ]
 ℰ!⟨⊤⟩ .snd _ = 0 , refl
\end{code}
%</top>
%<*bot>
\begin{code}
 ℰ!⟨⊥⟩ : ℰ! ⊥
 ℰ!⟨⊥⟩ = [] , λ ()
\end{code}
%</bot>
%<*sigma-sup>
\begin{code}
 sup-Σ : List A → (∀ x → List (U x)) → List (Σ A U)
 sup-Σ xs ys = do  x ← xs
                   y ← ys x
                   [ x , y ]
\end{code}
%</sigma-sup>
\begin{code}
 cov-Σ : (x : A)
       → (y : U x)
       → (xs : List A)
       → (ys : ∀ x → ℰ! (U x))
       → x ∈ xs
       → (x , y) ∈ sup-Σ xs (fst ∘ ys)
 cov-Σ xᵢ yᵢ (x ∷ xs) ys (fs n , x∈xs) =
   map (x ,_) (ys x .fst) ++◇ cov-Σ xᵢ yᵢ xs ys (n , x∈xs)
 cov-Σ xᵢ yᵢ (x ∷ xs) ys (f0  , x∈xs) =
   subst (λ x′ → (xᵢ , yᵢ) ∈ sup-Σ (x′ ∷ xs) (fst ∘ ys)) (sym x∈xs)
   (map (xᵢ ,_) (ys xᵢ .fst) ◇++ cong-∈ (xᵢ ,_) (ys xᵢ .fst) (ys xᵢ .snd yᵢ))


 _|Σ|_ : ℰ! A → (∀ x → ℰ! (U x)) → ℰ! (Σ A U)
 (xs |Σ| ys) .fst = sup-Σ (xs .fst) (fst ∘ ys)
 (xs |Σ| ys) .snd (x , y) = cov-Σ x y (xs .fst) ys (xs .snd x)

 _|×|_ : ℰ! A → ℰ! B → ℰ! (A × B)
 xs |×| ys = xs |Σ| const ys

 _|⊎|_ : ℰ! A → ℰ! B → ℰ! (A ⊎ B)
 (xs |⊎| ys) .fst = map inl (xs .fst) ++ map inr (ys .fst)
 (xs |⊎| ys) .snd (inl x) = map inl (xs .fst) ◇++ cong-∈ inl (xs .fst) (xs .snd x)
 (xs |⊎| ys) .snd (inr y) = map inl (xs .fst) ++◇ cong-∈ inr (ys .fst) (ys .snd y)

 _|+|_ : ℰ! A → ℰ! B → ℰ! (Σ[ t ⦂ Bool ] (if t then A else B))
 xs |+| ys = ℰ!⟨2⟩ |Σ| bool ys xs

 open import Data.Tuple

 ℰ!⟨Tuple⟩ : ∀ {n u} {U : Fin n → Type u} → (∀ i → ℰ! (U i)) → ℰ! (Tuple n U)
 ℰ!⟨Tuple⟩ {n = zero}  f = (_ ∷ []) , λ _ → f0 , refl
 ℰ!⟨Tuple⟩ {n = suc n} f = f f0 |×| ℰ!⟨Tuple⟩ (f ∘ fs)
\end{code}
