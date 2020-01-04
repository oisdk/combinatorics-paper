\begin{code}
{-# OPTIONS --cubical --safe #-}

module Cardinality.Finite.SplitEnumerable where

open import Prelude
open import Data.List
open import Data.List.Membership
open import Data.List.Relation.Unary
open import Data.List.Syntax
open import Data.Fin as Fin using (Fin; f0; fs; discreteFin)
open import Function.Surjective
open import Data.Vec.Iterated as Vec using (Vec)
import Data.Unit.UniversePolymorphic as Poly-⊤
open import Data.List.Sugar
private
  variable
    u : Level
    U : A → Type u
\end{code}
%<*definition>
\begin{code}
ℰ! : Type a → Type a
ℰ! A = Σ[ support ∈ List A ] (∀ x → x ∈ support)
\end{code}
%</definition>
\begin{code}
module WrongBool where
 open import Literals.Number
 open import Data.Fin.Literals
\end{code}
%<*wrong-bool>
\begin{code}
 ℰ!⟨Bool⟩ : ℰ! Bool
 ℰ!⟨Bool⟩ .fst        = [ false , true , false ]
 ℰ!⟨Bool⟩ .snd false  = at 2
 ℰ!⟨Bool⟩ .snd true   = at 1
\end{code}
%</wrong-bool>
\begin{code}
module _ where
 open import Literals.Number
 open import Data.Fin.Literals
\end{code}
%<*bool>
\begin{code}
 ℰ!⟨Bool⟩ : ℰ! Bool
 ℰ!⟨Bool⟩ .fst        = [ false , true ]
 ℰ!⟨Bool⟩ .snd false  = at 0
 ℰ!⟨Bool⟩ .snd true   = at 1
\end{code}
%</bool>
%<*empty>
\begin{code}
 ℰ!⟨⊥⟩ : ℰ! ⊥
 ℰ!⟨⊥⟩ .fst = []
 ℰ!⟨⊥⟩ .snd ()
\end{code}
%</empty>
%<*unit>
\begin{code}
 ℰ!⟨⊤⟩ : ℰ! ⊤
 ℰ!⟨⊤⟩ .fst    = [ tt ]
 ℰ!⟨⊤⟩ .snd x  = 0 , refl
\end{code}
%</unit>
%</from-surj>
%<*to-surj>
\begin{code}
ℰ!⇒Fin↠! : (E : ℰ! A) → Fin (length (fst E)) ↠! A
ℰ!⇒Fin↠! E .fst i  = E .fst ! i
ℰ!⇒Fin↠! E .snd    = E .snd
\end{code}
%</to-surj>
%<*from-surj>
\begin{code}
map-ℰ! : (f : A ↠! B) → ℰ! A → ℰ! B
map-ℰ! (f , surj) E .fst = map f (E .fst)
map-ℰ! (f , surj) E .snd x =
  let y , p = surj x
      z , q = cong-∈ f (E .fst) (E .snd y)
  in z , q ; p
\end{code}
%</from-surj>
%<*fin-inst>
\begin{code}
ℰ!⟨Fin⟩ : ∀ n → ℰ! (Fin n)
ℰ!⟨Fin⟩ n .fst  = tabulate n id
ℰ!⟨Fin⟩ n .snd  = fin∈tabulate id
\end{code}
%</fin-inst>
%<*discrete>
\begin{code}
ℰ!⇒Discrete : ℰ! A → Discrete A
ℰ!⇒Discrete fa = Discrete↠!A⇒Discrete⟨A⟩ (ℰ!⇒Fin↠! fa) discreteFin
\end{code}
%</discrete>
\begin{code}
cart : List A → List B → List (A × B)
cart xs ys = foldr (λ x → flip (foldr (λ y → (x , y) ∷_)) ys) [] xs

cart-cover : (x : A)
           → (y : B)
           → ∀ xs ys
           → x ∈ xs
           → y ∈ ys
           → (x , y) ∈ cart xs ys
cart-cover {A = A} {B = B} xᵢ yᵢ xs ys x∈xs y∈ys = foldrP Base₁ f₁ (λ ()) xs x∈xs
  where
  Base₁ : List A → Type _
  Base₁ xs = xᵢ ∈ xs → (xᵢ , yᵢ) ∈ cart xs ys

  Base₂ : (x : A) → List (A × B) → List B → Type _
  Base₂ x zs ys = yᵢ ∈ ys → (xᵢ , yᵢ) ∈ foldr (λ y → (x , y) ∷_) zs ys

  Base₃ : A → List (A × B) → List B → Type _
  Base₃ x zs ys = (xᵢ , yᵢ) ∈ foldr (λ y → (x , y) ∷_) zs ys

  f₂ : ∀ x → x ≡ xᵢ → ∀ zs y ys → Base₂ x zs ys → Base₂ x zs (y ∷ ys)
  f₂ x x∈xs zs y ys Pys (f0  , y∈ys) = f0 , cong₂ _,_ x∈xs y∈ys
  f₂ x x∈xs zs y ys Pys (fs n , y∈ys) = push (Pys (n , y∈ys))

  f₁ : ∀ x xs → Base₁ xs → Base₁ (x ∷ xs)
  f₁ x xs Pxs (f0   , x∈xs) = foldrP (Base₂ x _) (f₂ x x∈xs _) (λ ()) ys y∈ys
  f₁ x xs Pxs (fs n  , x∈xs) = foldrP (Base₃ x _) (λ _ _ → push) (Pxs (n , x∈xs)) ys
infixr 4 _|×|_
\end{code}
%<*prod-prf>
\begin{code}
_|×|_ : ℰ! A → ℰ! B → ℰ! (A × B)
(xs |×| ys) .fst         = cart (xs .fst) (ys .fst)
(xs |×| ys) .snd (x , y) = cart-cover x y (xs .fst) (ys .fst) (xs .snd x) (ys .snd y)
\end{code}
%</prod-prf>
%<*sum-prf>
\begin{code}
_|⊎|_ : ℰ! A → ℰ! B → ℰ! (A ⊎ B)
(xs |⊎| ys) .fst = map inl (fst xs) ++ map inr (fst ys)
(xs |⊎| ys) .snd (inl x) = map inl (xs .fst) ◇++ cong-∈ inl (xs .fst) (xs .snd x)
(xs |⊎| ys) .snd (inr y) = map inl (xs .fst) ++◇ cong-∈ inr (ys .fst) (ys .snd y)
\end{code}
%</sum-prf>
%<*sigma-enum>
\begin{code}
enum-Σ : (xs : List A) (ys : ∀ x → List (U x))
       → List (Σ A U)
enum-Σ xs ys = do
  x ← xs
  y ← ys x
  [ (x , y) ]
\end{code}
%</sigma-enum>
\begin{code}
enum-Σ-cover : {B : A → Type b}
             → (x : A)
             → (y : B x)
             → (xs : List A)
             → (ys : ∀ x → ℰ! (B x))
             → (x ∈ xs)
             → (x , y) ∈ enum-Σ xs (fst ∘ ys)
enum-Σ-cover xᵢ yᵢ (x ∷ xs) ys (fs n , x∈xs) = map (x ,_) (ys x .fst) ++◇ enum-Σ-cover xᵢ yᵢ xs ys (n , x∈xs)
enum-Σ-cover xᵢ yᵢ (x ∷ xs) ys (f0  , x∈xs) = subst (λ x′ → (xᵢ , yᵢ) ∈ enum-Σ (x′ ∷ xs) (fst ∘ ys)) (sym x∈xs)
                                                 (map (xᵢ ,_) (ys xᵢ .fst) ◇++ cong-∈ (xᵢ ,_) (ys xᵢ .fst) (ys xᵢ .snd yᵢ))
\end{code}
%<*sigma-fin>
\begin{code}
_|Σ|_ : {B : A → Type b} → ℰ! A → (∀ (x : A) → ℰ! (B x)) → ℰ! (Σ A B)
(xs |Σ| ys) .fst = enum-Σ (xs .fst) (fst ∘ ys)
(xs |Σ| ys) .snd (x , y) = enum-Σ-cover x y (xs .fst) ys (xs .snd x)
\end{code}
%</sigma-fin>
\begin{code}
ℰ!⟨⊤⟩-poly : ∀ {a} → ℰ! (Poly-⊤.⊤ {a})
fst ℰ!⟨⊤⟩-poly = Poly-⊤.tt ∷ []
snd ℰ!⟨⊤⟩-poly _ = f0 , refl
\end{code}
%<*fin-vec>
\begin{code}
ℰ!⟨Vec⟩ : ∀ {n} → ℰ! A → ℰ! (Vec A n)
ℰ!⟨Vec⟩ {n = zero}  xs = ℰ!⟨⊤⟩-poly
ℰ!⟨Vec⟩ {n = suc n} xs = xs |×| ℰ!⟨Vec⟩ xs
\end{code}
%</fin-vec>
\begin{code}
ℰ!⟨Lift⟩ : ∀ {ℓ} → ℰ! A → ℰ! (Lift ℓ A)
ℰ!⟨Lift⟩ xs .fst = map lift (xs .fst)
ℰ!⟨Lift⟩ xs .snd = cong-∈ lift (xs .fst) ∘ xs .snd ∘ lower
\end{code}
\begin{code}
variable
  p : Level
  P : A → Type p

module Quantifications {a} {A : Type a} {p} {P : A → Type p} where
  open import Relation.Nullary
  open import Data.List.Relation.Unary
  open Forall P
  open Exists P
\end{code}
%<*forall-quant>
\begin{code}
  for-each : ∀ xs → ◻ P xs → ∀ x → x ∈ xs → P x
  for-each xs ◻Pxs x (n , x∈xs) =
    subst P x∈xs (◻Pxs n)

  ∀? : ℰ! A → (∀ x → Dec (P x)) → Dec (∀ x → P x)
  ∀? (sup , cov) P? =
    ∣ ◻? P? sup
      ∣yes⇒  (λ ◻Pxs x →
                for-each sup ◻Pxs x (cov x))
      ∣no⇒   (λ f i → f (sup ! i))
\end{code}
%</forall-quant>
%<*exists-quant>
\begin{code}
  for-some : ∀ x → P x → ∀ xs → x ∈ xs → ◇ P xs
  for-some x Px xs (n , x∈xs) =
    n , subst P (sym x∈xs) Px

  ∃? : ℰ! A → (∀ x → Dec (P x)) → Dec (∃[ x ] P x)
  ∃? (sup , cov) P? =
    ∣ ◇? P? sup
      ∣yes⇒  (_ ,_) ∘ snd
      ∣no⇒   λ { ( x , Px ) → for-some x Px sup (cov x)}
\end{code}
%</exists-quant>
