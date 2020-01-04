\begin{code}
{-# OPTIONS --cubical --safe #-}

module Cardinality.Finite where

open import Data.List
open import Data.List.Membership
open import Data.List.Relation.Unary
open import Prelude
open import Data.Fin as Fin
import Data.Nat as ℕ
open import Data.Nat.Order using (_<_)
open import Path.Reasoning
open import Function.Injective
open import Data.Vec.Iterated using (Vec; Vec⇔Fin→)
import Data.Unit.UniversePolymorphic as Poly-⊤
open import Data.List.Syntax
open import Function.Surjective
open import Relation.Nullary
open import Function.Isomorphism

private
  variable
    n : ℕ
    x : A
    xs : List A
    y : B
    ys : List B

Dup : List A → Type _
Dup xs = ∃[ i ] ∃[ j ] (i ≢ᶠ j) × (xs ! i ≡ xs ! j)
\end{code}
%<*noetherian>
\begin{code}
data 𝒩ℓ (A : Type a) (xs : List A) : Type a where
  ask  : (∀ x → 𝒩ℓ A (x ∷ xs)) → 𝒩ℓ A xs
  stop : Dup xs → 𝒩ℓ A xs

Noetherian : Type a → Type a
Noetherian A = 𝒩ℓ A []
\end{code}
%</noetherian>
%<*bounded>
\begin{code}
Bounded : Type a → Type a
Bounded A = ∃[ n ] ∀ (xs : List A) → n < length xs → Dup xs
\end{code}
%</bounded>
%<*streamless>
\begin{code}
Streamless : Type a → Type a
Streamless A = ∀ (f : ℕ → A) → ∃[ n ] ∃[ m ] (n ≢ m) × (f n ≡ f m)
\end{code}
%</streamless>
%<*definition>
\begin{code}
ℰ : Type a → Type a
ℰ A = Σ[ support ∈ List A ] (∀ x → x ∈ support)
\end{code}
%</definition>
\begin{code}
module WrongBool where
 open import Literals.Number
 open import Data.Fin.Literals
\end{code}
%<*wrong-bool>
\begin{code}
 ℰ⟨Bool⟩ : ℰ Bool
 ℰ⟨Bool⟩ .fst        = [ false , true , false ]
 ℰ⟨Bool⟩ .snd false  = at 2
 ℰ⟨Bool⟩ .snd true   = at 1
\end{code}
%</wrong-bool>
\begin{code}
module _ where
 open import Literals.Number
 open import Data.Fin.Literals
\end{code}
%<*bool>
\begin{code}
 ℰ⟨Bool⟩ : ℰ Bool
 ℰ⟨Bool⟩ .fst        = [ false , true ]
 ℰ⟨Bool⟩ .snd false  = at 0
 ℰ⟨Bool⟩ .snd true   = at 1
\end{code}
%</bool>
%<*empty-unit>
\begin{code}
 ℰ⟨⊥⟩ : ℰ ⊥
 ℰ⟨⊥⟩ .fst = []
 ℰ⟨⊥⟩ .snd ()

 ℰ⟨⊤⟩ : ℰ ⊤
 ℰ⟨⊤⟩ .fst    = [ tt ]
 ℰ⟨⊤⟩ .snd x  = f0 , refl
\end{code}
%</empty-unit>
%<*from-surj>
\begin{code}
map-ℰ : (f : A ↠! B) → ℰ A → ℰ B
map-ℰ (f , surj) fa .fst = map f (fa .fst)
map-ℰ (f , surj) fa .snd x =
  let y , p = surj x
      z , q = cong-∈ f (fa .fst) (fa .snd y)
  in z , q ; p
\end{code}
%</from-surj>
%<*to-surj>
\begin{code}
ℰ⇒Fin↠! : (fa : ℰ A) → Fin (length (fst fa)) ↠! A
ℰ⇒Fin↠! fa .fst i = fa .fst ! i
ℰ⇒Fin↠! fa .snd = fa .snd
\end{code}
%</to-surj>
%<*fin-inst>
\begin{code}
ℰ⟨Fin⟩ : ∀ n → ℰ (Fin n)
ℰ⟨Fin⟩ n .fst  = tabulate n id
ℰ⟨Fin⟩ n .snd  = fin∈tabulate id
\end{code}
%</fin-inst>
%<*discrete>
\begin{code}
ℰ⇒Discrete : ℰ A → Discrete A
ℰ⇒Discrete fa = Discrete↠!A⇒Discrete⟨A⟩ (ℰ⇒Fin↠! fa) discreteFin
\end{code}
%</discrete>
%<*bishop>
\begin{code}
ℬ : Type a → Type a
ℬ A = Σ[ support ∈ List A ] (∀ x → x ∈! support)
\end{code}
%</bishop>
%<*bishop-to-kuratowski>
\begin{code}
ℬ⇒ℰ : ℬ A → ℰ A
ℬ⇒ℰ xs .fst    = xs .fst
ℬ⇒ℰ xs .snd x  = xs .snd x .fst
\end{code}
%</bishop-to-kuratowski>
%<*kuratowski-to-bishop>
\begin{code}
ℰ⇒ℬ : ℰ A → ℬ A
ℰ⇒ℬ xs .fst    = uniques (ℰ⇒Discrete xs) (fst xs)
ℰ⇒ℬ xs .snd x  = ∈⇒∈! (ℰ⇒Discrete xs) x (fst xs) (snd xs x)
\end{code}
%</kuratowski-to-bishop>
%<*bishop-equiv-fin>
\begin{code}
ℬ⇒Fin≃ : (ba : ℬ A) → Fin (length (fst ba)) ≃ A
ℬ⇒Fin≃ xs .fst n = fst xs ! n
ℬ⇒Fin≃ xs .snd .equiv-proof = snd xs
\end{code}
%</bishop-equiv-fin>
%<*kuratowski-equiv-fin>
\begin{code}
# : ℰ A → ℕ
# = length ∘ fst ∘ ℰ⇒ℬ

ℰ⇒Fin≃ : (fa : ℰ A) → Fin (# fa) ≃ A
ℰ⇒Fin≃ = ℬ⇒Fin≃ ∘ ℰ⇒ℬ
\end{code}
%</kuratowski-equiv-fin>
\begin{code}
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
%<*convolve>
\begin{code}
uncons-def : A → List A → A × List A
uncons-def d [] = d , []
uncons-def _ (x ∷ xs) = x , xs

convolveʳ  : A → B
           → (List (A × B) × List (List (A × B)) → List (List (A × B)))
           → (List (A × B) × List (List (A × B)) → List (List (A × B)))
convolveʳ x y ys (z , zs) = ((x , y) ∷ z) ∷ ys (uncons-def [] zs)

convolveˡ : List B → A → List (List (A × B)) → List (List (A × B))
convolveˡ ys x zs = foldr (convolveʳ x) (uncurry _∷_) ys ([] , zs)

convolve : List A → List B → List (List (A × B))
convolve xs ys = foldr (convolveˡ ys) [] xs

cantor : List A → List B → List (A × B)
cantor xs ys = concat (convolve xs ys)
\end{code}
%</convolve>
\begin{code}
shift-cover : ∀ {x : A} (ys : List B) {k : A × B} {z} {zs : List (List (A × B))}
            → k ∈² zs
            → k ∈² (foldr (convolveʳ x) (uncurry _∷_) ys (z , zs))
shift-cover [] (n , p) = fs n , p
shift-cover (_ ∷ ys) {zs = _ ∷  _ } (fs n , z∈zs) = Exists.push (_ ∈_) (shift-cover ys (n , z∈zs))
shift-cover (_ ∷ []) {zs = _ ∷ _ } (f0  , p) = fs f0 , p
shift-cover (_ ∷ _ ∷ ys) {zs = _ ∷ _} (f0 , p) = (fs f0 , push p)

convolveˡ-cover : ∀ {x xᵢ : A} {yᵢ : B} {z} {zs} ys
                → x ≡ xᵢ
                → yᵢ ∈ ys
                → (xᵢ , yᵢ) ∈² (foldr (convolveʳ x) (uncurry _∷_) ys (z , zs))
convolveˡ-cover (y ∷ ys) x≡ (f0 , y≡) = f0 , f0 , λ i → x≡ i , y≡ i
convolveˡ-cover (y ∷ ys) x≡ (fs n , y∈ys) = Exists.push (_ ∈_) (convolveˡ-cover ys x≡ (n , y∈ys))

convolve-cover : {xᵢ : A} (xs : List A) {yᵢ : B} (ys : List B)
               → xᵢ ∈ xs → yᵢ ∈ ys → (xᵢ , yᵢ) ∈² (convolve xs ys)
convolve-cover (x ∷ xs) ys (f0  , x∈xs) y∈ys = convolveˡ-cover ys x∈xs y∈ys
convolve-cover (x ∷ xs) ys (fs n , x∈xs) y∈ys = shift-cover ys (convolve-cover xs ys (n , x∈xs) y∈ys)

cantor-cover : {x : A} (xs : List A) {y : B} (ys : List B)
           → x ∈ xs → y ∈ ys → (x , y) ∈ cantor xs ys
cantor-cover {x = x} xs {y} ys x∈xs y∈ys = ∈²→∈ (convolve xs ys) (convolve-cover xs ys x∈xs y∈ys)

infixr 4 _|×|_
\end{code}
%<*prod-sig>
\begin{code}
_|×|_ : ℰ A → ℰ B → ℰ (A × B)
\end{code}
%</prod-sig>
\begin{code}
fst (xs |×| ys)     = cantor (fst xs) (fst ys)
snd (xs |×| ys) x,y = cantor-cover (xs .fst) (ys .fst) (snd xs (fst x,y)) (snd ys (snd x,y))
\end{code}
%<*interleave>
\begin{code}
interleaving : (A → C) → (B → C) → List A → List B → List C
interleaving f g []        ys = map g ys
interleaving f g (x ∷ xs)  ys = f x ∷ interleaving g f ys xs
\end{code}
%</interleave>
\begin{code}

_ :
\end{code}
%<*interleaving-example>
\begin{code}
 interleaving inl inr [ 1 , 2 , 3 ] [ 4 , 5 , 6 ]
   ≡
 [ inl 1 , inr 4 , inl 2 , inr 5 , inl 3 , inr 6 ]
\end{code}
%</interleaving-example>
\begin{code}
_ = refl

mutual
  interleaving-coverʳ : (xs : List A) {y : B} (ys : List B)
                      (f : A → C) → (g : B → C)
                    → (y ∈ ys) → g y ∈ interleaving f g xs ys
  interleaving-coverʳ [] ys f g y∈ys = cong-∈ g ys y∈ys
  interleaving-coverʳ (x ∷ xs) ys f g y∈ys = push (interleaving-coverˡ ys xs g f y∈ys)

  interleaving-coverˡ : {x : A} (xs : List A) (ys : List B)
                    (f : A → C) → (g : B → C)
                  → (x ∈ xs) → f x ∈ interleaving f g xs ys
  interleaving-coverˡ (_ ∷ _) ys g f (f0 , p) = f0 , cong g p
  interleaving-coverˡ (x ∷ xs) ys g f (fs n , x∈xs) = push (interleaving-coverʳ ys xs f g (n , x∈xs))
\end{code}
%<*sum-sig>
\begin{code}
_|⊎|_ : ℰ A → ℰ B → ℰ (A ⊎ B)
\end{code}
%</sum-sig>
\begin{code}
fst (xs |⊎| ys) = interleaving inl inr (fst xs) (fst ys)
snd (xs |⊎| ys) (inl x) = interleaving-coverˡ (fst xs) (fst ys) inl inr (snd xs x)
snd (xs |⊎| ys) (inr y) = interleaving-coverʳ (fst xs) (fst ys) inl inr (snd ys y)

ℰ⟨⊤⟩-poly : ∀ {a} → ℰ (Poly-⊤.⊤ {a})
fst ℰ⟨⊤⟩-poly = Poly-⊤.tt ∷ []
snd ℰ⟨⊤⟩-poly _ = f0 , refl
\end{code}
%<*fin-vec>
\begin{code}
ℰVec : ∀ {n} → ℰ A → ℰ (Vec A n)
ℰVec {n = zero} xs = ℰ⟨⊤⟩-poly
ℰVec {n = suc n} xs = xs |×| ℰVec xs
\end{code}
%</fin-vec>
%<*sigma-interleave>
\begin{code}
interleave-Σ : {B : A → Type b}
             → (xs : List A) (ys : ∀ x → List (B x))
             → List (Σ A B)
interleave-Σ xs ys =
  foldr (λ x ks → interleaving (_,_ x) id (ys x) ks) [] xs
\end{code}
%</sigma-interleave>
\begin{code}
interleave-Σ-cover : {B : A → Type b}
              → (x : A)
              → (y : B x)
              → (xs : List A)
              → (ys : ∀ x → ℰ (B x))
              → (x ∈ xs)
              → (x , y) ∈ interleave-Σ xs (fst ∘ ys)
interleave-Σ-cover {A = A} xᵢ yᵢ xs′ ys = foldrP Base f (λ ()) xs′
  where
  Base : List A → Type _
  Base xs = xᵢ ∈ xs → (xᵢ , yᵢ) ∈ interleave-Σ xs (fst ∘ ys)

  f : ∀ x xs  → Base xs → Base (x ∷ xs)
  f x xs Pxs (f0  , x∈xs) = subst (λ x′ → (xᵢ , yᵢ) ∈ interleave-Σ (x′ ∷ xs) (fst ∘ ys)) (sym x∈xs)
                              (interleaving-coverˡ (fst (ys xᵢ)) (interleave-Σ xs (fst ∘ ys)) (_,_ xᵢ) id (ys xᵢ .snd yᵢ))
  f x xs Pxs (fs n , x∈xs) = interleaving-coverʳ (fst (ys x )) (interleave-Σ xs (fst ∘ ys)) (_,_ x ) id (Pxs (n , x∈xs))
\end{code}
%<*sigma-fin>
\begin{code}
_|Σ|_ : {B : A → Type b} → ℰ A → (∀ (x : A) → ℰ (B x)) → ℰ (Σ A B)
\end{code}
%</sigma-fin>
\begin{code}
(xs |Σ| ys) .fst = interleave-Σ (xs .fst) (fst ∘ ys)
(xs |Σ| ys) .snd (x , y) = interleave-Σ-cover x y (xs .fst) ys (xs .snd x)
module Monomorphic where
 _|→|_ : {A B : Type₀} → ℰ A → ℰ B → ℰ (A → B)
\end{code}
%<*fun-prf>
\begin{code}
 _|→|_ {A = A} {B = B} xs ys = subst ℰ Vec⇔→ (ℰVec ys)
   where
   Vec⇔→ : Vec B (# xs) ≡ (A → B)
   Vec⇔→ =
     Vec B (# xs)      ≡⟨ isoToPath Vec⇔Fin→ ⟩
     (Fin (# xs) → B)  ≡⟨ (λ i → (ua (ℰ⇒Fin≃ xs) i → B)) ⟩
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

ℰLift : ∀ {ℓ} → ℰ A → ℰ (Lift ℓ A)
ℰLift xs .fst = map lift (xs .fst)
ℰLift xs .snd = cong-∈ lift (xs .fst) ∘ xs .snd ∘ lower

\end{code}
%<*fun-sig>
\begin{code}
_|→|_ : ∀ {A : Type a} {B : Type b} → ℰ A → ℰ B → ℰ (A → B)
\end{code}
%</fun-sig>
\begin{code}
_|→|_ {a} {b} {A = A} {B = B} xs ys = subst ℰ Vec≡→ (ℰLift (ℰVec ys))
  where
  Vec≡→ : Lift a (Vec B (# xs)) ≡ (A → B)
  Vec≡→ =
    Lift a (Vec B (# xs)) ≡⟨ isoToPath Lift⟨Vec⇔Fin→⟩ ⟩
    (Lift a (Fin (# xs)) → B)  ≡⟨ (λ i → (ua (ℬ⇒Lift⟨Fin⟩≃ (ℰ⇒ℬ xs)) i → B)) ⟩
    (A → B) ∎

open import Function.Injective

ℬ⇒∃Fin≃ : (ba : ℬ A) → ∃[ n ] (Fin n ≃ A)
ℬ⇒∃Fin≃ xs .fst = length (fst xs)
ℬ⇒∃Fin≃ xs .snd .fst n = fst xs ! n
ℬ⇒∃Fin≃ xs .snd .snd .equiv-proof = snd xs

ℬ⇒Fin↣ : (ba : ℬ A) → Fin (length (fst ba)) ↣ A
ℬ⇒Fin↣ ba = equiv⇒Injective (ℬ⇒Fin≃ ba)

ℬ⇒↣Fin : (ba : ℬ A) → A ↣ Fin (length (fst ba))
ℬ⇒↣Fin ba .fst x = ba .snd x .fst .fst
ℬ⇒↣Fin ba .snd x y fx≡fy =
  let (n , p) = ba .snd x .fst
      (m , q) = ba .snd y .fst
  in sym p ; cong (fst ba !_) fx≡fy ; q

ℬ⇒isSet : ℬ A → isSet A
ℬ⇒isSet ba = Discrete→isSet (A↣Discrete⇒Discrete⟨A⟩ (ℬ⇒↣Fin ba) discreteFin)

∃Fin≃⇒ℬ : ∃[ n ] (Fin n ≃ A) → ℬ A
∃Fin≃⇒ℬ (n , f≃A) .fst = tabulate n (f≃A .fst)
∃Fin≃⇒ℬ (n , f≃A) .snd x =
  let (y , z) = f≃A .snd .equiv-proof x .fst
  in
    f⟨i⟩∈!tab⟨f⟩
      (Discrete→isSet (Discrete↠!A⇒Discrete⟨A⟩ (equiv⇒surj f≃A) discreteFin))
      (equiv⇒Injective f≃A)
      y z

open import Cubical.HITs.PropositionalTruncation
\end{code}
%<*prop-finite>
\begin{code}
ℱ : Type a → Type a
ℱ A = ∃[ n ] ∥ Fin n ≃ A ∥
\end{code}
%</prop-finite>
\begin{code}
ℰ⇒ℱ : ℰ A → ℱ A
ℰ⇒ℱ x = # x , ∣ ℰ⇒Fin≃ x ∣

∥map∥ : (A → B) → ∥ A ∥ → ∥ B ∥
∥map∥ f = recPropTrunc propTruncIsProp (∣_∣ ∘ f)

∥ℰ⇒ℬ∥ : ∥ ℰ A ∥ → ∥ ℬ A ∥
∥ℰ⇒ℬ∥ = ∥map∥ ℰ⇒ℬ


-- open import Algebra.Construct.Free.CommutativeIdempotentMonoid
--   renaming (_∈_ to _𝒦∈_)
-- open import Cubical.HITs.S1

-- 𝒦-fin : Type a → Type a
-- 𝒦-fin A = Σ[ k ∈ 𝒦 A ] (∀ x → x 𝒦∈ k)

-- 𝒦-fin-S¹ : 𝒦-fin S¹
-- 𝒦-fin-S¹ .fst = base ∷ []
-- 𝒦-fin-S¹ .snd base = here
-- 𝒦-fin-S¹ .snd (loop i) = {!!}


-- This definitely works, just need to figure out where to put it.
-- _∥→∥_ : ℱ A → ℱ B → ℱ (A → B)
-- (xn , xs) ∥→∥ (yn , ys) = _ , recPropTrunc propTruncIsProp (λ xs≃ → recPropTrunc propTruncIsProp (λ ys≈ → {!!}) ys) xs

-- open import Algebra
-- module _ {ℓ} (mon : CommutativeMonoid ℓ) where
--  open CommutativeMonoid mon
--  module _ (f : A → 𝑆) where
--    summarise : ℱ A → 𝑆
--    summarise 

\end{code}
