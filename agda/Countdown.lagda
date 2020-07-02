\begin{code}
{-# OPTIONS --cubical --postfix-projections --safe #-}

module Countdown where

open import Prelude hiding (C)
open import Data.List
open import Data.Fin

open import Literals.Number
open import Data.Nat.Literals
open import Data.Fin.Literals
open import Data.Nat using (_+_; _*_)
open import Data.Nat.Properties using (pred; _<_)
open import Data.Fin.Properties using (FinToℕ)
open import Agda.Builtin.Nat using (_-_; _==_; div-helper)
open import Dyck
open import Data.Vec.Iterated

\end{code}
%<*ops-def>
\begin{code}
data Op : Type₀ where
  +′ ×′ -′ ÷′ : Op
\end{code}
%</ops-def>
\begin{code}
private
  variable
    n m k : ℕ

Subseq : ℕ → Type₀
Subseq = Vec Bool

private
  module WrongPerm where
\end{code}
%<*wrong-perm>
\begin{code}
    Perm : ℕ → Type₀
    Perm n = Fin n → Fin n
\end{code}
%</wrong-perm>
\begin{code}
private
  module IsoPerm where
\end{code}
%<*isomorphism>
\begin{code}
    Isomorphism : Type a → Type b → Type (a ℓ⊔ b)
    Isomorphism A B = Σ[ f ⦂ (A → B) ] Σ[ g ⦂ (B → A) ] (f ∘ g ≡ id) × (g ∘ f ≡ id)
\end{code}
%</isomorphism>
%<*iso-perm>
\begin{code}
    Perm : ℕ → Type₀
    Perm n = Isomorphism (Fin n) (Fin n)
\end{code}
%</iso-perm>
%<*perm-def>
\begin{code}
Perm : ℕ → Type₀
Perm zero     = ⊤
Perm (suc n)  = Fin (suc n) × Perm n
\end{code}
%</perm-def>
\begin{code}

private
  variable ns : List ℕ

count : Subseq n → ℕ
count = foldr′ (λ x xs → bool 0 1 x + xs) 0

Comb : ℕ → Type₀
Comb n = Σ[ s ⦂ Subseq n ] Perm (count s)

\end{code}
%<*expr-def>
\begin{code}
ExprTree : ℕ → Type₀
ExprTree zero     = ⊥
ExprTree (suc n)  = Dyck 0 n × Vec Op n

Expr : List ℕ → Type₀
Expr ns = Σ[ s ⦂ Subseq (length ns) ] let m = count s in Perm m × ExprTree m
\end{code}
%</expr-def>
\begin{code}

-- Σ[ c ⦂ Comb (length ns) ] (ExprTree (count (fst c)))


open import Cardinality.Finite.SplitEnumerable
open import Cardinality.Finite.SplitEnumerable.Inductive
open import Cardinality.Finite.SplitEnumerable.Isomorphism
open import Function.Surjective.Properties

private
  module OpSlop where
\end{code}
%<*op-slop>
\begin{code}
    ℰ!⟨Op⟩ : ℰ! Op
    ℰ!⟨Op⟩ .fst = +′ ∷ +′ ∷ ×′ ∷ -′ ∷ ÷′ ∷ []
    ℰ!⟨Op⟩ .snd +′  = 0 , refl
    ℰ!⟨Op⟩ .snd ×′  = 2 , refl
    ℰ!⟨Op⟩ .snd -′  = 3 , refl
    ℰ!⟨Op⟩ .snd ÷′  = 4 , refl
\end{code}
%</op-slop>
\begin{code}
ℰ!⟨Fin⟩ : ℰ! (Fin n)
ℰ!⟨Fin⟩ = 𝕃⇔ℒ⟨ℰ!⟩ .inv (ℰ!⇔Fin↠! .inv (_ , ↠!-ident))

import Data.Unit.UniversePolymorphic as Poly

ℰ!⟨Poly⊤⟩ : ∀ {ℓ} → ℰ! (Poly.⊤ {ℓ})
ℰ!⟨Poly⊤⟩ .fst = _ ∷ []
ℰ!⟨Poly⊤⟩ .snd _ = f0 , refl

\end{code}
%<*vec-fin>
\begin{code}
ℰ!⟨Vec⟩ : ℰ! A → ℰ! (Vec A n)
ℰ!⟨Vec⟩ {n = zero   } ℰ!⟨A⟩ = ℰ!⟨Poly⊤⟩
ℰ!⟨Vec⟩ {n = suc n  } ℰ!⟨A⟩ = ℰ!⟨A⟩ |×| ℰ!⟨Vec⟩ ℰ!⟨A⟩
\end{code}
%</vec-fin>
\begin{code}
ℰ!⟨Subseq⟩ : ℰ! (Subseq n)
ℰ!⟨Subseq⟩ = ℰ!⟨Vec⟩ ℰ!⟨2⟩
\end{code}
%<*perm-fin>
\begin{code}
ℰ!⟨Perm⟩ : ℰ! (Perm n)
ℰ!⟨Perm⟩ {n = zero   } = ℰ!⟨⊤⟩
ℰ!⟨Perm⟩ {n = suc n  } = ℰ!⟨Fin⟩ |×| ℰ!⟨Perm⟩
\end{code}
%</perm-fin>
%<*op-fin>
\begin{code}
ℰ!⟨Op⟩ : ℰ! Op
ℰ!⟨Op⟩ .fst = +′ ∷ ×′ ∷ -′ ∷ ÷′ ∷ []
ℰ!⟨Op⟩ .snd +′  = 0 , refl
ℰ!⟨Op⟩ .snd ×′  = 1 , refl
ℰ!⟨Op⟩ .snd -′  = 2 , refl
ℰ!⟨Op⟩ .snd ÷′  = 3 , refl
\end{code}
%</op-fin>
\begin{code}


runSubseq : (xs : List A) → (ys : Subseq (length xs)) → Vec A (count ys)
runSubseq []       ys = _
runSubseq (x ∷ xs) (false , snd₁) = runSubseq xs snd₁
runSubseq (x ∷ xs) (true , snd₁) = x , runSubseq xs snd₁

insert : A → Fin (suc n) → Vec A n → Vec A (suc n)
insert x f0 xs = x , xs
insert {n = suc _} x (fs i) (x₂ , xs) = x₂ , insert x i xs

runPerm : Perm n → Vec A n → Vec A n
runPerm {n = zero} ps _ = _
runPerm {n = suc n} (fst₁ , snd₁) (x , xs) = insert x fst₁ (runPerm snd₁ xs)

runComb : (xs : List A) → (c : Comb (length xs)) → Vec A (count (c .fst))
runComb xs (-′s , perm) = runPerm perm (runSubseq xs -′s)

\end{code}
%<*expr-finite>
\begin{code}
ℰ!⟨ExprTree⟩ : ℰ! (ExprTree n)
ℰ!⟨ExprTree⟩ {n = zero } = ℰ!⟨⊥⟩
ℰ!⟨ExprTree⟩ {n = suc n} = ℰ!⟨Dyck⟩ |×| ℰ!⟨Vec⟩ ℰ!⟨Op⟩

ℰ!⟨Expr⟩ : ℰ! (Expr ns)
ℰ!⟨Expr⟩ = ℰ!⟨Subseq⟩ |Σ| λ _ → ℰ!⟨Perm⟩ |×| ℰ!⟨ExprTree⟩
\end{code}
%</expr-finite>
\begin{code}

buildExpr : (xs : List ℕ) → Expr xs → Tree Op ℕ
buildExpr xs (subseq , rest) with count subseq | runSubseq xs subseq
buildExpr xs (subseq , (perm , tree , ops)) | suc n | ys = fromDyck tree ops (runPerm perm ys)


÷′′ : ℕ → ℕ → ℕ
÷′′ m zero = zero
÷′′ m (suc n) = div-helper 0 m n m

appOneOp : Op → ℕ → ℕ → ℕ
appOneOp +′ = _+_
appOneOp ×′ = _*_
appOneOp -′ = _-_
appOneOp ÷′ = ÷′′

runTree : Tree Op ℕ → ℕ
runTree (leaf x) = x
runTree (node o xs ys) = appOneOp o (runTree xs) (runTree ys)

data Disp : Type₀ where
  lit : ℕ → Disp
  _⟨+⟩_ : Disp → Disp → Disp
  _⟨*⟩_ : Disp → Disp → Disp
  _⟨-⟩_ : Disp → Disp → Disp
  _⟨÷⟩_ : Disp → Disp → Disp

appDispOp : Op → Disp → Disp → Disp
appDispOp +′  = _⟨+⟩_
appDispOp ×′ = _⟨*⟩_
appDispOp -′   = _⟨-⟩_
appDispOp ÷′   = _⟨÷⟩_

open import Agda.Builtin.Strict

infixr 0 _$!_
_$!_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $! x = primForce x f

dispTree : Tree Op ℕ → Disp
dispTree (leaf x) = lit x
dispTree (node o xs ys) = (appDispOp o $! dispTree xs) $! dispTree ys

take : ℕ → List A → List A
take zero _ = []
take (suc n) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs

filter : (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) = if p x then x ∷ filter p xs else filter p xs

example : List Disp
example = map dispTree (take 1 (filter (λ e → runTree e == 765) (map (buildExpr nums) (ℰ!⟨Expr⟩ {ns = nums} .fst))))
  where
  nums = (1 ∷ 3 ∷ 7 ∷ 10 ∷ 25 ∷ 50 ∷ [])

-- Uncomment for a type error which contains the answer
-- prf : example ≡ (lit 0 ∷ [])
-- prf = refl
\end{code}
