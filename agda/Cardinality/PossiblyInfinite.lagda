\begin{code}
{-# OPTIONS --cubical --safe --sized-types --postfix-projections #-}

module Cardinality.PossiblyInfinite where

open import Prelude

open import Codata.Covec
open import Codata.Size
open import Data.Fin.Infinite
open import Function.Surjective
open import HITs.InfNat hiding (∞)

private
  variable n m : ℕ+∞

\end{code}
%<*def>
\begin{code}
ℰ! : Type a → Type a
ℰ! A = ∃[ n ] Σ[ support ∈ Covec A ∞ n ] (∀ x → x ∈ support)
\end{code}
%</def>
\begin{code}
ℰ!⇒Fin↠! : (E : ℰ! A) → Fin (fst E) ↠! A
ℰ!⇒Fin↠! E .fst i = E .snd .fst ! i
ℰ!⇒Fin↠! E .snd = E .snd .snd

map-ℰ! : (f : A ↠! B) → ℰ! A → ℰ! B
map-ℰ! (f , surj) E .fst = E .fst
map-ℰ! (f , surj) E .snd .fst = map f (E .snd .fst)
map-ℰ! (f , surj) E .snd .snd x =
  let y , p = surj x
      z , q = cong-∈ f (E .snd .fst) (E .snd .snd y)
  in z , q ; p

ℰ!⇒Discrete : ℰ! A → Discrete A
ℰ!⇒Discrete E = Discrete↠!A⇒Discrete⟨A⟩ (ℰ!⇒Fin↠! E) (discreteFin {n = E .fst})

-- mutual
--   interleaving : (A → C) → (B → C) → Covec A i n → Covec B i m → Covec C i (n + m)
--   interleaving f g [] ys = {!!}
--   interleaving f g (∹ xs) ys = {!!}

--   interleaving⁺ : (A → C) → (B → C) → Covec⁺ A i n → Covec B i m → Covec⁺ C i (m + n)
--   interleaving⁺ f g xs ys .head = f (xs .head)
--   interleaving⁺ f g xs ys .tail = interleaving g f ys (xs .tail)

-- mutual
--   interleave-coverʳ : (xs : Covec A ∞) {y : B} {ys : Covec B ∞}
--                     → {f : A → C} (g : B → C)
--                     → (y ∈ ys) → g y ∈ interleaving f g xs ys
--   interleave-coverʳ [] {ys = ys}  g y∈ys = cong-∈ g ys y∈ys
--   interleave-coverʳ (∹ xs) {ys = ys} g y∈ys = push (interleave-coverˡ {xs = ys} (xs .tail) g y∈ys)

--   interleave-coverˡ : {x : A} {xs : Covec A ∞} (ys : Covec B ∞)
--                       (f : A → C) → {g : B → C}
--                       → (x ∈ xs) → f x ∈ interleaving f g xs ys
--   interleave-coverˡ {xs = ∹ x} ys g (zero  , x∈xs) = zero , cong g x∈xs
--   interleave-coverˡ {xs = ∹ x} ys g (suc n , x∈xs) = push (interleave-coverʳ ys g (n , x∈xs))

-- -- mutual
-- --   interleave-finiteʳ : (xs : Covec A ∞) {ys : Covec B ∞}
-- --                      → {f : A → C} (g : B → C)
-- --                      → Finite (length xs) → Finite (length ys)
-- --                      → Finite (length (interleaving f g xs ys))
-- --   interleave-finiteʳ [] {ys = ys} g fxs fys = subst Finite (map-length g ys) fys
-- --   interleave-finiteʳ (∹ xs) {ys = ys} g (suc n , fxs) fys = fin-suc (interleave-finiteˡ (xs .tail) g fys (n , fxs))

-- --   interleave-finiteˡ : {xs : Covec A ∞} (ys : Covec B ∞)
-- --                        (f : A → C) → {g : B → C}
-- --                      → Finite (length xs) → Finite (length ys) → Finite (length (interleaving f g xs ys))
-- --   interleave-finiteˡ {xs = []} ys g fxs fys = subst Finite (map-length _ ys) fys
-- --   interleave-finiteˡ {xs = ∹ xs} ys g (suc n , fxs) fys = fin-suc (interleave-finiteʳ ys g fys (n , fxs))

-- -- _|⊎|_ : 𝒩 A → 𝒩 B → 𝒩 (A ⊎ B)
-- -- support (xs |⊎| ys) = interleaving inl inr (support xs) (support ys)
-- -- cover (xs |⊎| ys) (inl x) = interleave-coverˡ {xs = support xs} (support ys) inl (cover xs x)
-- -- cover (xs |⊎| ys) (inr y) = interleave-coverʳ (support xs) inr (cover ys y)
-- -- \end{code}
-- -- %<*convolve>
-- -- \begin{code}
-- -- uncons-⁺ : Covec ((A × B) ⁺) i → ((A × B) ⋆) × Thunk (Covec ((A × B) ⁺)) i
-- -- uncons-⁺ [] .fst = []
-- -- uncons-⁺ [] .snd .force = []
-- -- uncons-⁺ (∹ xs) .fst = ∹ xs .head
-- -- uncons-⁺ (∹ xs) .snd .force = xs .tail

-- -- convolveʳ  : A → B
-- --            → Thunk (λ i → Covec ((A × B) ⁺) i → Covec ((A × B) ⁺) i) j
-- --            → ((A × B) ⋆ × Thunk (Covec ((A × B) ⁺)) j)
-- --            → Covec⁺ ((A × B) ⁺) j
-- -- convolveʳ x y k zs .head .head .fst = x
-- -- convolveʳ x y k zs .head .head .snd = y
-- -- convolveʳ x y k zs .head .tail = zs .fst
-- -- convolveʳ x y k zs .tail = k .force (zs .snd .force)

-- -- convolveʳ-fold : A → Covec B i → Covec ((A × B) ⁺) i → Covec ((A × B) ⁺) i
-- -- convolveʳ-fold  x ys zs = foldr (λ i → Covec ((_ × _) ⁺ ) i → Covec ((_ × _) ⁺) i)
-- --                                 (λ y ks zs → ∹ convolveʳ x y ks (uncons-⁺ zs))
-- --                                 id ys zs

-- -- convolveˡ : A → Covec⁺ B i → Thunk (Covec ((A × B) ⁺)) i → Covec⁺ ((A × B) ⁺) i
-- -- convolveˡ x ys zs .head .head .fst = x
-- -- convolveˡ x ys zs .head .head .snd = ys .head
-- -- convolveˡ x ys zs .head .tail = []
-- -- convolveˡ x ys zs .tail = convolveʳ-fold x (tail ys) (force zs)

-- -- convolve : Covec A i → Covec B i → Covec ((A × B) ⁺) i
-- -- convolve xs [] = []
-- -- convolve xs (∹ ys) =
-- --   foldr (Covec ((_ × _) ⁺)) (λ x zs → ∹ convolveˡ x ys zs) [] xs

-- -- cantor : Covec A i → Covec B i → Covec (A × B) i
-- -- cantor xs ys = concat (convolve xs ys)
-- -- \end{code}
-- -- %</convolve>
-- -- \begin{code}
-- -- infixr 5 _∈²_
-- -- _∈²_ : {A : Type a} (x : A) (xs : Covec (A ⁺) ∞) → Type a
-- -- x ∈² xs = ◇ (x Kleene.∈⁺_) xs

-- -- shift-cover : ∀ {x : A} (ys : Covec B ∞) {z} (zs : Covec ((A × B) ⁺) ∞)
-- --             → z ∈² zs
-- --             → z ∈² convolveʳ-fold x ys zs
-- -- shift-cover [] _ z∈zs = z∈zs
-- -- shift-cover (∹ ys) (∹ zs) (zero  , x∈xs) = (zero , Kleene.Exists.push (_≡ _) x∈xs)
-- -- shift-cover {x = x} (∹ ys) (∹ zs) (suc n , x∈xs) = Exists.push (Kleene._∈⁺_ _) (shift-cover (ys .tail) (zs .tail) (n , x∈xs))

-- -- convolveʳ-cover : ∀ {xᵢ : A} {yᵢ : B} (ys : Covec B ∞) (y∈ys : yᵢ ∈ ys) {zs : Covec ((A × B) ⁺) ∞}
-- --                   → (xᵢ , yᵢ) ∈² convolveʳ-fold xᵢ ys zs
-- -- convolveʳ-cover (∹ ys) (zero  , y∈ys) = (zero , subst (λ yᵢ →  (_ , yᵢ) Kleene.∈⁺ _) y∈ys (f0 , refl))
-- -- convolveʳ-cover (∹ ys) (suc n , y∈ys) = Exists.push (Kleene._∈⁺_ _) (convolveʳ-cover (ys .tail) (n , y∈ys))

-- -- convolveˡ-cover : ∀ {xᵢ : A} {yᵢ : B} (ys : Covec⁺ B ∞) (y∈ys : yᵢ ∈ ∹ ys)
-- --                 → {zs : Thunk (Covec ((A × B) ⁺)) ∞}
-- --                 → (xᵢ , yᵢ) ∈² ∹ (convolveˡ xᵢ ys  zs)
-- -- convolveˡ-cover ys (zero  , y∈ys) = (zero ,  subst (λ yᵢ → (_ , yᵢ) Kleene.∈⁺ _) y∈ys (f0 , refl))
-- -- convolveˡ-cover ys (suc i , y∈ys) = Exists.push (Kleene._∈⁺_ _) (convolveʳ-cover (ys .tail) (i , y∈ys))

-- -- convolve-cover : {xᵢ : A} (xs : Covec A ∞)
-- --                → {yᵢ : B} (ys : Covec B ∞)
-- --                → xᵢ ∈ xs → yᵢ ∈ ys
-- --                → (xᵢ , yᵢ) ∈² convolve xs ys
-- -- convolve-cover (∹ xs) (∹ ys) (zero  , x∈xs) y∈ys = subst (λ xᵢ → (xᵢ , _) ∈² (convolve (∹ xs) (∹ ys))) x∈xs (convolveˡ-cover ys y∈ys)
-- -- convolve-cover (∹ xs) (∹ ys) (suc n , x∈xs) y∈ys =
-- --   Exists.push (Kleene._∈⁺_ _) (shift-cover (ys .tail) _ (convolve-cover (xs .tail) (∹ ys) (n , x∈xs) y∈ys))

-- -- cantor-cover : {xᵢ : A} (xs : Covec A ∞)
-- --              → {yᵢ : B} (ys : Covec B ∞)
-- --              → xᵢ ∈ xs → yᵢ ∈ ys
-- --              → (xᵢ , yᵢ) ∈ cantor xs ys
-- -- cantor-cover xs ys x∈xs y∈ys = ◇-concat (_≡ _) _ (convolve-cover xs ys x∈xs y∈ys)

-- -- _|×|_ : 𝒩 A → 𝒩 B → 𝒩 (A × B)
-- -- (xs |×| ys) .support = cantor (xs .support) (ys .support)
-- -- (xs |×| ys) .cover (x , y) = cantor-cover (xs .support) (ys .support) (xs .cover x) (ys .cover y)

-- -- open import Data.List.Kleene

-- -- mutual
-- --   star-support : Covec A i → Covec⁺ (A ⋆) i
-- --   star-support xs .head = []
-- --   star-support xs .tail = map ∹_ (plus-support xs)

-- --   plus-support : Covec A i → Covec (A ⁺) i
-- --   plus-support xs = map (uncurry _&_) (cantor xs (∹ star-support xs))

-- -- mutual
-- --   star-cover : (sup : Covec A ∞) → (∀ (x : A) → x ∈ sup) → ∀ xs → xs ∈ ∹ star-support sup
-- --   star-cover sup fn [] = zero , refl
-- --   star-cover sup fn (∹ xs) = push (cong-∈ ∹_ _ (plus-cover sup fn xs))

-- --   plus-cover : (sup : Covec A ∞) → (∀ (x : A) → x ∈ sup) → ∀ xs → xs ∈ plus-support sup
-- --   plus-cover sup fn (x & xs) = cong-∈ (uncurry _&_) _ (cantor-cover sup (∹ star-support sup) (fn x) (star-cover sup fn xs))
-- -- \end{code}
-- -- %<*star-plus>
-- -- \begin{code}
-- -- star : 𝒩 A → 𝒩 (A ⋆)
-- -- plus : 𝒩 A → 𝒩 (A ⁺)
-- -- \end{code}
-- -- %</star-plus>
-- -- \begin{code}
-- -- star xs .support = ∹ star-support (xs .support)
-- -- star xs .cover   = star-cover (xs .support) (xs .cover)

-- -- plus xs .support = plus-support (xs .support)
-- -- plus xs .cover   = plus-cover (xs .support) (xs .cover)

-- -- open import Cardinality.Finite using (ℰ; #; ℰ⇒Fin≃)
-- -- open import Cardinality.Finite.Search using (∀?)
-- -- \end{code}
-- -- %<*from-finite>
-- -- \begin{code}
-- -- ℰ⇒𝒩 : ℰ A → 𝒩 A
-- -- ℰ⇒𝒩 xs .support = ListToCovec (xs .fst)
-- -- ℰ⇒𝒩 xs .cover x = ◇List⇒◇Covec (_≡ x) (xs .fst) (xs .snd x)
-- -- \end{code}
-- -- %</from-finite>
-- -- \begin{code}
-- -- open import Data.Vec.Iterated hiding (tabulate)
-- -- import Data.Unit.UniversePolymorphic as Poly

-- -- 𝒩Unit : ∀ {ℓ} → 𝒩 (Poly.⊤ {ℓ})
-- -- support 𝒩Unit = ∹ Poly.tt & []
-- -- cover   𝒩Unit _ = zero , refl

-- -- 𝒩Lift : ∀ {a b} {A : Type a} → 𝒩 A → 𝒩 (Lift b A)
-- -- support (𝒩Lift xs) = Codata.Covec.map lift (support xs)
-- -- cover   (𝒩Lift xs) (lift x) = cong-∈ lift (support xs) (cover xs x)

-- -- 𝒩Vec : ∀ {n} → 𝒩 A → 𝒩 (Vec A n)
-- -- 𝒩Vec {n = zero}  xs = 𝒩Unit
-- -- 𝒩Vec {n = suc n} xs = xs |×| 𝒩Vec xs

-- -- open import Path.Reasoning
-- -- \end{code}
-- -- %<*fun-sig>
-- -- \begin{code}
-- -- _|→|_ : {A B : Type₀} → ℰ A → 𝒩 B → 𝒩 (A → B)
-- -- \end{code}
-- -- %</fun-sig>
-- -- \begin{code}
-- -- _|→|_ {A = A} {B = B} xs ys = subst 𝒩 Vec⇔→ (𝒩Vec ys)
-- --   where
-- --   Vec⇔→ : Vec B (# xs) ≡ (A → B)
-- --   Vec⇔→ =
-- --     Vec B (# xs)      ≡⟨ isoToPath Vec⇔Fin→ ⟩
-- --     (Fin (# xs) → B)  ≡⟨ cong (λ a → a → B) (ua (ℰ⇒Fin≃ xs)) ⟩
-- --     (A → B) ∎

-- -- instance
-- --   lst-prod : ⦃ lhs : 𝒩 A ⦄ ⦃ rhs : 𝒩 B ⦄ → 𝒩 (A × B)
-- --   lst-prod ⦃ lhs ⦄ ⦃ rhs ⦄ = lhs |×| rhs

-- -- instance
-- --   lst-sum : ⦃ lhs : 𝒩 A ⦄ ⦃ rhs : 𝒩 B ⦄ → 𝒩 (A ⊎ B)
-- --   lst-sum ⦃ lhs ⦄ ⦃ rhs ⦄ = lhs |⊎| rhs

-- -- instance
-- --   lst-fun : {A B : Type₀} ⦃ lhs : ℰ A ⦄ ⦃ rhs : 𝒩 B ⦄ → 𝒩 (A → B)
-- --   lst-fun ⦃ lhs ⦄ ⦃ rhs ⦄ = lhs |→| rhs

-- -- instance
-- --   lst-str : ⦃ _ : 𝒩 A ⦄ → 𝒩 (A ⋆)
-- --   lst-str ⦃ na ⦄ = star na

-- -- instance
-- --   lst-pls : ⦃ _ : 𝒩 A ⦄ → 𝒩 (A ⁺)
-- --   lst-pls ⦃ na ⦄ = plus na

-- -- 𝒩⟨Cofin⟩ : ∀ {n} → 𝒩 (Cofin n)
-- -- 𝒩⟨Cofin⟩ .support = tabulate _ id
-- -- 𝒩⟨Cofin⟩ .cover   = fin∈tabulate id

-- -- 𝒩⟨ℕ⟩ : 𝒩 ℕ
-- -- 𝒩⟨ℕ⟩ = subst 𝒩 (isoToPath Cofin∞⇔ℕ) 𝒩⟨Cofin⟩

-- -- instance
-- --   lst-nat : 𝒩 ℕ
-- --   lst-nat = 𝒩⟨ℕ⟩

-- -- instance
-- --   lst-cofin : ∀ {n} → 𝒩 (Cofin n)
-- --   lst-cofin = 𝒩⟨Cofin⟩

-- -- instance
-- --   lst-bool : 𝒩 Bool
-- --   lst-bool = ℰ⇒𝒩 Cardinality.Finite.ℰ⟨Bool⟩

-- -- data Exhausted : Type₀ where
-- -- data UpTo (n : ℕ) : Type₀ where
-- -- module _ {a} {A : Type a} {p} {P : A → Type p} where
-- --   Found : ∀ {xs} → Search.Found P xs → Type₀
-- --   Found (Search.none x) = Exhausted
-- --   Found (Search.one x) = ⊤
-- --   Found (Search.upTo n x) = UpTo n

-- --   search : ℕ → (na : 𝒩 A) → (P? : ∀ x → Dec (P x)) → Search.Found P (na .support)
-- --   search n ka P? = Search.search P? n (ka .support)

-- --   found-witness : ∀ {xs} → (s : Search.Found P xs) → Found s → Σ A P
-- --   found-witness (Search.one (i , x)) p = (_ ! i , x)

-- --   ⌈_⌉∃! : ∀ n → ⦃ na : 𝒩 A ⦄ → (P? : ∀ x → Dec (P x)) → ⦃ _ : Found (search n na P?) ⦄ → Σ A P
-- --   ⌈ n ⌉∃! ⦃ na ⦄ P? ⦃ p ⦄ = found-witness _ p

-- -- open import Data.Nat using (_+_; _*_) renaming (discreteℕ to _≟_)
-- -- open import Data.Bool.Properties renaming (discreteBool to _B≟_)
-- -- open import Relation.Nullary.Decidable

-- -- force′ : ℕ → ℕ
-- -- force′ zero = zero
-- -- force′ (suc n) = suc (force′ n)

-- -- force″ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ
-- -- force″ (x , y , z) = force′ x , force′ y , force′ z

-- -- pyth : (ℕ × ℕ × ℕ)
-- -- pyth = force″ (fst (⌈ 2000 ⌉∃!
-- --   λ { (x , y , z) →
-- --             not (x ≟ 0 || y ≟ 0 || z ≟ 0) && (((x * x) + (y * y)) ≟ (z * z))
-- --             }))
-- -- \end{code}
