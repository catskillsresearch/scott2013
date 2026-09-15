{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Curry combinators, arithmetic operators, ∇, and the sequentializer
-- (PROGIC 2013, Theorems 3.8–3.9 and Definition 4.3)
------------------------------------------------------------------------

module Scott2013.GraphModel.Combinators where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc) renaming (Nat to ℕ)
open import Agda.Builtin.Unit using (⊤; tt)

open import Scott2013.Prelude
open import Scott2013.GraphModel.Basic
open import Scott2013.GraphModel.Application

------------------------------------------------------------------------
-- Identity, from λX. X
------------------------------------------------------------------------

I : 𝒫ℕ
I = lam (λ X → X)

I-correct-fwd : ∀ X m → (I · X) m → X m
I-correct-fwd X m (n , n∈X , inj₁ peq) = ⊥-elim (pair-ne-zero n m peq)
I-correct-fwd X m (n , n∈X , inj₂ (n′ , m′ , peq , m′∈n′)) =
  subst X (sym (proj₂ inj))
    (∈*-∀ n X n∈X m′ (subst (λ k → m′ ∈-set k) (sym (proj₁ inj)) m′∈n′))
  where
    inj = pair-injective n m n′ m′ peq

I-correct-bwd : ∀ X m → X m → (I · X) m
I-correct-bwd X m Xm =
  singleton-seq m , n∈X , inj₂ (singleton-seq m , m , refl , m∈set)
  where
    n∈X : singleton-seq m ∈* X
    n∈X = subst (All X) (sym (members-singleton m)) (Xm , tt)

    m∈set : m ∈-set singleton-seq m
    m∈set = subst (m ∈-list_) (sym (members-singleton m)) here

------------------------------------------------------------------------
-- K = λY.λX. Y  and  S = λZ.λY.λX. Z(X)(Y(X))   (Scott's RE codes)
------------------------------------------------------------------------

K : 𝒫ℕ
K = lam (λ Y → lam (λ _ → Y))

-- K is the binary graph of (Y, X) ↦ Y.
K-Φ : 𝒫ℕ → 𝒫ℕ → 𝒫ℕ
K-Φ Y _ = Y

K-Φ-cont : Continuous₂ K-Φ
K-Φ-cont Y X m = fwd , bwd
  where
    fwd : Y m → Σ ℕ (λ kY → Σ ℕ (λ kX →
            (kY ∈* Y) × (kX ∈* X) × setₚ kY m))
    fwd Ym = singleton-seq m , zero
           , subst (All Y) (sym (members-singleton m)) (Ym , tt)
           , tt
           , subst (m ∈-list_) (sym (members-singleton m)) here

    bwd : Σ ℕ (λ kY → Σ ℕ (λ kX →
            (kY ∈* Y) × (kX ∈* X) × setₚ kY m)) → Y m
    bwd (kY , _ , kY∈ , _ , m∈) = ∈*-∀ kY Y kY∈ m m∈

K-correct-fwd : ∀ Y X m → ((K · Y) · X) m → Y m
K-correct-fwd Y X m p = thm-3-5 K-Φ K-Φ-cont Y X m p

K-correct-bwd : ∀ Y X m → Y m → ((K · Y) · X) m
K-correct-bwd Y X m Ym =
  zero , tt , proj₂ (thm-3-5-outer K-Φ K-Φ-cont Y (pair zero m))
    (inj₂ (zero , m , refl , Ym))

S : 𝒫ℕ
S = lam (λ Z → lam (λ Y → lam (λ X → (Z · X) · (Y · X))))

s-op : 𝒫ℕ → 𝒫ℕ → 𝒫ℕ → 𝒫ℕ
s-op Z Y X = (Z · X) · (Y · X)

S-graph : ∀ k → S k ↔ lam (λ Z → lam (λ Y → lam (λ X → s-op Z Y X))) k
S-graph k = (λ p → p) , (λ p → p)

------------------------------------------------------------------------
-- Definition 3.9: arithmetic combinators as operators, then as graphs
------------------------------------------------------------------------

Succ-op : 𝒫ℕ → 𝒫ℕ
Succ-op X m = Σ ℕ (λ n → X n × (m ≡ suc n))

Pred-op : 𝒫ℕ → 𝒫ℕ
Pred-op X m = X (suc m)

Test-op : 𝒫ℕ → 𝒫ℕ → 𝒫ℕ → 𝒫ℕ
Test-op Z X Y n = (X n × Z zero) ⊎ (Y n × Σ ℕ (λ k → Z (suc k)))

Succ : 𝒫ℕ
Succ = lam Succ-op

Pred : 𝒫ℕ
Pred = lam Pred-op

Test : 𝒫ℕ
Test = lam (λ Z → lam (λ X → lam (λ Y → Test-op Z X Y)))

singleton : ℕ → 𝒫ℕ
singleton n m = m ≡ n

Test-op-zero : ∀ X Y n → Test-op (singleton zero) X Y n → X n
Test-op-zero X Y n (inj₁ (Xn , _)) = Xn
Test-op-zero X Y n (inj₂ (_ , k , ()))

-- Semantic universal RE interpreter (Definition 3.9, equations (i)–(vi)).
re-interp : 𝒫ℕ → ℕ → 𝒫ℕ
re-interp R zero = K
re-interp R (suc zero) = S
re-interp R (suc (suc zero)) = Test
re-interp R (suc (suc (suc zero))) = Succ
re-interp R (suc (suc (suc (suc zero)))) = Pred
re-interp R (suc (suc (suc (suc (suc k))))) =
  (R · singleton (proj₁ (unpair (suc k)))) ·
  (R · singleton (proj₂ (unpair (suc k))))

re-apply : 𝒫ℕ → 𝒫ℕ → 𝒫ℕ
re-apply R X m = Σ ℕ (λ n → X n × re-interp R n m)

re-interp-0 : ∀ R x → re-interp R zero x ↔ K x
re-interp-0 R x = (λ p → p) , (λ p → p)

re-interp-1 : ∀ R x → re-interp R (suc zero) x ↔ S x
re-interp-1 R x = (λ p → p) , (λ p → p)

re-interp-2 : ∀ R x → re-interp R (suc (suc zero)) x ↔ Test x
re-interp-2 R x = (λ p → p) , (λ p → p)

re-interp-3 : ∀ R x → re-interp R (suc (suc (suc zero))) x ↔ Succ x
re-interp-3 R x = (λ p → p) , (λ p → p)

re-interp-4 : ∀ R x → re-interp R (suc (suc (suc (suc zero)))) x ↔ Pred x
re-interp-4 R x = (λ p → p) , (λ p → p)

-- (vi) RE({4+(n,m)}) = RE({n})(RE({m})), pointwise on 𝒫ℕ.
re-interp-app : ∀ R n m x →
  re-interp R (suc (suc (suc (suc (pair n m))))) x ↔
  ((R · singleton n) · (R · singleton m)) x
re-interp-app R n m x with pair-is-suc n m
... | k , peq =
  subst (λ s → re-interp R (suc (suc (suc (suc s)))) x ↔
               ((R · singleton n) · (R · singleton m)) x)
        (sym peq)
        inner
  where
    u-eq : unpair (suc k) ≡ (n , m)
    u-eq = trans (cong unpair (sym peq)) (unpair-pair n m)

    inner : re-interp R (suc (suc (suc (suc (suc k))))) x ↔
            ((R · singleton n) · (R · singleton m)) x
    inner =
      subst (λ nm → re-interp R (suc (suc (suc (suc (suc k))))) x ↔
                    ((R · singleton (proj₁ nm)) · (R · singleton (proj₂ nm))) x)
            u-eq
            ((λ p → p) , (λ p → p))

------------------------------------------------------------------------
-- Theorem 3.8: ∇ = λX. Φ(X(X)),  P = ∇(∇)
------------------------------------------------------------------------

∇ : (𝒫ℕ → 𝒫ℕ) → 𝒫ℕ
∇ Φ = lam (λ X → Φ (X · X))

lfp : (𝒫ℕ → 𝒫ℕ) → 𝒫ℕ
lfp Φ = ∇ Φ · ∇ Φ

-- Theorem 3.8: P = ∇(∇) is a fixed point of Φ (one inclusion from
-- unfolding λ), and it is least among fixed points.
∇-unfold : ∀ (Φ : 𝒫ℕ → 𝒫ℕ) n m →
           ∇ Φ (pair n m) → (pair n m ≡ zero) ⊎ Φ (setₚ n · setₚ n) m
∇-unfold Φ n m (inj₁ peq) = inj₁ peq
∇-unfold Φ n m (inj₂ (n′ , m′ , peq , Φn)) =
  inj₂ (subst (λ m″ → Φ (setₚ n · setₚ n) m″) (sym (proj₂ inj))
    (subst (λ n″ → Φ (setₚ n″ · setₚ n″) m′) (sym (proj₁ inj)) Φn))
  where
    inj = pair-injective n m n′ m′ peq

thm-3-8-fp : ∀ (Φ : 𝒫ℕ → 𝒫ℕ) → Continuous₁ Φ →
             ∀ m → lfp Φ m → Φ (lfp Φ) m
thm-3-8-fp Φ Φc m (n , n∈∇ , ∇nm) with ∇-unfold Φ n m ∇nm
... | inj₁ peq = ⊥-elim (pair-ne-zero n m peq)
... | inj₂ Φnn with proj₁ (Φc (setₚ n · setₚ n) m) Φnn
... | k , k∈XX , Φk =
  proj₂ (Φc (lfp Φ) m)
    (k , All-mono (members k) (λ m′ p → n⊆∇-app {m′} p) k∈XX , Φk)
  where
    n⊆∇ : setₚ n ⊆ ∇ Φ
    n⊆∇ {j} q = ∈*-∀ n (∇ Φ) n∈∇ j q

    n⊆∇-app : (setₚ n · setₚ n) ⊆ lfp Φ
    n⊆∇-app {m′} (j , j∈n , pair∈n) =
      j , ∈*-mono j n⊆∇ j∈n , n⊆∇ pair∈n

-- Least: if Φ(Q)=Q then P ⊆ Q, by Scott's induction on sequence numbers.
thm-3-8-least : ∀ (Φ : 𝒫ℕ → 𝒫ℕ) (Q : 𝒫ℕ) → Continuous₁ Φ →
                (∀ m → Φ Q m → Q m) → (∀ m → Q m → Φ Q m) →
                ∀ m → lfp Φ m → Q m
thm-3-8-least Φ Q Φc ΦQ⊆Q Q⊆ΦQ m (n , n∈∇ , ∇nm) with ∇-unfold Φ n m ∇nm
... | inj₁ peq = ⊥-elim (pair-ne-zero n m peq)
... | inj₂ Φnn =
  ΦQ⊆Q m (cont₁-mono Φ Φc {X = setₚ n · setₚ n} {Y = Q}
    (ind n (<-wf n) (λ {j} q → ∈*-∀ n (∇ Φ) n∈∇ j q)) Φnn)
  where
    ind : ∀ k → Acc k → setₚ k ⊆ ∇ Φ → (setₚ k · setₚ k) ⊆ Q
    ind zero        _        _  (j , j∈0 , pair∈0) =
      ⊥-elim (no-members-zero _ pair∈0)
      where
        no-members-zero : ∀ x → x ∈-set zero → ⊥
        no-members-zero _ ()
    ind (suc k) (acc rec) sk⊆∇ {q} (j , j∈k , pair∈) =
      let pair< = members-bounded (suc k) (pair j q) pair∈
          j<    = <≤-trans (pair-first-< j q) (<⇒≤ pair<)
          sn⊆∇ : setₚ j ⊆ ∇ Φ
          sn⊆∇ {x} x∈j = sk⊆∇ (∈*-∀ j (setₚ (suc k)) j∈k x x∈j)
          ih = ind j (rec j j<) sn⊆∇
      in  ΦQ⊆Q q (cont₁-mono Φ Φc ih (∇-to-Φ j q (sk⊆∇ pair∈)))
      where
        ∇-to-Φ : ∀ j q → ∇ Φ (pair j q) → Φ (setₚ j · setₚ j) q
        ∇-to-Φ j q v with ∇-unfold Φ j q v
        ... | inj₁ peq = ⊥-elim (pair-ne-zero j q peq)
        ... | inj₂ p   = p

-- Universal RE as the least fixed point of the semantic interpreter graph.
RE-op : 𝒫ℕ → 𝒫ℕ
RE-op R = lam (re-apply R)

RE : 𝒫ℕ
RE = lfp RE-op

------------------------------------------------------------------------
-- Definition 4.3: sequentializer 𝕊
-- 𝕊(F)(⟨n₀,…,nₖ⟩) = F({nₖ}) ∘ ⋯ ∘ F({n₀})
--
-- `members` decodes a sequence number as [nₖ, …, n₀], so folding
-- application from the left applies F({n₀}) first.
------------------------------------------------------------------------

_∘ₒ_ : 𝒫ℕ → 𝒫ℕ → 𝒫ℕ
F ∘ₒ G = lam (λ X → F · (G · X))

run : 𝒫ℕ → List ℕ → 𝒫ℕ → 𝒫ℕ
run F []       Q = Q
run F (n ∷ ns) Q = (F · singleton n) · run F ns Q

-- Semantic action of the sequentializer on a sequence number.
𝕊-apply : 𝒫ℕ → ℕ → 𝒫ℕ → 𝒫ℕ
𝕊-apply F σ Q = run F (members σ) Q

-- Definition 4.3 recurrences (semantic sequentializer).
𝕊-empty : ∀ F Q m → 𝕊-apply F zero Q m ↔ Q m
𝕊-empty F Q m = (λ p → p) , (λ p → p)

𝕊-cons : ∀ F n m Q k →
  𝕊-apply F (pair n m) Q k ↔ ((F · singleton m) · 𝕊-apply F n Q) k
𝕊-cons F n m Q k =
  subst (λ xs → run F xs Q k → ((F · singleton m) · 𝕊-apply F n Q) k)
        (sym (members-pair n m))
        (λ p → p)
  , subst (λ xs → ((F · singleton m) · 𝕊-apply F n Q) k → run F xs Q k)
          (sym (members-pair n m))
          (λ p → p)

-- Graph of the sequentializer: 𝕊(F)(S)(Q) collects 𝕊-apply F σ Q
-- over sequence numbers σ ∈ S (typically a singleton {σ}).
𝕊-on : 𝒫ℕ → 𝒫ℕ → 𝒫ℕ → 𝒫ℕ
𝕊-on F S Q m = Σ ℕ (λ σ → S σ × 𝕊-apply F σ Q m)

𝕊 : 𝒫ℕ
𝕊 = lam (λ F → lam (λ S → lam (𝕊-on F S)))

------------------------------------------------------------------------
-- Theorem 4.4: regular languages in the model
------------------------------------------------------------------------

-- Finite alphabet `Alph`, automaton graph coded by `a`, state set coded by `q`.
RegularIn : (Alph : 𝒫ℕ) (L : 𝒫ℕ) → Set
RegularIn Alph L =
  Finite Alph ×
  Σ ℕ (λ a → Σ ℕ (λ q →
    ∀ σ → L σ ↔ ((σ ∈* Alph) × 𝕊-apply (setₚ a) σ (setₚ q) zero)))

-- The empty language is regular (empty automaton).
regular-none : ∀ (Alph : 𝒫ℕ) → Finite Alph → RegularIn Alph (λ _ → ⊥)
regular-none Alph finAlph =
  finAlph
  , zero
  , zero
  , λ σ → (λ ()) , (λ r → empty-run (members σ) (proj₂ r))
  where
    empty-run : ∀ xs → run (setₚ zero) xs (setₚ zero) zero → ⊥
    empty-run [] ()
    empty-run (x ∷ xs) (n , n∈ , k , k∈ , ())
