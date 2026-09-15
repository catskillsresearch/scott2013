{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Random variables in the graph model (PROGIC 2013, §4–5)
--
-- Definition 4.1, Theorem 4.2, and the fair-coin oracle of §5,
-- with Cantor space as the sample space.
------------------------------------------------------------------------

module Scott2013.Stochastic where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc) renaming (Nat to ℕ)
open import Agda.Builtin.Unit using (tt)

open import Scott2013.Prelude
open import Scott2013.GraphModel.Basic
open import Scott2013.GraphModel.Application
open import Scott2013.GraphModel.Combinators
open import Scott2013.Probability

------------------------------------------------------------------------
-- Definition 4.1: a random variable is a measurable map Ω → 𝒫(ℕ)
------------------------------------------------------------------------

record RandomVar : Set₁ where
  constructor rv-mk
  field
    rv            : Ω → 𝒫ℕ
    is-measurable : ∀ (n : ℕ) → Measurable (λ ω → rv ω n)

open RandomVar public

------------------------------------------------------------------------
-- Pointwise application (Section 4)
------------------------------------------------------------------------

_·ᵣ_ : RandomVar → RandomVar → (Ω → 𝒫ℕ)
(𝕏 ·ᵣ 𝕐) ω = rv 𝕏 ω · rv 𝕐 ω

-- Finite intersection: set(n) ⊆ 𝕐(ω) is measurable because set(n) is finite.
all-measurable : (𝕐 : RandomVar) (ks : List ℕ) →
                 Measurable (λ ω → All (rv 𝕐 ω) ks)
all-measurable 𝕐 []       = meas-full
all-measurable 𝕐 (k ∷ ks) = meas-inter (is-measurable 𝕐 k) (all-measurable 𝕐 ks)

finite-subset-measurable : ∀ (𝕐 : RandomVar) (n : ℕ) →
                           Measurable (λ ω → n ∈* rv 𝕐 ω)
finite-subset-measurable 𝕐 n = all-measurable 𝕐 (members n)

------------------------------------------------------------------------
-- Theorem 4.2: pointwise application of random variables is measurable
--
-- m ∈ (𝕏(ω) · 𝕐(ω))  iff  ∃ n.  set(n) ⊆ 𝕐(ω)  and  (n, m) ∈ 𝕏(ω)
--   1. set(n) ⊆ 𝕐(ω) is a finite intersection of measurable events
--   2. (n, m) ∈ 𝕏(ω) is measurable by 𝕏
--   3. the conjunction is measurable
--   4. ∃ n is a countable union
------------------------------------------------------------------------

thm-4-2 : ∀ (𝕏 𝕐 : RandomVar) (m : ℕ) →
          Measurable (λ ω → (𝕏 ·ᵣ 𝕐) ω m)
thm-4-2 𝕏 𝕐 m =
  meas-union λ n →
    meas-inter (finite-subset-measurable 𝕐 n)
               (is-measurable 𝕏 (pair n m))

apply-RV : RandomVar → RandomVar → RandomVar
apply-RV 𝕏 𝕐 = record
  { rv            = 𝕏 ·ᵣ 𝕐
  ; is-measurable = thm-4-2 𝕏 𝕐
  }

------------------------------------------------------------------------
-- Section 5: fair-coin oracle 𝕋
--
-- 𝕋(ω)({n}) ∈ {{0},{1}} according to the n-th bit of ω.
-- Encoding: 𝕋(ω) contains the pair (⟨n⟩, b) where b = bit(ω n)
-- and ⟨n⟩ = (0, n) codes the singleton {n}. Then
--   𝕋(ω) · {n} = { bit(ω n) }.
------------------------------------------------------------------------

coin-pred : Ω → 𝒫ℕ
coin-pred ω c =
  Σ ℕ (λ n →
    (ω n ≡ true  × c ≡ pair (singleton-seq n) zero) ⊎
    (ω n ≡ false × c ≡ pair (singleton-seq n) (suc zero)))

coin-measurable : ∀ c → Measurable (λ ω → coin-pred ω c)
coin-measurable c =
  meas-union λ n →
    meas-⊎ (meas-inter (meas-coord n true)  (meas-const-≡ c (pair (singleton-seq n) zero)))
           (meas-inter (meas-coord n false) (meas-const-≡ c (pair (singleton-seq n) (suc zero))))

𝕋 : RandomVar
𝕋 = record
  { rv            = coin-pred
  ; is-measurable = coin-measurable
  }

-- The n-th coordinate of 𝕋 is exactly the n-th bit of the sample.
coin-true : ∀ ω n → ω n ≡ true → coin-pred ω (pair (singleton-seq n) zero)
coin-true ω n eq = n , inj₁ (eq , refl)

coin-false : ∀ ω n → ω n ≡ false → coin-pred ω (pair (singleton-seq n) (suc zero))
coin-false ω n eq = n , inj₂ (eq , refl)

-- 𝕋({n}) = {bit(ω n)}: the n-th coin is 0 exactly when ω n is true.
coin-apply-fwd : ∀ ω n → ω n ≡ true → (coin-pred ω · singleton n) zero
coin-apply-fwd ω n eq =
  singleton-seq n
  , subst (All (singleton n)) (sym (members-singleton n)) (refl , tt)
  , coin-true ω n eq

coin-apply-bwd : ∀ ω n → (coin-pred ω · singleton n) zero → ω n ≡ true
coin-apply-bwd ω n (k , k∈ , c) with c
... | n′ , inj₁ (eq , peq) =
  subst (λ n″ → ω n″ ≡ true) n′≡n eq
  where
    inj = pair-injective k zero (singleton-seq n′) zero peq
    k≡⟨n′⟩ = proj₁ inj
    n′∈k : n′ ∈-set k
    n′∈k = subst (n′ ∈-list_) (sym (trans (cong members k≡⟨n′⟩) (members-singleton n′))) here
    n′≡n : n′ ≡ n
    n′≡n = ∈*-∀ k (singleton n) k∈ n′ n′∈k
... | n′ , inj₂ (_ , peq) =
  ⊥-elim (zero≢suc (proj₂ (pair-injective k zero (singleton-seq n′) (suc zero) peq)))
  where
    zero≢suc : zero ≢ suc zero
    zero≢suc ()

-- The event 0 ∈ 𝕋({n}) is the coordinate cylinder of measure 1/2.
coin-event-cyl : ∀ n ω → (coin-pred ω · singleton n) zero ↔ ⟦cyl⟧ ((n , true) ∷ []) ω
coin-event-cyl n ω =
  (λ p → coin-apply-bwd ω n p , tt) ,
  (λ (eq , _) → coin-apply-fwd ω n eq)

coin-event-half : ∀ n → μ-exp ((n , true) ∷ []) ≡ suc zero
coin-event-half n = coin-half n true

-- Independence of two distinct coins.
coin-indep-event : ∀ n m → n ≢ m →
  μ-exp ((n , true) ∷ (m , true) ∷ []) ≡ suc (suc zero)
coin-indep-event n m _ = coin-indep n m true true

-- 𝕋({n}) ∈ {{0},{1}}: the n-th coin is a singleton bit.
coin-apply-one-fwd : ∀ ω n → ω n ≡ false → (coin-pred ω · singleton n) (suc zero)
coin-apply-one-fwd ω n eq =
  singleton-seq n
  , subst (All (singleton n)) (sym (members-singleton n)) (refl , tt)
  , coin-false ω n eq

coin-true-is-zero : ∀ ω n → ω n ≡ true →
                    ∀ m → (coin-pred ω · singleton n) m → m ≡ zero
coin-true-is-zero ω n ωt m (k , k∈ , c) with c
... | n′ , inj₁ (_ , peq) = proj₂ (pair-injective k m (singleton-seq n′) zero peq)
... | n′ , inj₂ (ωf , peq) =
  ⊥-elim (true≢false (trans (sym ωt) (subst (λ n″ → ω n″ ≡ false) n′≡n ωf)))
  where
    inj = pair-injective k m (singleton-seq n′) (suc zero) peq
    k≡⟨n′⟩ = proj₁ inj
    n′∈k : n′ ∈-set k
    n′∈k = subst (n′ ∈-list_) (sym (trans (cong members k≡⟨n′⟩) (members-singleton n′))) here
    n′≡n : n′ ≡ n
    n′≡n = ∈*-∀ k (singleton n) k∈ n′ n′∈k

coin-false-is-one : ∀ ω n → ω n ≡ false →
                    ∀ m → (coin-pred ω · singleton n) m → m ≡ suc zero
coin-false-is-one ω n ωf m (k , k∈ , c) with c
... | n′ , inj₂ (_ , peq) = proj₂ (pair-injective k m (singleton-seq n′) (suc zero) peq)
... | n′ , inj₁ (ωt , peq) =
  ⊥-elim (true≢false (trans (sym (subst (λ n″ → ω n″ ≡ true) n′≡n ωt)) ωf))
  where
    inj = pair-injective k m (singleton-seq n′) zero peq
    k≡⟨n′⟩ = proj₁ inj
    n′∈k : n′ ∈-set k
    n′∈k = subst (n′ ∈-list_) (sym (trans (cong members k≡⟨n′⟩) (members-singleton n′))) here
    n′≡n : n′ ≡ n
    n′≡n = ∈*-∀ k (singleton n) k∈ n′ n′∈k

-- Threshold language: acceptance contains a fresh k-cylinder with 2^{-k} > 2^{-d}.
AboveThreshold : (Ω → Set) → ℕ → Set
AboveThreshold E d =
  Σ Cyl (λ xs → FreshCyl xs × (μ-exp xs < d) × (∀ ω → ⟦cyl⟧ xs ω → E ω))

-- Coin: P(0 ∈ 𝕋({n})) = 1/2 > 2^{-d} whenever d ≥ 2.
thm-4-5-coin : ∀ n d → suc zero < d →
               AboveThreshold (λ ω → (coin-pred ω · singleton n) zero) d
thm-4-5-coin n d 1<d =
  ((n , true) ∷ [])
  , fresh-one n true
  , 1<d
  , λ ω cyl → coin-apply-fwd ω n (proj₁ cyl)

------------------------------------------------------------------------
-- Sequentializer on random variables; Theorem 4.5
------------------------------------------------------------------------

const-rv-sing : ℕ → RandomVar
const-rv-sing k = record
  { rv            = λ _ → singleton k
  ; is-measurable = λ m → meas-const-≡ m k
  }

const-rv-set : ℕ → RandomVar
const-rv-set q = record
  { rv            = λ _ → setₚ q
  ; is-measurable = λ m →
      meas-const-dec (m ∈-set q) (∈-list-dec m (members q))
  }

run-rv : RandomVar → List ℕ → RandomVar → RandomVar
run-rv A []       Q = Q
run-rv A (n ∷ ns) Q = apply-RV (apply-RV A (const-rv-sing n)) (run-rv A ns Q)

𝕊-rv : RandomVar → ℕ → RandomVar → RandomVar
𝕊-rv A σ Q = run-rv A (members σ) Q

run-rv-fwd : ∀ A xs Q ω m →
  rv (run-rv A xs Q) ω m → run (rv A ω) xs (rv Q ω) m
run-rv-fwd A []       Q ω m p = p
run-rv-fwd A (n ∷ ns) Q ω m (k , k∈ , Fk) =
  k
  , All-mono (members k) (λ m′ p → run-rv-fwd A ns Q ω m′ p) k∈
  , Fk

run-rv-bwd : ∀ A xs Q ω m →
  run (rv A ω) xs (rv Q ω) m → rv (run-rv A xs Q) ω m
run-rv-bwd A []       Q ω m p = p
run-rv-bwd A (n ∷ ns) Q ω m (k , k∈ , Fk) =
  k
  , All-mono (members k) (λ m′ p → run-rv-bwd A ns Q ω m′ p) k∈
  , Fk

-- Theorem 4.5: the acceptance event is measurable, so the threshold
-- language { σ | #{ 0 ∈ 𝕊(A)(σ)(Q) } > δ } is well-defined.
thm-4-5 : ∀ (A Q : RandomVar) (σ : ℕ) →
          Measurable (λ ω → 𝕊-apply (rv A ω) σ (rv Q ω) zero)
thm-4-5 A Q σ =
  meas-resp
    (λ ω → run-rv-fwd A (members σ) Q ω zero
         , run-rv-bwd A (members σ) Q ω zero)
    (is-measurable (𝕊-rv A σ Q) zero)

-- Probabilistic languages are among those σ ∈ Σ* whose acceptance
-- event is measurable (the paper's #{…} > δ, with # a cylinder measure
-- when the event is clopen).
ProbabilisticIn : (Alph : 𝒫ℕ) (L : 𝒫ℕ) (A Q : RandomVar) → Set
ProbabilisticIn Alph L A Q =
  Finite Alph ×
  (∀ σ → L σ → (σ ∈* Alph) × Measurable (λ ω → 𝕊-apply (rv A ω) σ (rv Q ω) zero))

thm-4-5-lang : ∀ Alph L A Q → Finite Alph →
               (∀ σ → L σ → σ ∈* Alph) →
               ProbabilisticIn Alph L A Q
thm-4-5-lang Alph L A Q finAlph L⊆Alph =
  finAlph , λ σ Lσ → L⊆Alph σ Lσ , thm-4-5 A Q σ
