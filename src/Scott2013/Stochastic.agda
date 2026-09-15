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

open import Scott2013.Prelude
open import Scott2013.GraphModel.Basic
open import Scott2013.GraphModel.Application
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
