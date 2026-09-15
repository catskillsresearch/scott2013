{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Countably based T₀-spaces and injectivity of 𝒫ℕ
-- (PROGIC 2013, Theorems 3.10–3.12)
------------------------------------------------------------------------

module Scott2013.GraphModel.Topology where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc) renaming (Nat to ℕ)

open import Scott2013.Prelude
open import Scott2013.GraphModel.Basic
open import Scott2013.GraphModel.Application

------------------------------------------------------------------------
-- Countably based T₀-space (Theorem 3.10 hypotheses)
------------------------------------------------------------------------

record CountablyBasedT0 : Set₁ where
  field
    Point : Set
    basis : ℕ → Point → Set
    t0    : ∀ x y → (∀ n → basis n x ↔ basis n y) → x ≡ y

open CountablyBasedT0 public

-- ε(X) = { n | X ∈ U_n }
ε : (T : CountablyBasedT0) → Point T → 𝒫ℕ
ε T x n = basis T n x

-- Scott subbasis on 𝒫ℕ: Q_⟨m⟩ = { X | m ∈ X }
Q-sing : ℕ → 𝒫ℕ → Set
Q-sing m X = X m

-- Scott basis: Q_n = { X | n ∈ X* }
Qₙ : ℕ → 𝒫ℕ → Set
Qₙ n X = n ∈* X

-- Theorem 3.10: ε is injective because T is T₀.
thm-3-10-inj : (T : CountablyBasedT0) (x y : Point T) →
               (∀ n → ε T x n ↔ ε T y n) → x ≡ y
thm-3-10-inj T x y eq = t0 T x y eq

-- Continuity: ε⁻¹(Q_⟨m⟩) = U_m.
thm-3-10-cont : (T : CountablyBasedT0) (x : Point T) (m : ℕ) →
                Q-sing m (ε T x) ↔ basis T m x
thm-3-10-cont T x m = (λ p → p) , (λ p → p)

-- Bicontinuity: ε(U_m) = ε(T) ∩ Q_⟨m⟩.
thm-3-10-open : (T : CountablyBasedT0) (m : ℕ) (x : Point T) →
                basis T m x ↔ Q-sing m (ε T x)
thm-3-10-open T m x = (λ p → p) , (λ p → p)

------------------------------------------------------------------------
-- Definition 3.11 / Theorem 3.12: 𝒫ℕ is injective
--
-- T ⊆ U, Φ : T → 𝒫ℕ continuous. The sets T_n = { X ∈ T | n ∈ Φ(X) }
-- are open in T, hence T_n = T ∩ U_n for opens U_n of U. The canonical
-- extension is Ψ(Y) = { n | Y ∈ U_n }.
------------------------------------------------------------------------

module Injectivity
  (UPoint : Set)
  (T      : UPoint → Set)
  (Φ      : (x : UPoint) → T x → 𝒫ℕ)
  (Uₙ     : ℕ → UPoint → Set)
  (Tₙ=Uₙ  : ∀ n x (tx : T x) → Φ x tx n ↔ Uₙ n x)
  where

  Ψ : UPoint → 𝒫ℕ
  Ψ Y n = Uₙ n Y

  -- Ψ is continuous in the sense that Ψ⁻¹(Q_⟨n⟩) = U_n.
  thm-3-12-cont : ∀ Y n → Q-sing n (Ψ Y) ↔ Uₙ n Y
  thm-3-12-cont Y n = (λ p → p) , (λ p → p)

  -- Ψ extends Φ on T.
  thm-3-12-extends : ∀ x (tx : T x) n → Ψ x n ↔ Φ x tx n
  thm-3-12-extends x tx n =
    (λ Un → proj₂ (Tₙ=Uₙ n x tx) Un) ,
    (λ Φn → proj₁ (Tₙ=Uₙ n x tx) Φn)

-- Restriction of a continuous operator on 𝒫ℕ to a subspace.
restrict : (Ψ : 𝒫ℕ → 𝒫ℕ) (T : 𝒫ℕ → Set) →
           (X : 𝒫ℕ) → T X → 𝒫ℕ
restrict Ψ _ X _ = Ψ X
