{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Enumeration-operator application and λ-abstraction
-- (PROGIC 2013, Definitions 2.1 and 3.3; Theorems 3.1–3.2)
------------------------------------------------------------------------

module Scott2013.GraphModel.Application where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc) renaming (Nat to ℕ)
open import Agda.Builtin.Unit using (⊤; tt)

open import Scott2013.Prelude
open import Scott2013.GraphModel.Basic

------------------------------------------------------------------------
-- Definition 2.1: F(X) = { m | ∃ n ∈ X*. (n, m) ∈ F }
------------------------------------------------------------------------

infixl 7 _·_

_·_ : 𝒫ℕ → 𝒫ℕ → 𝒫ℕ
(F · X) m = Σ ℕ (λ n → (n ∈* X) × F (pair n m))

------------------------------------------------------------------------
-- Scott continuity (Definition 2.2)
------------------------------------------------------------------------

Continuous₁ : (𝒫ℕ → 𝒫ℕ) → Set₁
Continuous₁ Φ = ∀ (X : 𝒫ℕ) (m : ℕ) →
  Φ X m ↔ Σ ℕ (λ k → (k ∈* X) × Φ (setₚ k) m)

Continuous₂ : (𝒫ℕ → 𝒫ℕ → 𝒫ℕ) → Set₁
Continuous₂ Φ = ∀ (F X : 𝒫ℕ) (m : ℕ) →
  Φ F X m ↔
    Σ ℕ (λ kF → Σ ℕ (λ kX →
      (kF ∈* F) × (kX ∈* X) × Φ (setₚ kF) (setₚ kX) m))

------------------------------------------------------------------------
-- Theorem 3.1: application is continuous in both arguments
------------------------------------------------------------------------

thm-3-1-fwd : ∀ (F X : 𝒫ℕ) (m : ℕ) →
            (F · X) m →
            Σ ℕ (λ kF → Σ ℕ (λ kX →
              (kF ∈* F) × (kX ∈* X) × (setₚ kF · setₚ kX) m))
thm-3-1-fwd F X m (n , (nStar , Fn)) =
  singleton-seq (pair n m) , n , kF∈F , nStar , (n , ∈*-refl n , pair∈kF)
  where
    kF∈F : singleton-seq (pair n m) ∈* F
    kF∈F = subst (All F) (sym (members-singleton (pair n m))) (Fn , tt)

    pair∈kF : pair n m ∈-set singleton-seq (pair n m)
    pair∈kF = subst (pair n m ∈-list_) (sym (members-singleton (pair n m))) here

thm-3-1-bwd : ∀ (F X : 𝒫ℕ) (m : ℕ) →
            Σ ℕ (λ kF → Σ ℕ (λ kX →
              (kF ∈* F) × (kX ∈* X) × (setₚ kF · setₚ kX) m)) →
            (F · X) m
thm-3-1-bwd F X m (kF , kX , kF∈F , kX∈X , n , n∈set , pair∈) =
  n , n∈X , All-∀ F (members kF) kF∈F (pair n m) pair∈
  where
    n∈X : n ∈* X
    n∈X = ∀-∈* n X λ j j∈n →
      All-∀ X (members kX) kX∈X j
        (All-∀ (setₚ kX) (members n) n∈set j j∈n)

thm-3-1 : Continuous₂ _·_
thm-3-1 F X m = thm-3-1-fwd F X m , thm-3-1-bwd F X m

------------------------------------------------------------------------
-- Definition 3.3: λX. Φ(X) = {0} ∪ { (n, m) | m ∈ Φ(set(n)) }
------------------------------------------------------------------------

lam : (𝒫ℕ → 𝒫ℕ) → 𝒫ℕ
lam Φ k = (k ≡ zero) ⊎
          Σ ℕ (λ n → Σ ℕ (λ m → (k ≡ pair n m) × Φ (setₚ n) m))

-- Theorem 3.2 (application direction): the graph of a continuous
-- map applies to recover the map.
lam-app-fwd : ∀ (Φ : 𝒫ℕ → 𝒫ℕ) → Continuous₁ Φ →
            ∀ X m → (lam Φ · X) m → Φ X m
lam-app-fwd Φ Φ-cont X m (n , n∈X , inj₁ peq) =
  ⊥-elim (pair-ne-zero n m peq)
lam-app-fwd Φ Φ-cont X m (n , n∈X , inj₂ (n′ , m′ , peq , Φn)) =
  proj₂ (Φ-cont X m) (n′ , n′∈X , subst (Φ (setₚ n′)) (sym (proj₂ inj)) Φn)
  where
    inj = pair-injective n m n′ m′ peq
    n′∈X : n′ ∈* X
    n′∈X = subst (_∈* X) (proj₁ inj) n∈X

lam-app-bwd : ∀ (Φ : 𝒫ℕ → 𝒫ℕ) → Continuous₁ Φ →
            ∀ X m → Φ X m → (lam Φ · X) m
lam-app-bwd Φ Φ-cont X m ΦXm with proj₁ (Φ-cont X m) ΦXm
... | k , k∈X , Φk =
  k , k∈X , inj₂ (k , m , refl , Φk)

-- Theorem 3.2 (maximality): any other graph of Φ is contained in lam Φ.
lam-largest : ∀ (Φ : 𝒫ℕ → 𝒫ℕ) (G : 𝒫ℕ) →
              (∀ X m → (G · X) m ↔ Φ X m) →
              G ⊆ lam Φ
lam-largest Φ G G-app {zero}  Gk = inj₁ refl
lam-largest Φ G G-app {suc k} Gk with unpair-acc-correct (suc k) (<-wf (suc k))
... | inj₁ ()
... | inj₂ eq =
  inj₂ (n , m , sym eq , proj₁ (G-app (setₚ n) m) (n , ∈*-refl n , subst G (sym eq) Gk))
  where
    n = proj₁ (unpair (suc k))
    m = proj₂ (unpair (suc k))
