{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- The recursively enumerable sequentializer (Definition 4.3)
------------------------------------------------------------------------

module Scott2013.GraphModel.Sequentializer where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero) renaming (Nat to ℕ)
open import Agda.Builtin.Unit using (tt)

open import Scott2013.Prelude
open import Scott2013.GraphModel.Basic
open import Scott2013.GraphModel.Application
open import Scott2013.GraphModel.Combinators
import Scott2013.Computability.RE as R

swap-cont₂ : ∀ (Φ : 𝒫ℕ → 𝒫ℕ → 𝒫ℕ) → Continuous₂ Φ →
             Continuous₂ (λ X F → Φ F X)
swap-cont₂ Φ Φc X F m = fwd , bwd
  where
    fwd : Φ F X m →
      Σ ℕ (λ kX → Σ ℕ (λ kF →
        (kX ∈* X) × (kF ∈* F) × Φ (setₚ kF) (setₚ kX) m))
    fwd p with proj₁ (Φc F X m) p
    ... | kF , kX , kF∈ , kX∈ , q =
      kX , kF , kX∈ , kF∈ , q

    bwd : Σ ℕ (λ kX → Σ ℕ (λ kF →
        (kX ∈* X) × (kF ∈* F) × Φ (setₚ kF) (setₚ kX) m)) →
      Φ F X m
    bwd (kX , kF , kX∈ , kF∈ , q) =
      proj₂ (Φc F X m) (kF , kX , kF∈ , kX∈ , q)

cont₂-slice-left : ∀ (Φ : 𝒫ℕ → 𝒫ℕ → 𝒫ℕ) → Continuous₂ Φ →
                   ∀ X → Continuous₁ (λ F → Φ F X)
cont₂-slice-left Φ Φc X =
  cont₂-slice (λ X′ F → Φ F X′) (swap-cont₂ Φ Φc) X

ignore-left-cont₂ : Continuous₂ (λ _ Q → Q)
ignore-left-cont₂ F Q m =
  (λ Qm → zero , singleton-seq m
      , tt
      , subst (All Q) (sym (members-singleton m)) (Qm , tt)
      , subst (m ∈-list_) (sym (members-singleton m)) here)
  , (λ (_ , kQ , _ , kQ∈ , m∈) →
      ∈*-∀ kQ Q kQ∈ m m∈)

symbol-cont₂ : ∀ a → Continuous₂ (λ F _ → F · singleton a)
symbol-cont₂ a F Q m = fwd , bwd
  where
    fwd : (F · singleton a) m →
      Σ ℕ (λ kF → Σ ℕ (λ kQ →
        (kF ∈* F) × (kQ ∈* Q) × (setₚ kF · singleton a) m))
    fwd p with proj₁ (·-left-cont (singleton a) F m) p
    ... | kF , kF∈ , q = kF , zero , kF∈ , tt , q

    bwd : Σ ℕ (λ kF → Σ ℕ (λ kQ →
        (kF ∈* F) × (kQ ∈* Q) × (setₚ kF · singleton a) m)) →
      (F · singleton a) m
    bwd (kF , _ , kF∈ , _ , q) =
      proj₂ (·-left-cont (singleton a) F m) (kF , kF∈ , q)

run-cont₂ : ∀ xs → Continuous₂ (λ F Q → run F xs Q)
run-cont₂ [] = ignore-left-cont₂
run-cont₂ (a ∷ xs) =
  cont₂-substitute _·_
    (λ F Q → F · singleton a)
    (λ F Q → run F xs Q)
    thm-3-1 (symbol-cont₂ a) (run-cont₂ xs)

𝕊-on-cont₂ : ∀ F → Continuous₂ (𝕊-on F)
𝕊-on-cont₂ F S Q m = fwd , bwd
  where
    fwd : 𝕊-on F S Q m →
      Σ ℕ (λ kS → Σ ℕ (λ kQ →
        (kS ∈* S) × (kQ ∈* Q) ×
        𝕊-on F (setₚ kS) (setₚ kQ) m))
    fwd (σ , Sσ , p)
      with proj₁ (cont₂-slice (λ F′ Q′ → run F′ (members σ) Q′)
                    (run-cont₂ (members σ)) F Q m) p
    ... | kQ , kQ∈ , run-k =
      singleton-seq σ , kQ
      , subst (All S) (sym (members-singleton σ)) (Sσ , tt)
      , kQ∈
      , σ
      , subst (σ ∈-list_) (sym (members-singleton σ)) here
      , run-k

    bwd : Σ ℕ (λ kS → Σ ℕ (λ kQ →
        (kS ∈* S) × (kQ ∈* Q) ×
        𝕊-on F (setₚ kS) (setₚ kQ) m)) →
      𝕊-on F S Q m
    bwd (kS , kQ , kS∈ , kQ∈ , σ , σ∈ , p) =
      σ
      , ∈*-∀ kS S kS∈ σ σ∈
      , cont₁-mono (λ Q′ → run F (members σ) Q′)
          (cont₂-slice (λ F′ Q′ → run F′ (members σ) Q′)
            (run-cont₂ (members σ)) F)
          (∈*-to-⊆ kQ kQ∈) p

𝕊-on-F-cont : ∀ S Q → Continuous₁ (λ F → 𝕊-on F S Q)
𝕊-on-F-cont S Q F m = fwd , bwd
  where
    fwd : 𝕊-on F S Q m →
      Σ ℕ (λ kF → (kF ∈* F) × 𝕊-on (setₚ kF) S Q m)
    fwd (σ , Sσ , p)
      with proj₁ (cont₂-slice-left
        (λ F′ Q′ → run F′ (members σ) Q′)
        (run-cont₂ (members σ)) Q F m) p
    ... | kF , kF∈ , run-k = kF , kF∈ , σ , Sσ , run-k

    bwd : Σ ℕ (λ kF → (kF ∈* F) × 𝕊-on (setₚ kF) S Q m) →
      𝕊-on F S Q m
    bwd (kF , kF∈ , σ , Sσ , p) =
      σ , Sσ
      , cont₁-mono (λ F′ → run F′ (members σ) Q)
          (cont₂-slice-left
            (λ F′ Q′ → run F′ (members σ) Q′)
            (run-cont₂ (members σ)) Q)
          (∈*-to-⊆ kF kF∈) p

𝕊-lam₂-cont : Continuous₁ (λ F → lam₂ (𝕊-on F))
𝕊-lam₂-cont F k = fwd , bwd
  where
    fwd : lam₂ (𝕊-on F) k →
      Σ ℕ (λ j → (j ∈* F) × lam₂ (𝕊-on (setₚ j)) k)
    fwd (inj₁ refl) = zero , tt , inj₁ refl
    fwd (inj₂ (nS , mS , eqS , inj₁ refl)) =
      zero , tt , inj₂ (nS , mS , eqS , inj₁ refl)
    fwd (inj₂ (nS , mS , eqS , inj₂ (nQ , mQ , eqQ , p)))
      with proj₁ (𝕊-on-F-cont (setₚ nS) (setₚ nQ) F mQ) p
    ... | j , j∈ , pfinite =
      j , j∈ , inj₂ (nS , mS , eqS ,
        inj₂ (nQ , mQ , eqQ , pfinite))

    bwd : Σ ℕ (λ j → (j ∈* F) × lam₂ (𝕊-on (setₚ j)) k) →
      lam₂ (𝕊-on F) k
    bwd (_ , _ , inj₁ refl) = inj₁ refl
    bwd (_ , _ , inj₂ (nS , mS , eqS , inj₁ refl)) =
      inj₂ (nS , mS , eqS , inj₁ refl)
    bwd (j , j∈ , inj₂ (nS , mS , eqS ,
          inj₂ (nQ , mQ , eqQ , p))) =
      inj₂ (nS , mS , eqS , inj₂ (nQ , mQ , eqQ ,
        proj₂ (𝕊-on-F-cont (setₚ nS) (setₚ nQ) F mQ)
          (j , j∈ , p)))

𝕊-correct : ∀ F S Q m →
  (((𝕊 · F) · S) · Q) m ↔ 𝕊-on F S Q m
𝕊-correct F S Q m = fwd , bwd
  where
    fwd : (((𝕊 · F) · S) · Q) m → 𝕊-on F S Q m
    fwd (nQ , nQ∈ , nS , nS∈ , graph) =
      thm-3-5 (𝕊-on F) (𝕊-on-cont₂ F) S Q m
        (nQ , nQ∈ , nS , nS∈
        , lam-app-fwd (λ F′ → lam₂ (𝕊-on F′))
            𝕊-lam₂-cont F (pair nS (pair nQ m)) graph)

    bwd : 𝕊-on F S Q m → (((𝕊 · F) · S) · Q) m
    bwd p with
      proj₂ (thm-3-5-inner (𝕊-on F) (𝕊-on-cont₂ F) S Q m) p
    ... | nQ , nQ∈ , inner with
      proj₂ (thm-3-5-outer (𝕊-on F) (𝕊-on-cont₂ F)
        S (pair nQ m)) inner
    ... | nS , nS∈ , lam2 =
      nQ , nQ∈ , nS , nS∈
      , lam-app-bwd (λ F′ → lam₂ (𝕊-on F′))
          𝕊-lam₂-cont F (pair nS (pair nQ m)) lam2

𝕊-graph-run : ∀ F σ Q m →
  (((𝕊 · F) · singleton σ) · Q) m ↔ 𝕊-apply F σ Q m
𝕊-graph-run F σ Q m =
  (λ p → proj₁ (𝕊-on-sing F σ Q m)
            (proj₁ (𝕊-correct F (singleton σ) Q m) p))
  , (λ p → proj₂ (𝕊-correct F (singleton σ) Q m)
            (proj₂ (𝕊-on-sing F σ Q m) p))

∘ₒ-correct : ∀ F G X m →
  ((F ∘ₒ G) · X) m ↔ (F · (G · X)) m
∘ₒ-correct F G X m =
  lam-app-fwd (λ X′ → F · (G · X′)) body-cont X m
  , lam-app-bwd (λ X′ → F · (G · X′)) body-cont X m
  where
    body-cont : Continuous₁ (λ X′ → F · (G · X′))
    body-cont =
      cont-compose
        (λ Y → F · Y) (λ X′ → G · X′)
        (cont₂-slice _·_ thm-3-1 F)
        (cont₂-slice _·_ thm-3-1 G)

app-resp-right : ∀ F {X Y} → (∀ n → X n ↔ Y n) → ∀ m →
                 (F · X) m ↔ (F · Y) m
app-resp-right F eq m =
  (λ (n , n∈ , p) →
    n , All-mono (members n) (λ x → proj₁ (eq x)) n∈ , p)
  , (λ (n , n∈ , p) →
    n , All-mono (members n) (λ x → proj₂ (eq x)) n∈ , p)

𝕊-rec-empty : ∀ F Q m →
  (((𝕊 · F) · singleton zero) · Q) m ↔ (I · Q) m
𝕊-rec-empty F Q m =
  (λ p → I-correct-bwd Q m
    (proj₁ (𝕊-empty F Q m)
      (proj₁ (𝕊-graph-run F zero Q m) p)))
  , (λ p → proj₂ (𝕊-graph-run F zero Q m)
    (proj₂ (𝕊-empty F Q m) (I-correct-fwd Q m p)))

𝕊-rec-cons : ∀ F n a Q m →
  (((𝕊 · F) · singleton (pair n a)) · Q) m ↔
  ((((F · singleton a) ∘ₒ ((𝕊 · F) · singleton n)) · Q) m)
𝕊-rec-cons F n a Q m =
  (λ p → proj₂ (∘ₒ-correct (F · singleton a)
      ((𝕊 · F) · singleton n) Q m)
    (proj₁ (app-resp-right (F · singleton a)
      (λ x → sym↔ (𝕊-graph-run F n Q x)) m)
      (proj₁ (𝕊-cons F n a Q m)
        (proj₁ (𝕊-graph-run F (pair n a) Q m) p))))
  , (λ p → proj₂ (𝕊-graph-run F (pair n a) Q m)
    (proj₂ (𝕊-cons F n a Q m)
      (proj₂ (app-resp-right (F · singleton a)
        (λ x → sym↔ (𝕊-graph-run F n Q x)) m)
        (proj₁ (∘ₒ-correct (F · singleton a)
          ((𝕊 · F) · singleton n) Q m) p))))
  where
    sym↔ : ∀ {P Q : Set} → (P ↔ Q) → (Q ↔ P)
    sym↔ (f , g) = g , f

------------------------------------------------------------------------
-- Recursive enumerability
------------------------------------------------------------------------

run-re : ∀ {F Q} → R.RESet F → R.RESet Q → ∀ xs →
         R.RESet (run F xs Q)
run-re RF RQ []       = RQ
run-re RF RQ (a ∷ xs) =
  R.re-apply (R.re-apply RF (R.re-singleton a)) (run-re RF RQ xs)

𝕊-on-finite-re : ∀ nF nS nQ →
  R.RESet (𝕊-on (setₚ nF) (setₚ nS) (setₚ nQ))
𝕊-on-finite-re nF nS nQ m =
  R.semi-Σ λ σ →
    R.semi-× (R.re-setₚ nS σ)
      (run-re (R.re-setₚ nF) (R.re-setₚ nQ) (members σ) m)

𝕊-re : R.RESet 𝕊
𝕊-re =
  R.re-lam {Φ = λ F → lam (λ S → lam (𝕊-on F S))} λ nF →
    R.re-lam {Φ = λ S → lam (𝕊-on (setₚ nF) S)} λ nS →
      R.re-lam {Φ = 𝕊-on (setₚ nF) (setₚ nS)} λ nQ →
        𝕊-on-finite-re nF nS nQ
