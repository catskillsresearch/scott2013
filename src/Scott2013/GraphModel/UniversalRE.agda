{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Universal recursively enumerable graph (Definition 3.9, (i)–(vi))
------------------------------------------------------------------------

module Scott2013.GraphModel.UniversalRE where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc) renaming (Nat to ℕ)
open import Agda.Builtin.Unit using (tt)

open import Scott2013.Prelude
open import Scott2013.GraphModel.Basic
open import Scott2013.GraphModel.Application
open import Scott2013.GraphModel.Combinators
open import Scott2013.GraphModel.Arithmetic
import Scott2013.Computability.RE as R

------------------------------------------------------------------------
-- Continuity of the universal equation
------------------------------------------------------------------------

re-interp-cont : ∀ code → Continuous₁ (λ G → re-interp G code)
re-interp-cont zero = const-cont K
re-interp-cont (suc zero) = const-cont S
re-interp-cont (suc (suc zero)) = const-cont Test
re-interp-cont (suc (suc (suc zero))) = const-cont Succ
re-interp-cont (suc (suc (suc (suc zero)))) = const-cont Pred
re-interp-cont (suc (suc (suc (suc (suc k))))) =
  cont₂-compose _·_
    (λ G → G · singleton (proj₁ (unpair (suc k))))
    (λ G → G · singleton (proj₂ (unpair (suc k))))
    thm-3-1
    (·-left-cont (singleton (proj₁ (unpair (suc k)))))
    (·-left-cont (singleton (proj₂ (unpair (suc k)))))

re-apply-cont₂ : Continuous₂ re-apply
re-apply-cont₂ G X m = fwd , bwd
  where
    fwd : re-apply G X m →
          Σ ℕ (λ kG → Σ ℕ (λ kX →
            (kG ∈* G) × (kX ∈* X) ×
            re-apply (setₚ kG) (setₚ kX) m))
    fwd (code , Xcode , interp)
      with proj₁ (re-interp-cont code G m) interp
    ... | kG , kG∈ , interp-k =
      kG , singleton-seq code
      , kG∈
      , subst (All X) (sym (members-singleton code)) (Xcode , tt)
      , code
      , subst (code ∈-list_) (sym (members-singleton code)) here
      , interp-k

    bwd : Σ ℕ (λ kG → Σ ℕ (λ kX →
            (kG ∈* G) × (kX ∈* X) ×
            re-apply (setₚ kG) (setₚ kX) m)) →
          re-apply G X m
    bwd (kG , kX , kG∈ , kX∈ , code , code∈ , interp) =
      code
      , ∈*-∀ kX X kX∈ code code∈
      , cont₁-mono (λ H → re-interp H code)
          (re-interp-cont code) (∈*-to-⊆ kG kG∈) interp

RE-op-cont : Continuous₁ RE-op
RE-op-cont = thm-3-4 re-apply re-apply-cont₂

RE-fixed : ∀ m → RE m ↔ RE-op RE m
RE-fixed = thm-3-8-fixed RE-op RE-op-cont

RE-application : ∀ X m → (RE · X) m ↔ re-apply RE X m
RE-application X m = fwd , bwd
  where
    body-cont : Continuous₁ (re-apply RE)
    body-cont = cont₂-slice re-apply re-apply-cont₂ RE

    fwd : (RE · X) m → re-apply RE X m
    fwd (n , n∈X , REnm) =
      lam-app-fwd (re-apply RE) body-cont X m
        (n , n∈X , proj₁ (RE-fixed (pair n m)) REnm)

    bwd : re-apply RE X m → (RE · X) m
    bwd p with lam-app-bwd (re-apply RE) body-cont X m p
    ... | n , n∈X , op =
      n , n∈X , proj₂ (RE-fixed (pair n m)) op

re-apply-singleton : ∀ G code m →
  re-apply G (singleton code) m ↔ re-interp G code m
re-apply-singleton G code m = fwd , bwd
  where
    fwd : re-apply G (singleton code) m → re-interp G code m
    fwd (n , eq , p) =
      subst (λ j → re-interp G j m) eq p

    bwd : re-interp G code m → re-apply G (singleton code) m
    bwd p = code , refl , p

RE-code : ∀ code m → (RE · singleton code) m ↔ re-interp RE code m
RE-code code m =
  (λ p → proj₁ (re-apply-singleton RE code m)
            (proj₁ (RE-application (singleton code) m) p))
  , (λ p → proj₂ (RE-application (singleton code) m)
            (proj₂ (re-apply-singleton RE code m) p))

------------------------------------------------------------------------
-- Definition 3.9 equations (i)–(vi), as graph application equalities
------------------------------------------------------------------------

RE-i : ∀ m → (RE · singleton zero) m ↔ K m
RE-i m =
  (λ p → proj₁ (re-interp-0 RE m) (proj₁ (RE-code zero m) p))
  , (λ p → proj₂ (RE-code zero m) (proj₂ (re-interp-0 RE m) p))

RE-ii : ∀ m → (RE · singleton (suc zero)) m ↔ S m
RE-ii m =
  (λ p → proj₁ (re-interp-1 RE m)
            (proj₁ (RE-code (suc zero) m) p))
  , (λ p → proj₂ (RE-code (suc zero) m)
            (proj₂ (re-interp-1 RE m) p))

RE-iii : ∀ m → (RE · singleton (suc (suc zero))) m ↔ Test m
RE-iii m =
  (λ p → proj₁ (re-interp-2 RE m)
            (proj₁ (RE-code (suc (suc zero)) m) p))
  , (λ p → proj₂ (RE-code (suc (suc zero)) m)
            (proj₂ (re-interp-2 RE m) p))

RE-iv : ∀ m → (RE · singleton (suc (suc (suc zero)))) m ↔ Succ m
RE-iv m =
  (λ p → proj₁ (re-interp-3 RE m)
            (proj₁ (RE-code (suc (suc (suc zero))) m) p))
  , (λ p → proj₂ (RE-code (suc (suc (suc zero))) m)
            (proj₂ (re-interp-3 RE m) p))

RE-v : ∀ m →
  (RE · singleton (suc (suc (suc (suc zero))))) m ↔ Pred m
RE-v m =
  (λ p → proj₁ (re-interp-4 RE m)
            (proj₁ (RE-code (suc (suc (suc (suc zero)))) m) p))
  , (λ p → proj₂ (RE-code (suc (suc (suc (suc zero)))) m)
            (proj₂ (re-interp-4 RE m) p))

RE-vi : ∀ n k m →
  (RE · singleton (suc (suc (suc (suc (pair n k)))))) m ↔
  ((RE · singleton n) · (RE · singleton k)) m
RE-vi n k m =
  (λ p → proj₁ (re-interp-app RE n k m)
            (proj₁ (RE-code (suc (suc (suc (suc (pair n k))))) m) p))
  , (λ p → proj₂ (RE-code (suc (suc (suc (suc (pair n k))))) m)
            (proj₂ (re-interp-app RE n k m) p))

------------------------------------------------------------------------
-- Recursive enumerability witnesses
------------------------------------------------------------------------

K-re : R.RESet K
K-re =
  R.re-lam {Φ = λ Y → lam (λ _ → Y)} λ nY →
    R.re-lam {Φ = λ _ → setₚ nY} λ _ → R.re-setₚ nY

S-re : R.RESet S
S-re =
  R.re-lam {Φ = λ Z → lam (λ Y → lam (λ X →
      (Z · X) · (Y · X)))} λ nZ →
    R.re-lam {Φ = λ Y → lam (λ X →
        (setₚ nZ · X) · (Y · X))} λ nY →
      R.re-lam {Φ = λ X →
          (setₚ nZ · X) · (setₚ nY · X)} λ nX →
        R.re-apply
          (R.re-apply (R.re-setₚ nZ) (R.re-setₚ nX))
          (R.re-apply (R.re-setₚ nY) (R.re-setₚ nX))

Succ-re : R.RESet Succ
Succ-re = R.re-lam {Φ = Succ-op} λ nX m →
  R.semi-Σ λ n →
    R.semi-× (R.re-setₚ nX n)
      (R.semi-dec (m ≡ suc n) (ℕ-eq-dec m (suc n)))

Pred-re : R.RESet Pred
Pred-re = R.re-lam {Φ = Pred-op} λ nX m → R.re-setₚ nX (suc m)

Test-re : R.RESet Test
Test-re =
  R.re-lam {Φ = λ Z → lam (λ X → lam (λ Y → Test-op Z X Y))}
    λ nZ →
    R.re-lam {Φ = λ X → lam (λ Y → Test-op (setₚ nZ) X Y)}
      λ nX →
      R.re-lam {Φ = λ Y → Test-op (setₚ nZ) (setₚ nX) Y}
        λ nY m →
          R.semi-⊎
            (R.semi-× (R.re-setₚ nX m) (R.re-setₚ nZ zero))
            (R.semi-× (R.re-setₚ nY m)
              (R.semi-Σ λ k → R.re-setₚ nZ (suc k)))

re-interp-re : ∀ {G} → R.RESet G → ∀ code →
               R.RESet (re-interp G code)
re-interp-re RG zero = K-re
re-interp-re RG (suc zero) = S-re
re-interp-re RG (suc (suc zero)) = Test-re
re-interp-re RG (suc (suc (suc zero))) = Succ-re
re-interp-re RG (suc (suc (suc (suc zero)))) = Pred-re
re-interp-re RG (suc (suc (suc (suc (suc k))))) =
  R.re-apply
    (R.re-apply RG
      (R.re-singleton (proj₁ (unpair (suc k)))))
    (R.re-apply RG
      (R.re-singleton (proj₂ (unpair (suc k)))))

re-apply-re : ∀ {G X} → R.RESet G → R.RESet X →
              R.RESet (re-apply G X)
re-apply-re RG RX m =
  R.semi-Σ λ code → R.semi-× (RX code) (re-interp-re RG code m)

RE-op-finite-re : ∀ n → R.RESet (RE-op (setₚ n))
RE-op-finite-re n =
  R.re-lam {Φ = re-apply (setₚ n)}
    λ k → re-apply-re (R.re-setₚ n) (R.re-setₚ k)

RE-op-graph-re : R.RESet (lam RE-op)
RE-op-graph-re = R.re-lam {Φ = RE-op} RE-op-finite-re

RE-op-computable : R.Computable₁ RE-op
RE-op-computable = R.computable₁ RE-op-cont RE-op-graph-re

RE-re : R.RESet RE
RE-re = R.thm-3-8-computable RE-op RE-op-computable
