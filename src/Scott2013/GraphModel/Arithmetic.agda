{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Arithmetic combinators (PROGIC 2013, Definition 3.9)
------------------------------------------------------------------------

module Scott2013.GraphModel.Arithmetic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc) renaming (Nat to ℕ)
open import Agda.Builtin.Unit using (tt)

open import Scott2013.Prelude
open import Scott2013.GraphModel.Basic
open import Scott2013.GraphModel.Application
open import Scott2013.GraphModel.Combinators
  using (Succ-op; Pred-op; Test-op; Succ; Pred; Test; singleton; lam-ne)

Succ-op-cont : Continuous₁ Succ-op
Succ-op-cont X m = fwd , bwd
  where
    fwd : Succ-op X m →
          Σ ℕ (λ k → (k ∈* X) × Succ-op (setₚ k) m)
    fwd (n , Xn , eq) =
      singleton-seq n
      , subst (All X) (sym (members-singleton n)) (Xn , tt)
      , n
      , subst (n ∈-list_) (sym (members-singleton n)) here
      , eq

    bwd : Σ ℕ (λ k → (k ∈* X) × Succ-op (setₚ k) m) →
          Succ-op X m
    bwd (k , k∈X , n , n∈k , eq) =
      n , ∈*-∀ k X k∈X n n∈k , eq

Pred-op-cont : Continuous₁ Pred-op
Pred-op-cont X m =
  (λ p → singleton-seq (suc m)
       , subst (All X) (sym (members-singleton (suc m))) (p , tt)
       , subst (suc m ∈-list_) (sym (members-singleton (suc m))) here)
  , λ (k , k∈X , sm∈k) → ∈*-∀ k X k∈X (suc m) sm∈k

Succ-correct : ∀ X m → (Succ · X) m ↔ Succ-op X m
Succ-correct X m =
  lam-app-fwd Succ-op Succ-op-cont X m
  , lam-app-bwd Succ-op Succ-op-cont X m

Pred-correct : ∀ X m → (Pred · X) m ↔ Pred-op X m
Pred-correct X m =
  lam-app-fwd Pred-op Pred-op-cont X m
  , lam-app-bwd Pred-op Pred-op-cont X m

Test-correct-fwd : ∀ Z X Y m →
  (((Test · Z) · X) · Y) m → Test-op Z X Y m
Test-correct-fwd Z X Y m (nY , nY∈ , nX , nX∈ , nZ , nZ∈ , graph) =
  lift (lam-ne
    (λ Y′ → Test-op (setₚ nZ) (setₚ nX) Y′) nY m
    (lam-ne
      (λ X′ → lam (λ Y′ → Test-op (setₚ nZ) X′ Y′))
      nX (pair nY m)
      (lam-ne
        (λ Z′ → lam (λ X′ → lam (λ Y′ → Test-op Z′ X′ Y′)))
        nZ (pair nX (pair nY m)) graph)))
  where
    lift : Test-op (setₚ nZ) (setₚ nX) (setₚ nY) m →
           Test-op Z X Y m
    lift (inj₁ (m∈X , 0∈Z)) =
      inj₁
        (∈*-∀ nX X nX∈ m m∈X
        , ∈*-∀ nZ Z nZ∈ zero 0∈Z)
    lift (inj₂ (m∈Y , k , sk∈Z)) =
      inj₂
        (∈*-∀ nY Y nY∈ m m∈Y
        , k , ∈*-∀ nZ Z nZ∈ (suc k) sk∈Z)

Test-correct-bwd : ∀ Z X Y m →
  Test-op Z X Y m → (((Test · Z) · X) · Y) m
Test-correct-bwd Z X Y m (inj₁ (Xm , Z0)) =
  nY , tt , nX , nX∈ , nZ , nZ∈
  , inj₂ (nZ , pair nX (pair nY m) , refl
  , inj₂ (nX , pair nY m , refl
  , inj₂ (nY , m , refl , inj₁ (Xm-fin , Z0-fin))))
  where
    nZ = singleton-seq zero
    nX = singleton-seq m
    nY = zero

    nZ∈ : nZ ∈* Z
    nZ∈ = subst (All Z) (sym (members-singleton zero)) (Z0 , tt)

    nX∈ : nX ∈* X
    nX∈ = subst (All X) (sym (members-singleton m)) (Xm , tt)

    Xm-fin : setₚ nX m
    Xm-fin = subst (m ∈-list_) (sym (members-singleton m)) here

    Z0-fin : setₚ nZ zero
    Z0-fin = subst (zero ∈-list_) (sym (members-singleton zero)) here

Test-correct-bwd Z X Y m (inj₂ (Ym , k , Zsk)) =
  nY , nY∈ , nX , tt , nZ , nZ∈
  , inj₂ (nZ , pair nX (pair nY m) , refl
  , inj₂ (nX , pair nY m , refl
  , inj₂ (nY , m , refl , inj₂ (Ym-fin , k , Zsk-fin))))
  where
    nZ = singleton-seq (suc k)
    nX = zero
    nY = singleton-seq m

    nZ∈ : nZ ∈* Z
    nZ∈ = subst (All Z) (sym (members-singleton (suc k))) (Zsk , tt)

    nY∈ : nY ∈* Y
    nY∈ = subst (All Y) (sym (members-singleton m)) (Ym , tt)

    Ym-fin : setₚ nY m
    Ym-fin = subst (m ∈-list_) (sym (members-singleton m)) here

    Zsk-fin : setₚ nZ (suc k)
    Zsk-fin =
      subst (suc k ∈-list_) (sym (members-singleton (suc k))) here

Test-correct : ∀ Z X Y m →
  (((Test · Z) · X) · Y) m ↔ Test-op Z X Y m
Test-correct Z X Y m =
  Test-correct-fwd Z X Y m , Test-correct-bwd Z X Y m
