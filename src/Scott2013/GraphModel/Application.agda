{-# OPTIONS --without-K --safe #-}

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

------------------------------------------------------------------------
-- Monotonicity of application (used by Theorems 3.6 and 3.8)
------------------------------------------------------------------------

·-mono-left : ∀ {F G X} → F ⊆ G → (F · X) ⊆ (G · X)
·-mono-left F⊆G (n , n∈X , Fn) = n , n∈X , F⊆G Fn

·-mono-right : ∀ {F X Y} → X ⊆ Y → (F · X) ⊆ (F · Y)
·-mono-right X⊆Y (n , n∈X , Fn) = n , ∈*-mono n X⊆Y n∈X , Fn

cont₁-mono : ∀ (Φ : 𝒫ℕ → 𝒫ℕ) → Continuous₁ Φ →
             ∀ {X Y} → X ⊆ Y → Φ X ⊆ Φ Y
cont₁-mono Φ Φc X⊆Y ΦX =
  proj₂ (Φc _ _) (_ , ∈*-mono _ X⊆Y (proj₁ (proj₂ (proj₁ (Φc _ _) ΦX))) , proj₂ (proj₂ (proj₁ (Φc _ _) ΦX)))

-- Identity and constant maps are continuous (Definition 2.2).
id-cont : Continuous₁ (λ X → X)
id-cont X m =
  (λ Xm → singleton-seq m
        , subst (All X) (sym (members-singleton m)) (Xm , tt)
        , subst (m ∈-list_) (sym (members-singleton m)) here)
  , λ (k , k∈X , m∈k) → ∈*-∀ k X k∈X m m∈k

const-cont : ∀ (Y : 𝒫ℕ) → Continuous₁ (λ _ → Y)
const-cont Y X m = (λ Ym → zero , tt , Ym) , λ (_ , _ , Ym) → Ym

------------------------------------------------------------------------
-- Theorem 3.4: λ-abstraction preserves continuity in the remaining
-- variables.  For a binary continuous Φ, Y ↦ λX. Φ(Y,X) is continuous.
------------------------------------------------------------------------

cont₂-mono-right : ∀ (Φ : 𝒫ℕ → 𝒫ℕ → 𝒫ℕ) → Continuous₂ Φ →
                   ∀ {Y X X′} → X ⊆ X′ → Φ Y X ⊆ Φ Y X′
cont₂-mono-right Φ Φc X⊆X′ {m} p with proj₁ (Φc _ _ m) p
... | kY , kX , kY∈ , kX∈ , Φs =
  proj₂ (Φc _ _ m) (kY , kX , kY∈ , ∈*-mono kX X⊆X′ kX∈ , Φs)

cont₂-slice : ∀ (Φ : 𝒫ℕ → 𝒫ℕ → 𝒫ℕ) → Continuous₂ Φ →
              ∀ Y → Continuous₁ (λ X → Φ Y X)
cont₂-slice Φ Φc Y X m = fwd , bwd
  where
    fwd : Φ Y X m → Σ ℕ (λ k → (k ∈* X) × Φ Y (setₚ k) m)
    fwd p with proj₁ (Φc Y X m) p
    ... | kY , kX , kY∈ , kX∈ , Φs =
      kX , kX∈ , proj₂ (Φc Y (setₚ kX) m) (kY , kX , kY∈ , ∈*-refl kX , Φs)

    bwd : Σ ℕ (λ k → (k ∈* X) × Φ Y (setₚ k) m) → Φ Y X m
    bwd (k , k∈X , Φk) with proj₁ (Φc Y (setₚ k) m) Φk
    ... | kY , kX , kY∈ , kX∈k , Φs =
      proj₂ (Φc Y X m)
        (kY , kX , kY∈ , ∈*-mono kX (λ {x} x∈ → ∈*-∀ k X k∈X x x∈) kX∈k , Φs)

thm-3-4 : ∀ (Φ : 𝒫ℕ → 𝒫ℕ → 𝒫ℕ) → Continuous₂ Φ →
          Continuous₁ (λ Y → lam (λ X → Φ Y X))
thm-3-4 Φ Φc Y k = fwd , bwd
  where
    fwd : lam (λ X → Φ Y X) k →
          Σ ℕ (λ j → (j ∈* Y) × lam (λ X → Φ (setₚ j) X) k)
    fwd (inj₁ refl) = zero , tt , inj₁ refl
    fwd (inj₂ (n , m , peq , ΦYm)) with proj₁ (Φc Y (setₚ n) m) ΦYm
    ... | j , i , j∈Y , i∈n , Φji =
      j , j∈Y , inj₂ (n , m , peq ,
        cont₂-mono-right Φ Φc (λ {x} x∈i → ∈*-∀ i (setₚ n) i∈n x x∈i) Φji)

    bwd : Σ ℕ (λ j → (j ∈* Y) × lam (λ X → Φ (setₚ j) X) k) →
          lam (λ X → Φ Y X) k
    bwd (j , j∈Y , inj₁ refl) = inj₁ refl
    bwd (j , j∈Y , inj₂ (n , m , peq , Φj)) =
      inj₂ (n , m , peq , proj₂ (Φc Y (setₚ n) m) (j , n , j∈Y , ∈*-refl n , Φj))

-- Corollary 3.5: largest binary graph.
lam₂ : (𝒫ℕ → 𝒫ℕ → 𝒫ℕ) → 𝒫ℕ
lam₂ Φ = lam (λ Y → lam (λ X → Φ Y X))

thm-3-5-outer : ∀ (Φ : 𝒫ℕ → 𝒫ℕ → 𝒫ℕ) → Continuous₂ Φ →
                ∀ Y k → (lam₂ Φ · Y) k ↔ lam (λ X → Φ Y X) k
thm-3-5-outer Φ Φc Y k =
  lam-app-fwd (λ Y′ → lam (λ X → Φ Y′ X)) (thm-3-4 Φ Φc) Y k
  , lam-app-bwd (λ Y′ → lam (λ X → Φ Y′ X)) (thm-3-4 Φ Φc) Y k

thm-3-5-inner : ∀ (Φ : 𝒫ℕ → 𝒫ℕ → 𝒫ℕ) → Continuous₂ Φ →
                ∀ Y X m → (lam (λ X′ → Φ Y X′) · X) m ↔ Φ Y X m
thm-3-5-inner Φ Φc Y X m =
  lam-app-fwd (λ X′ → Φ Y X′) (cont₂-slice Φ Φc Y) X m
  , lam-app-bwd (λ X′ → Φ Y X′) (cont₂-slice Φ Φc Y) X m

thm-3-5 : ∀ (Φ : 𝒫ℕ → 𝒫ℕ → 𝒫ℕ) → Continuous₂ Φ →
          ∀ Y X m → ((lam₂ Φ · Y) · X) m → Φ Y X m
thm-3-5 Φ Φc Y X m (n , n∈X , hy) =
  proj₁ (thm-3-5-inner Φ Φc Y X m)
    (n , n∈X , proj₁ (thm-3-5-outer Φ Φc Y (pair n m)) hy)

------------------------------------------------------------------------
-- Theorem 3.6: lattice identities for λ-abstraction of application
------------------------------------------------------------------------

thm-3-6-⊆-fwd : ∀ (F G : 𝒫ℕ) →
  lam (λ X → F · X) ⊆ lam (λ X → G · X) → ∀ X → (F · X) ⊆ (G · X)
thm-3-6-⊆-fwd F G graphs X {m} (n , n∈X , Fn) with graphs (inj₂ (n , m , refl , (n , ∈*-refl n , Fn)))
... | inj₁ peq = ⊥-elim (pair-ne-zero n m peq)
... | inj₂ (n′ , m′ , peq , (j , j∈ , Gj)) =
  let inj = pair-injective n m n′ m′ peq
  in  j
    , ∈*-mono {X = setₚ n′} {Y = X} j
        (λ {x} x∈n′ → ∈*-∀ n X n∈X x
          (subst (λ n″ → x ∈-set n″) (sym (proj₁ inj)) x∈n′))
        j∈
    , subst G (cong (λ m″ → pair j m″) (sym (proj₂ inj))) Gj

thm-3-6-⊆-bwd : ∀ (F G : 𝒫ℕ) →
  (∀ X → (F · X) ⊆ (G · X)) → lam (λ X → F · X) ⊆ lam (λ X → G · X)
thm-3-6-⊆-bwd F G hyp {zero}  (inj₁ refl) = inj₁ refl
thm-3-6-⊆-bwd F G hyp {zero}  (inj₂ (n , m , peq , _)) = ⊥-elim (pair-ne-zero n m (sym peq))
thm-3-6-⊆-bwd F G hyp {suc k} (inj₁ ())
thm-3-6-⊆-bwd F G hyp {suc k} (inj₂ (n , m , peq , Fn)) =
  inj₂ (n , m , peq , hyp (setₚ n) {m} Fn)

thm-3-6-∩ : ∀ (F G : 𝒫ℕ) →
  lam (λ X → (F · X) ∩ₚ (G · X)) ⊆ (lam (λ X → F · X) ∩ₚ lam (λ X → G · X))
thm-3-6-∩ F G {zero}  (inj₁ refl) = inj₁ refl , inj₁ refl
thm-3-6-∩ F G {suc k} (inj₁ ())
thm-3-6-∩ F G {suc k} (inj₂ (n , m , peq , Fn , Gn)) =
  inj₂ (n , m , peq , Fn) , inj₂ (n , m , peq , Gn)
thm-3-6-∩ F G {zero}  (inj₂ (n , m , peq , _)) =
  ⊥-elim (pair-ne-zero n m (sym peq))

thm-3-6-∪ : ∀ (F G : 𝒫ℕ) →
  lam (λ X → (F · X) ∪ₚ (G · X)) ⊆ (lam (λ X → F · X) ∪ₚ lam (λ X → G · X))
thm-3-6-∪ F G {zero}  (inj₁ refl) = inj₁ (inj₁ refl)
thm-3-6-∪ F G {suc k} (inj₁ ())
thm-3-6-∪ F G {zero}  (inj₂ (n , m , peq , _)) = ⊥-elim (pair-ne-zero n m (sym peq))
thm-3-6-∪ F G {suc k} (inj₂ (n , m , peq , inj₁ Fn)) = inj₁ (inj₂ (n , m , peq , Fn))
thm-3-6-∪ F G {suc k} (inj₂ (n , m , peq , inj₂ Gn)) = inj₂ (inj₂ (n , m , peq , Gn))

-- Reverse inclusions for ∩ and ∪.
thm-3-6-∩-rev : ∀ (F G : 𝒫ℕ) →
  (lam (λ X → F · X) ∩ₚ lam (λ X → G · X)) ⊆ lam (λ X → (F · X) ∩ₚ (G · X))
thm-3-6-∩-rev F G {zero}  (inj₁ refl , _) = inj₁ refl
thm-3-6-∩-rev F G {zero}  (inj₂ (n , m , peq , _) , _) =
  ⊥-elim (pair-ne-zero n m (sym peq))
thm-3-6-∩-rev F G {suc k} (inj₁ () , _)
thm-3-6-∩-rev F G {suc k} (_ , inj₁ ())
thm-3-6-∩-rev F G {suc k} (inj₂ (n , m , peq , Fn) , inj₂ (n′ , m′ , peq′ , Gn)) =
  inj₂ (n , m , peq , Fn ,
    subst (λ n″ → (G · setₚ n″) m) (sym (proj₁ inj))
      (subst (λ m″ → (G · setₚ n′) m″) (sym (proj₂ inj)) Gn))
  where
    inj = pair-injective n m n′ m′ (trans (sym peq) peq′)

thm-3-6-∪-rev : ∀ (F G : 𝒫ℕ) →
  (lam (λ X → F · X) ∪ₚ lam (λ X → G · X)) ⊆ lam (λ X → (F · X) ∪ₚ (G · X))
thm-3-6-∪-rev F G {zero}  (inj₁ (inj₁ refl)) = inj₁ refl
thm-3-6-∪-rev F G {zero}  (inj₂ (inj₁ refl)) = inj₁ refl
thm-3-6-∪-rev F G {zero}  (inj₁ (inj₂ (n , m , peq , _))) = ⊥-elim (pair-ne-zero n m (sym peq))
thm-3-6-∪-rev F G {zero}  (inj₂ (inj₂ (n , m , peq , _))) = ⊥-elim (pair-ne-zero n m (sym peq))
thm-3-6-∪-rev F G {suc k} (inj₁ (inj₁ ()))
thm-3-6-∪-rev F G {suc k} (inj₂ (inj₁ ()))
thm-3-6-∪-rev F G {suc k} (inj₁ (inj₂ (n , m , peq , Fn))) = inj₂ (n , m , peq , inj₁ Fn)
thm-3-6-∪-rev F G {suc k} (inj₂ (inj₂ (n , m , peq , Gn))) = inj₂ (n , m , peq , inj₂ Gn)

------------------------------------------------------------------------
-- Continuity helpers for S and the sequentializer
------------------------------------------------------------------------

·-left-cont : ∀ X → Continuous₁ (λ F → F · X)
·-left-cont X F m = fwd , bwd
  where
    fwd : (F · X) m → Σ ℕ (λ k → (k ∈* F) × (setₚ k · X) m)
    fwd (n , n∈X , Fn) =
      singleton-seq (pair n m)
      , subst (All F) (sym (members-singleton (pair n m))) (Fn , tt)
      , n , n∈X
      , subst (pair n m ∈-list_) (sym (members-singleton (pair n m))) here

    bwd : Σ ℕ (λ k → (k ∈* F) × (setₚ k · X) m) → (F · X) m
    bwd (k , k∈F , n , n∈X , pair∈) =
      n , n∈X , ∈*-∀ k F k∈F (pair n m) pair∈

∈*-cont : ∀ (Φ : 𝒫ℕ → 𝒫ℕ) → Continuous₁ Φ → ∀ k X →
          k ∈* Φ X → Σ ℕ (λ kX → (kX ∈* X) × k ∈* Φ (setₚ kX))
∈*-cont Φ Φc k X p = go (members k) p
  where
    go : ∀ xs → All (Φ X) xs →
         Σ ℕ (λ kX → (kX ∈* X) × All (Φ (setₚ kX)) xs)
    go []       _            = zero , tt , tt
    go (m ∷ ms) (ΦXm , rest) with proj₁ (Φc X m) ΦXm | go ms rest
    ... | k1 , k1∈ , Φs | k2 , k2∈ , Φrest =
      seq-append k1 k2
      , ∈*-append k1 k2 k1∈ k2∈
      , proj₂ (Φc (setₚ (seq-append k1 k2)) m)
          (k1 , k1∈app , Φs)
      , All-mono ms
          (λ x Φx → proj₂ (Φc (setₚ (seq-append k1 k2)) x)
            (k2 , k2∈app , Φx))
          Φrest
      where
        k1∈app : k1 ∈* setₚ (seq-append k1 k2)
        k1∈app = All-mono (members k1)
          (λ x x∈ → set-append-left k1 k2 x∈) (∈*-refl k1)

        k2∈app : k2 ∈* setₚ (seq-append k1 k2)
        k2∈app = All-mono (members k2)
          (λ x x∈ → set-append-right k1 k2 x∈) (∈*-refl k2)

∈*-app-approx : ∀ k F X → k ∈* (F · X) →
                Σ ℕ (λ kF → Σ ℕ (λ kX →
                  (kF ∈* F) × (kX ∈* X) × k ∈* (setₚ kF · setₚ kX)))
∈*-app-approx k F X p = go (members k) p
  where
    go : ∀ xs → All (F · X) xs →
         Σ ℕ (λ kF → Σ ℕ (λ kX →
           (kF ∈* F) × (kX ∈* X) × All (setₚ kF · setₚ kX) xs))
    go []       _ = zero , zero , tt , tt , tt
    go (m ∷ ms) ((n , n∈X , Fn) , rest) with go ms rest
    ... | kF2 , kX2 , kF2∈ , kX2∈ , ih =
      seq-append kF1 kF2
      , seq-append n kX2
      , ∈*-append kF1 kF2 kF1∈F kF2∈
      , ∈*-append n kX2 n∈X kX2∈
      , (n , n∈kX , pair∈kF)
      , All-mono ms lift ih
      where
        kF1 : ℕ
        kF1 = singleton-seq (pair n m)

        kF1∈F : kF1 ∈* F
        kF1∈F = subst (All F) (sym (members-singleton (pair n m))) (Fn , tt)

        n∈kX : n ∈* setₚ (seq-append n kX2)
        n∈kX = All-mono (members n)
          (λ x x∈ → set-append-left n kX2 x∈) (∈*-refl n)

        pair∈kF : pair n m ∈-set (seq-append kF1 kF2)
        pair∈kF = set-append-left kF1 kF2
          (subst (pair n m ∈-list_) (sym (members-singleton (pair n m))) here)

        lift : ∀ x → (setₚ kF2 · setₚ kX2) x →
               (setₚ (seq-append kF1 kF2) · setₚ (seq-append n kX2)) x
        lift x (j , j∈ , pair∈) =
          j
          , All-mono (members j)
              (λ y y∈ → set-append-right n kX2 y∈) j∈
          , set-append-right kF1 kF2 pair∈

-- Composition: X ↦ Φ(X) · B is continuous when Φ is.
app-comp-right : ∀ (Φ : 𝒫ℕ → 𝒫ℕ) (B : 𝒫ℕ) → Continuous₁ Φ →
                 Continuous₁ (λ X → Φ X · B)
app-comp-right Φ B Φc X m = fwd , bwd
  where
    fwd : (Φ X · B) m → Σ ℕ (λ k → (k ∈* X) × (Φ (setₚ k) · B) m)
    fwd p with proj₁ (·-left-cont B (Φ X) m) p
    ... | kF , kF∈Φ , setB =
      let (kX , kX∈ , kF∈Φs) = ∈*-cont Φ Φc kF X kF∈Φ
      in  kX , kX∈
        , proj₂ (·-left-cont B (Φ (setₚ kX)) m) (kF , kF∈Φs , setB)

    bwd : Σ ℕ (λ k → (k ∈* X) × (Φ (setₚ k) · B) m) → (Φ X · B) m
    bwd (k , k∈ , n , n∈B , Φkn) =
      n , n∈B
      , proj₂ (Φc X (pair n m))
          (k
          , All-mono (members k) (λ x x∈ → ∈*-to-⊆ k k∈ x∈) (∈*-refl k)
          , Φkn)

