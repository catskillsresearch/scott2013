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

S : 𝒫ℕ
S = lam (λ Z → lam (λ Y → lam (λ X → (Z · X) · (Y · X))))

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

------------------------------------------------------------------------
-- Theorem 3.8: ∇ = λX. Φ(X(X)),  P = ∇(∇)
------------------------------------------------------------------------

∇ : (𝒫ℕ → 𝒫ℕ) → 𝒫ℕ
∇ Φ = lam (λ X → Φ (X · X))

lfp : (𝒫ℕ → 𝒫ℕ) → 𝒫ℕ
lfp Φ = ∇ Φ · ∇ Φ

------------------------------------------------------------------------
-- Definition 4.3: sequentializer 𝕊
-- 𝕊(F)(⟨n₀,…,nₖ⟩) = F({nₖ}) ∘ ⋯ ∘ F({n₀})
--
-- `members` decodes a sequence number as [nₖ, …, n₀], so folding
-- application from the left applies F({n₀}) first.
------------------------------------------------------------------------

singleton : ℕ → 𝒫ℕ
singleton n m = m ≡ n

_∘ₒ_ : 𝒫ℕ → 𝒫ℕ → 𝒫ℕ
F ∘ₒ G = lam (λ X → F · (G · X))

run : 𝒫ℕ → List ℕ → 𝒫ℕ → 𝒫ℕ
run F []       Q = Q
run F (n ∷ ns) Q = (F · singleton n) · run F ns Q

-- Semantic action of the sequentializer on a sequence number.
𝕊-apply : 𝒫ℕ → ℕ → 𝒫ℕ → 𝒫ℕ
𝕊-apply F σ Q = run F (members σ) Q
