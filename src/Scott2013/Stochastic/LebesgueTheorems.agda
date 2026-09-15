{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Literal Theorem 4.5 and Scott's fair-coin oracle (§5)
------------------------------------------------------------------------

module Scott2013.Stochastic.LebesgueTheorems where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc) renaming (Nat to ℕ)
open import Agda.Builtin.Unit using (tt)

open import Scott2013.Prelude
open import Scott2013.GraphModel.Basic
open import Scott2013.GraphModel.Application
open import Scott2013.GraphModel.Combinators
open import Scott2013.GraphModel.Sequentializer
open import Scott2013.MeasureTheory.Base
open import Scott2013.MeasureTheory.Lebesgue
open import Scott2013.Stochastic.Lebesgue

module Over (L : LebesgueUnitInterval) where

  module RV = Relative L
  open RV

  const-event-measurable : ∀ (P : Set) →
    Measurable (borel L) (λ _ → P)
  const-event-measurable P with classical L P
  ... | inj₁ p =
    measurable-resp (borel L)
      (λ t → (λ _ → p) , λ _ → tt)
      (measurable-full (borel L))
  ... | inj₂ np =
    measurable-resp (borel L)
      (λ t → (λ ()) , λ p → ⊥-elim (np p))
      (measurable-empty (borel L))

  run-rv : RandomVar → List ℕ → 𝒫ℕ → RandomVar
  run-rv A []       Q = const-rv Q
  run-rv A (a ∷ as) Q =
    (A ·ᵣ const-rv (singleton a)) ·ᵣ run-rv A as Q

  run-rv-value : ∀ A xs Q t m →
    value (run-rv A xs Q) t m ↔ run (value A t) xs Q m
  run-rv-value A [] Q t m = (λ p → p) , (λ p → p)
  run-rv-value A (a ∷ as) Q t m =
    app-resp-right (value A t · singleton a)
      (λ x → run-rv-value A as Q t x) m

  AcceptEvent : RandomVar → ℕ → 𝒫ℕ → Event ([0,1] L)
  AcceptEvent A σ Q t =
    run (value A t) (members σ) Q zero

  GraphAcceptEvent : RandomVar → ℕ → 𝒫ℕ → Event ([0,1] L)
  GraphAcceptEvent A σ Q t =
    (((𝕊 · value A t) · singleton σ) · Q) zero

  accept-event-measurable : ∀ A σ Q →
    Measurable (borel L) (AcceptEvent A σ Q)
  accept-event-measurable A σ Q =
    measurable-resp (borel L)
      (λ t → run-rv-value A (members σ) Q t zero)
      (coordinate (run-rv A (members σ) Q) zero)

  graph-accept-measurable : ∀ A σ Q →
    Measurable (borel L) (GraphAcceptEvent A σ Q)
  graph-accept-measurable A σ Q =
    measurable-resp (borel L)
      (λ t → proj₂ (𝕊-graph-run (value A t) σ Q zero)
             , proj₁ (𝕊-graph-run (value A t) σ Q zero))
      (accept-event-measurable A σ Q)

  record FiniteFiniteRange (A : RandomVar) : Set where
    constructor finite-finite-range
    field
      codes  : List ℕ
      covers : ∀ t → Σ ℕ (λ code →
        (code ∈-list codes) ×
        (∀ n → value A t n ↔ setₚ code n))

  open FiniteFiniteRange public

  record Theorem45Hypotheses : Set₁ where
    constructor theorem45-hypotheses
    field
      Alphabet : 𝒫ℕ
      alphabet-finite : Finite Alphabet
      initial-code : ℕ
      oracle : RandomVar
      oracle-range : FiniteFiniteRange oracle
      threshold : Value (probabilities L)
      threshold-lower :
        less-equal (probabilities L) (0# (probabilities L)) threshold
      threshold-upper :
        less-equal (probabilities L) threshold (1# (probabilities L))

  open Theorem45Hypotheses public

  Above : Event ([0,1] L) → Value (probabilities L) → Set
  Above E δ =
    less-than (probabilities L) δ (measure (lebesgue L) E)

  ThresholdLanguage : Theorem45Hypotheses → 𝒫ℕ
  ThresholdLanguage H σ =
    (σ ∈* Alphabet H) ×
    Above (GraphAcceptEvent (oracle H) σ (setₚ (initial-code H)))
      (threshold H)

  -- Theorem 4.5: all finiteness and interval hypotheses are explicit,
  -- the event uses graph-level 𝕊, and its literal Lebesgue measure is
  -- compared with δ.
  thm-4-5 : ∀ H →
    (∀ σ → Measurable (borel L)
      (GraphAcceptEvent (oracle H) σ (setₚ (initial-code H)))) ×
    (∀ σ → ThresholdLanguage H σ ↔
      ((σ ∈* Alphabet H) ×
       Above (GraphAcceptEvent (oracle H) σ
         (setₚ (initial-code H))) (threshold H)))
  thm-4-5 H =
    (λ σ → graph-accept-measurable
      (oracle H) σ (setₚ (initial-code H)))
    , λ σ → (λ p → p) , (λ p → p)

  ----------------------------------------------------------------------
  -- The fair, jointly independent oracle of §5
  ----------------------------------------------------------------------

  Coin : Bool → 𝒫ℕ
  Coin true  m = m ≡ zero
  Coin false m = m ≡ suc zero

  one≢zero : suc zero ≢ zero
  one≢zero ()

  coin-event-shape : ∀ b m →
    Coin b m ↔
    ((b ≡ true × m ≡ zero) ⊎
     (b ≡ false × m ≡ suc zero))
  coin-event-shape true m =
    (λ p → inj₁ (refl , p))
    , λ { (inj₁ (_ , p)) → p ; (inj₂ ((), _)) }
  coin-event-shape false m =
    (λ p → inj₂ (refl , p))
    , λ { (inj₁ ((), _)) ; (inj₂ (_ , p)) → p }

  coin-event : ℕ → ℕ → Event ([0,1] L)
  coin-event n m t =
    (digit L t n ≡ true × m ≡ zero) ⊎
    (digit L t n ≡ false × m ≡ suc zero)

  coin-event-measurable : ∀ n m →
    Measurable (borel L) (coin-event n m)
  coin-event-measurable n m =
    measurable-union (borel L)
      (measurable-inter (borel L)
        (digit-measurable L n true)
        (const-event-measurable (m ≡ zero)))
      (measurable-inter (borel L)
        (digit-measurable L n false)
        (const-event-measurable (m ≡ suc zero)))

  oracle-op : [0,1] L → 𝒫ℕ → 𝒫ℕ
  oracle-op t X m = Σ ℕ (λ n → X n × coin-event n m t)

  oracle-op-cont : ∀ t → Continuous₁ (oracle-op t)
  oracle-op-cont t X m = fwd , bwd
    where
      fwd : oracle-op t X m →
        Σ ℕ (λ k → (k ∈* X) × oracle-op t (setₚ k) m)
      fwd (n , Xn , coin) =
        singleton-seq n
        , subst (All X) (sym (members-singleton n)) (Xn , tt)
        , n
        , subst (n ∈-list_) (sym (members-singleton n)) here
        , coin

      bwd : Σ ℕ (λ k → (k ∈* X) × oracle-op t (setₚ k) m) →
        oracle-op t X m
      bwd (k , k∈ , n , n∈ , coin) =
        n , ∈*-∀ k X k∈ n n∈ , coin

  oracle-op-event-measurable : ∀ k m →
    Measurable (borel L) (λ t → oracle-op t (setₚ k) m)
  oracle-op-event-measurable k m =
    measurable-unionω (borel L) λ n →
      measurable-inter (borel L)
        (const-event-measurable (setₚ k n))
        (coin-event-measurable n m)

  𝕋-value : [0,1] L → 𝒫ℕ
  𝕋-value t = lam (oracle-op t)

  𝕋-coordinate : ∀ e →
    Measurable (borel L) (λ t → 𝕋-value t e)
  𝕋-coordinate e =
    measurable-union (borel L)
      (const-event-measurable (e ≡ zero))
      (measurable-unionω (borel L) λ k →
        measurable-unionω (borel L) λ m →
          measurable-inter (borel L)
            (const-event-measurable (e ≡ pair k m))
            (oracle-op-event-measurable k m))

  𝕋 : RandomVar
  𝕋 = random-var 𝕋-value 𝕋-coordinate

  coin-application : ∀ t n m →
    (value 𝕋 t · singleton n) m ↔ Coin (digit L t n) m
  coin-application t n m = fwd , bwd
    where
      lam-step : (value 𝕋 t · singleton n) m ↔
                 oracle-op t (singleton n) m
      lam-step =
        lam-app-fwd (oracle-op t) (oracle-op-cont t) (singleton n) m
        , lam-app-bwd (oracle-op t) (oracle-op-cont t) (singleton n) m

      lookup : oracle-op t (singleton n) m ↔ Coin (digit L t n) m
      lookup = lookup-fwd , lookup-bwd
        where
          lookup-fwd : oracle-op t (singleton n) m →
                       Coin (digit L t n) m
          lookup-fwd (j , refl , event) =
            proj₂ (coin-event-shape (digit L t n) m) event

          lookup-bwd : Coin (digit L t n) m →
                       oracle-op t (singleton n) m
          lookup-bwd p =
            n , refl , proj₁ (coin-event-shape (digit L t n) m) p

      fwd : (value 𝕋 t · singleton n) m →
            Coin (digit L t n) m
      fwd p = proj₁ lookup (proj₁ lam-step p)

      bwd : Coin (digit L t n) m →
            (value 𝕋 t · singleton n) m
      bwd p = proj₂ lam-step (proj₂ lookup p)

  coin-is-singleton : ∀ t n m →
    (value 𝕋 t · singleton n) m ↔
    ((digit L t n ≡ true × m ≡ zero) ⊎
     (digit L t n ≡ false × m ≡ suc zero))
  coin-is-singleton t n m =
    (λ p → proj₁ (coin-event-shape (digit L t n) m)
      (proj₁ (coin-application t n m) p))
    , (λ p → proj₂ (coin-application t n m)
      (proj₂ (coin-event-shape (digit L t n) m) p))

  coin-dichotomy : ∀ t n →
    (∀ m → (value 𝕋 t · singleton n) m ↔ m ≡ zero) ⊎
    (∀ m → (value 𝕋 t · singleton n) m ↔ m ≡ suc zero)
  coin-dichotomy t n with inspect (digit L t n)
  ... | true with≡ bit = inj₁ λ m →
    (λ p → subst (λ b → Coin b m) bit
      (proj₁ (coin-application t n m) p))
    , λ p → proj₂ (coin-application t n m)
      (subst (λ b → Coin b m) (sym bit) p)
  ... | false with≡ bit = inj₂ λ m →
    (λ p → subst (λ b → Coin b m) bit
      (proj₁ (coin-application t n m) p))
    , λ p → proj₂ (coin-application t n m)
      (subst (λ b → Coin b m) (sym bit) p)

  CoinZero : ℕ → Event ([0,1] L)
  CoinZero n = ⟦ 𝕋 ·ᵣ const-rv (singleton n) ≈
                  const-rv (singleton zero) ⟧

  coin-zero-fwd : ∀ n t → CoinZero n t → digit L t n ≡ true
  coin-zero-fwd n t eq with inspect (digit L t n)
  ... | true with≡ bit = bit
  ... | false with≡ bit =
    ⊥-elim (one≢zero (proj₁ eq (suc zero)
      (proj₂ (coin-is-singleton t n (suc zero))
        (inj₂ (bit , refl)))))

  coin-zero-bwd : ∀ n t →
    digit L t n ≡ true → CoinZero n t
  coin-zero-bwd n t bit =
    to-singleton , from-singleton
    where
      to-singleton : ∀ m →
        (value 𝕋 t · singleton n) m → m ≡ zero
      to-singleton m p with proj₁ (coin-is-singleton t n m) p
      ... | inj₁ (_ , m0) = m0
      ... | inj₂ (is-false , _) =
        ⊥-elim (true≢false (trans (sym bit) is-false))

      from-singleton : ∀ m →
        m ≡ zero → (value 𝕋 t · singleton n) m
      from-singleton m m0 =
        proj₂ (coin-is-singleton t n m) (inj₁ (bit , m0))

  coin-zero-digit : ∀ n t →
    CoinZero n t ↔ digit L t n ≡ true
  coin-zero-digit n t = coin-zero-fwd n t , coin-zero-bwd n t

  coin-half : ∀ n →
    measure (lebesgue L) (CoinZero n) ≡ ½# (probabilities L)
  coin-half n =
    trans (measure-resp (lebesgue L)
      (λ t → coin-zero-digit n t))
      (digit-half-true L n)

  CoinZeros : List ℕ → Event ([0,1] L)
  CoinZeros ns t = All (λ n → CoinZero n t) ns

  coin-zeros-digits : ∀ ns t →
    CoinZeros ns t ↔ DigitsEvent (digit L) ns (λ _ → true) t
  coin-zeros-digits [] t = (λ p → p) , (λ p → p)
  coin-zeros-digits (n ∷ ns) t =
    (λ p → proj₁ (coin-zero-digit n t) (proj₁ p)
           , proj₁ (coin-zeros-digits ns t) (proj₂ p))
    , (λ p → proj₂ (coin-zero-digit n t) (proj₁ p)
           , proj₂ (coin-zeros-digits ns t) (proj₂ p))

  coins-joint-independent : ∀ ns → NoDuplicates ns →
    measure (lebesgue L) (CoinZeros ns) ≡
    half-pow (probabilities L) (length ns)
  coins-joint-independent ns unique =
    trans (measure-resp (lebesgue L)
      (λ t → coin-zeros-digits ns t))
      (digit-joint-independent L ns unique (λ _ → true))
