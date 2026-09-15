{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Abstract measurable spaces and probability measures
------------------------------------------------------------------------

module Scott2013.MeasureTheory.Base where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Unit using (⊤)

open import Scott2013.Prelude

Event : Set → Set₁
Event Ω = Ω → Set

∅ᵉ : ∀ {Ω} → Event Ω
∅ᵉ _ = ⊥

Uᵉ : ∀ {Ω} → Event Ω
Uᵉ _ = ⊤

¬ᵉ_ : ∀ {Ω} → Event Ω → Event Ω
(¬ᵉ E) ω = ¬ E ω

_∪ᵉ_ : ∀ {Ω} → Event Ω → Event Ω → Event Ω
(E ∪ᵉ F) ω = E ω ⊎ F ω

_∩ᵉ_ : ∀ {Ω} → Event Ω → Event Ω → Event Ω
(E ∩ᵉ F) ω = E ω × F ω

⋃ᵉ : ∀ {Ω} → (ℕ → Event Ω) → Event Ω
⋃ᵉ E ω = Σ ℕ (λ n → E n ω)

⋂ᵉ : ∀ {Ω} → (ℕ → Event Ω) → Event Ω
⋂ᵉ E ω = ∀ n → E n ω

_≈ᵉ_ : ∀ {Ω} → Event Ω → Event Ω → Set
E ≈ᵉ F = ∀ ω → E ω ↔ F ω

record MeasurableSpace (Ω : Set) : Set₁ where
  field
    Measurable       : Event Ω → Set
    measurable-empty : Measurable ∅ᵉ
    measurable-full  : Measurable Uᵉ
    measurable-compl : ∀ {E} → Measurable E → Measurable (¬ᵉ E)
    measurable-union : ∀ {E F} → Measurable E → Measurable F →
                       Measurable (E ∪ᵉ F)
    measurable-inter : ∀ {E F} → Measurable E → Measurable F →
                       Measurable (E ∩ᵉ F)
    measurable-unionω : ∀ {E : ℕ → Event Ω} →
                        (∀ n → Measurable (E n)) →
                        Measurable (⋃ᵉ E)
    measurable-interω : ∀ {E : ℕ → Event Ω} →
                        (∀ n → Measurable (E n)) →
                        Measurable (⋂ᵉ E)
    measurable-resp  : ∀ {E F} → E ≈ᵉ F →
                       Measurable E → Measurable F

open MeasurableSpace public

record ProbabilityValues : Set₁ where
  field
    Value    : Set
    0# 1# ½# : Value
    less-than less-equal : Value → Value → Set
    Σ#       : (ℕ → Value) → Value
    half-pow : ℕ → Value
    half-pow-zero : half-pow zero ≡ 1#
    half-pow-one  : half-pow (suc zero) ≡ ½#

open ProbabilityValues public

PairwiseDisjoint : ∀ {Ω} → (ℕ → Event Ω) → Set
PairwiseDisjoint E =
  ∀ i j → i ≢ j → ∀ ω → ¬ (E i ω × E j ω)

record ProbabilityMeasure {Ω : Set}
  (M : MeasurableSpace Ω) (V : ProbabilityValues) : Set₁ where
  field
    measure       : Event Ω → Value V
    measure-empty : measure ∅ᵉ ≡ 0# V
    measure-full  : measure Uᵉ ≡ 1# V
    measure-resp  : ∀ {E F} → E ≈ᵉ F →
                    measure E ≡ measure F
    countable-additivity :
      ∀ {E : ℕ → Event Ω} →
      (∀ n → Measurable M (E n)) → PairwiseDisjoint E →
      measure (⋃ᵉ E) ≡ Σ# V (λ n → measure (E n))

open ProbabilityMeasure public

record MeasurableMap {Ω Ω′ : Set}
  (M : MeasurableSpace Ω) (M′ : MeasurableSpace Ω′)
  (f : Ω → Ω′) : Set₁ where
  field
    measurable-preimage : ∀ {E} → Measurable M′ E →
                          Measurable M (λ ω → E (f ω))
