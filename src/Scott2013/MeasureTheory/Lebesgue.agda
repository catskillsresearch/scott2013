{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Safe relative interface for literal [0,1] with Lebesgue measure
--
-- Constructive Agda does not manufacture the classical binary expansion
-- choice at dyadic points.  Results in §§4–5 therefore quantify over this
-- explicit structure and its laws; no unchecked axiom is used.
------------------------------------------------------------------------

module Scott2013.MeasureTheory.Lebesgue where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Scott2013.Prelude
open import Scott2013.MeasureTheory.Base

DigitEvent : ∀ {I} → (I → ℕ → Bool) → ℕ → Bool → Event I
DigitEvent digit n b t = digit t n ≡ b

DigitsEvent : ∀ {I} → (I → ℕ → Bool) →
              List ℕ → (ℕ → Bool) → Event I
DigitsEvent digit ns bits t =
  All (λ n → digit t n ≡ bits n) ns

record LebesgueUnitInterval : Set₂ where
  field
    [0,1]       : Set
    probabilities : ProbabilityValues
    borel       : MeasurableSpace [0,1]
    lebesgue    : ProbabilityMeasure borel probabilities
    classical   : (P : Set) → P ⊎ ¬ P

    -- Dyadic intervals witness the intended literal Lebesgue model.
    dyadic      : ℕ → ℕ → Event [0,1]
    dyadic-measurable : ∀ level index →
      Measurable borel (dyadic level index)
    dyadic-measure : ∀ level index →
      measure lebesgue (dyadic level index) ≡
      half-pow probabilities level

    -- A total classical binary expansion, with an explicit convention
    -- already chosen at dyadic boundary points.
    digit       : [0,1] → ℕ → Bool
    digit-measurable : ∀ n b →
      Measurable borel (DigitEvent digit n b)
    digit-half-true : ∀ n →
      measure lebesgue (DigitEvent digit n true) ≡
      ½# probabilities
    digit-half-false : ∀ n →
      measure lebesgue (DigitEvent digit n false) ≡
      ½# probabilities

    -- Every finite family of distinct digits is jointly fair.
    digit-joint-independent :
      ∀ ns → NoDuplicates ns → ∀ bits →
      measure lebesgue (DigitsEvent digit ns bits) ≡
      half-pow probabilities (length ns)

open LebesgueUnitInterval public

module On (L : LebesgueUnitInterval) where
  I : Set
  I = [0,1] L

  Borel : Event I → Set
  Borel = Measurable (borel L)

  #_ : Event I → Value (probabilities L)
  # E = measure (lebesgue L) E
