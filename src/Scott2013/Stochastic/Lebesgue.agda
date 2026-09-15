{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Literal [0,1]-valued random graph elements (Definitions 4.1–4.2)
------------------------------------------------------------------------

module Scott2013.Stochastic.Lebesgue where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Unit using (tt)

open import Scott2013.Prelude
open import Scott2013.GraphModel.Basic
open import Scott2013.GraphModel.Application
open import Scott2013.MeasureTheory.Base
open import Scott2013.MeasureTheory.Lebesgue

module Relative (L : LebesgueUnitInterval) where

  I : Set
  I = [0,1] L

  record RandomVar : Set₁ where
    constructor random-var
    field
      value      : I → 𝒫ℕ
      coordinate : ∀ n → Measurable (borel L) (λ t → value t n)

  open RandomVar public

  const-measurable : ∀ (X : 𝒫ℕ) (n : ℕ) →
    Measurable (borel L) (λ _ → X n)
  const-measurable X n with classical L (X n)
  ... | inj₁ Xn =
      measurable-resp (borel L)
        (λ t → (λ _ → Xn) , λ _ → tt)
        (measurable-full (borel L))
  ... | inj₂ ¬Xn =
      measurable-resp (borel L)
        (λ t → (λ ()) , λ p → ⊥-elim (¬Xn p))
        (measurable-empty (borel L))

  const-rv : 𝒫ℕ → RandomVar
  const-rv X = random-var (λ _ → X) (const-measurable X)

  AllEvent : RandomVar → List ℕ → Event I
  AllEvent X xs t = All (value X t) xs

  all-measurable : ∀ X xs →
    Measurable (borel L) (AllEvent X xs)
  all-measurable X [] = measurable-full (borel L)
  all-measurable X (n ∷ ns) =
    measurable-inter (borel L)
      (coordinate X n) (all-measurable X ns)

  infixl 70 _·ᵣ_

  _·ᵣ_ : RandomVar → RandomVar → RandomVar
  X ·ᵣ Y = random-var
    (λ t → value X t · value Y t)
    λ m →
      measurable-unionω (borel L) λ n →
        measurable-inter (borel L)
          (all-measurable Y (members n))
          (coordinate X (pair n m))

  -- Theorem 4.2, literally on [0,1].
  thm-4-2 : ∀ X Y → RandomVar
  thm-4-2 X Y = X ·ᵣ Y

  infix 4 ⟦_≈_⟧

  ⟦_≈_⟧ : RandomVar → RandomVar → Event I
  ⟦ X ≈ Y ⟧ t =
    (∀ n → value X t n → value Y t n) ×
    (∀ n → value Y t n → value X t n)

  CoordEq : RandomVar → RandomVar → ℕ → Event I
  CoordEq X Y n t = value X t n ↔ value Y t n

  coord-eq-measurable : ∀ X Y n →
    Measurable (borel L) (CoordEq X Y n)
  coord-eq-measurable X Y n =
    measurable-resp (borel L)
      (λ t → proj₂ (eq t) , proj₁ (eq t))
      (measurable-union (borel L)
        (measurable-inter (borel L)
          (coordinate X n) (coordinate Y n))
        (measurable-inter (borel L)
          (measurable-compl (borel L) (coordinate X n))
          (measurable-compl (borel L) (coordinate Y n))))
    where
      eq : ∀ t → CoordEq X Y n t ↔
        ((value X t n × value Y t n) ⊎
         (¬ value X t n × ¬ value Y t n))
      eq t with classical L (value X t n) | classical L (value Y t n)
      ... | inj₁ x | inj₁ y =
        (λ _ → inj₁ (x , y))
        , λ _ → (λ _ → y) , (λ _ → x)
      ... | inj₁ x | inj₂ ny =
        (λ xy → ⊥-elim (ny (proj₁ xy x)))
        , λ { (inj₁ (_ , y)) → ⊥-elim (ny y)
            ; (inj₂ (nx , _)) → ⊥-elim (nx x) }
      ... | inj₂ nx | inj₁ y =
        (λ xy → ⊥-elim (nx (proj₂ xy y)))
        , λ { (inj₁ (x , _)) → ⊥-elim (nx x)
            ; (inj₂ (_ , ny)) → ⊥-elim (ny y) }
      ... | inj₂ nx | inj₂ ny =
        (λ _ → inj₂ (nx , ny))
        , λ _ →
            (λ x → ⊥-elim (nx x))
            , (λ y → ⊥-elim (ny y))

  equality-event-measurable : ∀ X Y →
    Measurable (borel L) ⟦ X ≈ Y ⟧
  equality-event-measurable X Y =
    measurable-resp (borel L) eq
      (measurable-interω (borel L)
        (λ n → coord-eq-measurable X Y n))
    where
      eq : ∀ t → (∀ n → CoordEq X Y n t) ↔ ⟦ X ≈ Y ⟧ t
      eq t =
        (λ all → (λ n → proj₁ (all n)) , λ n → proj₂ (all n))
        , λ inclusions n → proj₁ inclusions n , proj₂ inclusions n

  equality-probability : RandomVar → RandomVar →
    Value (probabilities L)
  equality-probability X Y = measure (lebesgue L) ⟦ X ≈ Y ⟧
