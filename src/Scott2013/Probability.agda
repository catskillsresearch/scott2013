{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Probability space: Cantor space 2^ℕ in place of [0,1]
--
-- Scott (PROGIC 2013, §4): "We use the unit interval here as a standard
-- probability space. Any other convenient probability space (along with
-- its given measure) could have been used for this discussion."
--
-- In constructive univalent mathematics, Lebesgue measure on [0,1] is
-- heavy. Cantor space Ω = ℕ → Bool is already first-class in
-- TypeTopology (Escardó), so we take it as the sample space and generate
-- a σ-algebra of Borel codes from coordinate events {ω | ω n ≡ b}.
-- There are no postulates: measurability is interpreted by the codes.
------------------------------------------------------------------------

module Scott2013.Probability where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc) renaming (Nat to ℕ)
open import Agda.Builtin.Unit using (⊤; tt)

open import Scott2013.Prelude

-- Infinite streams of coin tosses.
Ω : Set
Ω = ℕ → Bool

------------------------------------------------------------------------
-- Borel codes on Cantor space
------------------------------------------------------------------------

data Borel : Set where
  emptyᵇ : Borel
  fullᵇ  : Borel
  coordᵇ : ℕ → Bool → Borel
  complᵇ : Borel → Borel
  unionᵇ : (ℕ → Borel) → Borel
  interᵇ : (ℕ → Borel) → Borel

⟦_⟧ : Borel → Ω → Set
⟦ emptyᵇ ⟧    ω = ⊥
⟦ fullᵇ ⟧     ω = ⊤
⟦ coordᵇ n b ⟧ ω = ω n ≡ b
⟦ complᵇ B ⟧  ω = ¬ ⟦ B ⟧ ω
⟦ unionᵇ F ⟧  ω = Σ ℕ (λ k → ⟦ F k ⟧ ω)
⟦ interᵇ F ⟧  ω = ∀ k → ⟦ F k ⟧ ω

-- A predicate is measurable when it is equivalent to a Borel code.
Measurable : (Ω → Set) → Set
Measurable E = Σ Borel (λ B → ∀ ω → E ω ↔ ⟦ B ⟧ ω)

------------------------------------------------------------------------
-- σ-algebra operations (no postulates)
------------------------------------------------------------------------

meas-empty : Measurable (λ _ → ⊥)
meas-empty = emptyᵇ , λ ω → (λ ()) , (λ ())

meas-full : Measurable (λ _ → ⊤)
meas-full = fullᵇ , λ ω → (λ _ → tt) , (λ _ → tt)

meas-coord : ∀ n b → Measurable (λ ω → ω n ≡ b)
meas-coord n b = coordᵇ n b , λ ω → (λ x → x) , (λ x → x)

meas-compl : ∀ {E} → Measurable E → Measurable (λ ω → ¬ E ω)
meas-compl (B , eq) = complᵇ B , λ ω →
  (λ ¬E ¬B → ¬E (proj₂ (eq ω) ¬B)) ,
  (λ ¬B  E → ¬B (proj₁ (eq ω) E))

meas-union : ∀ {E : ℕ → Ω → Set} →
             (∀ k → Measurable (E k)) →
             Measurable (λ ω → Σ ℕ (λ k → E k ω))
meas-union M =
  unionᵇ (λ k → proj₁ (M k)) , λ ω →
    (λ (k , e) → k , proj₁ (proj₂ (M k) ω) e) ,
    (λ (k , b) → k , proj₂ (proj₂ (M k) ω) b)

meas-inter-countable : ∀ {E : ℕ → Ω → Set} →
                       (∀ k → Measurable (E k)) →
                       Measurable (λ ω → ∀ k → E k ω)
meas-inter-countable M =
  interᵇ (λ k → proj₁ (M k)) , λ ω →
    (λ f k → proj₁ (proj₂ (M k) ω) (f k)) ,
    (λ f k → proj₂ (proj₂ (M k) ω) (f k))

meas-inter : ∀ {E₁ E₂} →
             Measurable E₁ → Measurable E₂ →
             Measurable (λ ω → E₁ ω × E₂ ω)
meas-inter (B₁ , e₁) (B₂ , e₂) =
  interᵇ (λ { zero → B₁ ; (suc _) → B₂ }) , λ ω →
    (λ (p , q) → λ { zero → proj₁ (e₁ ω) p ; (suc _) → proj₁ (e₂ ω) q }) ,
    (λ f → proj₂ (e₁ ω) (f zero) , proj₂ (e₂ ω) (f (suc zero)))

meas-⊎ : ∀ {E₁ E₂} →
         Measurable E₁ → Measurable E₂ →
         Measurable (λ ω → E₁ ω ⊎ E₂ ω)
meas-⊎ (B₁ , e₁) (B₂ , e₂) =
  unionᵇ (λ { zero → B₁ ; (suc _) → B₂ }) , λ ω →
    (λ { (inj₁ p) → zero , proj₁ (e₁ ω) p
       ; (inj₂ q) → suc zero , proj₁ (e₂ ω) q }) ,
    (λ { (zero  , b) → inj₁ (proj₂ (e₁ ω) b)
       ; (suc _ , b) → inj₂ (proj₂ (e₂ ω) b) })

-- Constant events {ω | x ≡ y}, using decidable equality on ℕ.
meas-const-≡ : ∀ (x y : ℕ) → Measurable (λ _ → x ≡ y)
meas-const-≡ x y with ℕ-eq-dec x y
... | inj₁ eq = fullᵇ  , λ ω → (λ _ → tt) , (λ _ → eq)
... | inj₂ ne = emptyᵇ , λ ω → (λ e → ne e) , (λ ())
