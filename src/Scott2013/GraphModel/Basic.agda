{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Graph-model encodings from *Stochastic λ-Calculi*
--
-- Primary source: Dana S. Scott, *Stochastic λ-calculi: An extended
-- abstract*, Journal of Applied Logic 12 (2014), 369–376 (PROGIC 2013).
-- Working PDF: sources/ScottPROGIC2013.pdf
--
-- This module records Scott's pairing function from §2. Later modules
-- will add sequence numbers, Kleene star, enumeration-operator
-- application, the graph-model λ-abstraction, and random variables
-- over P(ℕ).
------------------------------------------------------------------------

module Scott2013.GraphModel.Basic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat renaming (Nat to ℕ)

infixr 8 _^_

_^_ : ℕ → ℕ → ℕ
m ^ zero  = suc zero
m ^ suc n = m * (m ^ n)

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

-- Scott pairing (n, m) = 2^n (2m+1) (PROGIC 2013, §2).
pair : ℕ → ℕ → ℕ
pair n m = 2 ^ n * suc (m + m)

pow2-ne-zero : (n : ℕ) → (2 ^ n) ≢ 0
pow2-ne-zero zero ()
pow2-ne-zero (suc n) eq = pow2-ne-zero n (twice-zero (2 ^ n) eq)
  where
    twice-zero : (k : ℕ) → (2 * k) ≡ 0 → k ≡ 0
    twice-zero zero    _  = refl
    twice-zero (suc _) ()

-- The pairing lands in the positive integers; 0 is reserved for the
-- empty sequence number.
pair-ne-zero : (n m : ℕ) → pair n m ≢ 0
pair-ne-zero n m eq = pow2-ne-zero n (right-suc-zero (2 ^ n) (m + m) eq)
  where
    right-suc-zero : (a b : ℕ) → (a * suc b) ≡ 0 → a ≡ 0
    right-suc-zero zero    _ _  = refl
    right-suc-zero (suc _) _ ()
