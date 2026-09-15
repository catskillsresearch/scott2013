{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Independent finite deterministic automata
-- (standard side of PROGIC 2013, Theorem 4.4)
------------------------------------------------------------------------

module Scott2013.Automata.Finite where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (zero) renaming (Nat to ℕ)

open import Scott2013.Prelude
open import Scott2013.GraphModel.Basic

WordIn : 𝒫ℕ → List ℕ → Set
WordIn Alph xs = All Alph xs

seq-word : ∀ Alph σ → σ ∈* Alph ↔ WordIn Alph (members σ)
seq-word Alph σ = (λ p → p) , (λ p → p)

record DFA (Alph : 𝒫ℕ) : Set where
  constructor dfa
  field
    states       : List ℕ
    start        : ℕ
    start-state  : start ∈-list states
    step         : ℕ → ℕ → ℕ
    step-closed  : ∀ {q a} → q ∈-list states → Alph a →
                   step q a ∈-list states
    accepting    : ℕ → Bool

open DFA public

-- `members σ` stores the last symbol first.  Recursing into the tail
-- before stepping therefore executes Scott's word from left to right.
runDFA : ∀ {Alph} → DFA Alph → List ℕ → ℕ
runDFA M []       = start M
runDFA M (a ∷ as) = step M (runDFA M as) a

runDFA-closed : ∀ {Alph} (M : DFA Alph) xs →
  WordIn Alph xs → runDFA M xs ∈-list states M
runDFA-closed M []       _ = start-state M
runDFA-closed M (a ∷ as) (Aa , rest) =
  step-closed M (runDFA-closed M as rest) Aa

Accepts : ∀ {Alph} → DFA Alph → ℕ → Set
Accepts M σ = accepting M (runDFA M (members σ)) ≡ true

StandardRegular : (Alph L : 𝒫ℕ) → Set
StandardRegular Alph L =
  Finite Alph ×
  Σ (DFA Alph) (λ M →
    ∀ σ → L σ ↔ ((σ ∈* Alph) × Accepts M σ))

-- Lists and Scott sequence numbers are mutually inverse on words.
list→seq : List ℕ → ℕ
list→seq = encode-list

seq→list : ℕ → List ℕ
seq→list = members

list→seq→list : ∀ xs → seq→list (list→seq xs) ≡ xs
list→seq→list = members-encode-list
