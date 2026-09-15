{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Recursively enumerable predicates and computable graph operators
-- (PROGIC 2013, Definition 3.7 and Theorem 3.8, computability clause)
--
-- A proposition is r.e. when a total, fuel-indexed Boolean search
-- eventually returns true exactly when the proposition holds.  Since
-- Agda accepts only terminating definitions here, every search is an
-- effective semidecision procedure.
------------------------------------------------------------------------

module Scott2013.Computability.RE where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc) renaming (Nat to ℕ)
open import Agda.Builtin.Unit using (⊤; tt)

open import Scott2013.Prelude
open import Scott2013.GraphModel.Basic
open import Scott2013.GraphModel.Application
open import Scott2013.GraphModel.Combinators using (∇; lfp)

record Semi (P : Set) : Set where
  constructor semi
  field
    search   : ℕ → Bool
    sound    : ∀ {fuel} → search fuel ≡ true → P
    complete : P → Σ ℕ (λ fuel → search fuel ≡ true)

open Semi public

RESet : 𝒫ℕ → Set
RESet X = ∀ n → Semi (X n)

false≢true : false ≢ true
false≢true ()

semi-resp : ∀ {P Q} → (P ↔ Q) → Semi P → Semi Q
semi-resp (P→Q , Q→P) (semi s ok done) =
  semi s (λ eq → P→Q (ok eq)) (λ q → done (Q→P q))

semi-dec : ∀ (P : Set) → P ⊎ ¬ P → Semi P
semi-dec P (inj₁ p) =
  semi (λ _ → true) (λ _ → p) (λ _ → zero , refl)
semi-dec P (inj₂ ¬p) =
  semi (λ _ → false)
       (λ eq → ⊥-elim (false≢true eq))
       (λ p → ⊥-elim (¬p p))

_∧ᵇ_ : Bool → Bool → Bool
true  ∧ᵇ true  = true
true  ∧ᵇ false = false
false ∧ᵇ _     = false

∧ᵇ-true : ∀ a b → a ∧ᵇ b ≡ true → (a ≡ true) × (b ≡ true)
∧ᵇ-true true  true  _  = refl , refl
∧ᵇ-true true  false ()
∧ᵇ-true false true  ()
∧ᵇ-true false false ()

semi-× : ∀ {P Q} → Semi P → Semi Q → Semi (P × Q)
semi-× {P} {Q} (semi ps pok pcomplete) (semi qs qok qcomplete) =
  semi test (λ {fuel} eq → test-sound {fuel} eq) test-complete
  where
    test : ℕ → Bool
    test fuel =
      ps (proj₁ (unpair fuel)) ∧ᵇ qs (proj₂ (unpair fuel))

    test-sound : ∀ {fuel} → test fuel ≡ true → P × Q
    test-sound {fuel} eq =
      pok {fuel = proj₁ (unpair fuel)} (proj₁ (∧ᵇ-true
        (ps (proj₁ (unpair fuel)))
        (qs (proj₂ (unpair fuel))) eq))
      , qok {fuel = proj₂ (unpair fuel)} (proj₂ (∧ᵇ-true
        (ps (proj₁ (unpair fuel)))
        (qs (proj₂ (unpair fuel))) eq))

    test-complete : P × Q → Σ ℕ (λ fuel → test fuel ≡ true)
    test-complete (p , q) with pcomplete p | qcomplete q
    ... | fp , ep | fq , eq =
      pair fp fq , proof fp fq ep eq
      where
        proof : ∀ fp fq → ps fp ≡ true → qs fq ≡ true →
                test (pair fp fq) ≡ true
        proof fp fq ep eq rewrite unpair-pair fp fq | ep | eq = refl

semi-⊎ : ∀ {P Q} → Semi P → Semi Q → Semi (P ⊎ Q)
semi-⊎ {P} {Q} (semi ps pok pcomplete) (semi qs qok qcomplete) =
  semi test (λ {fuel} eq → test-sound {fuel} eq) test-complete
  where
    test : ℕ → Bool
    test fuel with unpair fuel
    ... | zero  , inner = ps inner
    ... | suc _ , inner = qs inner

    test-sound : ∀ {fuel} → test fuel ≡ true → P ⊎ Q
    test-sound {fuel} eq with unpair fuel
    ... | zero  , inner = inj₁ (pok {fuel = inner} eq)
    ... | suc _ , inner = inj₂ (qok {fuel = inner} eq)

    test-complete : P ⊎ Q → Σ ℕ (λ fuel → test fuel ≡ true)
    test-complete (inj₁ p) with pcomplete p
    ... | fp , ep = pair zero fp , proof fp ep
      where
        proof : ∀ fp → ps fp ≡ true → test (pair zero fp) ≡ true
        proof fp ep rewrite unpair-pair zero fp = ep
    test-complete (inj₂ q) with qcomplete q
    ... | fq , eq = pair (suc zero) fq , proof fq eq
      where
        proof : ∀ fq → qs fq ≡ true →
                test (pair (suc zero) fq) ≡ true
        proof fq eq rewrite unpair-pair (suc zero) fq = eq

semi-Σ : ∀ {P : ℕ → Set} → (∀ n → Semi (P n)) →
         Semi (Σ ℕ P)
semi-Σ {P} S =
  semi test (λ {fuel} eq → test-sound {fuel} eq) test-complete
  where
    test : ℕ → Bool
    test fuel =
      search (S (proj₁ (unpair fuel))) (proj₂ (unpair fuel))

    test-sound : ∀ {fuel} → test fuel ≡ true → Σ ℕ P
    test-sound {fuel} eq =
      proj₁ (unpair fuel)
      , sound (S (proj₁ (unpair fuel)))
          {fuel = proj₂ (unpair fuel)} eq

    test-complete : Σ ℕ P → Σ ℕ (λ fuel → test fuel ≡ true)
    test-complete (n , p) with complete (S n) p
    ... | fp , ep = pair n fp , proof n fp ep
      where
        proof : ∀ n fp → search (S n) fp ≡ true →
                test (pair n fp) ≡ true
        proof n fp ep rewrite unpair-pair n fp = ep

semi-All : ∀ {X : ℕ → Set} → RESet X → ∀ xs → Semi (All X xs)
semi-All RX []       = semi-dec ⊤ (inj₁ tt)
semi-All RX (x ∷ xs) = semi-× (RX x) (semi-All RX xs)

re-empty : RESet (λ _ → ⊥)
re-empty n = semi-dec ⊥ (inj₂ (λ p → p))

re-full : RESet (λ _ → ⊤)
re-full n = semi-dec ⊤ (inj₁ tt)

re-resp : ∀ {X Y} → (∀ n → X n ↔ Y n) → RESet X → RESet Y
re-resp eq RX n = semi-resp (eq n) (RX n)

re-union : ∀ {X Y} → RESet X → RESet Y → RESet (X ∪ₚ Y)
re-union RX RY n = semi-⊎ (RX n) (RY n)

re-inter : ∀ {X Y} → RESet X → RESet Y → RESet (X ∩ₚ Y)
re-inter RX RY n = semi-× (RX n) (RY n)

re-setₚ : ∀ n → RESet (setₚ n)
re-setₚ n m = semi-dec (m ∈-set n) (∈-list-dec m (members n))

re-singleton : ∀ n → RESet (λ m → m ≡ n)
re-singleton n m = semi-dec (m ≡ n) (ℕ-eq-dec m n)

-- Enumeration-operator application preserves recursive enumerability.
re-apply : ∀ {F X} → RESet F → RESet X → RESet (F · X)
re-apply RF RX m =
  semi-Σ λ n → semi-× (semi-All RX (members n)) (RF (pair n m))

-- λ-abstraction preserves recursive enumerability when every finite
-- instance of its body is uniformly r.e.
re-lam : ∀ {Φ : 𝒫ℕ → 𝒫ℕ} →
         (∀ n → RESet (Φ (setₚ n))) → RESet (lam Φ)
re-lam {Φ} RΦ k =
  semi-⊎
    (semi-dec (k ≡ zero) (ℕ-eq-dec k zero))
    (semi-Σ λ n → semi-Σ λ m →
      semi-×
        (semi-dec (k ≡ pair n m) (ℕ-eq-dec k (pair n m)))
        (RΦ n m))

------------------------------------------------------------------------
-- Definition 3.7
------------------------------------------------------------------------

record Computable₁ (Φ : 𝒫ℕ → 𝒫ℕ) : Set₁ where
  constructor computable₁
  field
    continuous₁ : Continuous₁ Φ
    graph-re₁   : RESet (lam Φ)

record Computable₂ (Φ : 𝒫ℕ → 𝒫ℕ → 𝒫ℕ) : Set₁ where
  constructor computable₂
  field
    continuous₂ : Continuous₂ Φ
    graph-re₂   : RESet (lam₂ Φ)

open Computable₁ public
open Computable₂ public

------------------------------------------------------------------------
-- Theorem 3.8: the least fixed point of a computable operator is r.e.
------------------------------------------------------------------------

∇-re : ∀ (Φ : 𝒫ℕ → 𝒫ℕ) → Continuous₁ Φ →
       RESet (lam Φ) → RESet (∇ Φ)
∇-re Φ Φc RΦ k =
  semi-⊎
    (semi-dec (k ≡ zero) (ℕ-eq-dec k zero))
    (semi-Σ λ n → semi-Σ λ m →
      semi-×
        (semi-dec (k ≡ pair n m) (ℕ-eq-dec k (pair n m)))
        (semi-resp
          (lam-app-fwd Φ Φc (setₚ n · setₚ n) m
          , lam-app-bwd Φ Φc (setₚ n · setₚ n) m)
          (re-apply RΦ (re-apply (re-setₚ n) (re-setₚ n)) m)))

thm-3-8-computable : ∀ (Φ : 𝒫ℕ → 𝒫ℕ) →
                     Computable₁ Φ → RESet (lfp Φ)
thm-3-8-computable Φ comp =
  re-apply
    (∇-re Φ (continuous₁ comp) (graph-re₁ comp))
    (∇-re Φ (continuous₁ comp) (graph-re₁ comp))
