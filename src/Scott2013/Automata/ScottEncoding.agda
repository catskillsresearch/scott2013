{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Scott finite graphs as ordinary finite automata (Theorem 4.4)
------------------------------------------------------------------------

module Scott2013.Automata.ScottEncoding where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc) renaming (Nat to ℕ)
open import Agda.Builtin.Unit using (tt)

open import Scott2013.Prelude
open import Scott2013.GraphModel.Basic
open import Scott2013.GraphModel.Application
open import Scott2013.GraphModel.Combinators
open import Scott2013.GraphModel.Sequentializer
open import Scott2013.Automata.Finite

memberᵇ : ℕ → List ℕ → Bool
memberᵇ n [] = false
memberᵇ n (x ∷ xs) with ℕ-eq-dec n x
... | inj₁ _ = true
... | inj₂ _ = memberᵇ n xs

memberᵇ-true : ∀ n xs → memberᵇ n xs ≡ true ↔ n ∈-list xs
memberᵇ-true n [] = (λ ()) , (λ ())
memberᵇ-true n (x ∷ xs) with ℕ-eq-dec n x
... | inj₁ refl = (λ _ → here) , (λ _ → refl)
... | inj₂ ne =
  (λ p → there (proj₁ (memberᵇ-true n xs) p))
  , λ { here → ⊥-elim (ne refl)
      ; (there p) → proj₂ (memberᵇ-true n xs) p }

dec-× : ∀ {P Q : Set} → P ⊎ ¬ P → Q ⊎ ¬ Q →
        (P × Q) ⊎ ¬ (P × Q)
dec-× (inj₁ p) (inj₁ q) = inj₁ (p , q)
dec-× (inj₂ np) _       = inj₂ λ pq → np (proj₁ pq)
dec-× _       (inj₂ nq) = inj₂ λ pq → nq (proj₂ pq)

entry-input : ℕ → ℕ
entry-input e = proj₁ (unpair e)

entry-inner : ℕ → ℕ
entry-inner e = proj₂ (unpair e)

entry-state : ℕ → ℕ
entry-state e = proj₁ (unpair (entry-inner e))

entry-output : ℕ → ℕ
entry-output e = proj₂ (unpair (entry-inner e))

Good : ℕ → ℕ → ℕ → Set
Good e a q =
  (pair (entry-input e) (entry-inner e) ≡ e) ×
  (pair (entry-state e) (entry-output e) ≡ entry-inner e) ×
  (entry-input e ∈* singleton a) ×
  (entry-state e ∈* setₚ q)

good-dec : ∀ e a q → Good e a q ⊎ ¬ Good e a q
good-dec e a q =
  dec-× (ℕ-eq-dec (pair (entry-input e) (entry-inner e)) e)
  (dec-×
    (ℕ-eq-dec (pair (entry-state e) (entry-output e))
      (entry-inner e))
    (dec-×
      (All-dec (singleton a) (λ x → ℕ-eq-dec x a)
        (members (entry-input e)))
      (All-dec (setₚ q) (λ x → ∈-list-dec x (members q))
        (members (entry-state e)))))

step-selected : ℕ → ℕ → ℕ → List ℕ
step-selected A a q = select (λ e → Good e a q)
  (λ e → good-dec e a q) (members A)

stepCode : ℕ → ℕ → ℕ → ℕ
stepCode A a q = encode-list (map entry-output (step-selected A a q))

stepCode-correct : ∀ A a q x →
  (((setₚ A · singleton a) · setₚ q) x) ↔
  setₚ (stepCode A a q) x
stepCode-correct A a q x = fwd , bwd
  where
    fwd : (((setₚ A · singleton a) · setₚ q) x) →
          setₚ (stepCode A a q) x
    fwd (k , k∈q , n , n∈a , entry) =
      subst (x ∈-list_) (sym (members-encode-list outputs))
        (subst (_∈-list outputs) out-eq
          (map-∈ entry-output selected selected-entry))
      where
        e = pair n (pair k x)
        selected = step-selected A a q
        outputs = map entry-output selected

        good : Good e a q
        good rewrite unpair-pair n (pair k x) | unpair-pair k x =
          refl , refl , n∈a , k∈q

        selected-entry : e ∈-list selected
        selected-entry =
          select-complete (λ z → Good z a q)
            (λ z → good-dec z a q) (members A) entry good

        out-eq : entry-output e ≡ x
        out-eq rewrite unpair-pair n (pair k x) | unpair-pair k x = refl

    bwd : setₚ (stepCode A a q) x →
          (((setₚ A · singleton a) · setₚ q) x)
    bwd x∈ with
      map-∈-split entry-output (step-selected A a q)
        (subst (x ∈-list_) (members-encode-list
          (map entry-output (step-selected A a q))) x∈)
    ... | e , e∈selected , out-eq =
      entry-state e
      , proj₂ (proj₂ (proj₂ good))
      , entry-input e
      , proj₁ (proj₂ (proj₂ good))
      , subst (_∈-list members A) (sym entry-eq) e∈A
      where
        selected-info =
          select-sound (λ z → Good z a q)
            (λ z → good-dec z a q) (members A) e∈selected
        e∈A = proj₁ selected-info
        good = proj₂ selected-info

        inner-eq : pair (entry-state e) x ≡ entry-inner e
        inner-eq =
          trans (cong (pair (entry-state e)) (sym out-eq))
                (proj₁ (proj₂ good))

        entry-eq :
          pair (entry-input e) (pair (entry-state e) x) ≡ e
        entry-eq =
          trans (cong (pair (entry-input e)) inner-eq)
                (proj₁ good)

scottStates : ℕ → ℕ → List ℕ
scottStates A q =
  q ∷ map (λ es → encode-list (map entry-output es))
          (sublists (members A))

ScottDFA : ∀ (Alph : 𝒫ℕ) → ℕ → ℕ → DFA Alph
ScottDFA Alph A q = dfa
  (scottStates A q)
  q
  here
  (λ s a → stepCode A a s)
  (λ {s} {a} s∈ Aa →
    there (map-∈
      (λ es → encode-list (map entry-output es))
      (sublists (members A))
      (select-sublists (λ e → Good e a s)
        (λ e → good-dec e a s) (members A))))
  (λ s → memberᵇ zero (members s))

run-scott : ∀ Alph A q xs x →
  run (setₚ A) xs (setₚ q) x ↔
  setₚ (runDFA (ScottDFA Alph A q) xs) x
run-scott Alph A q [] x = (λ p → p) , (λ p → p)
run-scott Alph A q (a ∷ xs) x =
  (λ p → proj₁ (stepCode-correct A a
      (runDFA (ScottDFA Alph A q) xs) x)
    (proj₁ (app-resp-right (setₚ A · singleton a)
      (run-scott Alph A q xs) x) p))
  , (λ p → proj₂ (app-resp-right (setₚ A · singleton a)
      (run-scott Alph A q xs) x)
    (proj₂ (stepCode-correct A a
      (runDFA (ScottDFA Alph A q) xs) x) p))

-- Scott representation implies ordinary finite-state regularity.
scott→standard : ∀ Alph L → RegularIn Alph L →
                 StandardRegular Alph L
scott→standard Alph L (finAlph , A , q , represents) =
  finAlph , ScottDFA Alph A q , λ σ → fwd σ , bwd σ
  where
    fwd : ∀ σ → L σ →
      (σ ∈* Alph) × Accepts (ScottDFA Alph A q) σ
    fwd σ Lσ =
      proj₁ accepted-data
      , proj₂ (memberᵇ-true zero
          (members (runDFA (ScottDFA Alph A q) (members σ))))
          (proj₁ (run-scott Alph A q (members σ) zero)
            (proj₂ accepted-data))
      where
        accepted-data = proj₁ (represents σ) Lσ

    bwd : ∀ σ →
      (σ ∈* Alph) × Accepts (ScottDFA Alph A q) σ → L σ
    bwd σ (word , accepted) =
      proj₂ (represents σ)
        (word
        , proj₂ (run-scott Alph A q (members σ) zero)
            (proj₁ (memberᵇ-true zero
              (members (runDFA (ScottDFA Alph A q) (members σ))))
              accepted))

------------------------------------------------------------------------
-- Ordinary DFA to a finite Scott graph
------------------------------------------------------------------------

state-list : ∀ {Alph} → DFA Alph → ℕ → List ℕ
state-list M q with accepting M q
... | true  = suc q ∷ zero ∷ []
... | false = suc q ∷ []

state-self : ∀ {Alph} (M : DFA Alph) q →
             suc q ∈-list state-list M q
state-self M q with accepting M q
... | true  = here
... | false = here

state-suc-only : ∀ {Alph} (M : DFA Alph) q r →
  suc r ∈-list state-list M q → r ≡ q
state-suc-only M q r p with accepting M q
state-suc-only M q .q here      | true = refl
state-suc-only M q r (there (there ())) | true
state-suc-only M q .q here      | false = refl
state-suc-only M q r (there ()) | false

state-zero : ∀ {Alph} (M : DFA Alph) q →
  zero ∈-list state-list M q ↔ accepting M q ≡ true
state-zero M q with accepting M q
... | true =
  (λ _ → refl) , (λ _ → there here)
... | false =
  (λ { (there ()) }) , (λ ())

dfa-entry : ℕ → ℕ → ℕ → ℕ
dfa-entry q a x =
  pair (singleton-seq a) (pair (singleton-seq (suc q)) x)

dfa-entries : ∀ {Alph} → DFA Alph → ℕ → ℕ → List ℕ
dfa-entries M q a =
  map (dfa-entry q a) (state-list M (step M q a))

dfa-graph-list : ∀ {Alph} → DFA Alph → List ℕ → List ℕ
dfa-graph-list M alphabet =
  concatMap (λ q → concatMap (dfa-entries M q) alphabet) (states M)

dfa-graph-code : ∀ {Alph} → DFA Alph → List ℕ → ℕ
dfa-graph-code M alphabet = encode-list (dfa-graph-list M alphabet)

dfa-start-code : ∀ {Alph} → DFA Alph → ℕ
dfa-start-code M = encode-list (state-list M (start M))

dfa-step-correct : ∀ {Alph} (M : DFA Alph) alphabet →
  (∀ a → Alph a ↔ a ∈-list alphabet) →
  ∀ q a x → q ∈-list states M → Alph a →
  (((setₚ (dfa-graph-code M alphabet) · singleton a) ·
      setₚ (encode-list (state-list M q))) x)
  ↔ x ∈-list state-list M (step M q a)
dfa-step-correct M alphabet alph q a x q∈ Aa = fwd , bwd
  where
    Acode = dfa-graph-code M alphabet
    qcode = encode-list (state-list M q)

    a∈ : a ∈-list alphabet
    a∈ = proj₁ (alph a) Aa

    fwd : (((setₚ Acode · singleton a) · setₚ qcode) x) →
          x ∈-list state-list M (step M q a)
    fwd (k , k∈q , n , n∈a , entry∈) with
      ∈-concatMap (λ q′ → concatMap (dfa-entries M q′) alphabet)
        (states M)
        (subst (pair n (pair k x) ∈-list_)
          (members-encode-list (dfa-graph-list M alphabet)) entry∈)
    ... | q′ , q′∈ , in-q with
      ∈-concatMap (dfa-entries M q′) alphabet in-q
    ... | a′ , a′∈ , in-a with
      map-∈-split (dfa-entry q′ a′)
        (state-list M (step M q′ a′)) in-a
    ... | x′ , x′∈ , stored-eq =
      subst (λ z → z ∈-list (state-list M (step M q a)))
        (sym x-eq)
        (subst (λ s → x′ ∈-list state-list M s) step-eq x′∈)
      where
        outer = pair-injective n (pair k x)
          (singleton-seq a′) (pair (singleton-seq (suc q′)) x′)
          (sym stored-eq)
        n-eq = proj₁ outer
        inner = pair-injective k x (singleton-seq (suc q′)) x′
          (proj₂ outer)
        k-eq = proj₁ inner
        x-eq = proj₂ inner

        a′∈n : a′ ∈-set n
        a′∈n =
          subst (a′ ∈-list_)
            (sym (trans (cong members n-eq) (members-singleton a′)))
            here
        a′-eq : a′ ≡ a
        a′-eq = ∈*-∀ n (singleton a) n∈a a′ a′∈n

        sq′∈k : suc q′ ∈-set k
        sq′∈k =
          subst (suc q′ ∈-list_)
            (sym (trans (cong members k-eq)
              (members-singleton (suc q′)))) here
        sq′∈state : suc q′ ∈-list state-list M q
        sq′∈state =
          subst (suc q′ ∈-list_)
            (members-encode-list (state-list M q))
            (∈*-∀ k (setₚ qcode) k∈q (suc q′) sq′∈k)
        q′-eq : q′ ≡ q
        q′-eq = state-suc-only M q q′ sq′∈state

        step-eq : step M q′ a′ ≡ step M q a
        step-eq = cong₂ (step M) q′-eq a′-eq

    bwd : x ∈-list state-list M (step M q a) →
          (((setₚ Acode · singleton a) · setₚ qcode) x)
    bwd x∈ =
      singleton-seq (suc q)
      , subst (All (setₚ qcode))
          (sym (members-singleton (suc q)))
          (subst (suc q ∈-list_) (sym (members-encode-list
            (state-list M q))) (state-self M q) , tt)
      , singleton-seq a
      , subst (All (singleton a)) (sym (members-singleton a))
          (refl , tt)
      , subst (entry ∈-list_) (sym (members-encode-list graph-list))
          (concatMap-∈
            (λ q′ → concatMap (dfa-entries M q′) alphabet)
            (states M) q∈
            (concatMap-∈ (dfa-entries M q) alphabet a∈
              (map-∈ (dfa-entry q a)
                (state-list M (step M q a)) x∈)))
      where
        entry = dfa-entry q a x
        graph-list = dfa-graph-list M alphabet

dfa-run-scott : ∀ {Alph} (M : DFA Alph) alphabet →
  (∀ a → Alph a ↔ a ∈-list alphabet) →
  ∀ xs → WordIn Alph xs → ∀ x →
  run (setₚ (dfa-graph-code M alphabet)) xs
      (setₚ (dfa-start-code M)) x
  ↔ setₚ (encode-list (state-list M (runDFA M xs))) x
dfa-run-scott M alphabet alph [] word x = (λ p → p) , (λ p → p)
dfa-run-scott M alphabet alph (a ∷ xs) (Aa , rest) x =
  (λ p → subst (x ∈-list_)
      (sym (members-encode-list
        (state-list M (step M (runDFA M xs) a))))
    (proj₁ (dfa-step-correct M alphabet alph
      (runDFA M xs) a x (runDFA-closed M xs rest) Aa)
      (proj₁ (app-resp-right
        (setₚ (dfa-graph-code M alphabet) · singleton a)
        (λ y → dfa-run-scott M alphabet alph xs rest y) x) p)))
  , (λ p → proj₂ (app-resp-right
      (setₚ (dfa-graph-code M alphabet) · singleton a)
      (λ y → dfa-run-scott M alphabet alph xs rest y) x)
    (proj₂ (dfa-step-correct M alphabet alph
      (runDFA M xs) a x (runDFA-closed M xs rest) Aa)
      (subst (x ∈-list_)
        (members-encode-list
          (state-list M (step M (runDFA M xs) a))) p)))

-- Ordinary finite-state regularity implies Scott representation.
standard→scott : ∀ Alph L → StandardRegular Alph L →
                 RegularIn Alph L
standard→scott Alph L (finAlph , M , recognizes) =
  finAlph
  , dfa-graph-code M alphabet
  , dfa-start-code M
  , λ σ → fwd σ , bwd σ
  where
    alphabet = members (proj₁ finAlph)
    alph : ∀ a → Alph a ↔ a ∈-list alphabet
    alph a = proj₂ finAlph a

    fwd : ∀ σ → L σ →
      (σ ∈* Alph) ×
      𝕊-apply (setₚ (dfa-graph-code M alphabet)) σ
        (setₚ (dfa-start-code M)) zero
    fwd σ Lσ =
      word
      , proj₂ (dfa-run-scott M alphabet alph (members σ) word zero)
          (subst (zero ∈-list_)
            (sym (members-encode-list
              (state-list M (runDFA M (members σ)))))
            (proj₂ (state-zero M (runDFA M (members σ))) accepted))
      where
        data′ = proj₁ (recognizes σ) Lσ
        word = proj₁ data′
        accepted = proj₂ data′

    bwd : ∀ σ →
      (σ ∈* Alph) ×
      𝕊-apply (setₚ (dfa-graph-code M alphabet)) σ
        (setₚ (dfa-start-code M)) zero → L σ
    bwd σ (word , run0) =
      proj₂ (recognizes σ)
        (word
        , proj₁ (state-zero M (runDFA M (members σ)))
            (subst (zero ∈-list_)
              (members-encode-list
                (state-list M (runDFA M (members σ))))
              (proj₁ (dfa-run-scott M alphabet alph
                (members σ) word zero) run0)))

-- The exact "if and only if" of Theorem 4.4.
thm-4-4 : ∀ Alph L → StandardRegular Alph L ↔ RegularIn Alph L
thm-4-4 Alph L =
  standard→scott Alph L , scott→standard Alph L
