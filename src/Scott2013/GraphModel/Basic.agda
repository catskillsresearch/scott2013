{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Graph-model encodings from *Stochastic λ-Calculi* §2
--
-- Primary source: Dana S. Scott, *Stochastic λ-calculi: An extended
-- abstract*, Journal of Applied Logic 12 (2014), 369–376 (PROGIC 2013).
-- Working PDF: sources/ScottPROGIC2013.pdf
--
-- Pairing (n, m) = 2^n (2m+1), sequence numbers, set(n), Kleene star.
------------------------------------------------------------------------

module Scott2013.GraphModel.Basic where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc; _+_; _*_) renaming (Nat to ℕ)
open import Agda.Builtin.Unit using (⊤; tt)

open import Scott2013.Prelude

------------------------------------------------------------------------
-- Exponentiation and Scott pairing
------------------------------------------------------------------------

infixr 8 _^_

_^_ : ℕ → ℕ → ℕ
m ^ zero  = suc zero
m ^ suc n = m * (m ^ n)

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

pair-ne-zero : (n m : ℕ) → pair n m ≢ 0
pair-ne-zero n m eq = pow2-ne-zero n (right-suc-zero (2 ^ n) (m + m) eq)
  where
    right-suc-zero : (a b : ℕ) → (a * suc b) ≡ 0 → a ≡ 0
    right-suc-zero zero    _ _  = refl
    right-suc-zero (suc _) _ ()

------------------------------------------------------------------------
-- Arithmetic for pairing
------------------------------------------------------------------------

+-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
+-assoc zero    b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

*-suc : ∀ k j → k * suc j ≡ k + k * j
*-suc zero    j = refl
*-suc (suc k) j = cong suc (begin
  j + k * suc j        ≡⟨ cong (j +_) (*-suc k j) ⟩
  j + (k + k * j)      ≡⟨ sym (+-assoc j k (k * j)) ⟩
  (j + k) + k * j      ≡⟨ cong (_+ k * j) (+-comm j k) ⟩
  (k + j) + k * j      ≡⟨ +-assoc k j (k * j) ⟩
  k + (j + k * j)      ∎)

*-distribʳ : ∀ a b c → (a + b) * c ≡ a * c + b * c
*-distribʳ zero    b c = refl
*-distribʳ (suc a) b c =
  trans (cong (c +_) (*-distribʳ a b c)) (sym (+-assoc c (a * c) (b * c)))

*-assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)
*-assoc zero    b c = refl
*-assoc (suc a) b c =
  trans (*-distribʳ b (a * b) c) (cong ((b * c) +_) (*-assoc a b c))

pair-double : ∀ n m → pair (suc n) m ≡ pair n m + pair n m
pair-double n m =
  trans (*-assoc (suc (suc zero)) (2 ^ n) (suc (m + m)))
        (cong (pair n m +_) (+-zero (pair n m)))

pair-zero : ∀ m → pair zero m ≡ suc (m + m)
pair-zero m = +-zero (suc (m + m))

pair-is-suc : ∀ n m → Σ ℕ (λ k → pair n m ≡ suc k)
pair-is-suc zero    m = (m + m) , pair-zero m
pair-is-suc (suc n) m with pair-is-suc n m
... | k , eq = suc (k + k) ,
  trans (pair-double n m)
        (trans (cong₂ _+_ eq eq) (suc-double k))

------------------------------------------------------------------------
-- Order lemmas used by unpairing
------------------------------------------------------------------------

≤-suc : {m n : ℕ} → m ≤ n → m ≤ suc n
≤-suc z≤n     = z≤n
≤-suc (s≤s p) = s≤s (≤-suc p)

n≤n+m : ∀ n m → n ≤ n + m
n≤n+m zero    m = z≤n
n≤n+m (suc n) m = s≤s (n≤n+m n m)

m≤n+m : ∀ n m → m ≤ n + m
m≤n+m zero    m = ≤-refl
m≤n+m (suc n) m = ≤-suc (m≤n+m n m)

n≤n+n : ∀ n → n ≤ n + n
n≤n+n n = n≤n+m n n

≤-+-mono : {a b c d : ℕ} → a ≤ c → b ≤ d → a + b ≤ c + d
≤-+-mono {b = b} {c = c} {d = d} z≤n q = ≤-trans q (m≤n+m c d)
≤-+-mono (s≤s p) q = s≤s (≤-+-mono p q)

div2-≤ : ∀ n → div2 n ≤ n
div2-≤ zero          = z≤n
div2-≤ (suc zero)    = z≤n
div2-≤ (suc (suc n)) = s≤s (≤-suc (div2-≤ n))

div2-suc-suc-< : ∀ n → suc (div2 n) < suc (suc n)
div2-suc-suc-< n = s≤s (s≤s (div2-≤ n))

pow2-ge-suc : ∀ n → suc n ≤ (2 ^ n)
pow2-ge-suc zero    = s≤s z≤n
pow2-ge-suc (suc n) =
  ≤-trans (subst (λ k → suc (suc n) ≤ k) (sym (suc-double n)) (s≤s (s≤s (n≤n+n n))))
          (≤-trans (≤-+-mono (pow2-ge-suc n) (pow2-ge-suc n))
                   (subst (λ k → (2 ^ n) + (2 ^ n) ≤ (2 ^ n) + k)
                          (sym (+-zero (2 ^ n)))
                          ≤-refl))

pair-first-< : ∀ a b → a < pair a b
pair-first-< a b =
  subst (λ k → suc a ≤ k)
        (sym (*-suc (2 ^ a) (b + b)))
        (≤-trans (pow2-ge-suc a) (n≤n+m (2 ^ a) ((2 ^ a) * (b + b))))

------------------------------------------------------------------------
-- Inverse of pairing
------------------------------------------------------------------------

unpair-acc : ∀ n → Acc n → ℕ × ℕ
unpair-acc zero          _         = zero , zero
unpair-acc (suc zero)    _         = zero , zero
unpair-acc (suc (suc n)) (acc rec) with even? (suc (suc n))
... | false = zero , suc (div2 n)
... | true  =
  let (a , b) = unpair-acc (suc (div2 n)) (rec (suc (div2 n)) (div2-suc-suc-< n))
  in  suc a , b

unpair-acc-irrel : ∀ n (p q : Acc n) → unpair-acc n p ≡ unpair-acc n q
unpair-acc-irrel zero          p q = refl
unpair-acc-irrel (suc zero)    p q = refl
unpair-acc-irrel (suc (suc n)) (acc rp) (acc rq) with even? (suc (suc n))
... | false = refl
... | true  = cong (λ r → suc (proj₁ r) , proj₂ r)
                   (unpair-acc-irrel (suc (div2 n))
                     (rp (suc (div2 n)) (div2-suc-suc-< n))
                     (rq (suc (div2 n)) (div2-suc-suc-< n)))

unpair-acc-cong-n : ∀ {n n′} (eq : n ≡ n′) (p : Acc n) →
                    unpair-acc n p ≡ unpair-acc n′ (subst Acc eq p)
unpair-acc-cong-n refl p = refl

unpair : ℕ → ℕ × ℕ
unpair n = unpair-acc n (<-wf n)

unpair-acc-0-0 : ∀ (p : Acc 1) → unpair-acc 1 p ≡ (zero , zero)
unpair-acc-0-0 _ = refl

unpair-acc-0-suc : ∀ m (p : Acc (suc (suc (suc (m + m))))) →
                   unpair-acc (suc (suc (suc (m + m)))) p ≡ (zero , suc m)
unpair-acc-0-suc m (acc rec) rewrite even?-suc-double m =
  cong (λ k → zero , suc k) (div2-odd-double m)

unpair-acc-pair : ∀ n m (p : Acc (pair n m)) → unpair-acc (pair n m) p ≡ (n , m)
unpair-acc-pair zero zero p = unpair-acc-0-0 p
unpair-acc-pair zero (suc m) p =
  let eq = trans (pair-zero (suc m)) (cong suc (suc-double m))
  in  trans (unpair-acc-cong-n eq p) (unpair-acc-0-suc m (subst Acc eq p))
unpair-acc-pair (suc n) m p with pair-is-suc n m
... | j , peq =
  let eq-pair : pair (suc n) m ≡ suc (suc (j + j))
      eq-pair = trans (pair-double n m) (trans (cong₂ _+_ peq peq) (suc-double j))
  in  trans (unpair-acc-cong-n eq-pair p) (lemma j peq (subst Acc eq-pair p))
  where
    lemma : ∀ j → pair n m ≡ suc j → (q : Acc (suc (suc (j + j)))) →
            unpair-acc (suc (suc (j + j))) q ≡ (suc n , m)
    lemma j peq (acc rec) rewrite even?-double j =
      let ih-acc = rec (suc (div2 (j + j))) (div2-suc-suc-< (j + j))
          eq-div : suc (div2 (j + j)) ≡ pair n m
          eq-div = trans (cong suc (div2-double j)) (sym peq)
      in  cong (λ r → suc (proj₁ r) , proj₂ r)
               (trans (unpair-acc-cong-n eq-div ih-acc)
                      (unpair-acc-pair n m (subst Acc eq-div ih-acc)))

unpair-pair : ∀ n m → unpair (pair n m) ≡ (n , m)
unpair-pair n m = trans (unpair-acc-irrel (pair n m) (<-wf (pair n m)) (<-wf (pair n m)))
                         -- the two <-wf are the same; just apply unpair-acc-pair
                         (unpair-acc-pair n m (<-wf (pair n m)))

------------------------------------------------------------------------
-- Correctness of unpair on every positive integer (surjectivity)
------------------------------------------------------------------------

odd-pair-suc : ∀ n → even? n ≡ false → pair zero (suc (div2 n)) ≡ suc (suc n)
odd-pair-suc n ev =
  trans (pair-zero (suc (div2 n)))
        (trans (cong suc (suc-double (div2 n)))
               (cong (λ k → suc (suc k)) (sym (odd-form n ev))))

unpair-acc-correct : ∀ n (p : Acc n) →
  (n ≡ zero) ⊎ (pair (proj₁ (unpair-acc n p)) (proj₂ (unpair-acc n p)) ≡ n)
unpair-acc-correct zero          p = inj₁ refl
unpair-acc-correct (suc zero)    p = inj₂ refl
unpair-acc-correct (suc (suc n)) (acc rec) with inspect (even? n)
... | false with≡ ev rewrite ev =
  inj₂ (odd-pair-suc n ev)
... | true  with≡ ev rewrite ev =
  inj₂ (even-case (unpair-acc-correct (suc (div2 n)) (rec (suc (div2 n)) (div2-suc-suc-< n))))
  where
    even-case : (suc (div2 n) ≡ zero) ⊎
                (pair (proj₁ (unpair-acc (suc (div2 n)) (rec (suc (div2 n)) (div2-suc-suc-< n))))
                      (proj₂ (unpair-acc (suc (div2 n)) (rec (suc (div2 n)) (div2-suc-suc-< n))))
                   ≡ suc (div2 n)) →
                pair (suc (proj₁ (unpair-acc (suc (div2 n)) (rec (suc (div2 n)) (div2-suc-suc-< n)))))
                     (proj₂ (unpair-acc (suc (div2 n)) (rec (suc (div2 n)) (div2-suc-suc-< n))))
                  ≡ suc (suc n)
    even-case (inj₁ ())
    even-case (inj₂ ih-eq) =
      trans (pair-double a′ b′)
            (trans (cong₂ _+_ ih-eq ih-eq)
                   (sym (even-split (suc (suc n)) ev)))
      where
        a′ = proj₁ (unpair-acc (suc (div2 n)) (rec (suc (div2 n)) (div2-suc-suc-< n)))
        b′ = proj₂ (unpair-acc (suc (div2 n)) (rec (suc (div2 n)) (div2-suc-suc-< n)))
        -- even-split (suc suc n) : suc suc n ≡ suc (div2 n) + suc (div2 n)
        -- pair (suc a′) b′ ≡ pair a′ b′ + pair a′ b′ ≡ suc (div2 n) + suc (div2 n)

-- The even-case above references `ev` from the with; keep it in scope by
-- not hiding the inspect.  (typecheck will confirm.)

unpair-fst-< : ∀ k → proj₁ (unpair (suc k)) < suc k
unpair-fst-< k with unpair-acc-correct (suc k) (<-wf (suc k))
... | inj₁ ()
... | inj₂ eq =
  subst (λ n → proj₁ (unpair (suc k)) < n) eq
        (pair-first-< (proj₁ (unpair (suc k))) (proj₂ (unpair (suc k))))

------------------------------------------------------------------------
-- Finite-set numbering: members n = the list coded by sequence number n
-- set(0) = ∅, set((n,m)) = set(n) ∪ {m}   (PROGIC 2013, §2)
------------------------------------------------------------------------

members-acc : ∀ n → Acc n → List ℕ
members-acc zero        _        = []
members-acc (suc k)     (acc rec) =
  let (ns , x) = unpair (suc k)
  in  x ∷ members-acc ns (rec ns (unpair-fst-< k))

members : ℕ → List ℕ
members n = members-acc n (<-wf n)

members-acc-irrel : ∀ n (p q : Acc n) → members-acc n p ≡ members-acc n q
members-acc-irrel zero    p q = refl
members-acc-irrel (suc k) (acc rp) (acc rq) =
  cong (proj₂ (unpair (suc k)) ∷_)
       (members-acc-irrel (proj₁ (unpair (suc k)))
         (rp (proj₁ (unpair (suc k))) (unpair-fst-< k))
         (rq (proj₁ (unpair (suc k))) (unpair-fst-< k)))

members-acc-cong-n : ∀ {n n′} (eq : n ≡ n′) (p : Acc n) →
                     members-acc n p ≡ members-acc n′ (subst Acc eq p)
members-acc-cong-n refl p = refl

members-zero : members zero ≡ []
members-zero = refl

-- set((n,m)) = set(n) ∪ {m}  (PROGIC 2013, §2)
members-acc-cong-idx : ∀ {n₁ n₂} (eq : n₁ ≡ n₂)
                       (p₁ : Acc n₁) (p₂ : Acc n₂) →
                       members-acc n₁ p₁ ≡ members-acc n₂ p₂
members-acc-cong-idx eq p₁ p₂ =
  trans (members-acc-cong-n eq p₁) (members-acc-irrel _ (subst Acc eq p₁) p₂)

members-pair : ∀ n m → members (pair n m) ≡ m ∷ members n
members-pair n m with pair-is-suc n m
... | k , peq = trans (cong members peq) (go (<-wf (suc k)))
  where
    u-eq : unpair (suc k) ≡ (n , m)
    u-eq = trans (cong unpair (sym peq)) (unpair-pair n m)

    n<sk : n < suc k
    n<sk = subst (n <_) peq (pair-first-< n m)

    go : (p : Acc (suc k)) → members-acc (suc k) p ≡ m ∷ members n
    go (acc rec) =
      cong₂ _∷_ (cong proj₂ u-eq)
        (trans (members-acc-cong-idx (cong proj₁ u-eq)
                  (rec (proj₁ (unpair (suc k))) (unpair-fst-< k))
                  (rec n n<sk))
               (members-acc-irrel n (rec n n<sk) (<-wf n)))

------------------------------------------------------------------------
-- The graph-model space 𝒫(ℕ), membership, Kleene star
------------------------------------------------------------------------

𝒫ℕ : Set₁
𝒫ℕ = ℕ → Set

_⊆_ : 𝒫ℕ → 𝒫ℕ → Set
X ⊆ Y = ∀ {k} → X k → Y k

-- m ∈ set(n)
_∈-set_ : ℕ → ℕ → Set
m ∈-set n = m ∈-list members n

-- The finite set coded by a sequence number, as a predicate.
setₚ : ℕ → 𝒫ℕ
setₚ n m = m ∈-set n

-- n ∈ X*  iff  set(n) ⊆ X   (PROGIC 2013, §2)
-- Implemented as a finite conjunction so later measurability proofs
-- can treat it as a finite intersection of coordinate events.
_∈*_ : ℕ → 𝒫ℕ → Set
n ∈* X = All X (members n)

infix 4 _∈-set_ _∈*_ _⊆_

∈*-∀ : ∀ n X → n ∈* X → ∀ m → m ∈-set n → X m
∈*-∀ n X p = All-∀ X (members n) p

∀-∈* : ∀ n X → (∀ m → m ∈-set n → X m) → n ∈* X
∀-∈* n X f = ∀-All X (members n) f

∈*-mono : ∀ {X Y} n → X ⊆ Y → n ∈* X → n ∈* Y
∈*-mono n X⊆Y p = All-mono (members n) (λ _ → X⊆Y) p

-- n ∈ set(n)*
∈*-refl : ∀ n → n ∈* (λ m → m ∈-set n)
∈*-refl n = ∀-∈* n (λ m → m ∈-set n) (λ m i → i)

singleton-seq : ℕ → ℕ
singleton-seq m = pair zero m

members-singleton : ∀ m → members (singleton-seq m) ≡ m ∷ []
members-singleton m = members-pair zero m

pair-injective : ∀ n₁ m₁ n₂ m₂ → pair n₁ m₁ ≡ pair n₂ m₂ → (n₁ ≡ n₂) × (m₁ ≡ m₂)
pair-injective n₁ m₁ n₂ m₂ eq =
  (cong proj₁ both) , (cong proj₂ both)
  where
    both : (n₁ , m₁) ≡ (n₂ , m₂)
    both = trans (sym (unpair-pair n₁ m₁))
                 (trans (cong unpair eq) (unpair-pair n₂ m₂))

⊆-refl : ∀ {X} → X ⊆ X
⊆-refl p = p

_∩ₚ_ : 𝒫ℕ → 𝒫ℕ → 𝒫ℕ
(X ∩ₚ Y) n = X n × Y n

_∪ₚ_ : 𝒫ℕ → 𝒫ℕ → 𝒫ℕ
(X ∪ₚ Y) n = X n ⊎ Y n

infixr 6 _∩ₚ_
infixr 5 _∪ₚ_

Finite : 𝒫ℕ → Set
Finite X = Σ ℕ (λ n → ∀ m → X m ↔ (m ∈-set n))

*2-double : ∀ m → 2 * m ≡ m + m
*2-double m = cong (m +_) (+-zero m)

pow2-is-suc : ∀ n → Σ ℕ (λ k → 2 ^ n ≡ suc k)
pow2-is-suc zero = zero , refl
pow2-is-suc (suc n) with pow2-is-suc n
... | k , eq = suc (k + k) ,
  trans (*2-double (2 ^ n)) (trans (cong (λ x → x + x) eq) (suc-double k))

<⇒≤ : ∀ {a b} → a < b → a ≤ b
<⇒≤ a<b = ≤-trans (≤-suc ≤-refl) a<b

pair-second-< : ∀ a b → b < pair a b
pair-second-< a b with pow2-is-suc a
... | k , eq =
  ≤-trans (s≤s (n≤n+m b b))
          (subst (λ p → suc (b + b) ≤ p * suc (b + b)) (sym eq)
                 (n≤n+m (suc (b + b)) (k * suc (b + b))))

-- Sequence-number concatenation: members (seq-append n m) ≡ members n ++ members m
seq-append-acc : ∀ n → Acc n → ℕ → ℕ
seq-append-acc zero        _        m = m
seq-append-acc (suc k)     (acc rec) m =
  let (ns , x) = unpair (suc k)
  in  pair (seq-append-acc ns (rec ns (unpair-fst-< k)) m) x

seq-append : ℕ → ℕ → ℕ
seq-append n m = seq-append-acc n (<-wf n) m

seq-append-acc-irrel : ∀ n (p q : Acc n) m →
                       seq-append-acc n p m ≡ seq-append-acc n q m
seq-append-acc-irrel zero    p q m = refl
seq-append-acc-irrel (suc k) (acc rp) (acc rq) m =
  cong (λ n′ → pair n′ (proj₂ (unpair (suc k))))
       (seq-append-acc-irrel (proj₁ (unpair (suc k)))
         (rp (proj₁ (unpair (suc k))) (unpair-fst-< k))
         (rq (proj₁ (unpair (suc k))) (unpair-fst-< k))
         m)

seq-append-zero : ∀ m → seq-append zero m ≡ m
seq-append-zero m = refl

members-unfold-suc : ∀ k →
  members (suc k) ≡ proj₂ (unpair (suc k)) ∷ members (proj₁ (unpair (suc k)))
members-unfold-suc k = unfold (<-wf (suc k))
  where
    unfold : (p : Acc (suc k)) →
      members-acc (suc k) p ≡
        proj₂ (unpair (suc k)) ∷ members (proj₁ (unpair (suc k)))
    unfold (acc rec) =
      cong (proj₂ (unpair (suc k)) ∷_)
        (members-acc-irrel (proj₁ (unpair (suc k)))
          (rec (proj₁ (unpair (suc k))) (unpair-fst-< k))
          (<-wf (proj₁ (unpair (suc k)))))

members-seq-append : ∀ n m → members (seq-append n m) ≡ members n ++ members m
members-seq-append n m = go n (<-wf n)
  where
    go : ∀ n (p : Acc n) →
         members (seq-append-acc n p m) ≡ members n ++ members m
    go zero        p        = refl
    go (suc k)     (acc rec) =
      let ns  = proj₁ (unpair (suc k))
          x   = proj₂ (unpair (suc k))
          pns = rec ns (unpair-fst-< k)
      in  trans (members-pair (seq-append-acc ns pns m) x)
          (trans (cong (x ∷_) (go ns pns))
                 (cong (_++ members m) (sym (members-unfold-suc k))))

∈*-to-⊆ : ∀ k {X} → k ∈* X → setₚ k ⊆ X
∈*-to-⊆ k p {x} x∈ = ∈*-∀ k _ p x x∈

set-append-left : ∀ n m {x} → x ∈-set n → x ∈-set (seq-append n m)
set-append-left n m {x} p =
  subst (x ∈-list_) (sym (members-seq-append n m))
    (∈-++-left (members n) (members m) p)

set-append-right : ∀ n m {x} → x ∈-set m → x ∈-set (seq-append n m)
set-append-right n m {x} p =
  subst (x ∈-list_) (sym (members-seq-append n m))
    (∈-++-right (members n) (members m) p)

∈*-append : ∀ {X} n m → n ∈* X → m ∈* X → seq-append n m ∈* X
∈*-append {X} n m n∈ m∈ =
  subst (All X) (sym (members-seq-append n m))
    (all-++ (members n) (members m) n∈ m∈)
  where
    all-++ : ∀ xs ys → All X xs → All X ys → All X (xs ++ ys)
    all-++ []       ys _        q = q
    all-++ (x ∷ xs) ys (px , p) q = px , all-++ xs ys p q

-- Every member of set(k) is strictly smaller than k (k > 0).
members-bounded : ∀ k x → x ∈-set k → x < k
members-bounded k x i = go k (<-wf k) x i
  where
    go : ∀ k → Acc k → ∀ x → x ∈-set k → x < k
    go zero        _        x ()
    go (suc k)     (acc rec) x i =
      from-cons (subst (x ∈-list_) (members-unfold-suc k) i)
      where
        y<sk : proj₂ (unpair (suc k)) < suc k
        y<sk with unpair-acc-correct (suc k) (<-wf (suc k))
        ... | inj₁ ()
        ... | inj₂ peq =
          subst (proj₂ (unpair (suc k)) <_) peq
                (pair-second-< (proj₁ (unpair (suc k))) (proj₂ (unpair (suc k))))

        from-cons : x ∈-list (proj₂ (unpair (suc k)) ∷ members (proj₁ (unpair (suc k)))) → x < suc k
        from-cons here =
          y<sk
        from-cons (there j) =
          <≤-trans (go (proj₁ (unpair (suc k))) (rec (proj₁ (unpair (suc k))) (unpair-fst-< k)) x j)
                   (<⇒≤ (unpair-fst-< k))

