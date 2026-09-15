{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Minimal prelude (no standard library; `agda --safe --no-libraries`).
-- `--without-K` is the TypeTopology flag: K-free, not Cubical Agda.
------------------------------------------------------------------------

module Scott2013.Prelude where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc; _+_; _*_) renaming (Nat to ℕ)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Empty type, negation, sums, products
------------------------------------------------------------------------

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

infixr 1 _⊎_
infixr 2 _×_
infix 1 _↔_

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 4 _,_

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

------------------------------------------------------------------------
-- Equality
------------------------------------------------------------------------

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq = eq

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {A B C : Set} (f : A → B → C)
        {x x′ : A} {y y′ : B} → x ≡ x′ → y ≡ y′ → f x y ≡ f x′ y′
cong₂ f refl refl = refl

subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl p = p

infix  3 _∎
infixr 2 _≡⟨_⟩_
infix  1 begin_

begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
begin eq = eq

_≡⟨_⟩_ : {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q

_∎ : {A : Set} (x : A) → x ≡ x
x ∎ = refl

suc-injective : {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

------------------------------------------------------------------------
-- Inspect idiom
------------------------------------------------------------------------

data Inspect {A : Set} (x : A) : Set where
  _with≡_ : (y : A) → x ≡ y → Inspect x

inspect : {A : Set} (x : A) → Inspect x
inspect x = x with≡ refl

------------------------------------------------------------------------
-- Decidable equality on ℕ
------------------------------------------------------------------------

ℕ-eq-dec : (x y : ℕ) → (x ≡ y) ⊎ (x ≢ y)
ℕ-eq-dec zero zero = inj₁ refl
ℕ-eq-dec zero (suc y) = inj₂ λ ()
ℕ-eq-dec (suc x) zero = inj₂ λ ()
ℕ-eq-dec (suc x) (suc y) with ℕ-eq-dec x y
... | inj₁ refl = inj₁ refl
... | inj₂ ne   = inj₂ λ eq → ne (suc-injective eq)

------------------------------------------------------------------------
-- Arithmetic lemmas
------------------------------------------------------------------------

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-zero : ∀ n → n + zero ≡ n
+-zero zero    = refl
+-zero (suc n) = cong suc (+-zero n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero    n = sym (+-zero n)
+-comm (suc m) n = trans (cong suc (+-comm m n)) (sym (+-suc n m))

suc-double : ∀ n → suc n + suc n ≡ suc (suc (n + n))
suc-double n = cong suc (+-suc n n)

double-inj : ∀ m n → m + m ≡ n + n → m ≡ n
double-inj zero    zero    eq = refl
double-inj zero    (suc n) ()
double-inj (suc m) zero    ()
double-inj (suc m) (suc n) eq =
  cong suc (double-inj m n (suc-injective (suc-injective (trans (sym (suc-double m)) (trans eq (suc-double n))))))

------------------------------------------------------------------------
-- Order and well-founded induction
------------------------------------------------------------------------

infix 4 _≤_ _<_

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n

≤-refl : {n : ℕ} → n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : {l m n : ℕ} → l ≤ m → m ≤ n → l ≤ n
≤-trans z≤n       _         = z≤n
≤-trans (s≤s l≤m) (s≤s m≤n) = s≤s (≤-trans l≤m m≤n)

<≤-trans : {l m n : ℕ} → l < m → m ≤ n → l < n
<≤-trans l<m m≤n = ≤-trans l<m m≤n

data Acc (n : ℕ) : Set where
  acc : (∀ m → m < n → Acc m) → Acc n

<-wf : ∀ n → Acc n
<-wf n = acc (go n)
  where
    go : ∀ n m → m < n → Acc m
    go (suc n) m (s≤s m≤n) = acc (λ k k<m → go n k (<≤-trans k<m m≤n))

n<suc-n : ∀ n → n < suc n
n<suc-n n = s≤s ≤-refl

------------------------------------------------------------------------
-- Parity and division by two
------------------------------------------------------------------------

even? : ℕ → Bool
even? zero          = true
even? (suc zero)    = false
even? (suc (suc n)) = even? n

div2 : ℕ → ℕ
div2 zero          = zero
div2 (suc zero)    = zero
div2 (suc (suc n)) = suc (div2 n)

even?-double : ∀ n → even? (n + n) ≡ true
even?-double zero    = refl
even?-double (suc n) = subst (λ k → even? k ≡ true) (sym (suc-double n)) (even?-double n)

even?-suc-double : ∀ n → even? (suc (n + n)) ≡ false
even?-suc-double zero    = refl
even?-suc-double (suc n) = subst (λ k → even? (suc k) ≡ false) (sym (suc-double n)) (even?-suc-double n)

div2-double : ∀ n → div2 (n + n) ≡ n
div2-double zero    = refl
div2-double (suc n) = subst (λ k → div2 k ≡ suc n) (sym (suc-double n)) (cong suc (div2-double n))

div2-odd-double : ∀ n → div2 (suc (n + n)) ≡ n
div2-odd-double zero    = refl
div2-odd-double (suc n) = subst (λ k → div2 (suc k) ≡ suc n) (sym (suc-double n)) (cong suc (div2-odd-double n))

even-split : ∀ n → even? n ≡ true → n ≡ div2 n + div2 n
even-split zero          _  = refl
even-split (suc zero)    ()
even-split (suc (suc n)) eq =
  trans (cong (λ k → suc (suc k)) (even-split n eq)) (double-suc-div2 n)
  where
    -- suc (div2 n) + suc (div2 n) = suc (suc (div2 n + div2 n))
    double-suc-div2 : ∀ n → suc (suc (div2 n + div2 n)) ≡ suc (div2 n) + suc (div2 n)
    double-suc-div2 n = sym (suc-double (div2 n))

odd-form : ∀ n → even? n ≡ false → n ≡ suc (div2 n + div2 n)
odd-form zero          ()
odd-form (suc zero)    _  = refl
odd-form (suc (suc n)) eq =
  trans (cong (λ k → suc (suc k)) (odd-form n eq)) (lem (div2 n))
  where
    lem : ∀ k → suc (suc (suc (k + k))) ≡ suc (suc k + suc k)
    lem k = cong suc (sym (suc-double k))

true≢false : true ≢ false
true≢false ()

even≢odd : ∀ n → even? n ≡ true → even? n ≡ false → ⊥
even≢odd n ev od = true≢false (trans (sym ev) od)

------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

infix 4 _∈-list_

data _∈-list_ {A : Set} (x : A) : List A → Set where
  here  : ∀ {xs} → x ∈-list (x ∷ xs)
  there : ∀ {y xs} → x ∈-list xs → x ∈-list (y ∷ xs)

All : {A : Set} (P : A → Set) → List A → Set
All P []       = ⊤
All P (x ∷ xs) = P x × All P xs

All-∀ : {A : Set} (P : A → Set) (xs : List A) →
        All P xs → ∀ x → x ∈-list xs → P x
All-∀ P (x ∷ xs) (px , _)  .x here      = px
All-∀ P (x ∷ xs) (_  , ps)  y (there i) = All-∀ P xs ps y i

∀-All : {A : Set} (P : A → Set) (xs : List A) →
        (∀ x → x ∈-list xs → P x) → All P xs
∀-All P []       _ = tt
∀-All P (x ∷ xs) f = f x here , ∀-All P xs (λ y i → f y (there i))

All-mono : {A : Set} {P Q : A → Set} (xs : List A) →
           (∀ x → P x → Q x) → All P xs → All Q xs
All-mono []       _  _        = tt
All-mono (x ∷ xs) pq (px , p) = pq x px , All-mono xs pq p

infixr 5 _++_

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

∈-++-left : {A : Set} {x : A} (xs ys : List A) →
            x ∈-list xs → x ∈-list (xs ++ ys)
∈-++-left (x ∷ xs) ys here      = here
∈-++-left (y ∷ xs) ys (there i) = there (∈-++-left xs ys i)

∈-++-right : {A : Set} {x : A} (xs ys : List A) →
             x ∈-list ys → x ∈-list (xs ++ ys)
∈-++-right []       ys i = i
∈-++-right (y ∷ xs) ys i = there (∈-++-right xs ys i)

∈-++-split : {A : Set} {x : A} (xs ys : List A) →
             x ∈-list (xs ++ ys) → (x ∈-list xs) ⊎ (x ∈-list ys)
∈-++-split []       ys i        = inj₂ i
∈-++-split (x ∷ xs) ys here     = inj₁ here
∈-++-split (x ∷ xs) ys (there i) with ∈-++-split xs ys i
... | inj₁ j = inj₁ (there j)
... | inj₂ j = inj₂ j

length : {A : Set} → List A → ℕ
length []       = zero
length (_ ∷ xs) = suc (length xs)

map : {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

concat : {A : Set} → List (List A) → List A
concat []         = []
concat (xs ∷ xss) = xs ++ concat xss

concatMap : {A B : Set} → (A → List B) → List A → List B
concatMap f xs = concat (map f xs)

map-id : {A : Set} → ∀ (xs : List A) → map (λ x → x) xs ≡ xs
map-id []       = refl
map-id (x ∷ xs) = cong (x ∷_) (map-id xs)

map-compose : {A B C : Set} (f : B → C) (g : A → B) →
              ∀ xs → map f (map g xs) ≡ map (λ x → f (g x)) xs
map-compose f g []       = refl
map-compose f g (x ∷ xs) = cong (f (g x) ∷_) (map-compose f g xs)

map-∈ : {A B : Set} (f : A → B) {x : A} (xs : List A) →
        x ∈-list xs → f x ∈-list map f xs
map-∈ f (x ∷ xs) here      = here
map-∈ f (y ∷ xs) (there p) = there (map-∈ f xs p)

map-∈-split : {A B : Set} (f : A → B) {y : B} (xs : List A) →
              y ∈-list map f xs → Σ A (λ x → (x ∈-list xs) × (f x ≡ y))
map-∈-split f (x ∷ xs) here = x , here , refl
map-∈-split f (x ∷ xs) (there p) with map-∈-split f xs p
... | y , y∈ , eq = y , there y∈ , eq

∈-concatMap : {A B : Set} (f : A → List B) {y : B} (xs : List A) →
  y ∈-list concatMap f xs →
  Σ A (λ x → (x ∈-list xs) × (y ∈-list f x))
∈-concatMap f [] ()
∈-concatMap f (x ∷ xs) p with ∈-++-split (f x) (concatMap f xs) p
... | inj₁ q = x , here , q
... | inj₂ q with ∈-concatMap f xs q
...   | y , y∈ , r = y , there y∈ , r

concatMap-∈ : {A B : Set} (f : A → List B) {x : A} {y : B}
  (xs : List A) → x ∈-list xs → y ∈-list f x →
  y ∈-list concatMap f xs
concatMap-∈ f [] ()
concatMap-∈ f (x ∷ xs) here q = ∈-++-left (f x) (concatMap f xs) q
concatMap-∈ f (x ∷ xs) (there p) q =
  ∈-++-right (f x) (concatMap f xs) (concatMap-∈ f xs p q)

∈-list-dec : (x : ℕ) (xs : List ℕ) → (x ∈-list xs) ⊎ ¬ (x ∈-list xs)
∈-list-dec x [] = inj₂ λ ()
∈-list-dec x (y ∷ ys) with ℕ-eq-dec x y
... | inj₁ refl = inj₁ here
... | inj₂ ne with ∈-list-dec x ys
...   | inj₁ i  = inj₁ (there i)
...   | inj₂ ni = inj₂ λ { here → ne refl ; (there i) → ni i }

All-dec : {A : Set} (P : A → Set) →
          (∀ x → P x ⊎ ¬ P x) → ∀ xs → All P xs ⊎ ¬ All P xs
All-dec P dec [] = inj₁ tt
All-dec P dec (x ∷ xs) with dec x | All-dec P dec xs
... | inj₁ px | inj₁ ps = inj₁ (px , ps)
... | inj₂ nx | _       = inj₂ λ p → nx (proj₁ p)
... | _       | inj₂ ns = inj₂ λ p → ns (proj₂ p)

data NoDuplicates {A : Set} : List A → Set where
  []-unique : NoDuplicates []
  _∷-unique_ : ∀ {x xs} → (x ∈-list xs → ⊥) →
               NoDuplicates xs → NoDuplicates (x ∷ xs)

select : {A : Set} (P : A → Set) →
         (∀ x → P x ⊎ ¬ P x) → List A → List A
select P dec [] = []
select P dec (x ∷ xs) with dec x
... | inj₁ _ = x ∷ select P dec xs
... | inj₂ _ = select P dec xs

select-sound : {A : Set} (P : A → Set)
  (dec : ∀ x → P x ⊎ ¬ P x) {x : A} (xs : List A) →
  x ∈-list select P dec xs → (x ∈-list xs) × P x
select-sound P dec [] ()
select-sound P dec (y ∷ ys) p with dec y
select-sound P dec (y ∷ ys) here      | inj₁ py = here , py
select-sound P dec (y ∷ ys) (there p) | inj₁ py with select-sound P dec ys p
... | q , px = there q , px
select-sound P dec (y ∷ ys) p         | inj₂ ny with select-sound P dec ys p
... | q , px = there q , px

select-complete : {A : Set} (P : A → Set)
  (dec : ∀ x → P x ⊎ ¬ P x) {x : A} (xs : List A) →
  x ∈-list xs → P x → x ∈-list select P dec xs
select-complete P dec [] ()
select-complete P dec (x ∷ xs) here px with dec x
... | inj₁ _  = here
... | inj₂ nx = ⊥-elim (nx px)
select-complete P dec (y ∷ ys) (there p) px with dec y
... | inj₁ _ = there (select-complete P dec ys p px)
... | inj₂ _ = select-complete P dec ys p px

sublists : {A : Set} → List A → List (List A)
sublists []       = [] ∷ []
sublists (x ∷ xs) =
  map (x ∷_) (sublists xs) ++ sublists xs

select-sublists : {A : Set} (P : A → Set)
  (dec : ∀ x → P x ⊎ ¬ P x) (xs : List A) →
  select P dec xs ∈-list sublists xs
select-sublists P dec [] = here
select-sublists P dec (x ∷ xs) with dec x
... | inj₁ px =
  ∈-++-left (map (x ∷_) (sublists xs)) (sublists xs)
    (map-∈ (x ∷_) (sublists xs) (select-sublists P dec xs))
... | inj₂ nx =
  ∈-++-right (map (x ∷_) (sublists xs)) (sublists xs)
    (select-sublists P dec xs)
