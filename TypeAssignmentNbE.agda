import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty renaming (⊥ to Empty)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Nat using (ℕ; zero; suc; _∸_; _<_)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Function using (_∘_)
open Eq using (_≡_; refl)

{- Normalization by Evaluation: Dependent Types and Impredicativity, Abel 2013 -}

-- NbE for type-assignment STLC, proof that untyped NbE is terminating
-- for typeable terms
module TypeAssignmentNbE where

{- Types -}

data Type : Set where
  bool : Type
  _⇒_ : Type → Type → Type
  _*_ : Type → Type → Type

infixr 7 _⇒_
infixr 9 _*_

{- Typing contexts -}

Ctx : ℕ → Set
Ctx n = Fin n → Type

_∷_ : ∀ {n : ℕ} → Ctx n → Type → Ctx (suc n)
(_ ∷ T) zero    = T
(Γ ∷ _) (suc m) = Γ m

infixl 5 _∷_

{- Syntax -}

data Term : Set where
  var : ℕ → Term       -- de Brujin indices (denoted by 'i')
  true : Term
  false : Term
  ƛ_  : Term → Term
  _·_ : Term → Term → Term
  if_then_else_ : Term → Term → Term → Term
  ⟨_,_⟩ : Term → Term → Term
  fst : Term → Term
  snd : Term → Term

infix 5 ƛ_
infixl 7 _·_
infix 6 if_then_else_
infix 5 ⟨_,_⟩

{- Syntactic Typing -}

data _⊢_⦂_ {n : ℕ} (Γ : Ctx n) : Term → Type → Set where
  typingTrue : Γ ⊢ true ⦂ bool

  typingFalse : Γ ⊢ false ⦂ bool

  typingIf : ∀ {t₁ t₂ t₃ : Term} {T : Type}
           → Γ ⊢ t₁ ⦂ bool
           → Γ ⊢ t₂ ⦂ T
           → Γ ⊢ t₃ ⦂ T
             -----------------------------
           → Γ ⊢ if t₁ then t₂ else t₃ ⦂ T

  typingVar : ∀ {m : Fin n} {T : Type}
            → T ≡ Γ m
              --------------------------
            → Γ ⊢ var (toℕ m) ⦂ T

  typingAbs : ∀ {S T : Type} {t : Term}
            → Γ ∷ S ⊢ t ⦂ T
              ---------------
            → Γ ⊢ ƛ t ⦂ S ⇒ T

  typingApp : ∀ {r s : Term} {S T : Type}
            → Γ ⊢ r ⦂ S ⇒ T
            → Γ ⊢ s ⦂ S
              -------------
            → Γ ⊢ r · s ⦂ T

  typingPair : ∀ {s t : Term} {S T : Type}
             → Γ ⊢ s ⦂ S
             → Γ ⊢ t ⦂ T
               ---------------------
             → Γ ⊢ ⟨ s , t ⟩ ⦂ S * T

  typingFst : ∀ {t : Term} {S T : Type}
            → Γ ⊢ t ⦂ S * T
              -------------
            → Γ ⊢ fst t ⦂ S

  typingSnd : ∀ {t : Term} {S T : Type}
            → Γ ⊢ t ⦂ S * T
              -------------
            → Γ ⊢ snd t ⦂ T

infix 4 _⊢_⦂_

{- Semantics -}

-- We model partial functions as inductive
-- relations,

-- A term is evaluated into the domain space
-- through partial funcitons. Then, there is
-- another partial function for reading back
-- a value in the domain space into a normal
-- term

mutual
  -- Neutral form: u
  data Ne : Set where
    var : ℕ → Ne
    _·_ : Ne → Nf → Ne
    if_then_else_ : Ne → Nf → Nf → Ne
    fst : Ne → Ne
    snd : Ne → Ne

  -- Normal form: v
  data Nf : Set where
    neutral : Ne → Nf
    ƛ_ : Nf → Nf
    true : Nf
    false : Nf
    ⟨_,_⟩ : Nf → Nf → Nf

mutual
  -- Domain: d, a, f, b
  -- equivalent of value
  -- adds neutral values
  data D : Set where
    closure : Term → Env → D
    neutral : Dⁿᵉ → D
    true : D
    false : D
    ⟨_,_⟩ : D → D → D

  -- Neutral domain: e
  data Dⁿᵉ : Set where
    level : ℕ → Dⁿᵉ      -- de Brujin level (denoted by 'k')
    _·_ : Dⁿᵉ → D → Dⁿᵉ
    if_then_else_ : Dⁿᵉ → D → D → Dⁿᵉ
    fst : Dⁿᵉ → Dⁿᵉ
    snd : Dⁿᵉ → Dⁿᵉ

  Env : Set
  Env = ℕ → D

_++_ : Env → D → Env
(ρ ++ d) zero    = d
(ρ ++ d) (suc i) = ρ i

infixl 5 _++_

mutual
  -- Partial first element projection
  data fst_↘_ : D → D → Set where
    fst-pair : ∀ {a b : D}
               -----------------
             → fst ⟨ a , b ⟩ ↘ a

    fst-neutral : ∀ {e : Dⁿᵉ}
                  -------------------------------
                → fst neutral e ↘ neutral (fst e)


  -- Partial second element projection
  data snd_↘_ : D → D → Set where
    snd-pair : ∀ {a b : D}
               -----------------
             → snd ⟨ a , b ⟩ ↘ b

    snd-neutral : ∀ {e : Dⁿᵉ}
                  -------------------------------
                → snd neutral e ↘ neutral (snd e)

  -- Partial if-then-else
  data if_then_else_↘_ : D → D → D → D → Set where
    if-true : ∀ {a b : D}
              -------------------------
            → if true then a else b ↘ a

    if-false : ∀ {a b : D}
               --------------------------
             → if false then a else b ↘ b

    if-neutral : ∀ {e : Dⁿᵉ} {a b : D}
                 ---------------------------------------------------------
               → if neutral e then a else b ↘ neutral (if e then a else b)

  -- Partial application
  data _·_↘_ : D → D → D → Set where
    app-closure : ∀ {ρ : Env} {t : Term} {a b : D}
                → ⟦ t ⟧ ρ ++ a ↘ b
                  -------------------
                → closure t ρ · a ↘ b

    app-neutral : ∀ {e : Dⁿᵉ} {d : D}
                → neutral e · d ↘ neutral (e · d)

  -- Partial evaluation
  data ⟦_⟧_↘_ : Term → Env → D → Set where
    eval-true : ∀ {ρ : Env}
                -----------------
              → ⟦ true ⟧ ρ ↘ true

    eval-false : ∀ {ρ : Env}
                --------------------
               → ⟦ false ⟧ ρ ↘ false

    eval-if : ∀ {t₁ t₂ t₃ : Term} {ρ : Env} {a₁ a₂ b d : D}
            → ⟦ t₁ ⟧ ρ ↘ b
            → ⟦ t₂ ⟧ ρ ↘ a₁
            → ⟦ t₃ ⟧ ρ ↘ a₂
            → if b then a₁ else a₂ ↘ d
              -------------------------------
            → ⟦ if t₁ then t₂ else t₃ ⟧ ρ ↘ d

    eval-var : ∀ {i : ℕ} {ρ : Env}
               -----------------
             → ⟦ var i ⟧ ρ ↘ ρ i

    eval-abs : ∀ {t : Term} {ρ : Env}
               -----------------------
             → ⟦ ƛ t ⟧ ρ ↘ closure t ρ

    eval-app : ∀ {r s : Term} {ρ : Env} {f a b : D}
             → ⟦ r ⟧ ρ ↘ f
             → ⟦ s ⟧ ρ ↘ a
             → f · a ↘ b
               ----------------
             → ⟦ r · s ⟧ ρ ↘ b

    eval-pair : ∀ {s t : Term} {ρ : Env} {a b : D}
              → ⟦ s ⟧ ρ ↘ a
              → ⟦ t ⟧ ρ ↘ b
                ---------------------------
              → ⟦ ⟨ s , t ⟩ ⟧ ρ ↘ ⟨ a , b ⟩

    eval-fst : ∀ {t : Term} {ρ : Env} {a d : D}
             → ⟦ t ⟧ ρ ↘ d
             → fst d ↘ a
               -------------------
             → ⟦ fst t ⟧ ρ ↘ a

    eval-snd : ∀ {t : Term} {ρ : Env} {b d : D}
             → ⟦ t ⟧ ρ ↘ d
             → snd d ↘ b
               -------------------
             → ⟦ snd t ⟧ ρ ↘ b

infix 4 if_then_else_↘_
infix 4 _·_↘_
infix 4 ⟦_⟧_↘_

mutual
  -- Readback neutrals from neutral domain
  data Rⁿᵉ_⦂_↦_ (n : ℕ) : Dⁿᵉ → Ne → Set where
    readback-var : ∀ {k : ℕ}
                   -----------------------------------
                 → Rⁿᵉ n ⦂ level k ↦ var (n ∸ (suc k))

    readback-app : ∀ {e : Dⁿᵉ} {u : Ne} {d : D} {v : Nf}
                 → Rⁿᵉ n ⦂ e ↦ u
                 → Rⁿᶠ n ⦂ d ↦ v
                   ---------------------
                 → Rⁿᵉ n ⦂ e · d ↦ u · v

    readback-if : ∀ {e : Dⁿᵉ} {u : Ne} {a₁ a₂ : D} {v₁ v₂ : Nf}
                → Rⁿᵉ n ⦂ e ↦ u
                → Rⁿᶠ n ⦂ a₁ ↦ v₁
                → Rⁿᶠ n ⦂ a₂ ↦ v₂
                  ---------------------------------------------------
                → Rⁿᵉ n ⦂ if e then a₁ else a₂ ↦ if u then v₁ else v₂

    readback-fst : ∀ {e : Dⁿᵉ} {u : Ne}
                 → Rⁿᵉ n ⦂ e ↦ u
                   ---------------------
                 → Rⁿᵉ n ⦂ fst e ↦ fst u

    readback-snd : ∀ {e : Dⁿᵉ} {u : Ne}
                 → Rⁿᵉ n ⦂ e ↦ u
                   ---------------------
                 → Rⁿᵉ n ⦂ snd e ↦ snd u

  -- Readback normals from normal domain
  data Rⁿᶠ_⦂_↦_ (n : ℕ) : D → Nf → Set where
    readback-true : Rⁿᶠ n ⦂ true ↦ true

    readback-false : Rⁿᶠ n ⦂ false ↦ false

    readback-abs : ∀ {t : Term} {ρ : Env} {b : D} {v : Nf}
                 → ⟦ t ⟧ ρ ++ neutral (level n) ↘ b
                 → Rⁿᶠ n ⦂ b ↦ v
                   ---------------------------
                 → Rⁿᶠ n ⦂ closure t ρ ↦ (ƛ v)

    readback-pair : ∀ {a b : D} {v₁ v₂ : Nf}
                  → Rⁿᶠ n ⦂ a ↦ v₁
                  → Rⁿᶠ n ⦂ b ↦ v₂
                    -------------------------------
                  → Rⁿᶠ n ⦂ ⟨ a , b ⟩ ↦ ⟨ v₁ , v₂ ⟩

    readback-neutral : ∀ {e : Dⁿᵉ} {u : Ne}
                     → Rⁿᵉ n ⦂ e ↦ u
                       -----------------------------
                     → Rⁿᶠ n ⦂ neutral e ↦ neutral u

infix 4 Rⁿᵉ_⦂_↦_
infix 4 Rⁿᶠ_⦂_↦_

{- Semantic typing -}

-- We will need to consider the semantic types of
-- well-typed terms to prove that they are well-behaved
-- and terminating in their evaluation. These will
-- just be predicates on the domain

SemanticType : Set₁
SemanticType = D → Set

-- To prove that any term evaluated into the domain space
-- can be read back into a normal term, we need to prove
-- that the semantic type of the evaluated term inhabits
-- a "candidate space" of reifiable terms

-- Bottom of candidate space: ⊥ (reifiable neutrals)
_∈⊥ : Dⁿᵉ → Set
e ∈⊥ = ∀ (n : ℕ) → ∃[ u ] Rⁿᵉ n ⦂ e ↦ u

-- Top of candidate space: ⊤ (reifiable normals)
_∈⊤ : D → Set
d ∈⊤ = ∀ (n : ℕ) → ∃[ v ] Rⁿᶠ n ⦂ d ↦ v

⊥ : SemanticType
⊥ (neutral e)     = e ∈⊥
⊥ (closure _ _)   = Empty
⊥ true            = Empty
⊥ false           = Empty
⊥ ⟨ _ , _ ⟩       = Empty

⊤ : SemanticType
⊤ = _∈⊤

-- Semantic function space is defined s.t. there is
-- evidence of the evaluation of the application of the
-- function to its argument into the result
_∈_⟶_ : D → SemanticType → SemanticType → Set
f ∈ _∈A ⟶ _∈B  = ∀ (a : D) → a ∈A → ∃[ b ] b ∈B × f · a ↘ b

infix 4 _∈_⟶_

-- Semantic pair space defined similarly
_∈_*_ : D → SemanticType → SemanticType → Set
d ∈ _∈A * _∈B = (∃[ a ] a ∈A × fst d ↘ a) × ∃[ b ] b ∈B × snd d ↘ b

infix 4 _∈_*_

-- We can now define semantic types for the STLC types,
-- with the bottom of the candidate space injected at the
-- base type so that semantic types inhabit the candidate space

_∈Bool : SemanticType
(closure _ _) ∈Bool = Empty
neutral e     ∈Bool = e ∈⊥
true          ∈Bool = Unit
false         ∈Bool = Unit
⟨ _ , _ ⟩     ∈Bool = Empty

mutual
  ⟦_⟧ : Type → SemanticType
  ⟦ T ⟧ d = d ∈⟦ T ⟧

  _∈⟦_⟧ : D → Type → Set
  d ∈⟦ bool ⟧  = d ∈Bool
  d ∈⟦ S * T ⟧ = d ∈ ⟦ S ⟧ * ⟦ T ⟧
  f ∈⟦ S ⇒ T ⟧ = f ∈ ⟦ S ⟧ ⟶ ⟦ T ⟧



-- The candidate space is chosen s.t. ⊥ ⊆ ⊤ → ⊥
-- and ⊥ → ⊤ ⊆ ⊤

⊥⊆⊤→⊥ : ∀ {e : Dⁿᵉ}
      → e ∈⊥
      → neutral e ∈ ⊤ ⟶ ⊥
⊥⊆⊤→⊥ {e} e∈⊥ d d∈⊤ =
  neutral (e · d) ,
  (λ n →
    let (u , e↦u) = e∈⊥ n in
    let (v , d↦v) = d∈⊤ n in
    u · v , readback-app e↦u d↦v) ,
  app-neutral

-- Lemma: Every level is a reifiable neutral
n∈⊥ : ∀ {n : ℕ}
    → level n ∈⊥
n∈⊥ {n} n′ = var (n′ ∸ suc n) , readback-var

⊥→⊤⊆⊤ : ∀ {f : D}
      → f ∈ ⊥ ⟶ ⊤
      → f ∈⊤
⊥→⊤⊆⊤ {true} _ n = true , readback-true
⊥→⊤⊆⊤ {false} _ n = false , readback-false
⊥→⊤⊆⊤ {⟨ a , b ⟩} a,b∈⊥→⊤ n
  with a,b∈⊥→⊤ (neutral (level n)) n∈⊥
... | ()
⊥→⊤⊆⊤ {closure t ρ} clos∈⊥→⊤ n
  with clos∈⊥→⊤ (neutral (level n)) n∈⊥
...  | d , d∈⊤ , app-closure ⟦t⟧ρ↘d
  with d∈⊤ n
...  | v , d↦v =
  ƛ v , readback-abs ⟦t⟧ρ↘d d↦v
⊥→⊤⊆⊤ {neutral e} e∈⊥→⊤ n
  with e∈⊥→⊤ (neutral (level n)) n∈⊥
...  | e·x , e·x∈⊤ , app-neutral
  with e·x∈⊤ n
...  | neutral (u · _) , readback-neutral (readback-app e↦u _) =
  neutral u , readback-neutral e↦u

-- With these properties, we can prove that semantic types inhabit
-- the candidate space
mutual
  ⊤→⊥⊆⟦_⇒_⟧ : ∀ (S T : Type) {f : D}
            → f ∈ ⊤ ⟶ ⊥
            → f ∈⟦ S ⇒ T ⟧
  ⊤→⊥⊆⟦ S ⇒ T ⟧ f∈⊤→⊥ a a∈⟦S⟧
    with ⟦ S ⟧⊆⊤ a∈⟦S⟧
  ...  | a∈⊤
    with f∈⊤→⊥ a a∈⊤
  ...  | neutral e , e∈⊥ , f·a↘e
    with ⊥⊆⟦ T ⟧ e∈⊥
  ...  | e∈⟦T⟧ =
    neutral e , e∈⟦T⟧ , f·a↘e

  ⊥⊆⟦_⟧ : ∀ {e : Dⁿᵉ} (T : Type)
        → e ∈⊥
        → neutral e ∈⟦ T ⟧
  ⊥⊆⟦ bool ⟧ e∈⊥ n = e∈⊥ n
  ⊥⊆⟦_⟧ {e} (S * T) e∈⊥ =
    (neutral (fst e) ,
    (⊥⊆⟦ S ⟧ λ n →
      let (u , e↦u) = e∈⊥ n in
      fst u , readback-fst e↦u) ,
    fst-neutral) ,
    neutral (snd e) ,
    (⊥⊆⟦ T ⟧ λ n →
      let (u , e↦u) = e∈⊥ n in
      snd u , readback-snd e↦u) ,
    snd-neutral
  ⊥⊆⟦ S ⇒ T ⟧ = ⊤→⊥⊆⟦ S ⇒ T ⟧ ∘ ⊥⊆⊤→⊥

  ⟦_⇒_⟧⊆⊥→⊤ : ∀ {f : D} (S T : Type)
            → f ∈⟦ S ⇒ T ⟧
            → f ∈ ⊥ ⟶ ⊤
  ⟦ S ⇒ T ⟧⊆⊥→⊤ f∈⟦S⇒T⟧ (neutral e) e∈⊥
    with f∈⟦S⇒T⟧ (neutral e) (⊥⊆⟦ S ⟧ e∈⊥)
  ...  | d , d∈⟦T⟧ , f·e↘d                 = d , ⟦ T ⟧⊆⊤ d∈⟦T⟧ , f·e↘d

  ⟦_⟧⊆⊤ : ∀ {d : D} (T : Type)
        → d ∈⟦ T ⟧
        → d ∈⊤
  ⟦_⟧⊆⊤ {d} bool pf n
    with d         | pf
  ...  | true      | _   = true , readback-true
  ...  | false     | _   = false , readback-false
  ...  | neutral e | e∈⊥
    with e∈⊥ n
  ...  | u , e↦u         = neutral u , readback-neutral e↦u
  ⟦ S * T ⟧⊆⊤ ((a , a∈⟦S⟧ , fst-pair) , b , b∈⟦T⟧ , snd-pair) n
    with ⟦ S ⟧⊆⊤ a∈⟦S⟧ n | ⟦ T ⟧⊆⊤ b∈⟦T⟧ n
  ...  | v₁ , a↦v₁       | v₂ , b↦v₂       =
    ⟨ v₁ , v₂ ⟩ , readback-pair a↦v₁ b↦v₂
  ⟦ S * T ⟧⊆⊤ ((_ , pf , fst-neutral) , _ , _ , _) n
    with ⟦ S ⟧⊆⊤ pf n
  ... | neutral (fst u) , readback-neutral (readback-fst e↦u) =
    neutral u , readback-neutral e↦u
  ⟦ S ⇒ T ⟧⊆⊤ = ⊥→⊤⊆⊤ ∘ ⟦ S ⇒ T ⟧⊆⊥→⊤

-- Semantically, a term t has type T if evaluating t
-- in an environment where every level is semantically
-- typed according to a context Γ yields a value of
-- semantic type ⟦ T ⟧

_⊨_ : ∀ {n : ℕ} → Ctx n → Env → Set
_⊨_ {n} Γ ρ = ∀ (m : Fin n)
                ------------------
              → ρ (toℕ m) ∈⟦ Γ m ⟧

infix 4 _⊨_

⊨-ext : ∀ {n : ℕ} {Γ : Ctx n} {ρ : Env} {a : D} {S : Type}
        → Γ ⊨ ρ
        → a ∈⟦ S ⟧
        → Γ ∷ S ⊨ ρ ++ a
⊨-ext Γ⊨ρ a∈⟦S⟧ zero    = a∈⟦S⟧
⊨-ext Γ⊨ρ a∈⟦S⟧ (suc m) = Γ⊨ρ m

_⊨_⦂_ : ∀ {n : ℕ} → Ctx n → Term → Type → Set
Γ ⊨ t ⦂ T = ∀ {ρ : Env}
            → Γ ⊨ ρ
              ------------------------------
            → ∃[ d ] d ∈⟦ T ⟧ × ⟦ t ⟧ ρ ↘ d

infix 4 _⊨_⦂_

semanticTrue : ∀ {n : ℕ} {Γ : Ctx n}
             → Γ ⊨ true ⦂ bool
semanticTrue _ = true , tt , eval-true

semanticFalse : ∀ {n : ℕ} {Γ : Ctx n}
             → Γ ⊨ false ⦂ bool
semanticFalse _ = false , tt , eval-false

semanticIf : ∀ {n : ℕ} {Γ : Ctx n} {t₁ t₂ t₃ : Term} {T : Type}
           → Γ ⊨ t₁ ⦂ bool
           → Γ ⊨ t₂ ⦂ T
           → Γ ⊨ t₃ ⦂ T
             -----------------------------
           → Γ ⊨ if t₁ then t₂ else t₃ ⦂ T
semanticIf {T = T} Γ⊨t₁⦂bool Γ⊨t₂⦂T Γ⊨t₃⦂T Γ⊨ρ
  with Γ⊨t₂⦂T Γ⊨ρ             | Γ⊨t₃⦂T Γ⊨ρ
...  | a₁ , a₁∈⟦T⟧ , ⟦t₂⟧ρ↘a₁ | a₂ , a₂∈⟦T⟧ , ⟦t₃⟧ρ↘a₂
  with Γ⊨t₁⦂bool Γ⊨ρ
... | neutral e , e∈⊥ , ⟦t₁⟧ρ↘e =
  neutral (if e then a₁ else a₂) ,
  ⊥⊆⟦ T ⟧
    (λ n →
      let (u , e↦u) = e∈⊥ n in
      let (v₁ , a₁↦v₁) = ⟦ T ⟧⊆⊤ a₁∈⟦T⟧ n in
      let (v₂ , a₂↦v₂) = ⟦ T ⟧⊆⊤ a₂∈⟦T⟧ n in
      if u then v₁ else v₂ , readback-if e↦u a₁↦v₁ a₂↦v₂) ,
  eval-if ⟦t₁⟧ρ↘e ⟦t₂⟧ρ↘a₁ ⟦t₃⟧ρ↘a₂ if-neutral
... | true , _ , ⟦t₁⟧ρ↘true =
  a₁ , a₁∈⟦T⟧ , eval-if ⟦t₁⟧ρ↘true ⟦t₂⟧ρ↘a₁ ⟦t₃⟧ρ↘a₂ if-true
... | false , _ , ⟦t₂⟧ρ↘false =
  a₂ , a₂∈⟦T⟧ , eval-if ⟦t₂⟧ρ↘false ⟦t₂⟧ρ↘a₁ ⟦t₃⟧ρ↘a₂ if-false

semanticVar : ∀ {n : ℕ} {Γ : Ctx n} {m : Fin n}
              ----------------------
            → Γ ⊨ var (toℕ m) ⦂ Γ m
semanticVar {m = m} {ρ} Γ⊨ρ = ρ (toℕ m) , Γ⊨ρ m , eval-var

semanticAbs : ∀ {n : ℕ} {Γ : Ctx n} {t : Term} {S T : Type}
            → Γ ∷ S ⊨ t ⦂ T
              ---------------
            → Γ ⊨ ƛ t ⦂ S ⇒ T
semanticAbs {t = t} Γ∷S⊨t⦂T {ρ = ρ} Γ⊨ρ =
  closure t ρ ,
 (λ a a∈⟦S⟧ →
    let (f , f∈⟦T⟧ , ⟦t⟧ρ↘f) = Γ∷S⊨t⦂T (⊨-ext Γ⊨ρ a∈⟦S⟧) in
    f , f∈⟦T⟧ , app-closure ⟦t⟧ρ↘f) ,
  eval-abs

semanticApp : ∀ {n : ℕ} {Γ : Ctx n} {r s : Term} {S T : Type}
            → Γ ⊨ r ⦂ S ⇒ T
            → Γ ⊨ s ⦂ S
              -------------
            → Γ ⊨ r · s ⦂ T
semanticApp Γ⊨r⦂S⇒T Γ⊨s⦂S Γ⊨ρ
  with Γ⊨r⦂S⇒T Γ⊨ρ           | Γ⊨s⦂S Γ⊨ρ
... | f ,  f∈⟦S⇒T⟧ , ⟦r⟧ρ↘f  | a , a∈⟦S⟧ , ⟦s⟧ρ↘a
  with f∈⟦S⇒T⟧ a a∈⟦S⟧
...  | b , b∈⟦T⟧ , f·a↘b                        =
  b , b∈⟦T⟧ , eval-app ⟦r⟧ρ↘f ⟦s⟧ρ↘a f·a↘b

semanticPair : ∀ {n : ℕ} {Γ : Ctx n} {s t : Term} {S T : Type}
             → Γ ⊨ s ⦂ S
             → Γ ⊨ t ⦂ T
               ---------------------
             → Γ ⊨ ⟨ s , t ⟩ ⦂ S * T
semanticPair Γ⊨s⦂S Γ⊨t⦂T Γ⊨ρ
  with Γ⊨s⦂S Γ⊨ρ          | Γ⊨t⦂T Γ⊨ρ
...  | a , a∈⟦S⟧ , ⟦s⟧ρ↘a | b , b∈⟦T⟧ , ⟦t⟧ρ↘b =
  ⟨ a , b ⟩ ,
  ((a , a∈⟦S⟧ , fst-pair) , b , b∈⟦T⟧ , snd-pair) ,
  eval-pair ⟦s⟧ρ↘a ⟦t⟧ρ↘b

semanticFst : ∀ {n : ℕ} {Γ : Ctx n} {t : Term} {S T : Type}
            → Γ ⊨ t ⦂ S * T
              -------------
            → Γ ⊨ fst t ⦂ S
semanticFst Γ⊨t⦂S*T Γ⊨ρ
  with Γ⊨t⦂S*T Γ⊨ρ
...  | ⟨ a , _ ⟩ , ((_ , a∈⟦S⟧ , fst-pair) , _) , ⟦t⟧ρ↘a,b =
  a , a∈⟦S⟧ , eval-fst ⟦t⟧ρ↘a,b fst-pair
... | neutral e , ((_ , fst-e∈⟦S⟧ , fst-neutral) , _) , ⟦t⟧ρ↘e =
  neutral (fst e) , fst-e∈⟦S⟧ , eval-fst ⟦t⟧ρ↘e fst-neutral

semanticSnd : ∀ {n : ℕ} {Γ : Ctx n} {t : Term} {S T : Type}
            → Γ ⊨ t ⦂ S * T
              -------------
            → Γ ⊨ snd t ⦂ T
semanticSnd Γ⊨t⦂S*T Γ⊨ρ
  with Γ⊨t⦂S*T Γ⊨ρ
...  | ⟨ _ , b ⟩ , (_ , (_ , b∈⟦T⟧ , snd-pair)) , ⟦t⟧ρ↘a,b =
  b , b∈⟦T⟧ , eval-snd ⟦t⟧ρ↘a,b snd-pair
... | neutral e , (_ , (_ , snd-e∈⟦T⟧ , snd-neutral)) , ⟦t⟧ρ↘e =
  neutral (snd e) , snd-e∈⟦T⟧ , eval-snd ⟦t⟧ρ↘e snd-neutral

-- We can also prove the fundamental lemma for logical relations:
-- a term of syntactic type T has semantic type T

fundamental-lemma : ∀ {n : ℕ} {Γ : Ctx n} {t : Term} {T : Type}
                  → Γ ⊢ t ⦂ T
                    ---------
                  → Γ ⊨ t ⦂ T
fundamental-lemma {Γ = Γ} typingTrue =
  semanticTrue {Γ = Γ}
fundamental-lemma {Γ = Γ} typingFalse =
  semanticFalse {Γ = Γ}
fundamental-lemma {Γ = Γ} {T = T} (typingIf Γ⊢t₁⦂bool Γ⊢t₂⦂T Γ⊢t₃⦂T) =
  semanticIf {Γ = Γ} {T = T}
    (fundamental-lemma Γ⊢t₁⦂bool)
    (fundamental-lemma Γ⊢t₂⦂T)
    (fundamental-lemma Γ⊢t₃⦂T)
fundamental-lemma {Γ = Γ} (typingVar refl) =
  semanticVar {Γ = Γ}
fundamental-lemma {T = _ ⇒ T} (typingAbs Γ⊢t⦂T) =
  semanticAbs {T = T} (fundamental-lemma Γ⊢t⦂T)
fundamental-lemma {Γ = Γ} (typingApp {S = S} {T} Γ⊢r⦂S⇒T Γ⊢s⦂S) =
  semanticApp {Γ = Γ} {S = S} {T}
    (fundamental-lemma Γ⊢r⦂S⇒T)
    (fundamental-lemma Γ⊢s⦂S)
fundamental-lemma {Γ = Γ} (typingPair {S = S} {T} Γ⊢s⦂S Γ⊢t⦂T) =
  semanticPair {Γ = Γ} {S = S} {T}
    (fundamental-lemma Γ⊢s⦂S)
    (fundamental-lemma Γ⊢t⦂T)
fundamental-lemma {Γ = Γ} (typingFst {S = S} {T} Γ⊢t⦂S*T) =
  semanticFst {Γ = Γ} {S = S} {T}
    (fundamental-lemma Γ⊢t⦂S*T)
fundamental-lemma {Γ = Γ} (typingSnd {S = S} {T} Γ⊢t⦂S*T) =
  semanticSnd {Γ = Γ} {S = S} {T}
    (fundamental-lemma Γ⊢t⦂S*T)

{- Strong normalization -}

-- Intial environment for evaluation of expression with free
-- indices below n
ρₙ : ℕ → Env
ρₙ n i = neutral (level (n ∸ (suc i)))

-- First, we prove that a well-typed term evaluates to a value of
-- type ⟦ T ⟧ using the fundamental lemma. Here, we use the fact
-- that semantic types inhabit the candidate space: each value in
-- the environment is a reifiable neutral ∈ ⊥ ⊆ ⟦ T ⟧, so each
-- value has the semantic type corresponding to the context
well-typed-evaluates : ∀ {n : ℕ} {Γ : Ctx n} {t : Term} {T : Type}
                     → Γ ⊢ t ⦂ T
                       --------------------------------
                     → ∃[ d ] d ∈⟦ T ⟧ × ⟦ t ⟧ ρₙ n ↘ d
well-typed-evaluates {n} {Γ} Γ⊢t⦂T = fundamental-lemma Γ⊢t⦂T Γ⊨ρₙ where
  Γ⊨ρₙ : Γ ⊨ ρₙ n
  Γ⊨ρₙ m = ⊥⊆⟦ Γ m ⟧ λ n′ → var (n′ ∸ suc (n ∸ suc (toℕ m))) , readback-var

nf_⦂_↦_ : ∀ ℕ → Term → Nf → Set
nf n ⦂ t ↦ v = ∃[ d ] ⟦ t ⟧ ρₙ n ↘ d × Rⁿᶠ n ⦂ d ↦ v

-- Now, we can prove that a well-typed term of type t normalizes
-- to a normal form again using the fact that semantic types inhabit
-- the candidate space: ⟦ T ⟧ ⊆ ⊤, therefore the value t evaluates to
-- is reifiable to a normal form
well-typed-strongly-normalizing : ∀ {n : ℕ} {Γ : Ctx n} {t : Term} {T : Type}
                                → Γ ⊢ t ⦂ T
                                  -------------------
                                → ∃[ v ] nf n ⦂ t ↦ v
well-typed-strongly-normalizing {n} {T = T} Γ⊢t⦂T
  with well-typed-evaluates Γ⊢t⦂T
...  | d , d∈⟦T⟧ , ⟦t⟧ρₙ↘d
  with ⟦ T ⟧⊆⊤ d∈⟦T⟧ n
...  | v , d↦v                    = v , d , ⟦t⟧ρₙ↘d , d↦v
