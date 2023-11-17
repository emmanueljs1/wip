import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _∸_; s≤s; _≤_)
open import Data.Nat.Properties as Nat using (≤-refl; ≤-trans)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Unary using (_∈_)
open Eq using (_≡_; refl; sym)

-- Type soundness for a language with nontermination
-- (if computation is finite, then it does not become "stuck")
module Nontermination where

suc≡n+1 : ∀ k → suc k ≡ k + 1
suc≡n+1 k
  rewrite Nat.+-suc k 0 | Nat.+-identityʳ k = refl

data Type : Set where
  base : Type
  _⇒_ : Type → Type → Type

infixr 7 _⇒_

variable S T : Type

data Ctx : Set where
  ∅ : Ctx
  _∷_ : Ctx → Type → Ctx

infixl 5 _∷_

variable Γ Δ : Ctx

data _∋_ : Ctx → Type → Set where
  zero : Γ ∷ T ∋ T
  suc : Γ ∋ T → Γ ∷ S ∋ T

infix 4 _∋_

variable x : Γ ∋ T

data _⊢_ : Ctx → Type → Set where
  var : Γ ∋ T → Γ ⊢ T
  ƛ_ : Γ ∷ S ⊢ T → Γ ⊢ S ⇒ T
  _·_ : Γ ⊢ S ⇒ T → Γ ⊢ S → Γ ⊢ T
  μ_ : Γ ∷ T ⊢ T → Γ ⊢ T

infix 4 _⊢_
infix 5 ƛ_
infix 5 μ_
infixl 7 _·_

variable r s t : Γ ⊢ T

mutual
  data Env : Ctx → Set where
    ∅ : Env ∅
    _∷_ : Env Γ → Domain T → Env (Γ ∷ T)

  data Domain : Type → Set where
    ⟨_⟩_ : Γ ⊢ T → Env Γ → Domain T

infix 6 ⟨_⟩_

variable γ : Env Γ
variable δ : Env Δ
variable a b d f : Domain T

_??_ : Env Γ → Γ ∋ T → Domain T
(γ ∷ a) ?? zero = a
(γ ∷ a) ?? suc x = γ ?? x

infix 5 _??_

variable n i j k j₁ j₂ : ℕ

data _⊢_⇓_#_ : Env Γ → Γ ⊢ T → Domain T → ℕ → Set where
  evalVar : γ ?? x ≡ ⟨ t ⟩ δ
          → δ ⊢ t ⇓ a # k
            -----------------
          → γ ⊢ var x ⇓ a # k

  evalAbs : γ ⊢ ƛ t ⇓ ⟨ ƛ t ⟩ γ # zero

  evalApp : γ ⊢ r ⇓ ⟨ ƛ t ⟩ δ # j₁
          → δ ∷ ⟨ s ⟩ γ ⊢ t ⇓ a # j₂
            -----------------------------
          → γ ⊢ r · s ⇓ a # suc (j₁ + j₂)

  evalRec : γ ∷ ⟨ μ t ⟩ γ ⊢ t ⇓ a # k
            -------------------------
          → γ ⊢ μ t ⇓ a # suc k

infix 4 _⊢_⇓_#_

mutual
  -- Step-indexed logical relation for domain
  𝒟[_,_] : (T : Type) → ℕ → Domain T → Set
  𝒟[ S ⇒ T , k ] (⟨ ƛ t ⟩ δ) =
    ∀ {j : ℕ}
    → j < k
    → ∀ {Γ} {γ : Env Γ} {s : Γ ⊢ S}
      → (γ , s) ∈ 𝒞[ S , j ]
      → (δ ∷ ⟨ s ⟩ γ , t) ∈ 𝒞[ T , j ]
  𝒟[ _ , _ ] _ = ⊥

  -- Step-indexed logical relation for terms
  𝒞[_,_] : (T : Type) → ℕ → Env Γ × Γ ⊢ T → Set
  𝒞[ T , k ] (γ , t) =
    ∀ {j} {b}
    → j < k
    → γ ⊢ t ⇓ b # j → b ∈ 𝒟[ T , k ∸ j ]

-- Step-indexed semantic typing for environments
_⊨_#_ : (Γ : Ctx) → Env Γ → ℕ → Set
Γ ⊨ γ # k = ∀ {T} {Δ : Ctx} {t : Δ ⊢ T} {δ : Env Δ}
            → (x : Γ ∋ T)
            → γ ?? x ≡ ⟨ t ⟩ δ
            → (δ , t) ∈ 𝒞[ T , k ]

infix 4 _⊨_#_

-- Extending semantically-typed environments
_^_ : Δ ⊨ δ # k → (γ , s) ∈ 𝒞[ S , k ] → Δ ∷ S ⊨ δ ∷ ⟨ s ⟩ γ # k
(⊨δ ^ s∈𝒞) zero refl = s∈𝒞
(⊨δ ^ s∈𝒞) (suc x) = ⊨δ x

-- Step-indexed semantic typing
⊨_#_ : Γ ⊢ T → ℕ → Set
⊨_#_ {Γ} {T} t k =
  ∀ {γ : Env Γ}
  → Γ ⊨ γ # k
  → (γ , t) ∈ 𝒞[ T , k ]

-- Semantic typing: step-indexed typing is satisfied at all finite numbers
⊨_ : Γ ⊢ T → Set
⊨_ {Γ} {T} t =
  ∀ (k : ℕ) → ⊨ t # k

𝒟-anti-monotonicity : j ≤ k → a ∈ 𝒟[ T , k ] → a ∈ 𝒟[ T , j ]
𝒟-anti-monotonicity {T = S ⇒ T} {⟨ ƛ t ⟩ δ} le a∈𝒟 le′ = a∈𝒟 (≤-trans le′ le)

𝒞-anti-monotonicity : j ≤ k → (γ , t) ∈ 𝒞[ T , k ] → (γ , t) ∈ 𝒞[ T , j ]
𝒞-anti-monotonicity le t∈𝒞 {j′} le′ t⇓ =
  𝒟-anti-monotonicity (Nat.∸-monoˡ-≤ j′ le) (t∈𝒞 (≤-trans le′ le) t⇓)

-- Semantic typing for environments is downwards closed
⊨-downwards-closure : j ≤ k → Γ ⊨ γ # k → Γ ⊨ γ # j
⊨-downwards-closure le ⊨γ x eq {j′} lt t⇓ =
  𝒟-anti-monotonicity (Nat.∸-monoˡ-≤ j′ le) (⊨γ x eq (≤-trans lt le) t⇓)

-- Well-typed terms are semantically typed
fundamental-lemma : (t : Γ ⊢ T) → ⊨ t
fundamental-lemma (var x) (suc k) {γ = γ} ⊨γ le (evalVar eq t⇓) =
  ⊨γ x eq le t⇓
fundamental-lemma (ƛ t) (suc k) {γ = γ} ⊨γ _ evalAbs {j} le s∈𝒞 =
  fundamental-lemma t j (⊨-downwards-closure {γ = γ} (Nat.<⇒≤ le) ⊨γ ^ s∈𝒞)
fundamental-lemma {T = T} (r · s) (suc k) {γ = γ} ⊨γ {b = b} (s≤s le)
  (evalApp {j₁ = j₁} {j₂ = j₂} r⇓ t⇓) =
  lemma
  where
    -- Inequality proofs
    le₀ = ≤-trans (≤-trans (Nat.n≤1+n j₁) (s≤s (Nat.m≤m+n j₁ j₂))) le
    le₁ = ≤-trans (s≤s le₀) (s≤s ≤-refl)
    le₂ = ≤-trans (Nat.m∸n≤m k j₁) (Nat.n≤1+n k)
    le₃ : suc (k ∸ j₁) ≤ suc k ∸ j₁
    le₃ rewrite suc≡n+1 k | Nat.+-∸-comm {k} 1 {j₁} le₀ | suc≡n+1 (k ∸ j₁) = ≤-refl
    le₄ : suc j₂ ≤ k ∸ j₁
    le₄ rewrite sym (Nat.+-suc j₁ j₂) with Nat.∸-monoˡ-≤ j₁ le
    ...  | le′ rewrite Nat.+-∸-comm {j₁} (suc j₂) {j₁} ≤-refl | Nat.n∸n≡0 j₁ = le′

    ihᵣ = fundamental-lemma r (suc k) ⊨γ le₁ r⇓
    ihₛ = fundamental-lemma s (k ∸ j₁) (⊨-downwards-closure {γ = γ} le₂ ⊨γ)

    lemma : 𝒟[ T , k ∸ (j₁ + j₂) ] b
    lemma with ihᵣ le₃ ihₛ le₄ t⇓
    ... | ih rewrite Nat.∸-+-assoc k j₁ j₂ = ih
fundamental-lemma (μ t) (suc n) {γ = γ} ⊨γ (s≤s le) (evalRec t⇓) =
  fundamental-lemma t n (⊨γ′ ^ fundamental-lemma (μ t) n ⊨γ′) le t⇓
  where
    ⊨γ′ = ⊨-downwards-closure {γ = γ} (Nat.n≤1+n n) ⊨γ
