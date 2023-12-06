import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _<_; _∸_)
open import Data.Nat.Properties as Nat using (≤-refl)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Relation.Unary using (_∈_)
open Eq using (_≡_; refl)

module StepIndexedInterpreter where

variable n k j : ℕ
variable x : Fin n

data Term : ℕ → Set where
  var : Fin n → Term n
  ƛ_ : Term (suc n) → Term n
  _·_ : Term n → Term n → Term n

variable r s t : Term n

infixl 7 _·_
infix 5 ƛ_

mutual
  data Env : ℕ → Set where
    ε : Env zero
    _•_ : Env n → Domain → Env (suc n)

  data Domain : Set where
    wrong : Domain
    timeout : Domain
    ⟨ƛ_⟩_ : Term (suc n) → Env n → Domain

variable γ δ : Env n
variable a b d f : Domain

infix 6 ⟨ƛ_⟩_

data Good : Domain → Set where
  timeoutGood : Good timeout
  closureGood : Good (⟨ƛ t ⟩ γ)

_??_ : Env n → Fin n → Domain
(_ • a) ?? zero = a
(γ • _) ?? suc x = γ ?? x

infix 5 _??_

eval : Term n → Env n → ℕ → Domain
eval t γ zero = timeout
eval (var x) γ (suc n) = γ ?? x
eval (ƛ t) γ (suc n) = ⟨ƛ t ⟩ γ
eval (r · s) γ (suc n)
  with eval r γ n
... | timeout = wrong
... | wrong = wrong
... | (⟨ƛ t ⟩ δ)
  with eval s γ n
... | a =
  eval t (δ • a) n

data Type : Set where
  ι : Type
  _⇒_ : Type → Type → Type

variable S T : Type

infixr 7 _⇒_

data Ctx : ℕ → Set where
  ε : Ctx zero
  _•_ : Ctx n → Type → Ctx (suc n)

variable Γ : Ctx n

data _∷_∈_ : Fin n → Type → Ctx n → Set where
  here : zero ∷ T ∈ Γ • T
  there : x ∷ T ∈ Γ → suc x ∷ T ∈ Γ • S

infix 4 _∷_∈_

data _⊢_∷_ : Ctx n → Term n → Type → Set where
  ⊢var : x ∷ T ∈ Γ → Γ ⊢ var x ∷ T

  ⊢abs : Γ • S ⊢ t ∷ T → Γ ⊢ ƛ t ∷ S ⇒ T

  ⊢app : Γ ⊢ r ∷ S ⇒ T → Γ ⊢ s ∷ S → Γ ⊢ r · s ∷ T

infix 4 _⊢_∷_

mutual
  𝒟⟦_,_⟧ : Type → ℕ → Domain → Set
  𝒟⟦ S ⇒ T , k ⟧ (⟨ƛ t ⟩ δ) =
    ∀ {j : ℕ}
    → j < k
    → ∀ {a} → a ∈ 𝒟⟦ S , j ⟧
      → (δ • a , t) ∈ ℰ⟦ T , j ⟧
  𝒟⟦ ι , _ ⟧ timeout = ⊤
  𝒟⟦ _ , _ ⟧ _ = ⊥

  ℰ⟦_,_⟧ : Type → ℕ → Env n × Term n → Set
  ℰ⟦ T , k ⟧ (γ , t) =
      ∀ {j} {b}
      → j < k
      → eval t γ j ≡ b → b ∈ 𝒟⟦ T , k ∸ j ⟧

_⊨_#_ : Ctx n → Env n → ℕ → Set
Γ ⊨ γ # k =
  ∀ {x} {T} {a} → x ∷ T ∈ Γ → γ ?? x ≡ a → a ∈ 𝒟⟦ T , k ⟧

infix 4 _⊨_#_

_⊨_∷_#_ : Ctx n → Term n → Type → ℕ → Set
Γ ⊨ t ∷ T # k =
  ∀ {γ} → Γ ⊨ γ # k → (γ , t) ∈ ℰ⟦ T , k ⟧

infix 4 _⊨_∷_#_

_⊨_∷_ : Ctx n → Term n → Type → Set
Γ ⊨ t ∷ T = ∀ k → Γ ⊨ t ∷ T # k

infix 4 _⊨_∷_

fundamental-lemma : Γ ⊢ t ∷ T → Γ ⊨ t ∷ T
fundamental-lemma (⊢var x) (suc k) x₁ x₂ x₃ = {!!}
fundamental-lemma (⊢abs x) (suc k) x₁ x₂ x₃ = {!!}
fundamental-lemma (⊢app x x₄) (suc k) x₁ x₂ x₃ = {!!}

𝒟→good : b ∈ 𝒟⟦ T , k ⟧ → Good b
𝒟→good {timeout} {ι} _ = timeoutGood
𝒟→good {⟨ƛ _ ⟩ _} {_ ⇒ _} _ = closureGood

type-soundness : ε ⊢ t ∷ T → Good (eval t ε n)
type-soundness {n = n} ⊢t =
  𝒟→good (fundamental-lemma ⊢t (suc n) (λ ()) ≤-refl refl)
