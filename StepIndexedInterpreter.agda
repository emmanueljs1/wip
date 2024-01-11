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

data Con (A : Set) : Set where
  ε : Con A
  _•_ : Con A → A → Con A

infixl 5 _•_

data Type : Set where
  ι : Type
  _⇒_ : Type → Type → Type

variable S T : Type

infixr 7 _⇒_

Ctx = Con Type
variable Γ : Ctx

data _∋_ : Ctx → Type → Set where
  zero : Γ • T ∋ T
  suc : Γ ∋ T → Γ • S ∋ T

infix 4 _∋_

data _⊢_ : Ctx → Type → Set where
  var : Γ ∋ T → Γ ⊢ T
  ƛ_ : Γ • S ⊢ T → Γ ⊢ S ⇒ T
  μ_ : Γ • T ⊢ T → Γ ⊢ T
  _·_ : Γ ⊢ S ⇒ T → Γ ⊢ S → Γ ⊢ T

infix 4 _⊢_

variable r s t : Γ ⊢ T

mutual
  data Env : Ctx → Set where
    ε : Env ε
    _•_ : Env Γ → Domain T → Env (Γ • T)

  data Domain : Type → Set where
    error : Domain T
    timeout : Domain T
    ⟨_⟩_ : Γ ⊢ T → Env Γ → Domain T

infix 6 ⟨_⟩_

variable γ δ : Env Γ
variable a b d f : Domain T

_??_ : Env Γ → Γ ∋ T → Domain T
(γ • a) ?? zero = a
(γ • _) ?? suc x = γ ?? x

infix 5 _??_

eval : Γ ⊢ T → Env Γ → ℕ → Domain T
eval t γ zero = timeout
eval (var x) γ (suc n)
  with γ ?? x
...  | timeout = error
...  | error = error
...  | ⟨ t ⟩ δ = eval t δ n
eval (ƛ t) γ (suc n) = ⟨ ƛ t ⟩ γ
eval (μ t) γ (suc n) = eval t (γ • ⟨ μ t ⟩ γ) n
eval (r · s) γ (suc n)
  with eval r γ n
... | ⟨ var _ ⟩ _ = error
... | ⟨ μ _ ⟩ _ = error
... | ⟨ _ · _ ⟩ _ = error
... | error = error
... | timeout = timeout
... | ⟨ ƛ t ⟩ δ = eval t (δ • ⟨ s ⟩ γ) n

data Good : Domain T → Set where
  closureGood : Good (⟨ t ⟩ δ)
  timeoutGood : Good {T} timeout

mutual
  𝒟[_,_] : (T : Type) → ℕ → Domain T → Set
  𝒟[ S ⇒ T , k ] (⟨ ƛ t ⟩ δ) =
    ∀ {j : ℕ}
    → j < k
    → ∀ {Γ} {γ : Env Γ} {s : Γ ⊢ S}
      → (γ , s) ∈ ℰ[ S , j ]
      → (δ • ⟨ s ⟩ γ , t) ∈ ℰ[ T , j ]
  𝒟[ _ , _ ] _ = ⊥

  ℰ[_,_] : (T : Type) → ℕ → Env Γ × Γ ⊢ T → Set
  ℰ[ T , k ] (γ , t) =
    ∀ {j} {b}
    → j < k
    → eval t γ j ≡ b → b ∈ 𝒟[ T , k ∸ j ]

_⊨_#_ : (Γ : Ctx) → Env Γ → ℕ → Set
Γ ⊨ γ # k =
  ∀ {T} → (x : Γ ∋ T) → ∀ {a} → γ ?? x ≡ a → a ∈ 𝒟[ T , k ]

infix 4 _⊨_#_

semantic-typing-k : (Γ : Ctx) → (T : Type) → Γ ⊢ T → ℕ → Set
semantic-typing-k Γ T t k = ∀ {γ} → Γ ⊨ γ # k → (γ , t) ∈ ℰ[ T , k ]

infix 4 semantic-typing-k
syntax semantic-typing-k Γ T t k = Γ ⊨ t ∷ T # k

semantic-typing : (Γ : Ctx) → (T : Type) → Γ ⊢ T → Set
semantic-typing Γ T t = ∀ k → Γ ⊨ t ∷ T # k

infix 4 semantic-typing
syntax semantic-typing Γ T t = Γ ⊨ t ∷ T

fundamental-lemma : ∀ (t : Γ ⊢ T) → Γ ⊨ t ∷ T
fundamental-lemma = {!!}

𝒟→Good : d ∈ 𝒟[ T , k ] → Good d
𝒟→Good {ι} {d = error} {k = zero} ()
𝒟→Good {_ ⇒ _} {d = error} {k = zero} ()
𝒟→Good {ι} {d = timeout} {k = zero} ()
𝒟→Good {_ ⇒ _} {d = timeout} {k = zero} _ = timeoutGood
𝒟→Good {_ ⇒ _} {d = ⟨ _ ⟩ _} {k = zero} _ = closureGood
𝒟→Good {ι} {d = error} {k = suc _} ()
𝒟→Good {_ ⇒ _} {d = error} {k = suc _} ()
𝒟→Good {ι} {d = timeout} {k = suc _} ()
𝒟→Good {_ ⇒ _} {d = timeout} {k = suc _} ()
𝒟→Good {_ ⇒ _} {d = ⟨ _ ⟩ _} {k = suc _} _ = closureGood

type-soundness : ∀ (t : ε ⊢ T) → eval t ε n ≡ d → Good d
type-soundness {n = n} t refl =
  𝒟→Good (fundamental-lemma t (suc n) (λ ()) ≤-refl refl)
