import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; s≤s; _<_; _∸_; _≤_)
open import Data.Nat.Properties as Nat using (≤-refl; ≤-trans)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
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
eval (ƛ t) γ (suc n) = ⟨ ƛ t ⟩ γ -- maybe: have to "save" max remaining steps
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
  𝒟[ _ , _ ] timeout = ⊤
  𝒟[ _ , _ ] _ = ⊥

  ℰ[_,_] : (T : Type) → ℕ → Env Γ × Γ ⊢ T → Set
  ℰ[ T , k ] (γ , t) =
    ∀ {j} {b}
    → j < k
    → eval t γ j ≡ b → b ∈ 𝒟[ T , k ∸ j ]

𝒟-anti-monotonicity : j ≤ k → d ∈ 𝒟[ T , k ] → d ∈ 𝒟[ T , j ]
𝒟-anti-monotonicity {T = ι} {d = error} le ()
𝒟-anti-monotonicity {T = _ ⇒ _} {d = error} le ()
𝒟-anti-monotonicity {T = ι} {d = timeout} le x = tt
𝒟-anti-monotonicity {T = _ ⇒ _} {d = timeout} le x = tt
𝒟-anti-monotonicity {T = S ⇒ T} {d = ⟨ ƛ t ⟩ δ} le d∈𝒟 lt =
  d∈𝒟 (≤-trans lt le)

ℰ-anti-monotonicity : j ≤ k → (γ , t) ∈ ℰ[ T , k ] → (γ , t) ∈ ℰ[ T , j ]
ℰ-anti-monotonicity le t∈ℰ {j′} lt refl =
  𝒟-anti-monotonicity (Nat.∸-monoˡ-≤ j′ le) (t∈ℰ (≤-trans lt le) refl)

_⊨_#_ : (Γ : Ctx) → Env Γ → ℕ → Set
Γ ⊨ γ # k =
  ∀ {T} → (x : Γ ∋ T) → ∃[ Δ ] Σ[ t ∈ Δ ⊢ T ] ∃[ δ ] γ ?? x ≡ ⟨ t ⟩ δ × (δ , t) ∈ ℰ[ T , k ]

infix 4 _⊨_#_

_^_ : Γ ⊨ γ # k → (δ , s) ∈ ℰ[ S , k ] → Γ • S ⊨ γ • ⟨ s ⟩ δ # k
_^_ = {!!}

⊨-anti-monotonicity : j ≤ k → Γ ⊨ γ # k → Γ ⊨ γ # j
⊨-anti-monotonicity le ⊨γ x with ⊨γ x
... | Δ , t , δ , eq , t∈ℰ =
  Δ , t , δ , eq , ℰ-anti-monotonicity le t∈ℰ

semantic-typing-idx : (Γ : Ctx) → (T : Type) → Γ ⊢ T → ℕ → Set
semantic-typing-idx Γ T t k = ∀ {γ} → Γ ⊨ γ # k → (γ , t) ∈ ℰ[ T , k ]

infix 4 semantic-typing-idx
syntax semantic-typing-idx Γ T t k = Γ ⊨ t ∷ T # k

semantic-typing : (Γ : Ctx) → (T : Type) → Γ ⊢ T → Set
semantic-typing Γ T t = ∀ k → Γ ⊨ t ∷ T # k

infix 4 semantic-typing
syntax semantic-typing Γ T t = Γ ⊨ t ∷ T

fundamental-lemma : ∀ (t : Γ ⊢ T) → Γ ⊨ t ∷ T
fundamental-lemma {T = ι} (var x) (suc k) {γ = γ} ⊨γ {zero} le refl = tt
fundamental-lemma {T = _ ⇒ _} (var x) (suc k) {γ = γ} ⊨γ {zero} le refl = tt
fundamental-lemma (var x) (suc k) {γ = γ} ⊨γ {suc j} (s≤s le) eq
  with ⊨γ x
... | Δ , t , δ , eq′ , t∈ℰ
  with γ ?? x     | eq′
...  | .(⟨ t ⟩ δ) | refl =
  𝒟-anti-monotonicity
    {!!}
    (t∈ℰ (≤-trans le (Nat.n≤1+n k)) eq)
fundamental-lemma (ƛ t) (suc k) ⊨γ {zero} lt refl = tt
fundamental-lemma (ƛ t) (suc k) {γ = γ} ⊨γ {suc j} (s≤s le) refl {j′} lt s∈ℰ =
  fundamental-lemma t j′ (⊨-anti-monotonicity {!!} ⊨γ ^ s∈ℰ)
fundamental-lemma (μ t) = {!!}
fundamental-lemma (r · s) = {!!}

𝒟→Good : d ∈ 𝒟[ T , k ] → Good d
𝒟→Good {ι} {d = error} {k = zero} ()
𝒟→Good {_ ⇒ _} {d = error} {k = zero} ()
𝒟→Good {d = timeout} _ = timeoutGood
𝒟→Good {_ ⇒ _} {d = ⟨ _ ⟩ _} {k = zero} _ = closureGood
𝒟→Good {ι} {d = error} {k = suc _} ()
𝒟→Good {_ ⇒ _} {d = error} {k = suc _} ()
𝒟→Good {_ ⇒ _} {d = ⟨ _ ⟩ _} {k = suc _} _ = closureGood

type-soundness : ∀ (t : ε ⊢ T) → eval t ε n ≡ d → Good d
type-soundness {n = n} t refl =
  𝒟→Good (fundamental-lemma t (suc n) (λ ()) ≤-refl refl)
