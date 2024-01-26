{-# OPTIONS --sized-types #-}

open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Data.Unit using (⊤)
open import Relation.Unary using (_∈_)
open import Size

module DelayCBN where

variable i : Size

data Type : Set where
  ι : Type
  _⇒_ : Type → Type → Type

infixr 7 _⇒_
variable S T : Type

data Ctx : Set where
  ε : Ctx
  _•_ : Ctx → Type → Ctx

infixl 5 _•_
variable Γ : Ctx

data _∋_ : Ctx → Type → Set where
  zero : Γ • T ∋ T
  suc : Γ ∋ T → Γ • S ∋ T

infix 4 _∋_
variable x : Γ ∋ T

data _⊢_ : Ctx → Type → Set where
  var : Γ ∋ T → Γ ⊢ T
  _∙_ : Γ ⊢ S ⇒ T → Γ ⊢ S → Γ ⊢ T
  ƛ_ : Γ • S ⊢ T → Γ ⊢ S ⇒ T

infix 4 _⊢_
variable r s t : Γ ⊢ T

mutual
  data Value : Type → Set where
    ⟨_⟩_ : Γ ⊢ T → Env Γ → Value T
    wrong : Value T

  data Env : Ctx → Set where
    ε : Env ε
    _•_ : Env Γ → Value T → Env (Γ • T)

infix 6 ⟨_⟩_
variable a b f : Value T
variable γ δ : Env Γ

_??_ : Env Γ → Γ ∋ T → Value T
γ • a ?? zero = a
γ • a ?? suc x = γ ?? x

infix 4 _??_

mutual
  data Delay (i : Size) (A : Set) : Set where
    now : A → Delay i A
    later : ∞Delay i A → Delay i A

  record ∞Delay (i : Size) (A : Set) : Set where
    coinductive
    field
      force : ∀ {j : Size< i} → Delay j A

open ∞Delay

mutual
  _>>=_ : ∀ {A B : Set} → Delay i A → (A → Delay i B) → Delay i B
  now a >>= f = f a
  later a∞ >>= f = later (a∞ ∞>>= f)

  _∞>>=_ : ∀ {A B : Set} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
  force (a∞ ∞>>= f) = force a∞ >>= f

infix 5 _>>=_

data _⇓_ {A : Set} : Delay ∞ A → A → Set where
  ⇓now : ∀ {a : A} → now a ⇓ a
  ⇓later : ∀ {a : A} {a∞ : ∞Delay ∞ A} → force a∞ ⇓ a → later a∞ ⇓ a

infix 4 _⇓_

_⇓ : ∀ {A : Set} → Delay ∞ A → Set
a? ⇓ = ∃[ a ] a? ⇓ a

mutual
  eval : Γ ⊢ T → Env Γ → ∞Delay i (Value T)
  eval (var x) γ
    with γ ?? x
  ... | ⟨ t ⟩ δ = λ{ .force → later (eval t δ) }
  ... | wrong = λ{ .force → now wrong }
  eval (r ∙ s) γ =
    eval r γ ∞>>= λ where
                      (⟨ ƛ t ⟩ δ) →
                        later λ{ .force → later (eval t (δ • ⟨ s ⟩ γ)) }
                      _ → now wrong
  eval (ƛ t) γ =
    λ{ .force → now (⟨ ƛ t ⟩ γ) }

mutual
  𝒱[_] : (T : Type) → Value T → Set
  𝒱[ S ⇒ T ] (⟨ ƛ t ⟩ δ) =
    ∀ {Γ} {γ : Env Γ} {s : Γ ⊢ S}
    → (γ , s) ∈ ℰ[ S ]
    → (δ • ⟨ s ⟩ γ , t) ∈ ℰ[ T ]
  𝒱[ _ ] _ = ⊥

  𝒟[_] : (T : Type) → Delay ∞ (Value T) → Set
  𝒟[ T ] a? = ∃[ a ] a? ⇓ a × a ∈ 𝒱[ T ]

  ℰ[_] : (T : Type) → Env Γ × Γ ⊢ T → Set
  ℰ[ T ] (γ , t) = force (eval t γ) ∈ 𝒟[ T ]

_⊨_ : (Γ : Ctx) → Env Γ → Set
ε ⊨ ε = ⊤
Γ • T ⊨ γ • a = Γ ⊨ γ × a ∈ 𝒱[ T ]

infix 4 _⊨_

semantic-typing : Γ ⊢ T → Set
semantic-typing {Γ} {T} t =
  ∀ {γ : Env Γ}
  → Γ ⊨ γ
  → (γ , t) ∈ ℰ[ T ]

infix 4 semantic-typing

syntax semantic-typing {Γ} {T} t = Γ ⊨ t ∷ T

fundamental-lemma : ∀ (t : Γ ⊢ T) → Γ ⊨ t ∷ T
fundamental-lemma (var x) ⊨γ = {!!}
fundamental-lemma (r ∙ s) ⊨γ = {!!}
fundamental-lemma (ƛ t) ⊨γ = {!!}
