{-# OPTIONS --sized-types #-}

open import Data.Empty using (⊥)
import Relation.Binary.PropositionalEquality as Eq
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Unary using (_∈_)
open import Size
open Eq using (_≡_; refl)

module DelayNontermination where

variable i : Size

data Type : Set where
  𝟚 : Type
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
  yes no : Γ ⊢ 𝟚
  var : Γ ∋ T → Γ ⊢ T
  _∙_ : Γ ⊢ S ⇒ T → Γ ⊢ S → Γ ⊢ T
  ƛ_ : Γ • S ⊢ T → Γ ⊢ S ⇒ T
  μ_ : Γ • T ⊢ T → Γ ⊢ T

infix 5 ƛ_ μ_
infix 4 _⊢_
variable r s t : Γ ⊢ T

mutual
  data Value : Type → Set where
    yes no : Value 𝟚
    ⟨_⟩_ : Γ ⊢ T → Env Γ → Value T
    wrong : Value T

  data Env : Ctx → Set where
    ε : Env ε
    _•_ : Env Γ → Value T → Env (Γ • T)

infix 6 ⟨_⟩_
variable a b f : Value T
variable γ δ : Env Γ

_??_ : Env Γ → Γ ∋ T → Value T
(γ • a) ?? zero = a
(γ • a) ?? suc x = γ ?? x

infix 5 _??_

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

bind⇓ : ∀ {A B : Set} {f : A → Delay ∞ B}
          {a? : Delay ∞ A} {a : A} {b : B}
        → a? ⇓ a → f a ⇓ b → a? >>= f ⇓ b
bind⇓ ⇓now a?⇓a = a?⇓a
bind⇓ (⇓later a∞⇓a) a?⇓a = ⇓later (bind⇓ a∞⇓a a?⇓a)

mutual
  eval : Γ ⊢ T → Env Γ → ∞Delay i (Value T)
  eval yes γ = λ{ .force → now yes }
  eval no γ = λ{ .force → now no }
  eval (var zero) (_ • ⟨ t ⟩ δ) = λ{ .force → later (eval t δ) }
  eval (var zero) (_ • _) = λ{ .force → now wrong }
  eval (var (suc x)) (γ • _) = eval (var x) γ
  eval (r ∙ s) γ =
    eval r γ ∞>>= λ where
                      (⟨ ƛ t ⟩ δ) →
                        later λ{ .force → later (eval t (δ • ⟨ s ⟩ γ)) }
                      _ → now wrong
  eval (ƛ t) γ =
    λ{ .force → now (⟨ ƛ t ⟩ γ) }
  eval (μ t) γ =
    λ{ .force → later (eval t (γ • ⟨ μ t ⟩ γ)) }

mutual
  𝒱[_] : (T : Type) → Value T → Set
  𝒱[ 𝟚 ] yes = ⊤
  𝒱[ 𝟚 ] no = ⊤
  𝒱[ S ⇒ T ] (⟨ ƛ t ⟩ δ) =
    ∀ {Γ} {γ : Env Γ} {s : Γ ⊢ S}
    → (γ , s) ∈ ℰ[ S ]
    → (δ • ⟨ s ⟩ γ , t) ∈ ℰ[ T ]
  𝒱[ _ ] _ = ⊥

--  𝒟[_] : (T : Type) → Delay ∞ (Value T) → Set
--  𝒟[ T ] a? = ∃[ a ] a? ⇓ a × a ∈ 𝒱[ T ]

  ℰ[_] : (T : Type) → Env Γ × Γ ⊢ T → Set
  ℰ[ T ] (γ , t) =
    ∀ {a} → force (eval t γ) ⇓ a → a ∈ 𝒱[ T ]

_⊨_ : (Γ : Ctx) → Env Γ → Set
ε ⊨ ε = ⊤
Γ • T ⊨ γ • ⟨ t ⟩ δ = Γ ⊨ γ × (δ , t) ∈ ℰ[ T ]
_ • _ ⊨ _ • _ = ⊥

infix 4 _⊨_

semantic-typing : Γ ⊢ T → Set
semantic-typing {Γ} {T} t =
  ∀ {γ : Env Γ}
  → Γ ⊨ γ
  → (γ , t) ∈ ℰ[ T ]

infix 4 semantic-typing

syntax semantic-typing {Γ} {T} t = Γ ⊨ t ∷ T

fundamental-lemma : ∀ (t : Γ ⊢ T) → Γ ⊨ t ∷ T
fundamental-lemma (μ t) ⊨γ (⇓later ⇓a) =
  fundamental-lemma t (⊨γ , fundamental-lemma (μ t) ⊨γ) ⇓a
fundamental-lemma t = {!!}

type-soundness : ∀ (t : ε ⊢ 𝟚) → force (eval t ε) ⇓ a → a ≡ yes ⊎ a ≡ no
type-soundness {a = a} t ⇓a
  with a  | fundamental-lemma t tt ⇓a
... | yes | _ = inj₁ refl
... | no  | _ = inj₂ refl
