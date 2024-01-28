{-# OPTIONS --sized-types #-}

open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Unary using (_∈_)
open import Size

module DelayCBN where

variable i : Size

-- Delay monad
module Delay where
  -- Delay monad is made up of Delay and ∞Delay
  mutual
    data Delay (i : Size) (A : Set) : Set where
      now : A → Delay i A
      later : ∞Delay i A → Delay i A

    record ∞Delay (i : Size) (A : Set) : Set where
      coinductive
      field
        force : ∀ {j : Size< i} → Delay j A

  open ∞Delay

  -- Bind
  mutual
    _>>=_ : ∀ {A B : Set} → Delay i A → (A → Delay i B) → Delay i B
    now a >>= f = f a
    later a∞ >>= f = later (a∞ ∞>>= f)

    _∞>>=_ : ∀ {A B : Set} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
    force (a∞ ∞>>= f) = force a∞ >>= f

  infix 5 _>>=_

  -- Convergence of a delayed value
  data _⇓_ {A : Set} : Delay ∞ A → A → Set where
    ⇓now : ∀ {a : A} → now a ⇓ a
    ⇓later : ∀ {a : A} {a∞ : ∞Delay ∞ A} → force a∞ ⇓ a → later a∞ ⇓ a

  infix 4 _⇓_

  -- A delayed value converges
  _⇓ : ∀ {A : Set} → Delay ∞ A → Set
  a? ⇓ = ∃[ a ] a? ⇓ a

  -- Bind + convergence
  bind⇓ : ∀ {A B : Set} {f : A → Delay ∞ B}
            {a? : Delay ∞ A} {a : A} {b : B}
          → a? ⇓ a → f a ⇓ b → a? >>= f ⇓ b
  bind⇓ ⇓now a?⇓a = a?⇓a
  bind⇓ (⇓later a∞⇓a) a?⇓a = ⇓later (bind⇓ a∞⇓a a?⇓a)

open Delay
open ∞Delay

{- Syntax + Typing -}

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

infix 4 _⊢_
variable r s t : Γ ⊢ T

{- Semantics: we evaluate terms to a delayed element in the domain -}
-- (cbn semantics)

mutual
  data Domain : Type → Set where
    yes no : Domain 𝟚
    ⟨_⟩_ : Γ ⊢ T → Env Γ → Domain T
    wrong : Domain T

  data Env : Ctx → Set where
    ε : Env ε
    _•_ : Env Γ → Domain T → Env (Γ • T)

infix 6 ⟨_⟩_
variable a b f : Domain T
variable γ δ : Env Γ

_??_ : Env Γ → Γ ∋ T → Domain T
(γ • a) ?? zero = a
(γ • a) ?? suc x = γ ?? x

infix 5 _??_

mutual
  eval-var : Γ ∋ T → Env Γ → ∞Delay i (Domain T)
  eval-var zero (_ • ⟨ t ⟩ δ) = λ{ .force → later (eval t δ) }
  eval-var (suc x) (γ • _) = eval-var x γ
  eval-var zero (_ • _) = λ{ .force → now wrong }

  eval-apply : Domain (S ⇒ T) → Γ ⊢ S → Env Γ → Delay i (Domain T)
  eval-apply (⟨ ƛ t ⟩ δ) s γ = later λ { .force → later (eval t (δ • ⟨ s ⟩ γ)) }
  eval-apply _ _ _ = now wrong

  eval : Γ ⊢ T → Env Γ → ∞Delay i (Domain T)
  eval yes γ = λ{ .force → now yes }
  eval no γ = λ{ .force → now no }
  eval (var x) γ = eval-var x γ
  eval (r ∙ s) γ = eval r γ ∞>>= λ f → eval-apply f s γ
  eval (ƛ t) γ = λ{ .force → now (⟨ ƛ t ⟩ γ) }

{- Logical relation -}

mutual
  𝒱[_] : (T : Type) → Domain T → Set
  𝒱[ 𝟚 ] yes = ⊤
  𝒱[ 𝟚 ] no = ⊤
  𝒱[ S ⇒ T ] (⟨ ƛ t ⟩ δ) =
    ∀ {Γ} {γ : Env Γ} {s : Γ ⊢ S}
    → (γ , s) ∈ ℰ[ S ]
    → (δ • ⟨ s ⟩ γ , t) ∈ ℰ[ T ]
  𝒱[ _ ] _ = ⊥

  𝒟[_] : (T : Type) → Delay ∞ (Domain T) → Set
  𝒟[ T ] a? = ∃[ a ] a? ⇓ a × a ∈ 𝒱[ T ]

  ℰ[_] : (T : Type) → Env Γ × Γ ⊢ T → Set
  ℰ[ T ] (γ , t) = later (eval t γ) ∈ 𝒟[ T ]

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

{- Fundamental lemma + type soundness -}

fundamental-lemma : ∀ (t : Γ ⊢ T) → Γ ⊨ t ∷ T
fundamental-lemma yes ⊨γ = yes  , ⇓later ⇓now , tt
fundamental-lemma no ⊨γ = no  , ⇓later ⇓now , tt
fundamental-lemma (var zero) {_ • ⟨ t ⟩ δ} (_ , (a , ⇓a , a∈𝒱)) =
  a , ⇓later ⇓a , a∈𝒱
fundamental-lemma (var (suc x)) {γ • ⟨ _ ⟩ _} (⊨γ , _) =
  fundamental-lemma (var x) ⊨γ
fundamental-lemma (r ∙ s) {γ} ⊨γ
  with fundamental-lemma r ⊨γ
...  | ⟨ ƛ t ⟩ δ , ⇓later r⇓ , f∈𝒱
  with f∈𝒱 {s = s} (fundamental-lemma s ⊨γ)
...  | b , ⇓later t⇓ , b∈𝒱 =
  b , ⇓later (bind⇓ r⇓ (⇓later (⇓later t⇓))) , b∈𝒱
fundamental-lemma (ƛ t) {γ} ⊨γ =
  ⟨ ƛ t ⟩ γ ,
  ⇓later ⇓now ,
  λ s∈ℰ → fundamental-lemma t (⊨γ , s∈ℰ)

-- Type soundness: well-typed terms of answer type evaluate to yes or no
-- (notably, their evaluation is terminating)
type-soundness : (t : ε ⊢ 𝟚) → force (eval t ε) ⇓ yes ⊎ force (eval t ε) ⇓ no
type-soundness t
  with fundamental-lemma t tt
... | yes , ⇓later ⇓yes , _ = inj₁ ⇓yes
... | no , ⇓later ⇓no , _ = inj₂ ⇓no
