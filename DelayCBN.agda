{-# OPTIONS --sized-types #-}

open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Unary using (_∈_)
open import Size

module DelayCBN where

variable i : Size

module Delay where
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

open Delay
open ∞Delay

data Type : Set where
  ∅ : Type
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

mutual
  data Thunk : Type → Set where
    ⟨_⟩_ : Γ ⊢ T → Env Γ → Thunk T

  data Env : Ctx → Set where
    ε : Env ε
    _•_ : Env Γ → Thunk T → Env (Γ • T)

infix 6 ⟨_⟩_
variable γ δ : Env Γ

_??_ : Env Γ → Γ ∋ T → Thunk T
γ • a ?? zero = a
γ • a ?? suc x = γ ?? x

infix 4 _??_

data Value : Type → Set where
  yes no : Value 𝟚
  clos_ƛ_ : Env Γ → Γ • S ⊢ T → Value (S ⇒ T)
  wrong : Value ∅

variable a b f : Value T
infix 6 clos_ƛ_

mutual
  apply : Value (S ⇒ T) → Thunk S → Delay i (Value T)
  apply (clos δ ƛ t) a = later (beta t δ a)

  beta : Γ • S ⊢ T → Env Γ → Thunk S → ∞Delay i (Value T)
  force (beta t δ a) = eval t (δ • a)

  eval : Γ ⊢ T → Env Γ → Delay i (Value T)
  eval yes _ = now yes
  eval no _ = now no
  eval (var x) γ
    with γ ?? x
  ... | ⟨ t ⟩ δ = later λ{ .force → eval t δ }
  eval (r ∙ s) γ =
    eval r γ >>= λ f → apply f (⟨ s ⟩ γ)
  eval (ƛ t) γ = now (clos γ ƛ t)

mutual
  𝒱[_] : (T : Type) → Value T → Set
  𝒱[ ∅ ] _ = ⊥
  𝒱[ 𝟚 ] yes = ⊤
  𝒱[ 𝟚 ] no = ⊤
  𝒱[ S ⇒ T ] (clos δ ƛ t) =
    ∀ {Γ} {s : Γ ⊢ S} {γ : Env Γ}
    → (γ , s) ∈ ℰ[ S ]
    → (δ • ⟨ s ⟩ γ , t) ∈ ℰ[ T ]

  𝒟[_] : (T : Type) → Delay ∞ (Value T) → Set
  𝒟[ T ] a? = ∃[ a ] a? ⇓ a × a ∈ 𝒱[ T ]

  ℰ[_] : (T : Type) → Env Γ × Γ ⊢ T → Set
  ℰ[ T ] (γ , t) = eval t γ ∈ 𝒟[ T ]

_⊨_ : (Γ : Ctx) → Env Γ → Set
ε ⊨ ε = ⊤
Γ • T ⊨ γ • ⟨ t ⟩ δ = Γ ⊨ γ × (δ , t) ∈ ℰ[ T ]

infix 4 _⊨_

semantic-typing : Γ ⊢ T → Set
semantic-typing {Γ} {T} t = ∀ {γ : Env Γ} → Γ ⊨ γ → (γ , t) ∈ ℰ[ T ]

infix 4 semantic-typing
syntax semantic-typing {Γ} {T} t = Γ ⊨ t ∷ T

fundamental-lemma : (t : Γ ⊢ T) → Γ ⊨ t ∷ T
fundamental-lemma yes ⊨γ = yes , ⇓now , tt
fundamental-lemma no ⊨γ = no , ⇓now , tt
fundamental-lemma (var zero) {_ • ⟨ t ⟩ δ} (_ , a , t⇓ , a∈𝒱) =
  a , ⇓later t⇓ , a∈𝒱
fundamental-lemma (var (suc x)) {γ • ⟨ _ ⟩ _} (⊨γ , _) =
  fundamental-lemma (var x) ⊨γ
fundamental-lemma (r ∙ s) ⊨γ
  with fundamental-lemma r ⊨γ
...  | clos _ ƛ _ , r⇓ , pf
  with pf (fundamental-lemma s ⊨γ)
...  | b , ⇓b , b∈𝒱 =
  b , bind⇓ r⇓ (⇓later ⇓b) , b∈𝒱
fundamental-lemma (ƛ t) {γ} ⊨γ =
  clos γ ƛ t ,
  ⇓now ,
  λ s∈𝒱 → fundamental-lemma t (⊨γ , s∈𝒱)

type-soundness : (t : ε ⊢ 𝟚) → eval t ε ⇓ yes ⊎ eval t ε ⇓ no
type-soundness t with fundamental-lemma t tt
...                 | yes , ⇓yes , _         = inj₁ ⇓yes
...                 | no , ⇓no , _           = inj₂ ⇓no
