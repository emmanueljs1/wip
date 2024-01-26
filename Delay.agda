{-# OPTIONS --sized-types #-}

import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Unary using (_∈_)
open import Size
open Eq using (_≡_; refl)

module Delay where

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

infix 5 ⟨_⟩_
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

bind⇓ : ∀ {A B : Set} {f : A → Delay ∞ B}
          {a? : Delay ∞ A} {a : A} {b : B}
        → a? ⇓ a → f a ⇓ b → a? >>= f ⇓ b
bind⇓ ⇓now a?⇓a = a?⇓a
bind⇓ (⇓later a∞⇓a) a?⇓a = ⇓later (bind⇓ a∞⇓a a?⇓a)

mutual
  apply : Value (S ⇒ T) → Value S → Delay i (Value T)
  apply (⟨ ƛ t ⟩ δ) a = later (beta t δ a)
  apply (⟨ var _ ⟩ _) _ = now wrong
  apply (⟨ _ ∙ _ ⟩ _) _ = now wrong
  apply wrong _ = now wrong

  beta : Γ • S ⊢ T → Env Γ → Value S → ∞Delay i (Value T)
  force (beta t δ a) = eval t (δ • a)

  eval : Γ ⊢ T → Env Γ → Delay i (Value T)
  eval yes _ = now yes
  eval no _ = now no
  eval (var x) γ = now (γ ?? x)
  eval (r ∙ s) γ =
    eval r γ >>= λ f → eval s γ >>= apply f
  eval (ƛ t) γ = now (⟨ ƛ t ⟩ γ)

mutual
  𝒱[_] : (T : Type) → Value T → Set
  𝒱[ 𝟚 ] yes = ⊤
  𝒱[ 𝟚 ] no = ⊤
  𝒱[ S ⇒ T ] f =
    ∀ {a : Value S}
    → a ∈ 𝒱[ S ]
    → apply f a ∈ 𝒟[ T ]
  𝒱[ _ ] _ = ⊥

  𝒟[_] : (T : Type) → Delay ∞ (Value T) → Set
  𝒟[ T ] a? = ∃[ a ] a? ⇓ a × a ∈ 𝒱[ T ]

_⊨_ : (Γ : Ctx) → Env Γ → Set
ε ⊨ ε = ⊤
Γ • T ⊨ γ • a = Γ ⊨ γ × a ∈ 𝒱[ T ]

infix 4 _⊨_

semantic-typing : Γ ⊢ T → Set
semantic-typing {Γ} {T} t =
  ∀ {γ : Env Γ}
  → Γ ⊨ γ
  → eval t γ ∈ 𝒟[ T ]

infix 4 semantic-typing

syntax semantic-typing {Γ} {T} t = Γ ⊨ t ∷ T

fundamental-lemma : ∀ (t : Γ ⊢ T) → Γ ⊨ t ∷ T
fundamental-lemma yes ⊨γ = yes , ⇓now , tt
fundamental-lemma no ⊨γ = no , ⇓now , tt
fundamental-lemma (var zero) {γ • a} (_ , a∈𝒱) = a , ⇓now , a∈𝒱
fundamental-lemma (var (suc x)) {γ • _} (⊨γ , _) = fundamental-lemma (var x) ⊨γ
fundamental-lemma (r ∙ s) ⊨γ
  with fundamental-lemma r ⊨γ | fundamental-lemma s ⊨γ
...  | f , ⇓f , f∈𝒱           | a , ⇓a , a∈𝒱
  with f∈𝒱 a∈𝒱
...  | b , ⇓b , b∈𝒱 =
  b , bind⇓ ⇓f (bind⇓ ⇓a ⇓b) , b∈𝒱
fundamental-lemma (ƛ t) {γ} ⊨γ =
  ⟨ ƛ t ⟩ γ  ,
  ⇓now ,
  λ a∈𝒱 →
    let (f , ⇓f , f∈𝒱) = fundamental-lemma t (⊨γ , a∈𝒱) in
    f , ⇓later ⇓f , f∈𝒱

type-soundness : (t : ε ⊢ 𝟚) → eval t ε ⇓ yes ⊎ eval t ε ⇓ no
type-soundness t
  with fundamental-lemma t tt
... | yes , ⇓yes , _ = inj₁ ⇓yes
... | no , ⇓no , _ = inj₂ ⇓no
