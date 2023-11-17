open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)

{- Layered Modal Type Theories, Hu & Pientka -}

-- Right now, this is only the type system in section 2
module Layered where

data Type : Set where
  nat : Type
  _⇒_ : Type → Type → Type
  □_ : Type → Type

infixr 7 _⇒_
infix 8 □_

variable S T : Type

data Ctx : Set where
  ∅ : Ctx
  _∷_ : Ctx → Type → Ctx

infixl 5 _∷_

variable Γ Ψ : Ctx

data Layer : Set where
  code : Layer
  comp : Layer

variable i : Layer

data _`core : Type → Set where
  natCore : nat `core
  arrCore : S `core → T `core → S ⇒ T `core

infix 6 _`core

data _`type : Type → Set where
  natType : nat `type
  arrType : S `type → T `type → S ⇒ T `type
  boxType : T `core → □ T `type

infix 6 _`type

_core : Ctx → Set
∅ core = ⊤
(Γ ∷ T) core = Γ core × T `core

infix 6 _core

_type : Ctx → Set
∅ type = ⊤
(Γ ∷ T) type = Γ type × T `type

infix 6 _type

data _∋_ : Ctx → Type → Set where
  zero : Γ ∷ T ∋ T
  suc : Γ ∋ T → Γ ∷ S ∋ T

infix 4 _∋_

-- validity requirement for local context based on layer
lctx : Ctx → Layer → Set
lctx Γ code = Γ core
lctx Γ comp = Γ type

data _,_⊢_#_ : Ctx → Ctx → Type → Layer → Set where
  zero : Ψ core → lctx Γ i
         ------------------
       → Ψ , Γ ⊢ nat # i

  suc : Ψ , Γ ⊢ nat # i → Ψ , Γ ⊢ nat # i

  gvar : Ψ core → lctx Γ i → (u : Ψ ∋ T)
         -------------------------------
       → Ψ , Γ ⊢ T # i

  lvar : Ψ core → lctx Γ i → (x : Γ ∋ T)
         -------------------------------
       → Ψ , Γ ⊢ T # i

  ƛ_ : Ψ , Γ ∷ S ⊢ T # i → Ψ , Γ ⊢ S ⇒ T # i

  _·_ : Ψ , Γ ⊢ S ⇒ T # i → Ψ , Γ ⊢ S # i → Ψ , Γ ⊢ T # i

  box : Γ type → Ψ , ∅ ⊢ T # code
        -------------------------
      → Ψ , Γ ⊢ □ T # comp

  letbox_⋯_ : Ψ , Γ ⊢ □ S # comp → Ψ ∷ T , Γ ⊢ T # comp
               -----------------------------------------
             → Ψ , Γ ⊢ T # comp

infix 5 ƛ_
infixl 7 _·_
infixr 5 letbox_⋯_
infix 4 _,_⊢_#_
