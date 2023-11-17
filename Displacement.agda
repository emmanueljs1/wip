open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)

{- An Order-Theoretic Analysis of Universe Polymorphism, POPL 2023 -}

-- This is a WIP representation of the type system for L-monomorphic
-- type theory, using ℕ as the poset
module Displacement where

variable n i : ℕ

infixl 5 _▹_
infix 4 ⊢_
infix 4 _⊢_
infix 4 _⊢_∷_
infix 4 _∷_∈_
infix 5 ƛ_
infixl 7 _·_
infixr 7 _⇒_

mutual
  data Ctx : Set where
    ∅ : Ctx
    _▹_ : Ctx → Type → Ctx

  data Type : Set where
    el : Term → Type
    𝒰 : ℕ → Type
    _⇒_ : Type → Type → Type
    base : Type

  data Term : Set where
    var : ℕ → Term
    code : Type → Term
    ƛ_ : Term → Term
    _·_ : Term → Term → Term

variable x : ℕ
variable Γ : Ctx
variable A B : Type
variable r s t : Term

data _∷_∈_ : ℕ → Type → Ctx → Set where
  here : zero ∷ A ∈ Γ ▹ A
  there : x ∷ A ∈ Γ → suc x ∷ A ∈ Γ ▹ B

mutual
  data ⊢_ : Ctx → Set where
    ∅ : ⊢ ∅
    _▹_ : ⊢ Γ → Γ ⊢ A → ⊢ Γ ▹ A

  data _⊢_ : Ctx → Type → Set where
    ⊢base : ⊢ Γ
            --------
          → Γ ⊢ base

    ⊢⇒ : Γ ⊢ A
       → Γ ⊢ B
         ---------
       → Γ ⊢ A ⇒ B

    ⊢el : Γ ⊢ t ∷ 𝒰 i
          -----------
        → Γ ⊢ el t

  data _⊢_∷_ : Ctx → Term → Type → Set where
    ⊢var : ⊢ Γ
         → x ∷ A ∈ Γ
           -------------
         → Γ ⊢ var x ∷ A

    ⊢abs : Γ ▹ A ⊢ t ∷ B
           ---------------
         → Γ ⊢ ƛ t ∷ A ⇒ B

    ⊢app : Γ ⊢ r ∷ A ⇒ B
         → Γ ⊢ s ∷ B
           -------------
         → Γ ⊢ r · s ∷ A

    ⊢code : Γ ⊢ A
            ----------------
          → Γ ⊢ code A ∷ 𝒰 i
