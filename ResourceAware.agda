import Data.Fin.Properties as Fin
import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; suc; zero; toℕ)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (_×_; ∃-syntax; _,_)
open import Data.Unit using (⊤)
open import Relation.Nullary using (¬_)
open Eq using (_≡_; refl)

{- Resource-Aware Soundness for Big-Step Semantics, OOPSLA 2023 -}
module ResourceAware where
  variable x n : ℕ
  variable m : Fin n

  record OrdSemiring : Set₁ where
    field
      Grade : Set

      _≤_ : Grade → Grade → Set

      _*_ : Grade → Grade → Grade

      _+_ : Grade → Grade → Grade

      O : Grade -- additive identity
      I : Grade -- multiplicative identity

      -- _+_ Commutative monoid laws

      +-assoc : ∀ {q₁ q₂ q₃ : Grade} → (q₁ + q₂) + q₃ ≡ q₁ + (q₂ + q₃)

      +-comm : ∀ {q₁ q₂ : Grade} → q₁ + q₂ ≡ q₂ + q₁

      +-O-idˡ : ∀ {q : Grade} → q + O ≡ q
      +-O-idʳ : ∀ {q : Grade} → O + q ≡ q

      -- _*_ monoid laws

      *-assoc : ∀ {q₁ q₂ q₃ : Grade} → (q₁ * q₂) * q₃ ≡ q₁ * (q₂ * q₃)

      *-I-idˡ : ∀ {q : Grade} → q * I ≡ q
      *-I-idʳ : ∀ {q : Grade} → I * q ≡ q

      -- Preorder laws

      ≤-refl : ∀ {q : Grade} → q ≤ q

      ≤-trans : ∀ {q₁ q₂ q₃ : Grade} → q₁ ≤ q₂ → q₂ ≤ q₃ → q₁ ≤ q₃

      -- Preorder compatibility laws

      ≤-+-compatibleʳ : ∀ {q₁ q₂ q : Grade} → q₁ ≤ q₂ → q₁ + q ≤ q₂ + q

      ≤-+-compatibleˡ : ∀ {q₁ q₂ q : Grade} → q₁ ≤ q₂ → q + q₁ ≤ q + q₂

      ≤-*-compatibleʳ : ∀ {q₁ q₂ q : Grade} → q₁ ≤ q₂ → q₁ * q ≤ q₂ * q

      ≤-*-compatibleˡ : ∀ {q₁ q₂ q : Grade} → q₁ ≤ q₂ → q * q₁ ≤ q * q₂

      -- Semiring laws

      *-Oˡ : ∀ {q : Grade} → q * O ≡ O
      *-Oʳ : ∀ {q : Grade} → O * q ≡ O

      *-+-distribˡ : ∀ {q₁ q₂ q : Grade} → q * (q₁ + q₂) ≡ q * q₁ + q * q₂

      *-+-distribʳ : ∀ {q₁ q₂ q : Grade} → (q₁ + q₂) * q ≡ q₁ * q + q₂ * q

    infix 4 _≤_
    infixl 7 _*_
    infixl 6 _+_
    variable r s r₁ r₂ : Grade

  module Soundness (R : OrdSemiring) where
    open OrdSemiring R

    mutual
      data Exp : Set where
        return : Val → Exp
        _·_ : Val → Val → Exp -- application
        _»_ : Val → Exp → Exp -- sequence
        split_⇒_ : Val → Exp → Exp -- split product
        case_inl⇒_inr⇒_ : Val → Exp → Exp → Exp -- case sum
        $≔_⋯_ : Exp → Exp → Exp -- letin

      GrVal = Grade × Val

      data Val : Set where
        μ_ : Exp → Val
        unit : Val
        ⟨_,_⟩ : GrVal → GrVal → Val
        inl : GrVal → Val
        inr : GrVal → Val
        var : ℕ → Val

    infix 5 μ_
    infixl 7 _·_
    infixr 6 split_⇒_
    infixr 6 case_inl⇒_inr⇒_
    infixr 6 $≔_⋯_

    variable e e₁ e₂ : Exp
    variable v v₁ v₂ : Val

    mutual
      data Type : Set where
        𝟙 : Type
        _⇒[_]_ : GrType → Grade → GrType → Type
        _∪_ : GrType → GrType → Type
        _⊗_ : GrType → GrType → Type

      GrType = Grade × Type

    infixr 7 _⇒[_]_
    infixr 9 _⊗_
    infixr 9 _∪_

    variable τ τ₁ τ₂ σ : Type

    variable S T : GrType

    _^_ : ∀ {A B : Set} → A → B → B × A
    τ ^ r = r , τ

    infix 10 _^_

    -- snoc lists
    data Con (A : Set) : ℕ → Set where
      ∅ : Con A zero
      _▹_ : Con A n → A → Con A (suc n)

    infixl 5 _▹_

    _⟨_⟩ : ∀ {A} → Con A n → Fin n → A
    (_ ▹ a) ⟨ zero ⟩ = a
    (c ▹ _) ⟨ suc m ⟩ = c ⟨ m ⟩

    _[_]≔_ : ∀ {A} → Con A n → Fin n → A → Con A n
    (c ▹ _) [ zero ]≔ a = c ▹ a
    (c ▹ b) [ suc m ]≔ a = c [ m ]≔ a ▹ b

    infix 6 _⟨_⟩ _[_]≔_

    GCtx = Con Grade -- Grade context
    variable γ γ₁ γ₂ δ : GCtx n

    _≽_ : GCtx n → GCtx n → Set
    ∅ ≽ ∅ = ⊤
    (γ ▹ s) ≽ (δ ▹ r) = γ ≽ δ × s ≤ r

    _⊹_ : GCtx n → GCtx n → GCtx n
    ∅ ⊹ ∅ = ∅
    (γ ▹ s) ⊹ (δ ▹ r) = γ ⊹ δ ▹ s + r

    infixl 6 _⊹_

    _⋆_ : Grade → GCtx n → GCtx n
    s ⋆ ∅ = ∅
    s ⋆ (γ ▹ r) = s ⋆ γ ▹ s * r

    infixl 7 _⋆_

    Ô : GCtx n
    Ô {zero} = ∅
    Ô {suc n} = Ô ▹ O

    TCtx = Con Type  -- Type context
    variable Γ Δ : TCtx n

    mutual
      data _·_⊩_∷_ : GCtx n → TCtx n → Val → GrType → Set where
        ⊩sub : γ · Γ ⊩ v ∷ τ ^ r
             → γ ≽ δ   →   s ≤ r
               -----------------
             → δ · Γ ⊩ v ∷ τ ^ s

        ⊩var : toℕ m ≡ x → Γ ⟨ m ⟩ ≡ τ → Ô [ m ]≔ r ≡ γ
               -----------------------------------------
             → γ · Γ ⊩ var x ∷ τ ^ s

        ⊩rec : γ ▹ s ▹ r₁ · Γ ▹ τ₁ ^ r₁ ⇒[ s ] τ₂ ^ r₂ ▹ τ₁ ⊢ e ∷ τ₂ ^ r₂
               ----------------------------------------------------------
             → r ⋆ γ · Γ ⊩ μ e ∷ (τ₁ ^ r₁ ⇒[ s ] τ₂ ^ r₂) ^ r

        ⊩unit : Ô · Γ ⊩ unit ∷ 𝟙 ^ s

        ⊩pair : γ₁ · Γ ⊩ v₁ ∷ τ₁ ^ r₁
              → γ₂ · Γ ⊩ v₂ ∷ τ₂ ^ r₂
                --------------------------------------------------------------------
              → r ⋆ (γ₁ ⊹ γ₂) · Γ ⊩ ⟨ v₁ ^ r₁ , v₂ ^ r₂ ⟩ ∷ (τ₁ ^ r₁ ⊗ τ₂ ^ r₂) ^ r

        ⊩inl : γ · Γ ⊩ v ∷ τ₁ ^ r₁
               --------------------------------------------------
             → r ⋆ γ · Γ ⊩ inl (v ^ r₁) ∷ (τ₁ ^ r₁ ∪ τ₂ ^ r₂) ^ r

        ⊩inr : γ · Γ ⊩ v ∷ τ₁ ^ r₁
               --------------------------------------------------
             → r ⋆ γ · Γ ⊩ inr (v ^ r₁) ∷ (τ₁ ^ r₁ ∪ τ₂ ^ r₂) ^ r

      data _·_⊢_∷_ : GCtx n → TCtx n → Exp → GrType → Set where
        ⊢sub : γ · Γ ⊢ e ∷ τ ^ r
             → γ ≽ δ   →   s ≤ r
               -----------------
             → δ · Γ ⊢ e ∷ τ ^ s

        ⊢ret : γ · Γ ⊩ v ∷ τ ^ r
             → ¬ (r ≡ O)
               ------------------------
             → γ · Γ ⊢ return v ∷ τ ^ r

        ⊢letin : γ₁ · Γ ⊢ e₁ ∷ τ₁ ^ r₁
               → γ₂ ▹ r · Γ ▹ τ₁ ⊢ e₂ ∷ τ₂ ^ r₂
                 -----------------------------------
               → γ₁ ⊹ γ₂ · Γ ⊢ $≔ e₁ ⋯ e₂ ∷ τ₂ ^ r₂

        ⊢app : γ₁ · Γ ⊩ v₁ ∷ (τ₁ ^ r₁ ⇒[ s ] τ₂ ^ r₂) ^ (r + r * s)
             → γ₂ · Γ ⊩ v₂ ∷ τ₂ ^ (r * r₁)              → ¬ (r ≡ O)
               ----------------------------------------------------
             → γ₁ ⊹ γ₂ · Γ ⊢ v₁ · v₂ ∷ τ₂ ^ (r * r₂)

        ⊢seq : γ₁ · Γ ⊩ v ∷ 𝟙 ^ r
             → γ₂ · Γ ⊢ e ∷ T
             → ¬ (r ≡ O)
               -----------------------
             → γ₁ ⊹ γ₂ · Γ ⊢ v » e ∷ T

        ⊢split : γ₁ · Γ ⊩ v ∷ (τ₁ ^ r₁ ⊗ τ₂ ^ r₂) ^ r
               → γ₂ ▹ r * r₁ ▹ r * r₂ · Γ ▹ τ₁ ▹ τ₂ ⊢ e ∷ T
               → ¬ (r ≡ O)
                 ------------------------------------------
               → γ₁ ⊹ γ₂ · Γ ⊢ split v ⇒ e ∷ T

        ⊢case : γ₁ · Γ ⊩ v ∷ (τ₁ ^ r₂ ∪ τ₂ ^ r₂) ^ r
              → γ₂ ▹ r * r₁ · Γ ▹ τ₁ ⊢ e₁ ∷ T
              → γ₂ ▹ r * r₂ · Γ ▹ τ₂ ⊢ e₂ ∷ T
                ----------------------------------------
              → γ₁ ⊹ γ₂ · Γ ⊢ case v inl⇒ e₁ inr⇒ e₂ ∷ T

    infix 4 _≽_ _·_⊢_∷_ _·_⊩_∷_

    demotion : γ · Γ ⊩ v ∷ τ ^ (s * r)
               ---------------------------------------
             → ∃[ γ′ ] s ⋆ γ′ ≽ γ × γ′ · Γ ⊩ v ∷ τ ^ r
    demotion (⊩sub ⊩v x x₁) = {!!}
    demotion (⊩var x x₁ x₂) = {!!}
    demotion (⊩rec x) = {!!}
    demotion ⊩unit = {!!}
    demotion (⊩pair ⊩v ⊩v₁) = {!!}
    demotion (⊩inl ⊩v) = {!!}
    demotion (⊩inr ⊩v) = {!!}
