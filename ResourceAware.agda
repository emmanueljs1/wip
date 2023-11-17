import Data.Fin.Properties as Fin
import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; suc; zero; toℕ)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (_×_; ∃-syntax; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open Eq using (_≡_; refl; trans; subst; sym)

{- Resource-Aware Soundness for Big-Step Semantics, OOPSLA 2023 -}
module ResourceAware where
  variable n : ℕ
  variable x m : Fin n

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
      data Exp : ℕ → Set where
        return : Val n → Exp n
        _·_ : Val n → Val n → Exp n -- application
        _»_ : Val n → Exp n → Exp n -- sequence
        split_⇒_ : Val n → Exp (suc (suc n)) → Exp n -- split product
        case_inl⇒_inr⇒_ : Val n → Exp (suc n) → Exp (suc n) → Exp n -- case sum
        $≔_⋯_ : Exp n → Exp (suc n) → Exp n -- letin

      GrVal : ℕ → Set
      GrVal n = Grade × Val n

      data Val : ℕ → Set where
        μ_ : Exp (suc (suc n)) → Val n
        unit : Val n
        ⟨_,_⟩ : GrVal n → GrVal n → Val n
        inl : GrVal n → Val n
        inr : GrVal n → Val n
        var : Fin n → Val n

    infix 5 μ_
    infixl 7 _·_
    infixr 6 split_⇒_
    infixr 6 case_inl⇒_inr⇒_
    infixr 6 $≔_⋯_

    variable e e₁ e₂ : Exp n
    variable v v₁ v₂ : Val n

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

    _̂_ : ∀ {A B : Set} → A → B → B × A
    τ ̂ r = r , τ

    infix 10 _̂_

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

    ≔-⟨⟩ : ∀ {A : Set} {a : A} (γ : Con A n) (m : Fin n)
         → (γ [ m ]≔ a) ⟨ m ⟩ ≡ a
    ≔-⟨⟩ (_ ▹ _) zero = refl
    ≔-⟨⟩ (γ ▹ _) (suc m) = ≔-⟨⟩ γ m

    GCtx = Con Grade -- Grade context
    variable γ γ₁ γ₂ γ₃ δ : GCtx n

    _≼_ : GCtx n → GCtx n → Set
    ∅ ≼ ∅ = ⊤
    (γ ▹ s) ≼ (δ ▹ r) = γ ≼ δ × s ≤ r

    ≼-pt : ∀ x → γ ≼ δ → γ ⟨ x ⟩ ≤ δ ⟨ x ⟩
    ≼-pt {γ = _ ▹ _} {_ ▹ _} zero (_ , pf) = pf
    ≼-pt {γ = _ ▹ _} {_ ▹ _} (suc x) (pf , _) = ≼-pt x pf

    ≼-trans : γ₁ ≼ γ₂ → γ₂ ≼ γ₃ → γ₁ ≼ γ₃
    ≼-trans {γ₁ = ∅} {∅} {∅} _ _ = tt
    ≼-trans {γ₁ = γ₁ ▹ r₁} {γ₂ ▹ r₂} {γ₃ ▹ r₃} (γ₁≼γ₂ , pf) (γ₂≼γ₃ , pf′) =
      ≼-trans γ₁≼γ₂ γ₂≼γ₃ , ≤-trans pf pf′

    ≼-reflexive : γ ≡ δ → γ ≼ δ
    ≼-reflexive {γ = ∅} refl = tt
    ≼-reflexive {γ = _ ▹ _} refl = ≼-reflexive refl , ≤-refl

    ≼-refl : γ ≼ γ
    ≼-refl = ≼-reflexive refl

    ≼-≔ : γ ≼ δ → s ≤ r → γ [ x ]≔ s ≼ δ [ x ]≔ r
    ≼-≔ {γ = γ ▹ s} {δ = δ ▹ r} {x = zero} (pf , _) pf′ = pf , pf′
    ≼-≔ {γ = γ ▹ _} {δ = δ ▹ _} {x = suc x} (pf , pf′) pf″ = ≼-≔ {γ = γ} {δ = δ} {x = x} pf pf″ , pf′

    _⊹_ : GCtx n → GCtx n → GCtx n
    ∅ ⊹ ∅ = ∅
    (γ ▹ s) ⊹ (δ ▹ r) = γ ⊹ δ ▹ s + r

    infixl 6 _⊹_

    _⋆_ : Grade → GCtx n → GCtx n
    s ⋆ ∅ = ∅
    s ⋆ (γ ▹ r) = s ⋆ γ ▹ s * r

    infixl 7 _⋆_

    ⋆-≔-distrib : ∀ (s : Grade) (γ : GCtx n) (m : Fin n) (r : Grade)
                → s ⋆ (γ [ m ]≔ r) ≡ (s ⋆ γ)[ m ]≔ (s * r)
    ⋆-≔-distrib _ (_ ▹ _) zero _ = refl
    ⋆-≔-distrib s (γ ▹ _) (suc m) r
      rewrite ⋆-≔-distrib s γ m r = refl

    Ô : GCtx n
    Ô {zero} = ∅
    Ô {suc _} = Ô ▹ O

    ⋆-Ô : ∀ {n} → s ⋆ Ô ≡ Ô {n}
    ⋆-Ô {n = zero} = refl
    ⋆-Ô {s} {suc n} rewrite ⋆-Ô {s} {n} | *-Oˡ {s} = refl

    ⋆-⋆ : r ⋆ (s ⋆ γ) ≡ (r * s) ⋆ γ
    ⋆-⋆ {γ = ∅} = refl
    ⋆-⋆ {r = r} {s} {γ = γ ▹ t}
      rewrite ⋆-⋆ {r = r} {s} {γ = γ} | *-assoc {r} {s} {t} = refl

    ⋆-≤ : r ≤ s → r ⋆ γ ≼ s ⋆ γ
    ⋆-≤ {γ = ∅} _ = tt
    ⋆-≤ {γ = γ ▹ t} pf = ⋆-≤ pf , ≤-*-compatibleʳ pf

    TCtx = Con Type  -- Type context
    variable Γ Δ : TCtx n

    mutual
      data _·_⊩_∷_ : GCtx n → TCtx n → Val n → GrType → Set where
        ⊩sub : γ · Γ ⊩ v ∷ τ ̂ r
             → γ ≼ δ   →   s ≤ r
               -----------------
             → δ · Γ ⊩ v ∷ τ ̂ s

        ⊩var : Γ ⟨ x ⟩ ≡ τ        →       Ô [ x ]≔ r ≡ γ
               -----------------------------------------
             → γ · Γ ⊩ var x ∷ τ ̂ r

        ⊩rec : γ ▹ s ▹ r₁ · Γ ▹ τ₁ ̂ r₁ ⇒[ s ] τ₂ ̂ r₂ ▹ τ₁ ⊢ e ∷ τ₂ ̂ r₂
               ----------------------------------------------------------
             → r ⋆ γ · Γ ⊩ μ e ∷ (τ₁ ̂ r₁ ⇒[ s ] τ₂ ̂ r₂) ̂ r

        ⊩unit : Ô · Γ ⊩ unit ∷ 𝟙 ̂ s

        ⊩pair : γ₁ · Γ ⊩ v₁ ∷ τ₁ ̂ r₁
              → γ₂ · Γ ⊩ v₂ ∷ τ₂ ̂ r₂
                --------------------------------------------------------------------
              → r ⋆ (γ₁ ⊹ γ₂) · Γ ⊩ ⟨ v₁ ̂ r₁ , v₂ ̂ r₂ ⟩ ∷ (τ₁ ̂ r₁ ⊗ τ₂ ̂ r₂) ̂ r

        ⊩inl : γ · Γ ⊩ v ∷ τ₁ ̂ r₁
               --------------------------------------------------
             → r ⋆ γ · Γ ⊩ inl (v ̂ r₁) ∷ (τ₁ ̂ r₁ ∪ τ₂ ̂ r₂) ̂ r

        ⊩inr : γ · Γ ⊩ v ∷ τ₂ ̂ r₂
               --------------------------------------------------
             → r ⋆ γ · Γ ⊩ inr (v ̂ r₂) ∷ (τ₁ ̂ r₁ ∪ τ₂ ̂ r₂) ̂ r

      data _·_⊢_∷_ : GCtx n → TCtx n → Exp n → GrType → Set where
        ⊢sub : γ · Γ ⊢ e ∷ τ ̂ r
             → γ ≼ δ   →   s ≤ r
               -----------------
             → δ · Γ ⊢ e ∷ τ ̂ s

        ⊢ret : γ · Γ ⊩ v ∷ τ ̂ r
             → ¬ (r ≡ O)
               ------------------------
             → γ · Γ ⊢ return v ∷ τ ̂ r

        ⊢letin : γ₁ · Γ ⊢ e₁ ∷ τ₁ ̂ r₁
               → γ₂ ▹ r · Γ ▹ τ₁ ⊢ e₂ ∷ τ₂ ̂ r₂
                 -----------------------------------
               → γ₁ ⊹ γ₂ · Γ ⊢ $≔ e₁ ⋯ e₂ ∷ τ₂ ̂ r₂

        ⊢app : γ₁ · Γ ⊩ v₁ ∷ (τ₁ ̂ r₁ ⇒[ s ] τ₂ ̂ r₂) ̂ (r + r * s)
             → γ₂ · Γ ⊩ v₂ ∷ τ₂ ̂ (r * r₁)              → ¬ (r ≡ O)
               ----------------------------------------------------
             → γ₁ ⊹ γ₂ · Γ ⊢ v₁ · v₂ ∷ τ₂ ̂ (r * r₂)

        ⊢seq : γ₁ · Γ ⊩ v ∷ 𝟙 ̂ r
             → γ₂ · Γ ⊢ e ∷ T
             → ¬ (r ≡ O)
               -----------------------
             → γ₁ ⊹ γ₂ · Γ ⊢ v » e ∷ T

        ⊢split : γ₁ · Γ ⊩ v ∷ (τ₁ ̂ r₁ ⊗ τ₂ ̂ r₂) ̂ r
               → γ₂ ▹ r * r₁ ▹ r * r₂ · Γ ▹ τ₁ ▹ τ₂ ⊢ e ∷ T
               → ¬ (r ≡ O)
                 ------------------------------------------
               → γ₁ ⊹ γ₂ · Γ ⊢ split v ⇒ e ∷ T

        ⊢case : γ₁ · Γ ⊩ v ∷ (τ₁ ̂ r₂ ∪ τ₂ ̂ r₂) ̂ r
              → γ₂ ▹ r * r₁ · Γ ▹ τ₁ ⊢ e₁ ∷ T
              → γ₂ ▹ r * r₂ · Γ ▹ τ₂ ⊢ e₂ ∷ T
                ----------------------------------------
              → γ₁ ⊹ γ₂ · Γ ⊢ case v inl⇒ e₁ inr⇒ e₂ ∷ T

    infix 4 _≼_ _·_⊢_∷_ _·_⊩_∷_

    -- Lemma A.1 (1)
    invert-var : γ · Γ ⊩ var x ∷ τ ̂ r
             → ∃[ r′ ] Ô [ x ]≔ r′ ≼ γ × r ≤ r′ × Γ ⟨ x ⟩ ≡ τ
    invert-var {x = x} (⊩sub ⊩pf γ≼δ r≤r′)
      with invert-var ⊩pf
    ... | r″ , pf , r′≤r″ , pf′ =
      r″ , ≼-trans pf γ≼δ , ≤-trans r≤r′ r′≤r″ , pf′
    invert-var {r = r} (⊩var refl refl) =
      r , ≼-refl , ≤-refl , refl

    -- Lemma A.1 (2)
    invert-rec : γ · Γ ⊩ μ e ∷ τ ̂ r
              → ∃[ r′ ] ∃[ γ′ ] ∃[ τ₁ ] ∃[ r₁ ] ∃[ τ₂ ] ∃[ r₂ ] ∃[ s ]
                  r′ ⋆ γ′ ≼ γ
                × τ ≡ τ₁ ̂ r₁ ⇒[ s ] τ₂ ̂ r₂
                × γ′ ▹ s ▹ r₁ · Γ ▹ τ ▹ τ₁ ⊢ e ∷ τ₂ ̂ r₂
                × r ≤ r′
    invert-rec (⊩sub ⊩pf γ≼δ r≤r′)
      with invert-rec ⊩pf
    ...  | r″ , γ′ , τ₁ , r₁ , τ₂ , r₂ , s , pf , refl , ⊢e , r′≤r″ =
      r″ , γ′ , τ₁ , r₁ , τ₂ , r₂ , s , ≼-trans pf γ≼δ , refl , ⊢e ,
        ≤-trans r≤r′ r′≤r″
    invert-rec {r = r} (⊩rec {γ = γ} {s} {r₁} {_} {τ₁} {τ₂} {r₂} ⊢e) =
      r , γ , τ₁ , r₁ , τ₂ , r₂ , s , ≼-refl , refl , ⊢e , ≤-refl

    -- Lemma A.1 (3)
    invert-unit : γ · Γ ⊩ unit ∷ τ ̂ r
                → τ ≡ 𝟙 × Ô ≼ γ
    invert-unit (⊩sub ⊩pf γ≼δ r≤r′)
      with invert-unit ⊩pf
    ...  | refl , O≼γ = refl , ≼-trans O≼γ γ≼δ
    invert-unit ⊩unit = refl , ≼-refl

    -- Lemma A.1 (4)
    invert-pair : γ · Γ ⊩ ⟨ v₁ ̂ r₁ , v₂ ̂ r₂ ⟩ ∷ τ ̂ r
                → ∃[ r′ ] ∃[ γ₁ ] ∃[ γ₂ ] ∃[ τ₁ ] ∃[ τ₂ ]
                    r′ ⋆ (γ₁ ⊹ γ₂) ≼ γ
                  × τ ≡ τ₁ ̂ r₁ ⊗ τ₂ ̂ r₂
                  × γ₁ · Γ ⊩ v₁ ∷ τ₁ ̂ r₁
                  × γ₂ · Γ ⊩ v₂ ∷ τ₂ ̂ r₂
                  × r ≤ r′
    invert-pair (⊩sub ⊩pf γ≼δ r≤r′)
      with invert-pair ⊩pf
    ...  | r″ , γ₁ , γ₂ , τ₁ , τ₂ , pf , refl , ⊩v₁ , ⊩v₂ , r′≤r″ =
      r″ , γ₁ , γ₂ , τ₁ , τ₂ , ≼-trans pf γ≼δ , refl , ⊩v₁ , ⊩v₂ , ≤-trans r≤r′ r′≤r″
    invert-pair {r = r} (⊩pair {γ₁ = γ₁} {τ₁ = τ₁} {γ₂ = γ₂} {τ₂ = τ₂} ⊩v₁ ⊩v₂) =
      r , γ₁ , γ₂ , τ₁ , τ₂ , ≼-refl , refl , ⊩v₁ , ⊩v₂ , ≤-refl

    -- Lemma A.1 (5)
    invert-inl : γ · Γ ⊩ inl (v ̂ r₁) ∷ τ ̂ r
               → ∃[ r′ ] ∃[ γ′ ] ∃[ τ₁ ] ∃[ τ₂ ] ∃[ r₂ ]
                   r′ ⋆ γ′ ≼ γ
                 × τ ≡ τ₁ ̂ r₁ ∪ τ₂ ̂ r₂
                 × γ′ · Γ ⊩ v ∷ τ₁ ̂ r₁
                 × r ≤ r′
    invert-inl (⊩sub ⊩pf γ≼δ r≤r′)
      with invert-inl ⊩pf
    ...  | r″ , γ′ , τ₁ , τ₂ , r₂ , pf , refl , ⊩v , r′≤r″ =
      r″ , γ′ , τ₁ , τ₂ , r₂ , ≼-trans pf γ≼δ , refl , ⊩v , ≤-trans r≤r′ r′≤r″
    invert-inl {r = r} (⊩inl {γ = γ} {τ₁ = τ₁} {τ₂ = τ₂} {r₂} ⊩v) =
      r , γ , τ₁ , τ₂ , r₂ , ≼-refl , refl , ⊩v , ≤-refl

    -- Lemma A.1 (6)
    invert-inr : γ · Γ ⊩ inr (v ̂ r₂) ∷ τ ̂ r
               → ∃[ r′ ] ∃[ γ′ ] ∃[ τ₁ ] ∃[ τ₂ ] ∃[ r₁ ]
                   r′ ⋆ γ′ ≼ γ
                 × τ ≡ τ₁ ̂ r₁ ∪ τ₂ ̂ r₂
                 × γ′ · Γ ⊩ v ∷ τ₂ ̂ r₂
                 × r ≤ r′
    invert-inr (⊩sub ⊩pf γ≼δ r≤r′)
      with invert-inr ⊩pf
    ...  | r″ , γ′ , τ₁ , τ₂ , r₁ , pf , refl , ⊩v , r′≤r″ =
      r″ , γ′ , τ₁ , τ₂ , r₁ , ≼-trans pf γ≼δ , refl , ⊩v , ≤-trans r≤r′ r′≤r″
    invert-inr {r = r} (⊩inr {γ = γ} {τ₂ = τ₂} {τ₁ = τ₁} {r₁} ⊩v) =
      r , γ , τ₁ , τ₂ , r₁ , ≼-refl , refl , ⊩v , ≤-refl

    -- Theorem 4.3
    demotion : γ · Γ ⊩ v ∷ τ ̂ (s * r)
               ---------------------------------------
             → ∃[ γ′ ] s ⋆ γ′ ≼ γ × γ′ · Γ ⊩ v ∷ τ ̂ r
    demotion {v = μ e} {r = r} pf
      with invert-rec pf
    ...  | _ , γ′ , _ , _ , _ , _ , _ , pf′ , refl , ⊢e , s*r≤r′ =
      r ⋆ γ′ , ≼-lemma , ⊩rec ⊢e
      where
        ≼-lemma = ≼-trans (≼-reflexive ⋆-⋆) (≼-trans (⋆-≤ s*r≤r′) pf′)
    demotion {v = unit} pf
      with invert-unit pf
    ...  | refl , pf′ =
      Ô , ≼-trans (≼-reflexive ⋆-Ô) pf′ , ⊩unit
    demotion {v = ⟨ v₁ , v₂ ⟩} {r = r} pf
      with invert-pair pf
    ...  | _ , γ₁ , γ₂ , _ , _ , pf′ , refl , ⊩v₁ , ⊩v₂ , s*r≤r′ =
      r ⋆ (γ₁ ⊹ γ₂) , ≼-lemma , ⊩pair ⊩v₁ ⊩v₂
      where
        ≼-lemma = ≼-trans (≼-reflexive ⋆-⋆) (≼-trans (⋆-≤ s*r≤r′) pf′)
    demotion {v = inl v} {r = r} pf
      with invert-inl pf
    ...  | _ , γ′ , _ , _ , _ , pf′ , refl , ⊩v , s*r≤r′ =
      r ⋆ γ′ , ≼-lemma , ⊩inl ⊩v
      where
        ≼-lemma = ≼-trans (≼-reflexive ⋆-⋆) (≼-trans (⋆-≤ s*r≤r′) pf′)
    demotion {v = inr v} {r = r} pf
      with invert-inr pf
    ...  | _ , γ′ , _ , _ , _ , pf′ , refl , ⊩v , s*r≤r′ =
      r ⋆ γ′ , ≼-lemma , ⊩inr ⊩v
      where
        ≼-lemma = ≼-trans (≼-reflexive ⋆-⋆) (≼-trans (⋆-≤ s*r≤r′) pf′)
    demotion {v = var x} {s = s} {r = r} pf
      with invert-var pf
    ...  | r′ , pf′ , s*r≤r′ , refl =
      Ô [ x ]≔ r , ≼-lemma , ⊩var refl refl
      where
        ≼-lemma = ≼-trans
                (≼-reflexive (⋆-≔-distrib s Ô x r))
                (≼-trans (≼-≔ (≼-reflexive ⋆-Ô) s*r≤r′) pf′)
