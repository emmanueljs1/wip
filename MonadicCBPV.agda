open import Category.Monad using (RawMonad)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Unit using (⊤; tt)

module MonadicCBPV (𝑻 : Set → Set) (MonadT : RawMonad 𝑻) where
  open RawMonad MonadT renaming (return to η)

  infix 4 _∋_ _⊩_ _⊢_ _??_
  infixl 5 _•_
  infix 5 𝑼_ 𝑭_ ƛ_
  infix 6 _!
  infixr 6 $_⟵_
  infixr 7 _⇒_
  infixl 7 _·_

  mutual
    data ValType : Set where
      𝟙 : ValType
      𝑼_ : CompType → ValType

    data CompType : Set where
      _⇒_ : ValType → CompType → CompType
      𝑭_ : ValType → CompType

  variable A A₁ A₂ : ValType
  variable B : CompType

  data Ctx : Set where
    ε : Ctx
    _•_ : Ctx → ValType → Ctx

  variable Γ : Ctx

  data _∋_ : Ctx → ValType → Set where
    zero : Γ • A ∋ A
    suc : Γ ∋ A₁ → Γ • A₂ ∋ A₁

  mutual
    data _⊩_ : Ctx → ValType → Set where
      var : Γ ∋ A → Γ ⊩ A   -- variable
      ⟪_⟫ : Γ ⊢ B → Γ ⊩ 𝑼 B -- thunk
      one : Γ ⊩ 𝟙           -- unit

    data _⊢_ : Ctx → CompType → Set where
      return : Γ ⊩ A → Γ ⊢ 𝑭 A          -- return
      _·_ : Γ ⊢ A ⇒ B → Γ ⊩ A → Γ ⊢ B   -- app
      ƛ_ : Γ • A ⊢ B → Γ ⊢ A ⇒ B        -- abs
      _! : Γ ⊩ 𝑼 B → Γ ⊢ B              -- force
      $_⟵_ : Γ ⊢ 𝑭 A → Γ • A ⊢ B → Γ ⊢ B -- let in

  variable V V₁ V₂ : Γ ⊩ A
  variable M N M₁ M₂ : Γ ⊢ B

  record MonadAlgebra : Set₁ where
    field
      𝑋 : Set
      α : 𝑻 𝑋 → 𝑋

  open MonadAlgebra

  mutual
    ValDomain : ValType → Set
    ValDomain 𝟙 = ⊤
    ValDomain (𝑼 B) = ⊤ → Carrier B

    Carrier : CompType → Set
    Carrier B = 𝑋 (Domain B)

    Domain : CompType → MonadAlgebra
    𝑋 (Domain (A ⇒ B)) = ValDomain A → Carrier B
    α (Domain (A ⇒ B)) 𝑻f W = α (Domain B) (𝑻f >>= λ f → η (f W))

    𝑋 (Domain (𝑭 A)) = 𝑻 (ValDomain A)
    α (Domain (𝑭 A)) 𝑻𝑻W = join 𝑻𝑻W

  variable W : ValDomain A
  variable T : Carrier B

  Env : Ctx → Set
  Env ε = ⊤
  Env (Γ • A) = Env Γ × ValDomain A

  variable γ : Env Γ

  _??_ : Env Γ → Γ ∋ A → ValDomain A
  (_ , a) ?? zero = a
  (γ , _) ?? suc x = γ ?? x

  mutual
    ⟦_⟧v : Γ ⊩ A → Env Γ → ValDomain A
    ⟦ var x ⟧v γ = γ ?? x
    ⟦ ⟪ M ⟫ ⟧v γ = λ _ → ⟦ M ⟧c γ
    ⟦ one ⟧v γ = tt

    ⟦_⟧c : Γ ⊢ B → Env Γ → Carrier B
    ⟦ return V ⟧c γ = η (⟦ V ⟧v γ)
    ⟦ ƛ M ⟧c γ = λ W → ⟦ M ⟧c (γ , W)
    ⟦ M · V ⟧c γ = ⟦ M ⟧c γ (⟦ V ⟧v γ)
    ⟦ V ! ⟧c γ = ⟦ V ⟧v γ tt
    ⟦_⟧c {B = B} ($ M ⟵ N) γ = α (Domain B) (⟦ M ⟧c γ >>= λ W → η (⟦ N ⟧c (γ , W)))
