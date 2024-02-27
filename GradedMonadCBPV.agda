import Axiom.Extensionality.Propositional as Extensionality
import Relation.Binary.PropositionalEquality as Eq
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_; id)
open import Level using (0ℓ)
open import Relation.Unary using (_∈_)
open Eq using (_≡_; refl; sym; cong; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open Extensionality using (Extensionality)

module GradedMonadCBPV  where
  record PoMonoid : Set₁ where
    infix 4 _≤_
    infixl 6 _+_

    field
      ∣𝔼∣ : Set

      ⊥ : ∣𝔼∣

      _+_ : ∣𝔼∣ → ∣𝔼∣ → ∣𝔼∣

      instance +-assoc : ∀ {φ₁ φ₂ φ₃}
                       → (φ₁ + φ₂) + φ₃ ≡ φ₁ + (φ₂ + φ₃)

      instance +-idʳ : ∀ {φ} → φ + ⊥ ≡ φ

      instance +-idˡ : ∀ {φ} → ⊥ + φ ≡ φ

      _≤_ : ∣𝔼∣ → ∣𝔼∣ → Set

      ≤-refl : ∀ {φ : ∣𝔼∣} → φ ≤ φ

      ≤-trans : ∀ {φ₁ φ₂ φ₃ : ∣𝔼∣}
              → φ₁ ≤ φ₂
              → φ₂ ≤ φ₃
              → φ₁ ≤ φ₃

      ≤-+-compatibleʳ : ∀ {φ₁ φ₂ ψ : ∣𝔼∣}
                      → φ₁ ≤ φ₂
                      → φ₁ + ψ ≤ φ₂ + ψ

      ≤-+-compatibleˡ : ∀ {φ₁ φ₂ ψ : ∣𝔼∣}
                      → φ₁ ≤ φ₂
                      → ψ + φ₁ ≤ ψ + φ₂

    variable φ φ′ φ₁ φ₂ φ₃ ψ ψ₁ ψ₂ : ∣𝔼∣

    ≤-reflexive : ∀ {φ φ′} → φ ≡ φ′ → φ ≤ φ′
    ≤-reflexive refl = ≤-refl

  module Typing (𝔼 : PoMonoid) where
    open PoMonoid 𝔼

    infix 4 _∋_ _⊩_ _⊢_#_
    infixl 5 _•_
    infix 5 𝑭_ ƛ_
    infix 6 _!
    infixr 6 $_⟵_
    infixr 7 _⇒_
    infixl 7 _·_

    mutual
      data ValType : Set where
        𝟙 : ValType
        𝑼 : ∣𝔼∣ → CompType → ValType

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
        ⟪_⟫ : Γ ⊢ B # φ → Γ ⊩ 𝑼 φ B -- thunk
        one : Γ ⊩ 𝟙           -- unit

      data _⊢_#_ : Ctx → CompType → ∣𝔼∣ → Set where
        return : Γ ⊩ A → Γ ⊢ 𝑭 A # ⊥
        _·_ : Γ ⊢ A ⇒ B # φ → Γ ⊩ A → Γ ⊢ B # φ
        ƛ_ : Γ • A ⊢ B # φ → Γ ⊢ A ⇒ B # φ
        _! : Γ ⊩ 𝑼 φ B → Γ ⊢ B # φ
        $_⟵_ : Γ ⊢ 𝑭 A # φ → Γ • A ⊢ B # ψ → Γ ⊢ B # φ + ψ
        subeff : Γ ⊢ B # φ → φ ≤ ψ → Γ ⊢ B # ψ

  record GradedMonad (𝔼 : PoMonoid) (𝑇 : PoMonoid.∣𝔼∣ 𝔼 → Set → Set) : Set₁ where
    open PoMonoid 𝔼 public
    infixl 1 _>>=_

    field
      η : ∀ {X} → X → 𝑇 ⊥ X
      _>>=_ : ∀ {X Y φ ψ φ′} → ⦃ _ : φ + ψ ≡ φ′ ⦄ → 𝑇 φ X → (X → 𝑇 ψ Y) → 𝑇 φ′ Y
      sub : ∀ {X φ ψ} → 𝑇 φ X → φ ≤ ψ → 𝑇 ψ X

      sub-id : ∀ {X φ} {m : 𝑇 φ X} {φ≤φ : φ ≤ φ} → sub m φ≤φ ≡ m
      sub-compose : ∀ {X φ φ′ φ″} → (φ≤φ′ : φ ≤ φ′) (φ′≤φ″ : φ′ ≤ φ″) (φ≤φ″ : φ ≤ φ″) (m : 𝑇 φ X)
                  → sub (sub m φ≤φ′) φ′≤φ″ ≡ sub m φ≤φ″

      -- sub-monotonic : sub m >>= sub ∘ f ≡ sub m >>= f

      >>=-identityˡ : ∀ {X Y φ} ⦃ eq : ⊥ + φ ≡ φ ⦄ (x : X) (f : X → 𝑇 φ Y) → (_>>=_ ⦃ eq ⦄ (η x) f) ≡ f x
      >>=-identityʳ : ∀ {X φ} (m : 𝑇 φ X) → (m >>= η) ≡ m
      >>=-assoc : ∀ {X Y Z φ₁ φ₂ φ₃} (m : 𝑇 φ₁ X) (g : X → 𝑇 φ₂ Y) (h : Y → 𝑇 φ₃ Z)
                → (m >>= g >>= h) ≡ (m >>= λ x → g x >>= h)

  module Denotational (𝔼 : PoMonoid) (𝑻 : PoMonoid.∣𝔼∣ 𝔼 → Set → Set)
      (GradedMonad : GradedMonad 𝔼 𝑻)
    where
    open Typing 𝔼
    open GradedMonad GradedMonad

    postulate
      fext : Extensionality 0ℓ 0ℓ

    infix 4 _??_ semantic-typing-val semantic-typing-comp

    -- Semantic domains
    mutual
      Domainᵛ : ValType → Set
      Domainᵛ 𝟙 = ⊤
      Domainᵛ (𝑼 φ B) = ⊤ → Domainᶜ φ B

      Domainᶜ : ∣𝔼∣ → CompType → Set
      Domainᶜ φ (A ⇒ B) = Domainᵛ A → Domainᶜ φ B
      Domainᶜ φ (𝑭 A) = 𝑻 φ (Domainᵛ A)

    sub-domain : Domainᶜ φ B → φ ≤ ψ → Domainᶜ ψ B
    sub-domain {B = A ⇒ B} f φ≤ψ = λ a → sub-domain {B = B} (f a) φ≤ψ
    sub-domain {B = 𝑭 A} fm φ≤ψ = sub fm φ≤ψ

    -- Algebra for semantic domain for computation types
    α[_,_] : (B : CompType) (φ : ∣𝔼∣) ⦃ _ : ψ + φ ≡ φ′ ⦄ → 𝑻 ψ (Domainᶜ φ B) → Domainᶜ φ′ B
    α[ A ⇒ B , φ ] fm a = α[ B , φ ] (fm >>= λ f → η (f a))
    α[ 𝑭 A , φ ] fm = fm >>= id

    -- Algebra laws
    α-η : ∀ a → α[ B , φ ] (η a) ≡ a
    α-η {A ⇒ B} {φ} f = fext lemma where
      lemma = λ a →
        begin
          α[ B , φ ] (η f >>= λ g → η (g a))
        ≡⟨ cong (α[ B , φ ]) (>>=-identityˡ f λ g → η (g a)) ⟩
          α[ B , φ ] (η (f a))
        ≡⟨ α-η {B = B} (f a) ⟩
          f a
        ∎
    α-η {𝑭 A} a = >>=-identityˡ a id

    Env : Ctx → Set
    Env ε = ⊤
    Env (Γ • A) = Env Γ × Domainᵛ A

    variable γ : Env Γ

    _??_ : Env Γ → Γ ∋ A → Domainᵛ A
    (_ , a) ?? zero = a
    (γ , _) ?? suc x = γ ?? x

    mutual
      ⟦_⟧v : Γ ⊩ A → Env Γ → Domainᵛ A
      ⟦ var x ⟧v γ = γ ?? x
      ⟦ ⟪ M ⟫ ⟧v γ = λ _ → ⟦ M ⟧c γ
      ⟦ one ⟧v γ = tt

      ⟦_⟧c : Γ ⊢ B # φ → Env Γ → Domainᶜ φ B
      ⟦ return V ⟧c γ = η (⟦ V ⟧v γ)
      ⟦ ƛ M ⟧c γ = λ a → ⟦ M ⟧c (γ , a)
      ⟦ M · V ⟧c γ = ⟦ M ⟧c γ (⟦ V ⟧v γ)
      ⟦ V ! ⟧c γ = ⟦ V ⟧v γ tt
      ⟦_⟧c {B = B} ($_⟵_ {ψ = ψ} M N) γ = α[ B , ψ ] (⟦ M ⟧c γ >>= λ a → η (⟦ N ⟧c (γ , a)))
      ⟦_⟧c {B = B} (subeff M φ≤ψ) γ = sub-domain {B = B} (⟦ M ⟧c γ) φ≤ψ

    mutual
      𝒱[_] : (A : ValType) → Domainᵛ A → Set
      𝒱[ 𝟙 ] tt = ⊤
      𝒱[ 𝑼 φ B ] a = (φ , a tt) ∈ 𝒞[ B ]

      𝒞[_] : (B : CompType) → ∃[ φ ] Domainᶜ φ B → Set
      𝒞[ A ⇒ B ] (φ , f) =
        ∀ {a : Domainᵛ A} → a ∈ 𝒱[ A ] → (φ , f a) ∈ 𝒞[ B ]
      𝒞[ 𝑭 A ] (φ , b) = ∃[ a ] Σ[ pf ∈ ⊥ ≤ φ ] b ≡ sub (η a) pf × a ∈ 𝒱[ A ]

    𝒞-closed-≤ : ∀ {b : Domainᶜ φ B} → (φ , b) ∈ 𝒞[ B ] → (φ≤φ′ : φ ≤ φ′)
               → (φ′ , sub-domain {B = B} b φ≤φ′) ∈ 𝒞[ B ]
    𝒞-closed-≤ {B = A ⇒ B} b∈𝒞 φ≤φ′ a∈𝒱 = 𝒞-closed-≤ (b∈𝒞 a∈𝒱) φ≤φ′
    𝒞-closed-≤ {B = 𝑭 A} (a , ⊥≤φ , refl , a∈𝒱) φ≤φ′ =
      a , ⊥≤φ′ , sub-compose ⊥≤φ φ≤φ′ ⊥≤φ′ (η a) , a∈𝒱
      where
        ⊥≤φ′ = ≤-trans ⊥≤φ φ≤φ′

    _⊨_ : (Γ : Ctx) → Env Γ → Set
    ε ⊨ tt = ⊤
    (Γ • A) ⊨ (γ , a) = Γ ⊨ γ × a ∈ 𝒱[ A ]

    semantic-typing-val : Γ ⊩ A → Set
    semantic-typing-val {Γ} {A} V =
      ∀ {γ : Env Γ} → Γ ⊨ γ → ⟦ V ⟧v γ ∈ 𝒱[ A ]

    syntax semantic-typing-val {Γ} {A} V = Γ ⊫ V ∷ A

    semantic-typing-comp : Γ ⊢ B # φ → Set
    semantic-typing-comp {Γ} {B} {φ} M =
      ∀ {γ : Env Γ} → Γ ⊨ γ → (φ , ⟦ M ⟧c γ) ∈ 𝒞[ B ]

    syntax semantic-typing-comp {Γ} {B} {φ} M = Γ ⊨ M ∷ B # φ

    mutual
      fundamental-lemma-val : (V : Γ ⊩ A) → Γ ⊫ V ∷ A
      fundamental-lemma-val (var zero) (_ , ⊫a) = ⊫a
      fundamental-lemma-val (var (suc x)) (⊨γ , _) = fundamental-lemma-val (var x) ⊨γ
      fundamental-lemma-val ⟪ M ⟫ ⊨γ = fundamental-lemma-comp M ⊨γ
      fundamental-lemma-val one ⊨γ = tt

      fundamental-lemma-comp : (M : Γ ⊢ B # φ) → Γ ⊨ M ∷ B # φ
      fundamental-lemma-comp (return V) {γ} ⊨γ =
        ⟦ V ⟧v γ , ≤-refl , sym sub-id , fundamental-lemma-val V ⊨γ
      fundamental-lemma-comp (M · V) ⊨γ =
        fundamental-lemma-comp M ⊨γ (fundamental-lemma-val V ⊨γ)
      fundamental-lemma-comp (ƛ M) ⊨γ {a} a∈𝒱 =
        fundamental-lemma-comp M (⊨γ , a∈𝒱)
      fundamental-lemma-comp (V !) ⊨γ = fundamental-lemma-val V ⊨γ
      fundamental-lemma-comp {B = B} ($ M ⟵ N) {γ = γ} ⊨γ
        with fundamental-lemma-comp M ⊨γ
      ...  | a , pf , eq , a∈𝒱
        rewrite eq =
--           | >>=-identityˡ a (λ a → η (⟦ N ⟧c (γ , a))) =
--           | α-η {B} (⟦ N ⟧c (γ , a)) =
--        fundamental-lemma-comp N (⊨γ , a∈𝒱)
        {!!}
      fundamental-lemma-comp (subeff M φ≤ψ) ⊨γ =
        𝒞-closed-≤ (fundamental-lemma-comp M ⊨γ) φ≤ψ

--    type-soundness-comp : (M : ε ⊢ 𝑭 A # φ) → ∃[ a ] ⟦ M ⟧c tt ≡ η a × a ∈ 𝒱[ A ]
--    type-soundness-comp M = fundamental-lemma-comp M tt
