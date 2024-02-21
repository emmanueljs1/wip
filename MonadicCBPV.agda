import Axiom.Extensionality.Propositional as Extensionality
import Relation.Binary.PropositionalEquality as Eq
open import Category.Monad using (RawMonad)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_; id)
open import Level using (0ℓ)
open import Relation.Unary using (_∈_)
open Eq using (_≡_; refl; trans; sym; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open Extensionality using (Extensionality)

module MonadicCBPV  where
  module Typing where
    infix 4 _∋_ _⊩_ _⊢_
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

  record Monad {𝑇 : Set → Set} (RawMonadT : RawMonad 𝑇) : Set₁ where
    open RawMonad RawMonadT renaming (return to η) public

    -- Monad laws
    field
      >>=-identityˡ : ∀ {A B} (a : A) (f : A → 𝑇 B) → (η a >>= f) ≡ f a
      >>=-identityʳ : ∀ {A} (m : 𝑇 A) → (m >>= η) ≡ m
      >>=-assoc : ∀ {A B C} (m : 𝑇 A) (g : A → 𝑇 B) (h : B → 𝑇 C)
                → (m >>= g >>= h) ≡ (m >>= λ x → g x >>= h)

  module Denotational (𝑻 : Set → Set) (RawMonadT : RawMonad 𝑻) (Monad : Monad RawMonadT) where
    open Typing
    open Monad Monad

    postulate
      fext : Extensionality 0ℓ 0ℓ

    infix 4 _??_ semantic-typing-val semantic-typing-comp

    -- Semantic domains
    mutual
      Domainᵛ : ValType → Set
      Domainᵛ 𝟙 = ⊤
      Domainᵛ (𝑼 B) = ⊤ → Domainᶜ B

      Domainᶜ : CompType → Set
      Domainᶜ (A ⇒ B) = Domainᵛ A → Domainᶜ B
      Domainᶜ (𝑭 A) = 𝑻 (Domainᵛ A)

    -- Algebra for semantic domain for computation types
    α[_] : (B : CompType) → 𝑻 (Domainᶜ B) → Domainᶜ B
    α[ A ⇒ B ] fm a = α[ B ] (fm >>= λ f → η (f a))
    α[ 𝑭 A ] = join

    -- Algebra laws
    α-η : ∀ a → α[ B ] (η a) ≡ a
    α-η {A ⇒ B} f = fext lemma where
      lemma : ∀ a → α[ B ] (η f >>= λ g → η (g a)) ≡ f a
      lemma a rewrite >>=-identityˡ f (λ g → η (g a)) = α-η {B} (f a)
    α-η {𝑭 A} a = >>=-identityˡ a id

    α->>= : ∀ {X} f (am : 𝑻 X)
          → α[ B ] (am >>= η ∘ α[ B ] ∘ f) ≡ α[ B ] (am >>= f)
    α->>= {A ⇒ B} f am = fext lemma where
      lemma = λ a →
        begin
          α[ B ] (am >>= η ∘ α[ A ⇒ B ] ∘ f >>= λ g → η (g a))
        ≡⟨ cong α[ B ]
             (begin
               (am >>= η ∘ α[ A ⇒ B ] ∘ f >>= λ g → η (g a))
             ≡⟨ >>=-assoc am (η ∘ α[ A ⇒ B ] ∘ f) (λ g → η (g a)) ⟩
                (am >>= λ y → η (α[ A ⇒ B ] (f y)) >>= λ g → η (g a))
             ≡⟨ cong (am >>=_) (fext (λ y → >>=-identityˡ (α[ A ⇒ B ] (f y)) λ g → η (g a))) ⟩
               (am >>= η ∘ α[ B ] ∘ (λ y → f y >>= λ g → η (g a)))
             ∎)
        ⟩
          α[ B ] (am >>= η ∘ α[ B ] ∘ (λ y → f y >>= λ g → η (g a)))
        ≡⟨ α->>= {B} ((λ y → f y >>= λ g → η (g a))) am ⟩
          α[ B ] (am >>= λ y → f y >>= λ g → η (g a))
        ≡⟨ cong α[ B ] (sym (>>=-assoc am f (λ g → η (g a)))) ⟩
          α[ B ] (am >>= f >>= λ g → η (g a))
        ∎
    α->>= {𝑭 A} f am
      rewrite >>=-assoc am (η ∘ join ∘ f) id
            | fext λ x → >>=-identityˡ (join (f x)) id = sym (>>=-assoc am f id)

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

      ⟦_⟧c : Γ ⊢ B → Env Γ → Domainᶜ B
      ⟦ return V ⟧c γ = η (⟦ V ⟧v γ)
      ⟦ ƛ M ⟧c γ = λ a → ⟦ M ⟧c (γ , a)
      ⟦ M · V ⟧c γ = ⟦ M ⟧c γ (⟦ V ⟧v γ)
      ⟦ V ! ⟧c γ = ⟦ V ⟧v γ tt
      ⟦_⟧c {B = B} ($ M ⟵ N) γ = α[ B ] (⟦ M ⟧c γ >>= λ a → η (⟦ N ⟧c (γ , a)))

    mutual
      𝒱[_] : (A : ValType) → Domainᵛ A → Set
      𝒱[ 𝟙 ] tt = ⊤
      𝒱[ 𝑼 B ] a = a tt ∈ 𝒞[ B ]

      𝒞[_] : (B : CompType) → Domainᶜ B → Set
      𝒞[ A ⇒ B ] f =
        ∀ {W : Domainᵛ A} → W ∈ 𝒱[ A ] → f W ∈ 𝒞[ B ]
      𝒞[ 𝑭 A ] b = ∃[ a ] b ≡ η a × a ∈ 𝒱[ A ]

    _⊨_ : (Γ : Ctx) → Env Γ → Set
    ε ⊨ tt = ⊤
    (Γ • A) ⊨ (γ , a) = Γ ⊨ γ × a ∈ 𝒱[ A ]

    semantic-typing-val : Γ ⊩ A → Set
    semantic-typing-val {Γ} {A} V =
      ∀ {γ : Env Γ} → Γ ⊨ γ → ⟦ V ⟧v γ ∈ 𝒱[ A ]

    syntax semantic-typing-val {Γ} {A} V = Γ ⊫ V ∷ A

    semantic-typing-comp : Γ ⊢ B → Set
    semantic-typing-comp {Γ} {B} M =
      ∀ {γ : Env Γ} → Γ ⊨ γ → ⟦ M ⟧c γ ∈ 𝒞[ B ]

    syntax semantic-typing-comp {Γ} {B} M = Γ ⊨ M ∷ B

    mutual
      fundamental-lemma-val : (V : Γ ⊩ A) → Γ ⊫ V ∷ A
      fundamental-lemma-val (var zero) (_ , ⊫a) = ⊫a
      fundamental-lemma-val (var (suc x)) (⊨γ , _) = fundamental-lemma-val (var x) ⊨γ
      fundamental-lemma-val ⟪ M ⟫ ⊨γ = fundamental-lemma-comp M ⊨γ
      fundamental-lemma-val one ⊨γ = tt

      fundamental-lemma-comp : (M : Γ ⊢ B) → Γ ⊨ M ∷ B
      fundamental-lemma-comp (return V) {γ} ⊨γ =
        ⟦ V ⟧v γ , refl , fundamental-lemma-val V ⊨γ
      fundamental-lemma-comp (M · V) ⊨γ =
        fundamental-lemma-comp M ⊨γ (fundamental-lemma-val V ⊨γ)
      fundamental-lemma-comp (ƛ M) ⊨γ {a} a∈𝒱 =
        fundamental-lemma-comp M (⊨γ , a∈𝒱)
      fundamental-lemma-comp (V !) ⊨γ = fundamental-lemma-val V ⊨γ
      fundamental-lemma-comp {B = B} ($ M ⟵ N) {γ = γ} ⊨γ
        with fundamental-lemma-comp M ⊨γ
      ...  | a , eq , a∈𝒱
        rewrite eq
           | >>=-identityˡ a (λ a → η (⟦ N ⟧c (γ , a)))
           | α-η {B} (⟦ N ⟧c (γ , a)) =
        fundamental-lemma-comp N (⊨γ , a∈𝒱)

    type-soundness-comp : (M : ε ⊢ 𝑭 A) → ∃[ a ] ⟦ M ⟧c tt ≡ η a × a ∈ 𝒱[ A ]
    type-soundness-comp M = fundamental-lemma-comp M tt
