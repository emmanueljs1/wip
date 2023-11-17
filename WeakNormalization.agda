import Relation.Binary.PropositionalEquality as Eq
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open Eq using (_≡_; sym)

-- Normalization with weak-head reduction of STLC.
--
-- adapted from "How to (Re)Invent Tait's Method" (Harper, 2022)
-- https://www.cs.cmu.edu/~rwh/courses/chtt/pdfs/tait.pdf
--
-- currently missing proofs for substitution lemmas

module WeakNormalization where

data Type : Set where
  unit : Type
  _⇒_  : Type → Type → Type

infixr 7 _⇒_

variable
  S T : Type

data Ctx : Set where
  ∅ : Ctx
  _∷_ : Ctx → Type → Ctx

infixl 5 _∷_

variable
  Γ Γ′ Γ″ Δ Δ′ Δ″ : Ctx

data _∋_ : Ctx → Type → Set where
  zero : Γ ∷ T ∋ T
  suc : Γ ∋ T → Γ ∷ S ∋ T

infix 4 _∋_

data _⊢_ : Ctx → Type → Set where
  one : Γ ⊢ unit

  var : Γ ∋ T
        -----
      → Γ ⊢ T

  ƛ_ : Γ ∷ S ⊢ T
       ---------
     → Γ ⊢ S ⇒ T

  _·_ : Γ ⊢ S ⇒ T
      → Γ ⊢ S
        ---------
      → Γ ⊢ T

variable
  r r′ r″ : Γ ⊢ S ⇒ T
  s s′ s″ : Γ ⊢ S
  t t′ t″ t₁ t₂ t₃ u v : Γ ⊢ T

infix 4 _⊢_

Ren : Ctx → Ctx → Set
Ren Γ Δ = ∀ {T} → Δ ∋ T → Γ ∋ T

Sub : Ctx → Ctx → Set
Sub Γ Δ = ∀ {T} → Δ ∋ T → Γ ⊢ T

variable
  γ : Sub Γ Δ

ext : Ren Γ Δ → ∀ {T} → Ren (Γ ∷ T) (Δ ∷ T)
ext ρ zero     = zero
ext ρ (suc x)  = suc (ρ x)

rename : Ren Γ Δ → Δ ⊢ T → Γ ⊢ T
rename _ one = one
rename ρ (var x) = var (ρ x)
rename ρ (ƛ t) = ƛ rename (ext ρ) t
rename ρ (r · s) = rename ρ r · rename ρ s

rename-id-identity : rename (λ x → x) t ≡ t
rename-id-identity = {!!}

exts : Sub Γ Δ → ∀ {T} → Sub (Γ ∷ T) (Δ ∷ T)
exts σ zero    = var zero
exts σ (suc x) = rename suc (σ x)

subst : Sub Γ Δ → Δ ⊢ T → Γ ⊢ T
subst _ one = one
subst σ (var x) = σ x
subst σ (ƛ t) = ƛ subst (exts σ) t
subst σ (s · t) = subst σ s · subst σ t

id : Sub Γ Γ
id x = var x

postulate
  subst-id-identity : subst id t ≡ t

_++_ : Sub Γ Δ → Γ ⊢ S → Sub Γ (Δ ∷ S)
(_ ++ s) zero     = s
(σ ++ _) (suc x)  = σ x

infix 8 _++_

_[_] : Γ ∷ S ⊢ T → Γ ⊢ S → Γ ⊢ T
t [ s ] = subst (id ++ s) t

data _⟶ᵦ_ : Γ ⊢ T → Γ ⊢ T → Set where
  β-⟶ : ∀ {t : Γ ∷ S ⊢ T} {s : Γ ⊢ S}
        --------------------
      → (ƛ t) · s ⟶ᵦ t [ s ]

  app : ∀ {r r′ : Γ ⊢ S ⇒ T} {s : Γ ⊢ S}
       → r ⟶ᵦ r′
         ---------------
       → r · s ⟶ᵦ r′ · s

infix 4 _⟶ᵦ_

postulate
  ⟶ᵦ-closed-substitution : t ⟶ᵦ t′
                         → subst γ t ⟶ᵦ subst γ t′

value : Γ ⊢ T → Set
value t = ¬ (∃[ t′ ] t ⟶ᵦ t′)

data _⟶ᵦ*_ : Γ ⊢ T → Γ ⊢ T → Set where
  reflᵦ* : t ⟶ᵦ* t

  transᵦ* : t₁ ⟶ᵦ t₂
          → t₂ ⟶ᵦ* t₃
            ---------
          → t₁ ⟶ᵦ* t₃

infix 4 _⟶ᵦ*_

transᵦ*-⟶ᵦ : t ⟶ᵦ* t′
           → t′ ⟶ᵦ t″
            --------
           → t ⟶ᵦ* t″
transᵦ*-⟶ᵦ reflᵦ* β-⟶ = transᵦ* β-⟶ reflᵦ*
transᵦ*-⟶ᵦ reflᵦ* (app r⟶ᵦr′) = transᵦ* (app r⟶ᵦr′) reflᵦ*
transᵦ*-⟶ᵦ (transᵦ* t⟶ᵦt′ t′⟶ᵦ*t″) t″⟶ᵦt‴ = transᵦ* t⟶ᵦt′ (transᵦ*-⟶ᵦ t′⟶ᵦ*t″ t″⟶ᵦt‴)

⟶ᵦ*-app-compatible : r ⟶ᵦ* r′
                   → r · s ⟶ᵦ* r′ · s
⟶ᵦ*-app-compatible reflᵦ* = reflᵦ*
⟶ᵦ*-app-compatible (transᵦ* r⟶ᵦr′ r′⟶ᵦ*r″) =
  transᵦ* (app r⟶ᵦr′) (⟶ᵦ*-app-compatible r′⟶ᵦ*r″)

⟶ᵦ*-closed-substitution : t ⟶ᵦ* t′
                        → subst γ t ⟶ᵦ* subst γ t′
⟶ᵦ*-closed-substitution reflᵦ* = reflᵦ*
⟶ᵦ*-closed-substitution (transᵦ* t⟶ᵦt′ t′⟶ᵦ*t″) =
  transᵦ* (⟶ᵦ-closed-substitution t⟶ᵦt′) (⟶ᵦ*-closed-substitution t′⟶ᵦ*t″)


HT : Δ ⊢ T → Set
HT {T = unit} t  = t ⟶ᵦ* one
HT {Δ} {S ⇒ T} r =
  ∃[ t ] r ⟶ᵦ* ƛ t × ∀ {s : Δ ⊢ S} → HT s → HT (t [ s ])

head-expansion : ∀ {T} {t t′ : Γ ⊢ T}
               → t ⟶ᵦ t′
               → HT t′
                 ------
               → HT t
head-expansion {T = unit} t⟶ᵦt′ t′⟶ᵦ*one =
  transᵦ* t⟶ᵦt′ t′⟶ᵦ*one
head-expansion {T = S ⇒ T} r⟶ᵦr′ (t , r⟶ᵦƛt , ht) =
  t , transᵦ* r⟶ᵦr′ r⟶ᵦƛt , ht

head-expansion* : ∀ {T} {t t′ : Γ ⊢ T}
                → t ⟶ᵦ* t′
                → HT t′
                  --------
                → HT t
head-expansion* reflᵦ* ht = ht
head-expansion* (transᵦ* t⟶ᵦt′ t′⟶ᵦ*t″) ht =
  head-expansion t⟶ᵦt′ (head-expansion* t′⟶ᵦ*t″ ht)

_⊨_ : (Γ : Ctx) → Sub Δ Γ → Set
Γ ⊨ γ = ∀ {T} (x : Γ ∋ T) → HT (γ x)

infix 4 _⊨_

⊨_ : Γ ⊢ T → Set
⊨_ {Γ} t = ∀ {Δ} {γ : Sub Δ Γ}
           → Γ ⊨ γ
           → HT (subst γ t)

infix 4 ⊨_

⊨one : ⊨ one {Γ}
⊨one _ = reflᵦ*

⊨var : ∀ (x : Γ ∋ T)
       --------
     → ⊨ var x
⊨var x Γ⊨γ = Γ⊨γ x

ext-⊨ : Γ ⊨ γ
      → HT s
        --------------
      → Γ ∷ S ⊨ γ ++ s
ext-⊨ _ ht zero     = ht
ext-⊨ Γ⊨γ _ (suc x) = Γ⊨γ x

postulate
  substitution-lemma : (subst (exts γ) t) [ s ] ≡ subst (γ ++ s) t

⊨ƛ : ∀ {t : Γ ∷ S ⊢ T}
   → ⊨ t
     -----
   → ⊨ ƛ t
⊨ƛ {t = t} ⊨t {γ = γ} Γ⊨γ =
--  with ⊨t (ext-⊨ Γ⊨γ ht-s)
--...  | ht
--  rewrite sym (substitution-lemma {γ = γ} {t = t} {s = s}) =
  subst (exts γ) t ,
  reflᵦ* ,
  λ {s} ht-s →
    Eq.subst
      HT
      (sym (substitution-lemma {γ = γ} {t = t} {s = s}))
      (⊨t (ext-⊨ Γ⊨γ ht-s))

⊨· : ∀ {r : Γ ⊢ S ⇒ T} {s : Γ ⊢ S}
   → ⊨ r
   → ⊨ s
     -------
   → ⊨ r · s
⊨· {r = r} {s} ⊨r ⊨s {γ = γ} Γ⊨γ
  with ⊨r Γ⊨γ
...  | t , r⟶ᵦ*ƛt , ht =
  head-expansion*
    (transᵦ*-⟶ᵦ (⟶ᵦ*-app-compatible r⟶ᵦ*ƛt) β-⟶)
    (ht (⊨s Γ⊨γ))

fundamental-theorem : (t : Γ ⊢ T) → ⊨ t
fundamental-theorem one = ⊨one
fundamental-theorem (var x) = ⊨var x
fundamental-theorem (ƛ t) = ⊨ƛ {t = t} (fundamental-theorem t)
fundamental-theorem (r · s) =
  ⊨· {r = r} {s} (fundamental-theorem r) (fundamental-theorem s)

weakly-normalizing : ∀ {T : Type} {t : ∅ ⊢ T}
                   → ∃[ t′ ] t ⟶ᵦ* t′ × value t′
weakly-normalizing {T} {t} with fundamental-theorem t {γ = id} (λ ())
weakly-normalizing {unit} {t}  | t⟶ᵦ*one
  rewrite subst-id-identity {t = t} = one , t⟶ᵦ*one , (λ ())
weakly-normalizing {S ⇒ T} {t} | t′ , t⟶ᵦ*ƛt′ , _
  rewrite subst-id-identity {t = t} = ƛ t′ , t⟶ᵦ*ƛt′ , (λ ())
