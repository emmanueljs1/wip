import Relation.Binary.PropositionalEquality as Eq
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open Eq using (_≡_; sym)

-- Normalization with full reductions for STLC
--
-- adapted from "Kripke-Style Logical Relations for Normalization" (Harper, 2022)
-- https://www.cs.cmu.edu/~rwh/courses/chtt/pdfs/kripke.pdf
--
-- currently incomplete

module Normalization where

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
  r r′ : Γ ⊢ S ⇒ T
  s s′ s″ : Γ ⊢ S
  t t′ t″ t₁ t₂ t₃ u v : Γ ⊢ T

infix 4 _⊢_

Ren : Ctx → Ctx → Set
Ren Γ Δ = ∀ {T} → Δ ∋ T → Γ ∋ T

Sub : Ctx → Ctx → Set
Sub Γ Δ = ∀ {T} → Δ ∋ T → Γ ⊢ T

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

subst-id-identity : subst id t ≡ t
subst-id-identity = {!!}

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

  app₁ : ∀ {r r′ : Γ ⊢ S ⇒ T} {s : Γ ⊢ S}
       → r ⟶ᵦ r′
         ---------------
       → r · s ⟶ᵦ r′ · s

  app₂ : ∀ {r : Γ ⊢ S ⇒ T} {s s′ : Γ ⊢ S}
       → s ⟶ᵦ s′
         ---------------
       → r · s ⟶ᵦ r · s′

  lam : ∀ {t t′ : Γ ∷ S ⊢ T}
      → t ⟶ᵦ t′
        ----------
      → ƛ t ⟶ᵦ ƛ t′

infix 4 _⟶ᵦ_

β-normal-form : Γ ⊢ T → Set
β-normal-form t = ¬ (∃[ t′ ] t ⟶ᵦ t′)

data _⟶ᵦ*_ : Γ ⊢ T → Γ ⊢ T → Set where
  step : t ⟶ᵦ t′
         --------
       → t ⟶ᵦ* t′

  reflᵦ* : t ⟶ᵦ* t

  transᵦ* : t₁ ⟶ᵦ* t₂
          → t₂ ⟶ᵦ* t₃
            ---------
          → t₁ ⟶ᵦ* t₃

infix 4 _⟶ᵦ*_

⟶ᵦ*-app-compatible : r ⟶ᵦ* r′
                   → s ⟶ᵦ* s′
                   → r · s ⟶ᵦ* r′ · s′
⟶ᵦ*-app-compatible (step r⟶ᵦr′) (step s⟶ᵦs′) =
  transᵦ* (step (app₂ s⟶ᵦs′)) (step (app₁ r⟶ᵦr′))
⟶ᵦ*-app-compatible (step r⟶ᵦr′) reflᵦ* = step (app₁ r⟶ᵦr′)
⟶ᵦ*-app-compatible (step r⟶ᵦr′) (transᵦ* s⟶ᵦ*s′ s′⟶ᵦs″) =
  transᵦ*
    (⟶ᵦ*-app-compatible reflᵦ* s⟶ᵦ*s′)
    (⟶ᵦ*-app-compatible (step r⟶ᵦr′) s′⟶ᵦs″)
⟶ᵦ*-app-compatible reflᵦ* (step s⟶ᵦs′) = step (app₂ s⟶ᵦs′)
⟶ᵦ*-app-compatible reflᵦ* reflᵦ* = reflᵦ*
⟶ᵦ*-app-compatible reflᵦ* (transᵦ* s⟶ᵦ*s′ s′⟶ᵦ*s″) =
  transᵦ*
    (⟶ᵦ*-app-compatible reflᵦ* s⟶ᵦ*s′)
    (⟶ᵦ*-app-compatible reflᵦ* s′⟶ᵦ*s″)
⟶ᵦ*-app-compatible (transᵦ* r⟶ᵦ*r′ r′⟶ᵦ*r″) s′⟶ᵦ*s″ =
  transᵦ*
    (⟶ᵦ*-app-compatible r⟶ᵦ*r′ s′⟶ᵦ*s″)
    (⟶ᵦ*-app-compatible r′⟶ᵦ*r″ reflᵦ*)

normᵦ : Γ ⊢ T → Set
normᵦ t = ∃[ t′ ] β-normal-form t′ × t ⟶ᵦ* t′

data _≤_ : Ctx → Ctx → Set where
  refl≤ : Γ ≤ Γ

  ∷≤ : Γ′ ≤ Γ
       ----------
     → Γ′ ∷ T ≤ Γ

infix 4 _≤_

trans≤ : Γ″ ≤ Γ′ → Γ′ ≤ Γ → Γ″ ≤ Γ
trans≤ refl≤ Γ′≤Γ             = Γ′≤Γ
trans≤ (∷≤ Γ″≤Γ′) refl≤       = ∷≤ Γ″≤Γ′
trans≤ (∷≤ Γ″≤Γ′∷T) (∷≤ Γ′≤Γ) = ∷≤ (trans≤ Γ″≤Γ′∷T (∷≤ Γ′≤Γ))

weakening : Γ′ ≤ Γ → Ren Γ′ Γ
weakening refl≤     x = x
weakening (∷≤ Γ′≤Γ) x = suc (weakening Γ′≤Γ x)

weaken : Γ′ ≤ Γ → Γ ⊢ T → Γ′ ⊢ T
weaken Γ′≤Γ t = rename (weakening Γ′≤Γ) t

weaken-weaken : ∀ (Γ″≤Γ′ : Γ″ ≤ Γ′) (Γ′≤Γ : Γ′ ≤ Γ) (t : Γ ⊢ T)
  → weaken Γ″≤Γ′ (weaken Γ′≤Γ t) ≡ weaken (trans≤ Γ″≤Γ′ Γ′≤Γ) t
weaken-weaken = {!!}

⟶ᵦ-closed-weakening : ∀ {t t′ : Γ ⊢ T} (Γ′≤Γ : Γ′ ≤ Γ)
                    → t ⟶ᵦ t′
                      -------------------------------
                    → weaken Γ′≤Γ t ⟶ᵦ weaken Γ′≤Γ t′
⟶ᵦ-closed-weakening = {!!}

normᵦ-closed-weakening : ∀ (Γ′≤Γ : Γ′ ≤ Γ) (t : Γ ⊢ T)
                       → normᵦ t
                         ---------------------
                       → normᵦ (weaken Γ′≤Γ t)
normᵦ-closed-weakening = {!!}

HN : Δ ⊢ T → Set
HN {T = unit} t  = normᵦ t
HN {Δ} {S ⇒ T} t =
  ∀ {Δ′} → (Δ′≤Δ : Δ′ ≤ Δ) (s : Δ′ ⊢ S)
  → HN s
  → HN (weaken Δ′≤Δ t · s)

hn-anti-monotonicity : ∀ (Δ′≤Δ : Δ′ ≤ Δ) (t : Δ ⊢ T)
                     → HN t
                       ------------------
                     → HN (weaken Δ′≤Δ t)
hn-anti-monotonicity {T = unit}                         =
  normᵦ-closed-weakening
hn-anti-monotonicity {T = S ⇒ T} Δ′≤Δ r hnᵣ Δ″≤Δ′ s hnₛ
    rewrite weaken-weaken Δ″≤Δ′ Δ′≤Δ r                  =
  hnᵣ (trans≤ Δ″≤Δ′ Δ′≤Δ) s hnₛ

head-expansion : ∀ {T} {t t′ : Γ ⊢ T}
               → t ⟶ᵦ t′
               → HN t′
                 ------
               → HN t
head-expansion {T = unit} t⟶ᵦt′ (t″ , nf-t″ , t′⟶ᵦ*t″) =
  t″ , nf-t″ , transᵦ* (step t⟶ᵦt′) t′⟶ᵦ*t″
head-expansion {T = S ⇒ T} r⟶ᵦr′ hnᵣ Δ′≤Δ s hnₛ =
  head-expansion
    (app₁ (⟶ᵦ-closed-weakening Δ′≤Δ r⟶ᵦr′))
    (hnᵣ Δ′≤Δ s hnₛ)

_⊨_ : (Γ : Ctx) → Sub Δ Γ → Set
Γ ⊨ γ = ∀ {T} (x : Γ ∋ T) → HN (γ x)

infix 4 _⊨_

⊨_ : Γ ⊢ T → Set
⊨_ {Γ} t = ∀ {Δ} {γ : Sub Δ Γ}
           → Γ ⊨ γ
           → HN (subst γ t)

infix 4 ⊨_

⊨one : ⊨ one {Γ}
⊨one _ = one , (λ ()) , reflᵦ*

⊨var : ∀ (x : Γ ∋ T)
       --------
     → ⊨ var x
⊨var x Γ⊨γ = Γ⊨γ x

⊨ƛ : ∀ {t : Γ ∷ S ⊢ T}
   → ⊨ t
     -----
   → ⊨ ƛ t
⊨ƛ {Γ} {S} {t = t} ⊨t {γ = γ} Γ⊨γ {Δ′} Δ′≤Δ s hnₛ =
  head-expansion
    β-⟶
    hn
  where
    γ′ : Sub Δ′ Γ
    γ′ x = weaken Δ′≤Δ (γ x)

    Δ′∷S⊨γ′++s : Γ ∷ S ⊨ γ′ ++ s
    Δ′∷S⊨γ′++s zero    = hnₛ
    Δ′∷S⊨γ′++s (suc x) = hn-anti-monotonicity Δ′≤Δ (γ x) (Γ⊨γ x)

    t[γ′++s] = rename (ext (weakening Δ′≤Δ)) (subst (exts γ) t) [ s ]

    substitution-lemma : t[γ′++s] ≡ (subst (γ′ ++ s) t)
    substitution-lemma = {!!}

    hn : HN t[γ′++s]
    hn rewrite substitution-lemma = ⊨t Δ′∷S⊨γ′++s

⊨· : ∀ {r : Γ ⊢ S ⇒ T} {s : Γ ⊢ S}
   → ⊨ r
   → ⊨ s
     -------
   → ⊨ r · s
⊨· {r = r} {s} ⊨r ⊨s {γ = γ} Γ⊨γ
    rewrite sym (rename-id-identity {t = subst γ r}) =
  ⊨r Γ⊨γ refl≤ (subst γ s) (⊨s Γ⊨γ)

fundamental-theorem : (t : Γ ⊢ T) → ⊨ t
fundamental-theorem one = ⊨one
fundamental-theorem (var x) = ⊨var x
fundamental-theorem (ƛ t) = ⊨ƛ {t = t} (fundamental-theorem t)
fundamental-theorem (r · s) =
  ⊨· {r = r} {s} (fundamental-theorem r) (fundamental-theorem s)

data Ne : Γ ⊢ T → Set where
  ne-var : ∀ (x : Γ ∋ T)
         → Ne (var x)

  ne-app : ∀ {u : Γ ⊢ S ⇒ T}
         → Ne u
         → (s : Γ ⊢ S)
         → Ne (u · s)

ne-closed-weakening : ∀ (Δ′≤Δ : Δ′ ≤ Δ)
                    → Ne u
                    → Ne (weaken Δ′≤Δ u)
ne-closed-weakening Δ′≤Δ (ne-var x) =
  ne-var (weakening Δ′≤Δ x)
ne-closed-weakening Δ′≤Δ (ne-app ne s) =
  ne-app (ne-closed-weakening Δ′≤Δ ne) (weaken Δ′≤Δ s)

NN : ∀ {u : Δ ⊢ T} → Ne u → Set
NN (ne-var _)      = ⊤
NN (ne-app ne s) = NN ne × normᵦ s

nn→normᵦ : ∀ {ne : Ne u}
         → NN ne
           ----------------------------------------
         → Σ[ normᵦ-u ∈ normᵦ u ] Ne (proj₁ normᵦ-u)
nn→normᵦ {ne = ne-var x} nn = (var x , (λ ()) , reflᵦ*) , ne-var x
nn→normᵦ {ne = ne-app ne s} (nn , normᵦ-s)
  with nn→normᵦ nn                 | normᵦ-s
...  | (u′ , ¬u′⟶ᵦ , u⟶ᵦ*u′) , ne′ | s′ , ¬s′⟶ᵦ , s⟶ᵦ*s′ =
  (u′ · s′ ,
  (λ where
       (u″ · s′ , app₁ u′⟶ᵦu″) → ¬u′⟶ᵦ (u″ , u′⟶ᵦu″)
       (u′ · s″ , app₂ s′⟶ᵦs″) → ¬s′⟶ᵦ (s″ , s′⟶ᵦs″)) ,
  ⟶ᵦ*-app-compatible u⟶ᵦ*u′ s⟶ᵦ*s′) ,
  ne-app ne′ s′

nn-anti-monotonicity : ∀ (Δ′≤Δ : Δ′ ≤ Δ) (ne : Ne u)
                     → NN ne
                     → NN (ne-closed-weakening Δ′≤Δ ne)
nn-anti-monotonicity Δ′≤Δ (ne-var _) _ = tt
nn-anti-monotonicity Δ′≤Δ (ne-app ne s) (nn , normᵦ-s) =
  nn-anti-monotonicity Δ′≤Δ ne nn ,
  normᵦ-closed-weakening Δ′≤Δ s normᵦ-s

{- Pas-de-deux -}
mutual
  nn→hn : ∀ {T} {u : Δ ⊢ T} (ne : Ne u)
        → NN ne
          -----
        → HN u
  nn→hn {T = unit} ne nn = let (hn , _) = nn→normᵦ nn in hn
  nn→hn {T = S ⇒ T} ne nn Δ′≤Δ s hnₛ =
    nn→hn
      (ne-app (ne-closed-weakening Δ′≤Δ ne) s)
      (nn-anti-monotonicity Δ′≤Δ ne nn , hn→normᵦ hnₛ)

  hn→normᵦ : ∀ {T} {t : Δ ⊢ T}
           → HN t
             -------
           → normᵦ t
  hn→normᵦ {T = unit} hn = hn
  hn→normᵦ {T = S ⇒ T} hn
    with hn→normᵦ (hn (∷≤ {T = S} refl≤) (var zero) (nn→hn (ne-var zero) tt))
  ...  | t′ , ¬t′⟶ᵦ , r·x⟶ᵦ*t′ =
    ƛ t′ ,
    (λ where (ƛ t″ , lam t′⟶ᵦt″) → ¬t′⟶ᵦ (t″ , t′⟶ᵦt″)) ,
    {!!} -- TODO: prove normᵦ(r · s) ⇒ normᵦ(r) and normᵦ(rename r) ⇒ normᵦ(r)

normalization : (t : Γ ⊢ T)
              → normᵦ t
normalization t
  with fundamental-theorem t
...  | ⊨t
  with ⊨t (λ x → nn→hn (ne-var x) tt)
...  | hn
  with hn→normᵦ hn
...  | normᵦ-t
  rewrite subst-id-identity {t = t}    = normᵦ-t
