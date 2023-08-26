{-# OPTIONS --rewriting #-}
module AltTypes where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Level
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong; module ≡-Reasoning)

-- infix   2  _—↠_
-- infixr  2  _—→⟨_⟩_
-- infix   3  _∎∎
-- infix   4  _⊢_
infix   4  _⇛_
-- infix   4  _==>_
-- infix   4  _—→_
-- infixl  6  _▷_
infixr  7  _⇒_
-- infix   8  _⟪_⟫_
-- infix   8  □⟪_⟫_
-- infix   8  _⟪_⟫□
-- infixl  9  _·_
-- infix   9  □·_
-- infix   9  _·□
infix  10  _↑
infix  15 _⨟_
infixl 17 _⟨_⟩

----------------------------------------------------------------------
-- attempt with Phil's weakening approach
----------------------------------------------------------------------

-- level environments

LEnv : Set
LEnv = List Level

variable l l′ l₁ l₂ l₃ : Level
variable Δ Δ₁ Δ₂ Δ₃ Δ₄ : LEnv

-- types

data Type : LEnv → Level → Set where
  𝟘   : Type (l ∷ Δ) l

  _↑  : Type Δ l
     →  Type (l′ ∷ Δ) l

  _⇒_ : Type Δ l → Type Δ l′
      → Type Δ (l ⊔ l′)

  `∀  : ∀ l → Type (l ∷ Δ) l′
      → Type Δ (suc l ⊔ l′)

  `ℕ  : Type Δ zero

-- semantic environments

data Env* : LEnv → Setω where
  []  : Env* []
  _∷_ : Set l → Env* Δ → Env* (l ∷ Δ)

-- apply-env : Env* Δ → l ∈ Δ → Set l
-- apply-env [] ()
-- apply-env (x ∷ _) here = x
-- apply-env (_ ∷ η) (there x) = apply-env η x

-- the meaning of a stratified type in terms of Agda universes

⟦_⟧ : (T : Type Δ l) → Env* Δ → Set l
⟦ 𝟘 ⟧ (α ∷ η) = α
⟦ T ↑ ⟧ (_ ∷ η) = ⟦ T ⟧ η
⟦ T₁ ⇒ T₂ ⟧ η = ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η
⟦ `∀ l T ⟧ η = (α : Set l) → ⟦ T ⟧ (α ∷ η)
⟦ `ℕ ⟧ η = ℕ

-- type substitutions

data _⇛_ : LEnv → LEnv → Set where

  id : Δ ⇛ Δ

  _↑ : Δ₂ ⇛ Δ₁
       ------------
     → (l ∷ Δ₂) ⇛ Δ₁

  _∷_ : Type Δ₂ l → Δ₂ ⇛ Δ₁
        -------------------
      → Δ₂ ⇛ (l ∷ Δ₁)

-- applying a substitution

pattern △ = _ ∷ _

_⟨_⟩ : Type Δ₁ l
    → Δ₂ ⇛ Δ₁
      -------
    → Type Δ₂ l
T ⟨ id ⟩ = T
T ⟨ σ ↑ ⟩ = T ⟨ σ ⟩ ↑
𝟘 ⟨ T′ ∷ _ ⟩ = T′
(T ↑) ⟨ _ ∷ σ ⟩ = T ⟨ σ ⟩
(T₁ ⇒ T₂) ⟨ σ@△ ⟩ = T₁ ⟨ σ ⟩ ⇒ T₂ ⟨ σ ⟩
`∀ l T ⟨ σ@△ ⟩ = `∀ l (T ⟨ 𝟘 ∷ σ ↑ ⟩)
`ℕ ⟨ σ@△ ⟩ = `ℕ

-- composition of substitutions

_⨟_ : Δ₂ ⇛ Δ₁
    → Δ₃ ⇛ Δ₂
      -----
    → Δ₃ ⇛ Δ₁
σ ⨟ id = σ
σ ⨟ (τ ↑) = (σ ⨟ τ) ↑
id ⨟ τ@△ = τ
(σ ↑) ⨟ (_ ∷ τ) = σ ⨟ τ
(T ∷ σ) ⨟ τ@△ = T ⟨ τ ⟩ ∷ (σ ⨟ τ)

-- composition and application

lemma-⨟ : 
    (T : Type Δ₁ l)
  → (σ : Δ₂ ⇛ Δ₁)
  → (τ : Δ₃ ⇛ Δ₂)
    ---------------------------
  → T ⟨ σ ⟩ ⟨ τ ⟩ ≡ T ⟨ σ ⨟ τ ⟩
lemma-⨟ T σ id = refl
lemma-⨟ T σ (τ ↑) = cong _↑ (lemma-⨟ T σ τ)
lemma-⨟ T id τ@△ = refl
lemma-⨟ T (σ ↑) (_ ∷ τ) = lemma-⨟ T σ τ
lemma-⨟ 𝟘 (T′ ∷ σ) τ@△ = refl
lemma-⨟ (T ↑) (T′ ∷ σ) τ@△ = lemma-⨟ T σ τ
lemma-⨟ (T₁ ⇒ T₂) σ@△ τ@△ = cong₂ _⇒_ (lemma-⨟ T₁ σ τ) (lemma-⨟ T₂ σ τ)
lemma-⨟ (`∀ l T) σ@△ τ@△ = cong (`∀ l) (lemma-⨟ T (𝟘 ∷ σ ↑) (𝟘 ∷ τ ↑))
lemma-⨟ `ℕ σ@△ τ@△ = refl

{-# REWRITE lemma-⨟ #-}

-- substitute for the last variable in the environment

_[_]T : Type (l ∷ Δ) l′
      → Type Δ l
        ---------
      → Type Δ l′
T [ U ]T = T ⟨ U ∷ id ⟩

-- composition has left and right identity

left-id : (τ : Δ₂ ⇛ Δ₁) → id ⨟ τ ≡ τ
left-id id = refl
left-id (τ ↑) = cong _↑ (left-id τ)
left-id (T ∷ τ) = refl

right-id : (τ : Δ₂ ⇛ Δ₁) → τ ⨟ id ≡ τ
right-id τ = refl

-- composition is associative

assoc :
    (σ : Δ₂ ⇛ Δ₁)
  → (τ : Δ₃ ⇛ Δ₂)
  → (υ : Δ₄ ⇛ Δ₃)
    -----------------------
  → (σ ⨟ τ) ⨟ υ ≡ σ ⨟ (τ ⨟ υ)
assoc σ τ id = refl
assoc σ τ (υ ↑) = cong _↑ (assoc σ τ υ)
assoc σ id υ@△ = refl
assoc σ (τ ↑) (_ ∷ υ) = assoc σ τ υ
assoc id τ@△ υ@△ = refl
assoc (σ ↑) (_ ∷ τ) υ@△ = assoc σ τ υ
assoc (x ∷ σ) τ@△ υ@△ = cong₂ _∷_ refl (assoc σ τ υ)

-- last line of proof requires rewriting with lemma-⨟

{-# REWRITE left-id assoc #-}

-- compatibility lemmas

sub-comp-n : ∀ (σ : Δ₂ ⇛ Δ₁)
  → `ℕ ⟨ σ ⟩ ≡ `ℕ
sub-comp-n id = refl
sub-comp-n (σ ↑) = {!!} -- `ℕ ⟨ σ ⟩ ↑ ≡ `ℕ
sub-comp-n (x ∷ σ) = refl

sub-comp-⇒ : ∀ (σ : Δ₂ ⇛ Δ₁) (T₁ : Type Δ₁ l₁) (T₂ : Type Δ₁ l₂)
  → (T₁ ⇒ T₂) ⟨ σ ⟩ ≡ T₁ ⟨ σ ⟩ ⇒ T₂ ⟨ σ ⟩
sub-comp-⇒ id T₁ T₂ = refl
sub-comp-⇒ (σ ↑) T₁ T₂ = {!!} -- (T₁ ⇒ T₂) ⟨ σ ⟩ ↑ ≡ T₁ ⟨ σ ⟩ ↑ ⇒ T₂ ⟨ σ ⟩ ↑
sub-comp-⇒ (x ∷ σ) T₁ T₂ = refl

sub-comp-∀ : ∀ {l} (σ : Δ₂ ⇛ Δ₁) (T : Type (l ∷ Δ₁) l′)
  → (`∀ l T) ⟨ σ ⟩ ≡ `∀ l (T ⟨ 𝟘 ∷ σ ↑ ⟩)
sub-comp-∀ id _ = {!!} -- `∀ l T ≡ `∀ l (T ⟨ 𝟘 ∷ (id ↑) ⟩)
sub-comp-∀ (σ ↑) _ = {!!} -- `∀ l T ⟨ σ ⟩ ↑ ≡ `∀ l (T ⟨ 𝟘 ∷ ((σ ↑) ↑) ⟩)
sub-comp-∀ (x ∷ σ) _ = refl

{-# REWRITE sub-comp-n sub-comp-⇒ sub-comp-∀ #-}

----- expressions


-- type environments

data TEnv : LEnv → Set where
  ∅    : TEnv []
  _◁_  : Type Δ l → TEnv Δ → TEnv Δ
  _◁*_ : (l : Level) → TEnv Δ → TEnv (l ∷ Δ)

variable Γ Γ₁ Γ₂ : TEnv Δ

data inn : Type Δ l → TEnv Δ → Set where
  here  : ∀ {T Γ} → inn {Δ}{l} T (T ◁ Γ)
  there : ∀ {T : Type Δ l}{T′ : Type Δ l′}{Γ} → inn {Δ}{l} T Γ → inn {Δ} T (T′ ◁ Γ)
  tskip : ∀ {T l Γ} → inn {Δ}{l′} T Γ → inn (T ↑) (l ◁* Γ)

data Expr (Δ : LEnv) (Γ : TEnv Δ) : Type Δ l → Set where
  #_   : (n : ℕ)
       → Expr Δ Γ `ℕ
  `_   : ∀ {T : Type Δ l}
       → inn T Γ
       → Expr Δ Γ T
  ƛ_   : ∀ {T : Type Δ l}{T′ : Type Δ l′}
       → Expr Δ (T ◁ Γ) T′
       → Expr Δ Γ (T ⇒ T′)
  _·_  : ∀ {T : Type Δ l}{T′ : Type Δ l′}
       → Expr Δ Γ (T ⇒ T′) → Expr Δ Γ T
       → Expr Δ Γ T′
  Λ_⇒_ : ∀ (l : Level) → {T : Type (l ∷ Δ) l′}
       → Expr (l ∷ Δ) (l ◁* Γ) T
       → Expr Δ Γ (`∀ l T)
  _∙_  : ∀ {T : Type (l ∷ Δ) l′}
       → Expr Δ Γ (`∀ l T) → (T′ : Type Δ l)
       → Expr Δ Γ (T [ T′ ]T)

----- how to define expression renamings? are they even needed or can we define expression substitutions straight away?
-- let type substitutions pose as renamings

variable T : Type Δ l

Tren : Δ₂ ⇛ Δ₁ → Type Δ₁ l → Type Δ₂ l
Tren ρ* T = T ⟨ ρ* ⟩

TRen : LEnv → LEnv → Set
TRen Δ₁ Δ₂ = Δ₂ ⇛ Δ₁

Tid : Δ ⇛ Δ
Tid = id

Tliftᵣ : TRen Δ₁ Δ₂ → (l : Level) → TRen (l ∷ Δ₁) (l ∷ Δ₂)
Tliftᵣ ρ* _ = 𝟘 ∷ ρ* ↑

ERen : TRen Δ₁ Δ₂ → TEnv Δ₁ → TEnv Δ₂ → Set
ERen {Δ₁}{Δ₂} ρ* Γ₁ Γ₂ = ∀ {l} {T : Type Δ₁ l} → inn T Γ₁ → inn (Tren ρ* T) Γ₂

Eidᵣ : ERen Tid Γ Γ 
Eidᵣ = λ x → x

Edropᵣ : (ρ* : TRen Δ₁ Δ₂) → ERen ρ* (T ◁ Γ₁) Γ₂ → ERen ρ* Γ₁ Γ₂
Edropᵣ ρ* ρ x = ρ (there x)

Ewkᵣ : (ρ* : TRen Δ₁ Δ₂) → ERen ρ* Γ₁ Γ₂ → ERen ρ* Γ₁ (T ◁ Γ₂) 
Ewkᵣ ρ* ρ x = there (ρ x) 

Eliftᵣ : ∀ {ρ* : TRen Δ₁ Δ₂} → ERen ρ* Γ₁ Γ₂ → ERen ρ* (T ◁ Γ₁) (Tren ρ* T ◁ Γ₂)
Eliftᵣ ρ here = here
Eliftᵣ ρ (there x) = there (ρ x)

Eliftᵣ-l : {ρ* : TRen Δ₁ Δ₂} → ERen ρ* Γ₁ Γ₂ → ERen (Tliftᵣ ρ* l) (l ◁* Γ₁) (l ◁* Γ₂)
Eliftᵣ-l {Γ₂ = Γ₂} {l = l} {ρ* = ρ*} ρ (tskip x) = tskip (ρ x)

Eren : {ρ* : TRen Δ₁ Δ₂} → ERen ρ* Γ₁ Γ₂ → Expr Δ₁ Γ₁ T → Expr Δ₂ Γ₂ (Tren ρ* T)
Eren ρ (# n) = # n
Eren ρ (` x) = ` ρ x
Eren {ρ* = ρ*} ρ (ƛ e) = ƛ (Eren {ρ* = ρ*} (Eliftᵣ {ρ* = ρ*} ρ) e)
Eren {ρ* = ρ*} ρ (e₁ · e₂) = Eren {ρ* = ρ*} ρ e₁ · Eren {ρ* = ρ*} ρ e₂
Eren {ρ* = ρ*} ρ (Λ l ⇒ e) = Λ l ⇒ Eren  {ρ* = Tliftᵣ ρ* l} (Eliftᵣ-l ρ) e
Eren {ρ* = ρ*} ρ (_∙_ {T = T} e  T′) =
  let r = Eren  {ρ* = ρ*} ρ e ∙ Tren ρ* T′  in
    subst (Expr _ _) (lemma ρ* T T′) r
  where
    lemma : ∀ (σ : Δ₂ ⇛ Δ₁) (T : Type (l₁ ∷ Δ₁) l) (T′  : Type Δ₁ l₁)
      → T ⟨ (T′ ⟨ σ ⟩) ∷ σ ⟩ ≡ T ⟨ (T′ ∷ id) ⨟ σ ⟩
    lemma id T T′ = refl
    lemma (σ ↑) T T′ = {!!}
    lemma (x ∷ σ) T T′ = refl

