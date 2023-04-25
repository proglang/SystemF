{-# OPTIONS --rewriting #-}

module Taggy where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Level
-- open import Data.Fin
open import Data.Nat using (ℕ)
open import Data.String
open import Data.List
open import Data.Vec

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

-- syntax

Ident = String

variable l l′ : Level

lof : ℕ → Level
lof ℕ.zero = Level.zero
lof (ℕ.suc n) = Level.suc (lof n)

open import Data.Unit

-- level environments
LEnv = List Level
variable Δ Δ₁ Δ₂ : LEnv

data _∈_ : Level → LEnv → Set where
  here  : ∀ {l ls} → l ∈ (l ∷ ls)
  there : ∀ {l l′ ls} → l ∈ ls → l ∈ (l′ ∷ ls)

data Type (Δ : LEnv) : Level → Set where
  `_     : ∀ {l} → l ∈ Δ → Type Δ l
  _⇒_    : Type Δ l → Type Δ l′ → Type Δ (l ⊔ l′)
  `∀α_,_ : (l : Level) → Type (l ∷ Δ) l′ → Type Δ (suc l ⊔ l′)
  𝟙      : Type Δ zero

-- level of type according to Leivant'91
level : Type Δ l → Level
level {l = l} T = l


Env* : LEnv → Setω
Env* Δ = ∀ {l} → l ∈ Δ → Set l

-- extend must be a named function so that the definition of evaluation goes through
extend-η : ∀ {l} {Δ : LEnv} → Set l → Env* Δ → Env* (l ∷ Δ)
extend-η α η here = α
extend-η α η (there x) = η x

-- the meaning of a stratified type in terms of Agda universes
⟦_⟧ : (T : Type Δ l) → Env* Δ → Set l
⟦ ` x ⟧ η = η x
⟦ T₁ ⇒ T₂ ⟧ η = ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η
⟦ `∀α l , T ⟧ η = (α : Set l) → ⟦ T ⟧ (extend-η α η)
⟦ 𝟙 ⟧ η = ⊤

-- renaming on types
Ren : LEnv → LEnv → Set
Ren Δ₁ Δ₂ = ∀ n → n ∈ Δ₁ → n ∈ Δ₂

wkᵣ : Ren Δ (l ∷ Δ)
wkᵣ _ = there

extᵣ : Ren Δ₁ Δ₂ → ∀ l → Ren (l ∷ Δ₁) (l ∷ Δ₂)
extᵣ ρ _ _ here = here
extᵣ ρ _ _ (there x) = there (ρ _ x)

renT : Ren Δ₁ Δ₂ → (Type Δ₁ l → Type Δ₂ l)
renT ρ (`_ {n} x) = ` ρ n x
renT ρ (T₁ ⇒ T₂) = renT ρ T₁ ⇒ renT ρ T₂
renT ρ (`∀α lev , T) = `∀α lev , renT (extᵣ ρ lev) T
renT ρ 𝟙 = 𝟙 

wkT : Type Δ l′ → Type (l ∷ Δ) l′
wkT = renT wkᵣ 

-- substitution on types
Sub : LEnv → LEnv → Set
Sub Δ₁ Δ₂ = ∀ l → l ∈ Δ₁ → Type Δ₂ l

idₛ : Sub Δ Δ
idₛ _ = `_

wkₛ : Ren Δ (l ∷ Δ)
wkₛ _ = there

extₛ : Sub Δ₁ Δ₂ → ∀ l → Sub (l ∷ Δ₁) (l ∷ Δ₂)
extₛ σ _ _ here = ` here
extₛ σ _ _ (there x) = wkT (σ _ x)

subT : Sub Δ₁ Δ₂ → (Type Δ₁ l → Type Δ₂ l)
subT σ (`_ {n} x) = σ n x
subT σ (T₁ ⇒ T₂) = subT σ T₁ ⇒ subT σ T₂
subT σ (`∀α lev , T) = `∀α lev , subT (extₛ σ lev) T
subT σ 𝟙 = 𝟙 

singleₛ : Sub Δ₁ Δ₂ → ∀ l → Type Δ₂ l → Sub (l ∷ Δ₁) Δ₂
singleₛ σ _ T' _ here = T'
singleₛ σ _ T' _ (there x) = σ _ x

_[_]T : Type (l ∷ Δ) l′ → Type Δ l → Type Δ l′
_[_]T {l} T T' = subT (singleₛ idₛ l T') T

-- type environments
data TEnv : LEnv → Set where
  ∅    : TEnv []
  _◁_  : Type Δ l → TEnv Δ → TEnv Δ
  _◁*_ : (l : Level) → TEnv Δ → TEnv (l ∷ Δ)

data inn : ∀ {Δ}{l} → Type Δ l → TEnv Δ → Set where
  here  : ∀ {T Γ} → inn {Δ}{l} T (T ◁ Γ)
  there : ∀ {T : Type Δ l}{T′ : Type Δ l′}{Γ} → inn {Δ}{l} T Γ → inn {Δ} T (T′ ◁ Γ)
  tskip : ∀ {T l Γ} → inn {Δ}{l′} T Γ → inn (wkT T) (l ◁* Γ)

data Expr : (Δ : LEnv) → TEnv Δ → Type Δ l → Set where
  `_   : ∀ {T : Type Δ l}{Γ : TEnv Δ} → inn T Γ → Expr Δ Γ T
  ƛ_   : ∀ {T : Type Δ l}{T′ : Type Δ l′}{Γ : TEnv Δ} → Expr Δ (T ◁ Γ) T′ → Expr Δ Γ (T ⇒ T′)
  _·_  : ∀ {T : Type Δ l}{T′ : Type Δ l′}{Γ : TEnv Δ} → Expr Δ Γ (T ⇒ T′) → Expr Δ Γ T → Expr Δ Γ T′
  Λα_⇒_ : ∀ {Γ : TEnv Δ} → (l : Level) → {T : Type (l ∷ Δ) l′} → Expr (l ∷ Δ) (l ◁* Γ) T → Expr Δ Γ (`∀α l , T)
  _∙_  : ∀ {l}{T : Type (l ∷ Δ) l′}{Γ : TEnv Δ} → Expr Δ Γ (`∀α l , T) → (T′ : Type Δ l) → Expr Δ Γ (T [ T′ ]T)

Env : (Δ : LEnv) → TEnv Δ → Env* Δ → Setω
Env Δ Γ η = ∀ {l}{T : Type Δ l} → (x : inn T Γ) → ⟦ T ⟧ η

extend : ∀ {T : Type Δ l}{Γ : TEnv Δ}{η : Env* Δ} → Env Δ Γ η → ⟦ T ⟧ η → Env Δ (T ◁ Γ) η
extend γ v here = v
extend γ v (there x) = γ x

postulate
  -- Function extensionality
  funext :
    {A : Set l}
    {B : A → Set l′}
    {f g : (x : A) → B x}
    (_ : (x : A) → f x ≡ g x)
    → -----------------------
    f ≡ g


weak-extend-η : ∀ {Δ}{l l′} (T : Type Δ l) (⟦α⟧ : Set l′) (η : Env* Δ)
  → ⟦ wkT T ⟧ (extend-η ⟦α⟧ η) ≡ ⟦ T ⟧ η
weak-extend-η (` x) ⟦α⟧ η = refl
weak-extend-η (T₁ ⇒ T₂) ⟦α⟧ η
  rewrite weak-extend-η T₁ ⟦α⟧ η | weak-extend-η T₂ ⟦α⟧ η = refl
weak-extend-η (`∀α l , T) ⟦β⟧ η = {!!}
weak-extend-η 𝟙 ⟦α⟧ η = refl

extend-tskip : ∀ {Δ : LEnv}{Γ : TEnv Δ}{η : Env* Δ}{⟦α⟧ : Set l}
  → Env Δ Γ η → Env (l ∷ Δ) (l ◁* Γ) (extend-η ⟦α⟧ η)
extend-tskip {η = η} {⟦α⟧ = ⟦α⟧} γ (tskip{T = T} x)
  rewrite weak-extend-η T ⟦α⟧ η = γ x

E⟦_⟧ : ∀ {Δ}{l}{T : Type Δ l}{Γ : TEnv Δ} → Expr Δ Γ T → (η : Env* Δ) → Env Δ Γ η → ⟦ T ⟧ η
E⟦ ` x ⟧ η γ = γ x
E⟦ ƛ_ e ⟧ η γ = λ v → E⟦ e ⟧ η (extend γ v)
E⟦ e₁ · e₂ ⟧ η γ = E⟦ e₁ ⟧ η γ (E⟦ e₂ ⟧ η γ)
E⟦_⟧ {Δ}{_}{`∀α l , T} (Λα l ⇒ e) η γ = λ ⟦α⟧ → E⟦ e ⟧ (extend-η ⟦α⟧ η) (extend-tskip γ)
E⟦ (e ∙ T′) ⟧ η γ with ⟦ T′ ⟧ η
... | S = {! !}
