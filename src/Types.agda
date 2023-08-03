module Types where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; length; lookup; tabulate)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong; module ≡-Reasoning)
open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open ≡-Reasoning

variable l l′ l₁ l₂ l₃ : Level

open import Ext

----------------------------------------------------------------------

-- level environments

LEnv = List Level
variable Δ Δ₁ Δ₂ Δ₃ : LEnv

-- type variables

data _∈_ : Level → LEnv → Set where
  here  : l ∈ (l ∷ Δ)
  there : l ∈ Δ → l ∈ (l′ ∷ Δ)

-- types

data Type Δ : Level → Set where
  `_     : l ∈ Δ → Type Δ l
  _⇒_    : Type Δ l → Type Δ l′ → Type Δ (l ⊔ l′)
  `∀α_,_ : ∀ l → Type (l ∷ Δ) l′ → Type Δ (suc l ⊔ l′)
  `ℕ     : Type Δ zero

variable T T′ T₁ T₂ : Type Δ l


-- level of type according to Leivant'91
level : Type Δ l → Level
level {l = l} T = l

-- semantic environments (mapping level l to an element of Set l)

{- 
-- Set l instead of Setω?
data Env*′ (l : Level) : LEnv′ l → Set l where
  []  : Env*′ l []
  _∷_[_] : ∀{Δ : LEnv′ l} → Set l′ → Env*′ l Δ → (eq : l ⊔ l′ ≡ l) → 
    Env*′ l (l′ ∷ Δ [ eq ]) 
-}

data Env* : LEnv → Setω where
  []  : Env* []
  _∷_ : Set l → Env* Δ → Env* (l ∷ Δ)

variable
  η η₁ η₂ : Env* Δ  

apply-env : Env* Δ → l ∈ Δ → Set l
apply-env [] ()
apply-env (x ∷ _) here = x
apply-env (_ ∷ η) (there x) = apply-env η x

-- the meaning of a stratified type in terms of Agda universes

⟦_⟧ : (T : Type Δ l) → Env* Δ → Set l
⟦ ` x ⟧ η = apply-env η x
⟦ T₁ ⇒ T₂ ⟧ η = ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η
⟦ `∀α l , T ⟧ η = (α : Set l) → ⟦ T ⟧ (α ∷ η)
⟦ `ℕ ⟧ η = ℕ

-- renaming on types

TRen : LEnv → LEnv → Set
TRen Δ₁ Δ₂ = ∀ l → l ∈ Δ₁ → l ∈ Δ₂

variable 
  ρ* ρ*₁ ρ*₂ : TRen Δ₁ Δ₂

Tidᵣ : TRen Δ Δ
Tidᵣ _ = id

Tdropᵣ : TRen (l ∷ Δ₁) Δ₂ → TRen Δ₁ Δ₂
Tdropᵣ ρ* _ x = ρ* _ (there x)

Twkᵣ : TRen Δ₁ Δ₂ → TRen Δ₁ (l ∷ Δ₂)
Twkᵣ ρ* _ x = there (ρ* _ x)

Tliftᵣ : TRen Δ₁ Δ₂ → (l : Level) → TRen (l ∷ Δ₁) (l ∷ Δ₂)
Tliftᵣ ρ* _ _ here = here
Tliftᵣ ρ* _ _ (there x) = there (ρ* _ x)

Tren : TRen Δ₁ Δ₂ → (Type Δ₁ l → Type Δ₂ l)
Tren ρ* (` x) = ` ρ* _ x
Tren ρ* (T₁ ⇒ T₂) = Tren ρ* T₁ ⇒ Tren ρ* T₂
Tren ρ* (`∀α l , T) = `∀α l , Tren (Tliftᵣ ρ* l) T
Tren ρ* `ℕ = `ℕ

Twk : Type Δ l′ → Type (l ∷ Δ) l′
Twk = Tren (Twkᵣ Tidᵣ)

-- the action of renaming on semantic environments

TRen* : (ρ* : TRen Δ₁ Δ₂) → (η₁ : Env* Δ₁) → (η₂ : Env* Δ₂) → Setω
TRen* {Δ₁} ρ* η₁ η₂ = ∀ {l : Level} → (x : l ∈ Δ₁) → apply-env η₂ (ρ* _ x) ≡ apply-env η₁ x

wkᵣ∈Ren* : ∀ (η : Env* Δ) (⟦α⟧ : Set l) → TRen* (Twkᵣ {Δ₁ = Δ}{l = l} Tidᵣ) η (⟦α⟧ ∷ η)
wkᵣ∈Ren* η ⟦α⟧ x = refl

Tren*-id : (η : Env* Δ) → TRen* (λ _ x → x) η η
Tren*-id η x = refl

Tren*-pop : (ρ* : TRen (l ∷ Δ₁) Δ₂) (α : Set l) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂) → 
  TRen* ρ* (α ∷ η₁) η₂ → TRen* (λ _ x → ρ* _ (there x)) η₁ η₂
Tren*-pop ρ* α η₁ η₂ Tren* x = Tren* (there x)

Tren*-lift : ∀ {ρ* : TRen Δ₁ Δ₂}{η₁ : Env* Δ₁}{η₂ : Env* Δ₂} (α : Set l)
  → TRen* ρ* η₁ η₂ → TRen* (Tliftᵣ ρ* _) (α ∷ η₁) (α ∷ η₂)
Tren*-lift α Tren* here = refl
Tren*-lift α Tren* (there x) = Tren* x

Tren*-preserves-semantics : ∀ {ρ* : TRen Δ₁ Δ₂}{η₁ : Env* Δ₁}{η₂ : Env* Δ₂}
  → (Tren* : TRen* ρ* η₁ η₂) → (T : Type Δ₁ l) →  ⟦ Tren ρ* T ⟧ η₂ ≡ ⟦ T ⟧ η₁
Tren*-preserves-semantics {ρ* = ρ*} {η₁} {η₂} Tren* (` x) = Tren* x
Tren*-preserves-semantics {ρ* = ρ*} {η₁} {η₂} Tren* (T₁ ⇒ T₂)
  rewrite Tren*-preserves-semantics {ρ* = ρ*} {η₁} {η₂} Tren* T₁
  | Tren*-preserves-semantics {ρ* = ρ*} {η₁} {η₂} Tren* T₂
  = refl
Tren*-preserves-semantics {ρ* = ρ*} {η₁} {η₂} Tren* (`∀α l , T) = dep-ext λ where 
  α → Tren*-preserves-semantics{ρ* = Tliftᵣ ρ* _}{α ∷ η₁}{α ∷ η₂} (Tren*-lift {ρ* = ρ*} α Tren*) T
Tren*-preserves-semantics Tren* `ℕ = refl

-- substitution on types

TSub : LEnv → LEnv → Set
TSub Δ₁ Δ₂ = ∀ l → l ∈ Δ₁ → Type Δ₂ l

variable 
  σ* σ*₁ σ*₂ : TSub Δ₁ Δ₂
 
Tidₛ : TSub Δ Δ
Tidₛ _ = `_

Tdropₛ : TSub (l ∷ Δ₁) Δ₂ → TSub Δ₁ Δ₂
Tdropₛ σ* _ x = σ* _ (there x)

Twkₛ : TSub Δ₁ Δ₂ → TSub Δ₁ (l ∷ Δ₂)
Twkₛ σ* _ x = Twk (σ* _ x)

Tliftₛ : TSub Δ₁ Δ₂ → (l : Level) → TSub (l ∷ Δ₁) (l ∷ Δ₂)
Tliftₛ σ* _ _ here = ` here
Tliftₛ σ* _ _ (there x) = Twk (σ* _ x)

Tsub : TSub Δ₁ Δ₂ → Type Δ₁ l → Type Δ₂ l
Tsub σ* (` x) = σ* _ x
Tsub σ* (T₁ ⇒ T₂) = Tsub σ* T₁ ⇒ Tsub σ* T₂
Tsub σ* (`∀α l , T) = `∀α l , Tsub (Tliftₛ σ* _) T
Tsub σ* `ℕ = `ℕ

Textₛ : TSub Δ₁ Δ₂ → Type Δ₂ l → TSub (l ∷ Δ₁) Δ₂
Textₛ σ* T' _ here = T'
Textₛ σ* T' _ (there x) = σ* _ x

_[_]T : Type (l ∷ Δ) l′ → Type Δ l → Type Δ l′
_[_]T T T' = Tsub (Textₛ Tidₛ T') T

