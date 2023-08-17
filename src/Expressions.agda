module Expressions where

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

open import Ext
open import SetOmega
open import Types
open import TypeSubstitution

-- type environments

data TEnv : LEnv → Set where
  ∅    : TEnv []
  _◁_  : Type Δ l → TEnv Δ → TEnv Δ
  _◁*_ : (l : Level) → TEnv Δ → TEnv (l ∷ Δ)

variable Γ Γ₁ Γ₂ : TEnv Δ

data inn : Type Δ l → TEnv Δ → Set where
  here  : ∀ {T Γ} → inn {Δ}{l} T (T ◁ Γ)
  there : ∀ {T : Type Δ l}{T′ : Type Δ l′}{Γ} → inn {Δ}{l} T Γ → inn {Δ} T (T′ ◁ Γ)
  tskip : ∀ {T l Γ} → inn {Δ}{l′} T Γ → inn (Twk T) (l ◁* Γ)

data Expr (Δ : LEnv) (Γ : TEnv Δ) : Type Δ l → Set where
  #_   : (n : ℕ) → Expr Δ Γ `ℕ
  `_   : ∀ {T : Type Δ l} → inn T Γ → Expr Δ Γ T
  ƛ_   : ∀ {T : Type Δ l}{T′ : Type Δ l′} → Expr Δ (T ◁ Γ) T′ → Expr Δ Γ (T ⇒ T′)
  _·_  : ∀ {T : Type Δ l}{T′ : Type Δ l′} → Expr Δ Γ (T ⇒ T′) → Expr Δ Γ T → Expr Δ Γ T′
  Λ_⇒_ : ∀ (l : Level) → {T : Type (l ∷ Δ) l′} → Expr (l ∷ Δ) (l ◁* Γ) T → Expr Δ Γ (`∀α l , T)
  _∙_  : ∀ {T : Type (l ∷ Δ) l′} → Expr Δ Γ (`∀α l , T) → (T′ : Type Δ l) → Expr Δ Γ (T [ T′ ]T)

variable e e₁ e₂ e₃ : Expr Δ Γ T
variable n : ℕ

-- value environments

Env : (Δ : LEnv) → TEnv Δ → Env* Δ → Setω
Env Δ Γ η = ∀ l (T : Type Δ l) → (x : inn T Γ) → ⟦ T ⟧ η

variable 
  γ γ₁ γ₂ : Env Δ Γ η

extend : ∀ {T : Type Δ l}{Γ : TEnv Δ}{η : Env* Δ}
  → Env Δ Γ η → ⟦ T ⟧ η → Env Δ (T ◁ Γ) η
extend γ v _ _ here = v
extend γ v _ _ (there x) = γ _ _ x

extend-tskip : ∀ {Δ : LEnv}{Γ : TEnv Δ}{η : Env* Δ}{⟦α⟧ : Set l}
  → Env Δ Γ η → Env (l ∷ Δ) (l ◁* Γ) (⟦α⟧ ∷ η)
extend-tskip {η = η} {⟦α⟧ = ⟦α⟧} γ _ _ (tskip{T = T} x)
  {- rewrite Tren*-preserves-semantics {ρ = Twkᵣ Tidᵣ} {η} {⟦α⟧ ∷ η} (wkᵣ∈Ren* η ⟦α⟧) T -}
  = subst id (sym (Tren*-preserves-semantics {ρ* = Twkᵣ Tidᵣ} {η} {⟦α⟧ ∷ η} (wkᵣ∈Ren* η ⟦α⟧) T)) (γ _ _ x) -- γ _ _ x 
  
subst-to-env* : TSub Δ₁ Δ₂ → Env* Δ₂ → Env* Δ₁
subst-to-env* {[]} σ* η₂ = []
subst-to-env* {x ∷ Δ₁} σ* η₂ = ⟦ σ* _ here ⟧ η₂ ∷ subst-to-env* (Tdropₛ σ*) η₂

subst-var-preserves : (x  : l ∈ Δ₁) (σ*  : TSub Δ₁ Δ₂) (η₂ : Env* Δ₂) → ⟦ σ* _ x ⟧ η₂ ≡ apply-env (subst-to-env* σ* η₂) x
subst-var-preserves here σ* η₂ = refl
subst-var-preserves (there x) σ* η₂ = subst-var-preserves x (Tdropₛ σ*) η₂

subst-to-env*-wk : (σ*  : TSub Δ₁ Δ₂) → (α  : Set l) → (η₂ : Env* Δ₂) → 
  subst-to-env* (Twkₛ σ*) (α ∷ η₂) ≡ω subst-to-env* σ* η₂
subst-to-env*-wk {Δ₁ = []} σ* α η₂ = refl
subst-to-env*-wk {Δ₁ = l ∷ Δ₁} σ* α η₂
  rewrite Tren*-preserves-semantics {ρ* = Twkᵣ Tidᵣ}{η₂}{α ∷ η₂} (wkᵣ∈Ren* η₂ α) (σ* _ here)
  = congωω (⟦ (σ* _ here) ⟧ η₂ ∷_) (subst-to-env*-wk (Tdropₛ σ*) α η₂)

subst-to-env*-build : ∀ (ρ* : TRen Δ₁ Δ₂) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂) → TRen* ρ* η₁ η₂
  → subst-to-env* (λ _ x → ` ρ* _ x) η₂ ≡ω η₁
subst-to-env*-build ρ* [] η₂ Tren* = refl
subst-to-env*-build {Δ₁ = _ ∷ Δ₁} ρ* (α ∷ η₁) η₂ Tren* = 
  transω (congωω (λ H → apply-env η₂ (ρ* _ here) ∷ H) (subst-to-env*-build (λ _ x → ρ* _ (there x)) η₁ η₂ (Tren*-pop ρ* α η₁ η₂ Tren*)))
         (conglω (_∷ η₁) (Tren* here))

subst-to-env*-id : (η : Env* Δ) → subst-to-env* Tidₛ η ≡ω η
subst-to-env*-id {Δ = Δ} η = subst-to-env*-build {Δ₁ = Δ} (λ _ x → x) η η (Tren*-id η)

subst-preserves-type : Setω
subst-preserves-type =
  ∀ {Δ₁ Δ₂}{l}{η₂ : Env* Δ₂}
  → (σ* : TSub Δ₁ Δ₂) (T : Type Δ₁ l)
  → ⟦ Tsub σ* T ⟧ η₂ ≡ ⟦ T ⟧ (subst-to-env* σ* η₂)

subst-preserves : subst-preserves-type
subst-preserves {η₂ = η₂} σ* (` x) = subst-var-preserves x σ* η₂
subst-preserves {η₂ = η₂} σ* (T₁ ⇒ T₂)
  rewrite subst-preserves{η₂ = η₂} σ* T₁
  |  subst-preserves{η₂ = η₂} σ* T₂ = refl
subst-preserves {η₂ = η₂} σ* (`∀α l , T) =
  dep-ext (λ ⟦α⟧ →
    trans (subst-preserves {η₂ = ⟦α⟧ ∷ η₂} (Tliftₛ σ* _) T)
          (congωl (λ H → ⟦ T ⟧ (⟦α⟧ ∷ H)) (subst-to-env*-wk σ* ⟦α⟧ η₂)))
subst-preserves σ* `ℕ = refl
 
Tsingle-subst-preserves : ∀ (η : Env* Δ) (T′ : Type Δ l) (T : Type (l ∷ Δ) l′) → 
  ⟦ T [ T′ ]T ⟧ η ≡ ⟦ T ⟧ (⟦ T′ ⟧ η ∷ η)
Tsingle-subst-preserves {Δ = Δ} {l = l}{l′ = l′} η T′ T =
  trans (subst-preserves (Textₛ Tidₛ T′) T)
        (congωl (λ H → ⟦ T ⟧ (⟦ T′ ⟧ η ∷ H)) (subst-to-env*-id η))

E⟦_⟧ : ∀ {T : Type Δ l}{Γ : TEnv Δ} → Expr Δ Γ T → (η : Env* Δ) → Env Δ Γ η → ⟦ T ⟧ η
E⟦ # n ⟧ η γ = n
E⟦ ` x ⟧ η γ = γ _ _ x
E⟦ ƛ_ e ⟧ η γ = λ v → E⟦ e ⟧ η (extend γ v)
E⟦ e₁ · e₂ ⟧ η γ = E⟦ e₁ ⟧ η γ (E⟦ e₂ ⟧ η γ)
E⟦ Λ l ⇒ e ⟧ η γ = λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ η) (extend-tskip γ)
E⟦ _∙_ {T = T} e T′ ⟧ η γ  = 
  subst id (sym (Tsingle-subst-preserves η T′ T)) (E⟦ e ⟧ η γ (⟦ T′ ⟧ η))
  