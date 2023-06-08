module Tagless-final where

open import Level
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; length; lookup; tabulate)
open import Data.Unit
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

----------------------------------------------------------------------

postulate
  dependent-extensionality :
    ∀ {a b}{A : Set a}{F G : (α : A) → Set b}
    → (∀ (α : A) → F α ≡ G α)
    → ((α : A) → F α) ≡ ((α : A) → G α)

-- equality involving Setω

data _≡ω_ {A : Setω} (x : A) : A → Setω where
  refl : x ≡ω x

congωl : ∀ {b} {A : Setω} {B : Set b} (f : A → B) {x y : A} → x ≡ω y → f x ≡ f y
congωl f refl = refl

conglω : ∀ {a} {A : Set a} {B : Setω} (f : A → B) {x y : A} → x ≡ y → f x ≡ω f y
conglω f refl = refl

congωω : ∀ {A : Setω} {B : Setω} (f : A → B) {x y : A} → x ≡ω y → f x ≡ω f y
congωω f refl = refl

transω : ∀ {A : Setω} {x y z : A} → x ≡ω y → y ≡ω z → x ≡ω z
transω refl refl = refl

----------------------------------------------------------------------

-- variables in a list

data _∈_ {A : Set} (a : A) : List A → Set where
  here  : ∀{Δ} → a ∈ (a ∷ Δ)
  there : ∀{a′ Δ} → a ∈ Δ → a ∈ (a′ ∷ Δ)

-- level environments

LEnv = List Level
variable Δ Δ₁ Δ₂ : LEnv
variable l l′ : Level

-- types

data Type Δ : Level → Set where
  𝟙     : Type Δ zero
  `_    : l ∈ Δ → Type Δ l
  _⇒_   : Type Δ l → Type Δ l′ → Type Δ (l ⊔ l′)
  ∀α_,_ : ∀ l → Type (l ∷ Δ) l′ → Type Δ (suc l ⊔ l′)

-- level of type according to Leivant'91
level : Type Δ l → Level
level {l = l} T = l

-- semantic environments (mapping level l to an element of Set l)

data Env* : LEnv → Setω where
  []  : Env* []
  _∷_ : Set l → Env* Δ → Env* (l ∷ Δ)

apply-env : Env* Δ → l ∈ Δ → Set l
apply-env [] ()
apply-env (x ∷ _) here = x
apply-env (_ ∷ η) (there x) = apply-env η x

-- the meaning of a stratified type in terms of Agda universes

𝓣⟦_⟧ : (T : Type Δ l) → Env* Δ → Set l
𝓣⟦ 𝟙 ⟧ η = ⊤
𝓣⟦ ` α ⟧ η = apply-env η α
𝓣⟦ T₁ ⇒ T₂ ⟧ η = 𝓣⟦ T₁ ⟧ η → 𝓣⟦ T₂ ⟧ η
𝓣⟦ ∀α l , T ⟧ η = (⟦α⟧ : Set l) → 𝓣⟦ T ⟧ (⟦α⟧ ∷ η)

-- renaming on types

Ren : LEnv → LEnv → Set
Ren Δ₁ Δ₂ = ∀ {l} → l ∈ Δ₁ → l ∈ Δ₂

wkᵣ : Ren Δ (l ∷ Δ)
wkᵣ = there

extᵣ : Ren Δ₁ Δ₂ → Ren (l ∷ Δ₁) (l ∷ Δ₂)
extᵣ ρ here = here
extᵣ ρ (there x) = there (ρ x)

renT : Ren Δ₁ Δ₂ → (Type Δ₁ l → Type Δ₂ l)
renT ρ (` x) = ` ρ x
renT ρ (T₁ ⇒ T₂) = renT ρ T₁ ⇒ renT ρ T₂
renT ρ (∀α lev , T) = ∀α lev , renT (extᵣ ρ) T
renT ρ 𝟙 = 𝟙 

wkT : Type Δ l′ → Type (l ∷ Δ) l′
wkT = renT wkᵣ

-- the action of renaming on semantic environments

Ren* : (ρ : Ren Δ₁ Δ₂) → (η₁ : Env* Δ₁) → (η₂ : Env* Δ₂) → Setω
Ren* {Δ₁} ρ η₁ η₂ = ∀ {l : Level} → (x : l ∈ Δ₁) → apply-env η₂ (ρ x) ≡ apply-env η₁ x

wkᵣ∈Ren* : ∀ (η : Env* Δ) (⟦α⟧ : Set l)
  → Ren* (wkᵣ{Δ}{l}) η (⟦α⟧ ∷ η)
wkᵣ∈Ren* η ⟦α⟧ x = refl

ren*-id : (η : Env* Δ) → Ren* id η η
ren*-id η x = refl

ren*-pop : (ρ : Ren (l ∷ Δ₁) Δ₂) (α : Set l) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂)
  → Ren* ρ (α ∷ η₁) η₂
  → Ren* (ρ ∘ there) η₁ η₂
ren*-pop ρ α η₁ η₂ ren* x = ren* (there x)

ren*-ext : ∀ {ρ : Ren Δ₁ Δ₂}{η₁ : Env* Δ₁}{η₂ : Env* Δ₂} (α : Set l)
  → Ren* ρ η₁ η₂
  → Ren* (extᵣ ρ) (α ∷ η₁) (α ∷ η₂)
ren*-ext α ren* here = refl
ren*-ext α ren* (there x) = ren* x

ren*-preserves-semantics : ∀ {ρ : Ren Δ₁ Δ₂}{η₁ : Env* Δ₁}{η₂ : Env* Δ₂}
  → (ren* : Ren* ρ η₁ η₂) → (T : Type Δ₁ l)
  → 𝓣⟦ renT ρ T ⟧ η₂ ≡ 𝓣⟦ T ⟧ η₁
ren*-preserves-semantics ren* (` x) = ren* x
ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* (T₁ ⇒ T₂)
  rewrite ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* T₁
  | ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* T₂
  = refl
ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* (∀α l , T) =
  dependent-extensionality (λ α →
    ren*-preserves-semantics{ρ = extᵣ ρ}{α ∷ η₁}{α ∷ η₂} (ren*-ext{ρ = ρ} α ren*) T)
ren*-preserves-semantics ren* 𝟙 = refl

-- substitution on types

data Sub : LEnv → LEnv → Set where
  []  : Sub [] Δ₂
  _∷_ : Type Δ₂ l → Sub Δ₁ Δ₂ → Sub (l ∷ Δ₁) Δ₂

apply-sub : Sub Δ₁ Δ₂ → l ∈ Δ₁ → Type Δ₂ l
apply-sub (T ∷ _) here = T
apply-sub (_ ∷ σ) (there x) = apply-sub σ x

build-id : (Δ₁ : LEnv) → Ren Δ₁ Δ → Sub Δ₁ Δ
build-id [] ρ = []
build-id (l ∷ Δ₁) ρ = (` ρ here) ∷ build-id Δ₁ (ρ ∘ there)

idₛ : Sub Δ Δ
idₛ {Δ} = build-id Δ id

wkₛ : Sub Δ₁ Δ₂ → Sub Δ₁ (l ∷ Δ₂)
wkₛ [] = []
wkₛ (T ∷ σ) = wkT T ∷ wkₛ σ

extₛ : Sub Δ₁ Δ₂ → ∀ {l} → Sub (l ∷ Δ₁) (l ∷ Δ₂)
extₛ σ = ` here ∷ wkₛ σ

subT : Sub Δ₁ Δ₂ → Type Δ₁ l → Type Δ₂ l
subT σ 𝟙 = 𝟙
subT σ (` α) = apply-sub σ α
subT σ (T₁ ⇒ T₂) = subT σ T₁ ⇒ subT σ T₂
subT σ (∀α l , T) = ∀α l , subT (extₛ σ) T

singleₛ : Sub Δ₁ Δ₂ → ∀ {l} → Type Δ₂ l → Sub (l ∷ Δ₁) Δ₂
singleₛ σ T' = T' ∷ σ

_[_]T : Type (l ∷ Δ) l′ → Type Δ l → Type Δ l′
_[_]T T T' = subT (singleₛ idₛ T') T

-- type environments

data TEnv : LEnv → Set where
  ∅    : TEnv []
  _◁_  : Type Δ l → TEnv Δ → TEnv Δ
  _◁*_ : (l : Level) → TEnv Δ → TEnv (l ∷ Δ)

data inn : Type Δ l → TEnv Δ → Set where
  here  : ∀ {T Γ} → inn {Δ}{l} T (T ◁ Γ)
  there : ∀ {T : Type Δ l}{T′ : Type Δ l′}{Γ} → inn {Δ}{l} T Γ → inn {Δ} T (T′ ◁ Γ)
  tskip : ∀ {T l Γ} → inn {Δ}{l′} T Γ → inn (wkT T) (l ◁* Γ)

data Expr (Δ : LEnv) (Γ : TEnv Δ) : Type Δ l → Set where
  `_   : ∀ {T : Type Δ l} → inn T Γ → Expr Δ Γ T
  ƛ_   : ∀ {T : Type Δ l}{T′ : Type Δ l′} → Expr Δ (T ◁ Γ) T′ → Expr Δ Γ (T ⇒ T′)
  _·_  : ∀ {T : Type Δ l}{T′ : Type Δ l′} → Expr Δ Γ (T ⇒ T′) → Expr Δ Γ T → Expr Δ Γ T′
  Λ_⇒_ : ∀ (l : Level) → {T : Type (l ∷ Δ) l′} → Expr (l ∷ Δ) (l ◁* Γ) T → Expr Δ Γ (∀α l , T)
  _∙_  : ∀ {T : Type (l ∷ Δ) l′} → Expr Δ Γ (∀α l , T) → (T′ : Type Δ l) → Expr Δ Γ (T [ T′ ]T)

-- value environments

Env : (Δ : LEnv) → TEnv Δ → Env* Δ → Setω
Env Δ Γ η = ∀ {l}{T : Type Δ l} → inn T Γ → 𝓣⟦ T ⟧ η

extend : ∀ {T : Type Δ l}{Γ : TEnv Δ}{η : Env* Δ}
  → Env Δ Γ η
  → 𝓣⟦ T ⟧ η
  → Env Δ (T ◁ Γ) η
extend γ v here = v
extend γ v (there x) = γ x

extend-tskip : ∀ {Δ : LEnv}{Γ : TEnv Δ}{η : Env* Δ}{⟦α⟧ : Set l}
  → Env Δ Γ η
  → Env (l ∷ Δ) (l ◁* Γ) (⟦α⟧ ∷ η)
extend-tskip {η = η} {⟦α⟧ = ⟦α⟧} γ (tskip{T = T} x)
  rewrite ren*-preserves-semantics {ρ = wkᵣ}{η}{⟦α⟧ ∷ η} (wkᵣ∈Ren* η ⟦α⟧) T
  = γ x

subst-to-env* : (σ : Sub Δ₁ Δ₂) → (η₂ : Env* Δ₂) → Env* Δ₁
subst-to-env* [] η₂ = []
subst-to-env* (T ∷ σ) η₂ = 𝓣⟦ T ⟧ η₂ ∷ subst-to-env* σ η₂

subst-var-preserves : (α : l ∈ Δ₁) (σ : Sub Δ₁ Δ₂) (η₂ : Env* Δ₂)
  → 𝓣⟦ apply-sub σ α ⟧ η₂ ≡ apply-env (subst-to-env* σ η₂) α
subst-var-preserves here (T ∷ σ) η₂ = refl
subst-var-preserves (there α) (_ ∷ σ) η₂ = subst-var-preserves α σ η₂

subst-to-env*-wk : (σ : Sub Δ₁ Δ₂) (⟦α⟧ : Set l) (η₂ : Env* Δ₂)
  → subst-to-env* (wkₛ σ) (⟦α⟧ ∷ η₂) ≡ω subst-to-env* σ η₂
subst-to-env*-wk [] ⟦α⟧ η₂ = refl
subst-to-env*-wk (T ∷ σ) ⟦α⟧ η₂
  rewrite ren*-preserves-semantics {ρ = wkᵣ}{η₂}{⟦α⟧ ∷ η₂} (wkᵣ∈Ren* η₂ ⟦α⟧) T
  = congωω (𝓣⟦ T ⟧ η₂ ∷_) (subst-to-env*-wk σ ⟦α⟧ η₂)

subst-to-env*-build : ∀ (ρ : Ren Δ₁ Δ₂) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂)
  → Ren* ρ η₁ η₂
  → subst-to-env* (build-id Δ₁ ρ) η₂ ≡ω η₁
subst-to-env*-build ρ [] η₂ ren* = refl
subst-to-env*-build {Δ₁ = _ ∷ Δ₁} ρ (⟦α⟧ ∷ η₁) η₂ ren* = 
  transω (congωω (apply-env η₂ (ρ here) ∷_) (subst-to-env*-build (ρ ∘ there) η₁ η₂ (ren*-pop ρ ⟦α⟧ η₁ η₂ ren*)))
         (conglω (_∷ η₁) (ren* here))

subst-to-env*-id : (η : Env* Δ) → subst-to-env* idₛ η ≡ω η
subst-to-env*-id {Δ} η = subst-to-env*-build {Δ₁ = Δ} id η η (ren*-id η)

subst-preserves : 
  ∀ {Δ₁ Δ₂}{l}{η₂ : Env* Δ₂}
  → (σ : Sub Δ₁ Δ₂) (T : Type Δ₁ l)
  → 𝓣⟦ subT σ T ⟧ η₂ ≡ 𝓣⟦ T ⟧ (subst-to-env* σ η₂)
subst-preserves σ 𝟙 = refl
subst-preserves {η₂ = η₂} σ (` α) = subst-var-preserves α σ η₂
subst-preserves{η₂ = η₂} σ (T₁ ⇒ T₂)
  rewrite subst-preserves{η₂ = η₂} σ T₁
  |  subst-preserves{η₂ = η₂} σ T₂ = refl
subst-preserves {η₂ = η₂} σ (∀α l , T) =
  dependent-extensionality (λ ⟦α⟧ →
    trans (subst-preserves {η₂ = ⟦α⟧ ∷ η₂} (extₛ σ) T)
          (congωl (λ H → 𝓣⟦ T ⟧ (⟦α⟧ ∷ H)) (subst-to-env*-wk σ ⟦α⟧ η₂)))

single-subst-preserves : ∀ (η : Env* Δ) (T′ : Type Δ l) (T : Type (l ∷ Δ) l′)
  → 𝓣⟦ T [ T′ ]T ⟧ η ≡ 𝓣⟦ T ⟧ (𝓣⟦ T′ ⟧ η ∷ η)
single-subst-preserves {Δ = Δ} {l = l}{l′ = l′} η T′ T =
  trans (subst-preserves (singleₛ idₛ T′) T)
        (congωl (λ H → 𝓣⟦ T ⟧ (𝓣⟦ T′ ⟧ η ∷ H)) (subst-to-env*-id η))

𝓔⟦_⟧ : ∀ {T : Type Δ l}{Γ : TEnv Δ} → Expr Δ Γ T → (η : Env* Δ) → Env Δ Γ η → 𝓣⟦ T ⟧ η
𝓔⟦ ` x ⟧ η γ = γ x
𝓔⟦ ƛ_ e ⟧ η γ = λ v → 𝓔⟦ e ⟧ η (extend γ v)
𝓔⟦ e₁ · e₂ ⟧ η γ = 𝓔⟦ e₁ ⟧ η γ (𝓔⟦ e₂ ⟧ η γ)
𝓔⟦ Λ l ⇒ e ⟧ η γ = λ ⟦α⟧ → 𝓔⟦ e ⟧ (⟦α⟧ ∷ η) (extend-tskip γ)
𝓔⟦ _∙_ {T = T} e T′ ⟧ η γ = subst id (sym (single-subst-preserves η T′ T)) (𝓔⟦ e ⟧ η γ (𝓣⟦ T′ ⟧ η))
