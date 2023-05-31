module Tagless-op_sem where

open import Level
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; length; lookup; tabulate)
open import Data.Unit
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

variable l l′ l₁ l₂ : Level

----------------------------------------------------------------------

postulate
  dependent-extensionality :
    ∀ {a b}{A : Set a}{F G : (α : A) → Set b}
    → (∀ (α : A) → F α ≡ G α)
    → ((α : A) → F α) ≡ ((α : A) → G α)

-- equality for Setω

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

-- level environments

LEnv = List Level
variable Δ Δ₁ Δ₂ : LEnv

-- type variables

data _∈_ : Level → LEnv → Set where
  here  : l ∈ (l ∷ Δ)
  there : l ∈ Δ → l ∈ (l′ ∷ Δ)

-- types

data Type Δ : Level → Set where
  `_     : l ∈ Δ → Type Δ l
  _⇒_    : Type Δ l → Type Δ l′ → Type Δ (l ⊔ l′)
  `∀α_,_ : ∀ l → Type (l ∷ Δ) l′ → Type Δ (suc l ⊔ l′)
  𝟙      : Type Δ zero

variable T T₁ T₂ : Type Δ l


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

⟦_⟧ : (T : Type Δ l) → Env* Δ → Set l
⟦ ` x ⟧ η = apply-env η x
⟦ T₁ ⇒ T₂ ⟧ η = ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η
⟦ `∀α l , T ⟧ η = (α : Set l) → ⟦ T ⟧ (α ∷ η)
⟦ 𝟙 ⟧ η = ⊤

-- renaming on types

TRen : LEnv → LEnv → Set
TRen Δ₁ Δ₂ = ∀ {l} → l ∈ Δ₁ → l ∈ Δ₂

Twkᵣ : TRen Δ (l ∷ Δ)
Twkᵣ = there

Textᵣ : TRen Δ₁ Δ₂ → TRen (l ∷ Δ₁) (l ∷ Δ₂)
Textᵣ ρ here = here
Textᵣ ρ (there x) = there (ρ x)

Tren : TRen Δ₁ Δ₂ → (Type Δ₁ l → Type Δ₂ l)
Tren ρ (` x) = ` ρ x
Tren ρ (T₁ ⇒ T₂) = Tren ρ T₁ ⇒ Tren ρ T₂
Tren ρ (`∀α lev , T) = `∀α lev , Tren (Textᵣ ρ) T
Tren ρ 𝟙 = 𝟙 

Twk : Type Δ l′ → Type (l ∷ Δ) l′
Twk = Tren Twkᵣ

-- the action of renaming on semantic environments

TRen* : (ρ : TRen Δ₁ Δ₂) → (η₁ : Env* Δ₁) → (η₂ : Env* Δ₂) → Setω
TRen* {Δ₁} ρ η₁ η₂ = ∀ {l : Level} → (x : l ∈ Δ₁) → apply-env η₂ (ρ x) ≡ apply-env η₁ x

wkᵣ∈Ren* : ∀ (η : Env* Δ) (⟦α⟧ : Set l) → TRen* (Twkᵣ{Δ}{l}) η (⟦α⟧ ∷ η)
wkᵣ∈Ren* η ⟦α⟧ x = refl

Tren*-id : (η : Env* Δ) → TRen* (λ x → x) η η
Tren*-id η x = refl

Tren*-pop : (ρ : TRen (l ∷ Δ₁) Δ₂) (α : Set l) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂) → TRen* ρ (α ∷ η₁) η₂ → TRen* (ρ ∘ there) η₁ η₂
Tren*-pop ρ α η₁ η₂ Tren* x = Tren* (there x)

Tren*-ext : ∀ {ρ : TRen Δ₁ Δ₂}{η₁ : Env* Δ₁}{η₂ : Env* Δ₂} (α : Set l)
  → TRen* ρ η₁ η₂ → TRen* (Textᵣ ρ) (α ∷ η₁) (α ∷ η₂)
Tren*-ext α Tren* here = refl
Tren*-ext α Tren* (there x) = Tren* x

Tren*-preserves-semantics : ∀ {ρ : TRen Δ₁ Δ₂}{η₁ : Env* Δ₁}{η₂ : Env* Δ₂}
  → (Tren* : TRen* ρ η₁ η₂) → (T : Type Δ₁ l) →  ⟦ Tren ρ T ⟧ η₂ ≡ ⟦ T ⟧ η₁
Tren*-preserves-semantics {ρ = ρ}{η₁}{η₂} Tren* (` x) = Tren* x
Tren*-preserves-semantics {ρ = ρ}{η₁}{η₂} Tren* (T₁ ⇒ T₂)
  rewrite Tren*-preserves-semantics {ρ = ρ}{η₁}{η₂} Tren* T₁
  | Tren*-preserves-semantics {ρ = ρ}{η₁}{η₂} Tren* T₂
  = refl
Tren*-preserves-semantics {ρ = ρ}{η₁}{η₂} Tren* (`∀α l , T) =
  dependent-extensionality (λ α →
    Tren*-preserves-semantics{ρ = Textᵣ ρ}{α ∷ η₁}{α ∷ η₂} (Tren*-ext{ρ = ρ} α Tren*) T)
Tren*-preserves-semantics Tren* 𝟙 = refl

-- substitution on types

data TSub : LEnv → LEnv → Set where
  []  : TSub [] Δ₂
  _∷_ : Type Δ₂ l → TSub Δ₁ Δ₂ → TSub (l ∷ Δ₁) Δ₂

apply-TSub : l ∈ Δ₁ → TSub Δ₁ Δ₂ → Type Δ₂ l
apply-TSub here (T ∷ _) = T
apply-TSub (there x) (_ ∷ σ) = apply-TSub x σ

build-Tidₛ : (Δ₁ : LEnv) → TRen Δ₁ Δ → TSub Δ₁ Δ
build-Tidₛ [] ρ = []
build-Tidₛ (l ∷ Δ₁) ρ = (` ρ here) ∷ build-Tidₛ Δ₁ (ρ ∘ there)

Tidₛ : TSub Δ Δ
Tidₛ {Δ} = build-Tidₛ Δ (λ x → x)

Twkₛ : TSub Δ₁ Δ₂ → TSub Δ₁ (l ∷ Δ₂)
Twkₛ [] = []
Twkₛ (T ∷ σ) = Twk T ∷ Twkₛ σ

Textₛ : TSub Δ₁ Δ₂ → ∀ {l} → TSub (l ∷ Δ₁) (l ∷ Δ₂)
Textₛ σ = ` here ∷ Twkₛ σ

Tsub : TSub Δ₁ Δ₂ → Type Δ₁ l → Type Δ₂ l
Tsub σ (` x) = apply-TSub x σ
Tsub σ (T₁ ⇒ T₂) = Tsub σ T₁ ⇒ Tsub σ T₂
Tsub σ (`∀α l , T) = `∀α l , Tsub (Textₛ σ) T
Tsub σ 𝟙 = 𝟙

Tsingleₛ : TSub Δ₁ Δ₂ → ∀ {l} → Type Δ₂ l → TSub (l ∷ Δ₁) Δ₂
Tsingleₛ σ T' = T' ∷ σ

_[_]T : Type (l ∷ Δ) l′ → Type Δ l → Type Δ l′
_[_]T T T' = Tsub (Tsingleₛ Tidₛ T') T

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
  `_   : ∀ {T : Type Δ l} → inn T Γ → Expr Δ Γ T
  ƛ_   : ∀ {T : Type Δ l}{T′ : Type Δ l′} → Expr Δ (T ◁ Γ) T′ → Expr Δ Γ (T ⇒ T′)
  _·_  : ∀ {T : Type Δ l}{T′ : Type Δ l′} → Expr Δ Γ (T ⇒ T′) → Expr Δ Γ T → Expr Δ Γ T′
  Λ_⇒_ : ∀ (l : Level) → {T : Type (l ∷ Δ) l′} → Expr (l ∷ Δ) (l ◁* Γ) T → Expr Δ Γ (`∀α l , T)
  _∙_  : ∀ {T : Type (l ∷ Δ) l′} → Expr Δ Γ (`∀α l , T) → (T′ : Type Δ l) → Expr Δ Γ (T [ T′ ]T)

variable e e₁ e₂ e₃ : Expr Δ Γ T

-- value environments

Env : (Δ : LEnv) → TEnv Δ → Env* Δ → Setω
Env Δ Γ η = ∀ {l}{T : Type Δ l} → (x : inn T Γ) → ⟦ T ⟧ η

extend : ∀ {T : Type Δ l}{Γ : TEnv Δ}{η : Env* Δ}
  → Env Δ Γ η → ⟦ T ⟧ η → Env Δ (T ◁ Γ) η
extend γ v here = v
extend γ v (there x) = γ x

extend-tskip : ∀ {Δ : LEnv}{Γ : TEnv Δ}{η : Env* Δ}{⟦α⟧ : Set l}
  → Env Δ Γ η → Env (l ∷ Δ) (l ◁* Γ) (⟦α⟧ ∷ η)
extend-tskip {η = η} {⟦α⟧ = ⟦α⟧} γ (tskip{T = T} x)
  rewrite Tren*-preserves-semantics {ρ = Twkᵣ}{η}{⟦α⟧ ∷ η} (wkᵣ∈Ren* η ⟦α⟧) T
  = γ x

subst-to-env* : (σ : TSub Δ₁ Δ₂) → (η₂ : Env* Δ₂) → Env* Δ₁
subst-to-env* [] η₂ = []
subst-to-env* (T ∷ σ) η₂ = ⟦ T ⟧ η₂ ∷ subst-to-env* σ η₂

subst-var-preserves : (x  : l ∈ Δ₁) (σ  : TSub Δ₁ Δ₂) (η₂ : Env* Δ₂) → ⟦ apply-TSub x σ ⟧ η₂ ≡ apply-env (subst-to-env* σ η₂) x
subst-var-preserves here (T ∷ σ) η₂ = refl
subst-var-preserves (there x) (_ ∷ σ) η₂ = subst-var-preserves x σ η₂

subst-to-env*-wk : (σ  : TSub Δ₁ Δ₂) → (α  : Set l) → (η₂ : Env* Δ₂) → subst-to-env* (Twkₛ σ) (α ∷ η₂) ≡ω subst-to-env* σ η₂
subst-to-env*-wk [] α η₂ = refl
subst-to-env*-wk (T ∷ σ) α η₂
  rewrite Tren*-preserves-semantics {ρ = Twkᵣ}{η₂}{α ∷ η₂} (wkᵣ∈Ren* η₂ α) T
  = congωω (⟦ T ⟧ η₂ ∷_) (subst-to-env*-wk σ α η₂)

subst-to-env*-build : ∀ (ρ : TRen Δ₁ Δ₂) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂) → TRen* ρ η₁ η₂
  → subst-to-env* (build-Tidₛ Δ₁ ρ) η₂ ≡ω η₁
subst-to-env*-build ρ [] η₂ Tren* = refl
subst-to-env*-build {Δ₁ = _ ∷ Δ₁} ρ (α ∷ η₁) η₂ Tren* = 
  transω (congωω (λ H → apply-env η₂ (ρ here) ∷ H) (subst-to-env*-build (ρ ∘ there) η₁ η₂ (Tren*-pop ρ α η₁ η₂ Tren*)))
         (conglω (_∷ η₁) (Tren* here))

subst-to-env*-id : (η : Env* Δ) → subst-to-env* Tidₛ η ≡ω η
subst-to-env*-id {Δ} η = subst-to-env*-build {Δ₁ = Δ} (λ x → x) η η (Tren*-id η)

subst-preserves-type : Setω
subst-preserves-type =
  ∀ {Δ₁ Δ₂}{l}{η₂ : Env* Δ₂}
  → (σ : TSub Δ₁ Δ₂) (T : Type Δ₁ l)
  → ⟦ Tsub σ T ⟧ η₂ ≡ ⟦ T ⟧ (subst-to-env* σ η₂)

subst-preserves : subst-preserves-type
subst-preserves {η₂ = η₂} σ (` x) = subst-var-preserves x σ η₂
subst-preserves{η₂ = η₂} σ (T₁ ⇒ T₂)
  rewrite subst-preserves{η₂ = η₂} σ T₁
  |  subst-preserves{η₂ = η₂} σ T₂ = refl
subst-preserves {η₂ = η₂} σ (`∀α l , T) =
  dependent-extensionality (λ α →
    trans (subst-preserves {η₂ = α ∷ η₂} (Textₛ σ) T)
          (congωl (λ H → ⟦ T ⟧ (α ∷ H)) (subst-to-env*-wk σ α η₂)))
subst-preserves σ 𝟙 = refl

single-subst-preserves : ∀ (η : Env* Δ) (T′ : Type Δ l) (T : Type (l ∷ Δ) l′) → ⟦ T [ T′ ]T ⟧ η ≡ ⟦ T ⟧ (⟦ T′ ⟧ η ∷ η)
single-subst-preserves {Δ = Δ} {l = l}{l′ = l′} η T′ T =
  trans (subst-preserves (Tsingleₛ Tidₛ T′) T)
        (congωl (λ H → ⟦ T ⟧ (⟦ T′ ⟧ η ∷ H)) (subst-to-env*-id η))

E⟦_⟧ : ∀ {T : Type Δ l}{Γ : TEnv Δ} → Expr Δ Γ T → (η : Env* Δ) → Env Δ Γ η → ⟦ T ⟧ η
E⟦ ` x ⟧ η γ = γ x
E⟦ ƛ_ e ⟧ η γ = λ v → E⟦ e ⟧ η (extend γ v)
E⟦ e₁ · e₂ ⟧ η γ = E⟦ e₁ ⟧ η γ (E⟦ e₂ ⟧ η γ)
E⟦ Λ l ⇒ e ⟧ η γ = λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ η) (extend-tskip γ)
E⟦ _∙_ {T = T} e T′ ⟧ η γ
  with E⟦ e ⟧ η γ (⟦ T′ ⟧ η)
... | v rewrite single-subst-preserves η T′ T = v 

-- expr in expr substitution

ERen : TEnv Δ → TEnv Δ → Set
ERen {Δ} Γ₁ Γ₂ = ∀ {l} {T : Type Δ l} → inn T Γ₁ → inn T Γ₂

Ewkᵣ : ERen Γ (T ◁ Γ)
Ewkᵣ = there

Eextᵣ : ERen Γ₁ Γ₂ → ERen (T ◁ Γ₁) (T ◁ Γ₂)
Eextᵣ ρ here = here
Eextᵣ ρ (there x) = there (ρ x)

Eextᵣ-l : ERen Γ₁ Γ₂ → ERen (l ◁* Γ₁) (l ◁* Γ₂)
Eextᵣ-l ρ (tskip x) = tskip (ρ x) 

Eren : ERen Γ₁ Γ₂ → (Expr Δ Γ₁ T → Expr Δ Γ₂ T)
Eren ρ (` x) = ` ρ x
Eren ρ (ƛ e) = ƛ Eren (Eextᵣ ρ) e
Eren ρ (e₁ · e₂) = Eren ρ e₁ · Eren ρ e₂
Eren ρ (Λ l ⇒ e) = Λ l ⇒ Eren (Eextᵣ-l ρ) e
Eren ρ (e ∙ T′) = Eren ρ e ∙ T′

Ewk : Expr Δ Γ T → Expr Δ (T₁ ◁ Γ) T 
Ewk = Eren Ewkᵣ

Ewk-l : Expr Δ Γ T → Expr (l ∷ Δ) (l ◁* Γ) (Twk T)  
Ewk-l = {!  !}

ESub : TEnv Δ → TEnv Δ → Set
ESub {Δ} Γ₁ Γ₂ = ∀ {l} {T : Type Δ l} → inn T Γ₁ → Expr Δ Γ₂ T

Eidₛ : ESub Γ Γ
Eidₛ = `_

Ewkₛ : ESub Γ₁ Γ₂ → ESub Γ₁ (T ◁ Γ₂)
Ewkₛ σ x = Ewk (σ x)

Eextₛ : ESub Γ₁ Γ₂ → ESub (T ◁ Γ₁) (T ◁ Γ₂)
Eextₛ σ here = ` here
Eextₛ σ (there x) = Ewk (σ x)

Eextₛ-l : ESub Γ₁ Γ₂ → ESub (l ◁* Γ₁) (l ◁* Γ₂)
Eextₛ-l σ (tskip x) = Ewk-l (σ x)

Esub : ESub Γ₁ Γ₂ → Expr Δ Γ₁ T → Expr Δ Γ₂ T
Esub σ (` x) = σ x
Esub σ (ƛ e) = ƛ Esub (Eextₛ σ) e
Esub σ (e₁ · e₂) = Esub σ e₁ · Esub σ e₂
Esub σ (Λ l ⇒ e) = Λ l ⇒ Esub (Eextₛ-l σ) e
Esub σ (e ∙ T) = Esub σ e ∙ T

Esingleₛ : ESub Γ₁ Γ₂ → Expr Δ Γ₂ T → ESub (T ◁ Γ₁) Γ₂
Esingleₛ σ e' here = e'
Esingleₛ σ e' (there x) = σ x

_[_]E : Expr Δ (T₁ ◁ Γ) T₂ → Expr Δ Γ T₁ → Expr Δ Γ T₂
_[_]E e e' = Esub (Esingleₛ Eidₛ e') e

-- type in expr substitution

Tsub-Γ : (σ : TSub Δ₁ Δ₂) → TEnv Δ₁ → TEnv Δ₂
Tsub-Γ {Δ₂ = []} [] ∅ = ∅
Tsub-Γ {Δ₂ = l ∷ Δ₂} [] ∅ = l ◁* Tsub-Γ [] ∅
Tsub-Γ σ (T ◁ Γ) = Tsub σ T ◁ Tsub-Γ σ Γ
Tsub-Γ (T ∷ σ) (l ◁* Γ) = Tsub-Γ σ Γ

ETsub : (σ : TSub Δ₁ Δ₂) → Expr Δ₁ Γ T → Expr Δ₂ (Tsub-Γ σ Γ) (Tsub σ T)
ETsub σ e = {!   !}

_[_]ET : Expr (l ∷ Δ) (l ◁* Γ) T  → (T′ : Type Δ l) → Expr Δ Γ (T [ T′ ]T)
_[_]ET e T′ = {!   !}

-- small step call by value semantics

data Val : Expr Δ Γ T → Set where
  v-ƛ : Val (ƛ e)
  v-Λ : Val (Λ l ⇒ e)

data _↪_ : Expr Δ Γ T → Expr Δ Γ T → Set where
  β-ƛ : 
     Val e₂ →
     ((ƛ e₁) · e₂) ↪ (e₁ [ e₂ ]E)
  β-Λ :
     ((Λ l ⇒ e) ∙ T) ↪ (e [ T ]ET)
  ξ-·₁ :
    e₁ ↪ e →
    (e₁ · e₂) ↪ (e · e₂)
  ξ-·₂ : 
    e₂ ↪ e → 
    Val e₁ →
    (e₁ · e₂) ↪ (e₁ · e)
  ξ-∙ :
    e₁ ↪ e₂ →
    (e₁ ∙ T) ↪ (e₂ ∙ T)

data _↪*_ : Expr Δ Γ T → Expr Δ Γ T → Set where
  refl :
    e ↪* e
  step :
    e₁ ↪* e₂ →
    e₂ ↪ e₃ →
    e₁ ↪* e₃

sem-eq : {!   !}
sem-eq = {!   !}

    