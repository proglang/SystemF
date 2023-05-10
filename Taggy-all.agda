module Taggy-all where

open import Level
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; length; lookup; tabulate)
open import Data.Unit
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; sym; cong; cong₂; trans; module ≡-Reasoning)
open ≡-Reasoning using (begin_; _≡⟨⟩_; step-≡˘; step-≡; _∎)


-- syntax

variable l l′ : Level

----------------------------------------------------------------------

postulate
  extensionality :
    ∀ {a b}{A : Set a}{F G : (x : A) → Set b}
    → (∀ (x : A) → F x ≡ G x)
    → F ≡ G

  dependent-extensionality :
    ∀ {a b}{A : Set a}{F G : (α : A) → Set b}
    → (∀ (α : A) → F α ≡ G α)
    → ((α : A) → F α) ≡ ((α : A) → G α)

-- equality for Setω

data _≡ω_ {A : Setω} (x : A) : A → Setω where
  refl : x ≡ω x

congω : ∀ {b} {A : Setω} {B : Set b} (f : A → B) {x y : A} → x ≡ω y → f x ≡ f y
congω f refl = refl

-- level environments
LEnv = List Level
variable Δ Δ₁ Δ₂ : LEnv

data _∈_ : Level → LEnv → Set where
  here  : l ∈ (l ∷ Δ)
  there : l ∈ Δ → l ∈ (l′ ∷ Δ)

data Type Δ : Level → Set where
  `_     : l ∈ Δ → Type Δ l
  _⇒_    : Type Δ l → Type Δ l′ → Type Δ (l ⊔ l′)
  `∀α_,_ : ∀ l → Type (l ∷ Δ) l′ → Type Δ (suc l ⊔ l′)
  𝟙      : Type Δ zero

-- level of type according to Leivant'91
level : Type Δ l → Level
level {l = l} T = l

-- semantic environments (mapping l to an element of Set l)
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
Ren : LEnv → LEnv → Set
Ren Δ₁ Δ₂ = ∀ l → l ∈ Δ₁ → l ∈ Δ₂

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


-- the action of renaming on semantic environments
Ren* : (ρ : Ren Δ₁ Δ₂) → (η₁ : Env* Δ₁) → (η₂ : Env* Δ₂) → Setω
Ren* {Δ₁}{Δ₂} ρ η₁ η₂ = ∀ (l : Level) → (x : l ∈ Δ₁) → apply-env η₂ (ρ l x) ≡ apply-env η₁ x

wkᵣ∈Ren* : ∀ (η : Env* Δ) (⟦α⟧ : Set l) → Ren* (wkᵣ{Δ}{l}) η (⟦α⟧ ∷ η)
wkᵣ∈Ren* η ⟦α⟧ _ x = refl

ren*-ext : ∀ {ρ : Ren Δ₁ Δ₂}{η₁ : Env* Δ₁}{η₂ : Env* Δ₂} (α : Set l)
  → Ren* ρ η₁ η₂ → Ren* (extᵣ ρ l) (α ∷ η₁) (α ∷ η₂)
ren*-ext α ren* l₁ here = refl
ren*-ext α ren* l₁ (there x) = ren* l₁ x

ren*-preserves-semantics : ∀ {ρ : Ren Δ₁ Δ₂}{η₁ : Env* Δ₁}{η₂ : Env* Δ₂}
  → (ren* : Ren* ρ η₁ η₂) → (T : Type Δ₁ l) →  ⟦ renT ρ T ⟧ η₂ ≡ ⟦ T ⟧ η₁
ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* (` x) = ren* _ x
ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* (T₁ ⇒ T₂)
  rewrite ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* T₁
  | ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* T₂
  = refl
ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* (`∀α l , T) =
  dependent-extensionality (λ α →
    ren*-preserves-semantics{ρ = extᵣ ρ l}{α ∷ η₁}{α ∷ η₂} (ren*-ext{ρ = ρ} _ ren*) T)
ren*-preserves-semantics ren* 𝟙 = refl

-- substitution on types
Sub : LEnv → LEnv → Set
Sub Δ₁ Δ₂ = ∀ l → l ∈ Δ₁ → Type Δ₂ l

idₛ : Sub Δ Δ
idₛ _ = `_

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

data inn : Type Δ l → TEnv Δ → Set where
  here  : ∀ {T Γ} → inn {Δ}{l} T (T ◁ Γ)
  there : ∀ {T : Type Δ l}{T′ : Type Δ l′}{Γ} → inn {Δ}{l} T Γ → inn {Δ} T (T′ ◁ Γ)
  tskip : ∀ {T l Γ} → inn {Δ}{l′} T Γ → inn (wkT T) (l ◁* Γ)

data Expr (Δ : LEnv) (Γ : TEnv Δ) : Type Δ l → Set where
  `_   : ∀ {T : Type Δ l} → inn T Γ → Expr Δ Γ T
  ƛ_   : ∀ {T : Type Δ l}{T′ : Type Δ l′} → Expr Δ (T ◁ Γ) T′ → Expr Δ Γ (T ⇒ T′)
  _·_  : ∀ {T : Type Δ l}{T′ : Type Δ l′} → Expr Δ Γ (T ⇒ T′) → Expr Δ Γ T → Expr Δ Γ T′
  Λ_⇒_ : ∀ (l : Level) → {T : Type (l ∷ Δ) l′} → Expr (l ∷ Δ) (l ◁* Γ) T → Expr Δ Γ (`∀α l , T)
  _∙_  : ∀ {T : Type (l ∷ Δ) l′} → Expr Δ Γ (`∀α l , T) → (T′ : Type Δ l) → Expr Δ Γ (T [ T′ ]T)

Env : (Δ : LEnv) → TEnv Δ → Env* Δ → Setω
Env Δ Γ η = ∀ {l}{T : Type Δ l} → (x : inn T Γ) → ⟦ T ⟧ η

extend : ∀ {T : Type Δ l}{Γ : TEnv Δ}{η : Env* Δ} → Env Δ Γ η → ⟦ T ⟧ η → Env Δ (T ◁ Γ) η
extend γ v here = v
extend γ v (there x) = γ x

extend-tskip : ∀ {Δ : LEnv}{Γ : TEnv Δ}{η : Env* Δ}{⟦α⟧ : Set l}
  → Env Δ Γ η → Env (l ∷ Δ) (l ◁* Γ) (⟦α⟧ ∷ η)
extend-tskip {η = η} {⟦α⟧ = ⟦α⟧} γ (tskip{T = T} x)
  rewrite ren*-preserves-semantics {ρ = wkᵣ}{η}{⟦α⟧ ∷ η} (wkᵣ∈Ren* η ⟦α⟧) T
  = γ x

subst-shrink : (σ : Sub (l ∷ Δ₁) Δ₂) → Sub Δ₁ Δ₂
subst-shrink σ l′ x = σ l′ (there x)

subst-shrink-ext : (σ : Sub Δ₁ Δ₂) → ∀ l′ x → subst-shrink (extₛ σ l) l′ x ≡ wkT (σ l′ x)
subst-shrink-ext σ _ here = refl
subst-shrink-ext σ _ (there x) = refl

subst-shrink-single : ∀ {l} {T′} → ∀ l′ x → subst-shrink{Δ₁ = Δ}{Δ₂ = Δ} (singleₛ idₛ l T′) l′ x ≡ idₛ l′ x
subst-shrink-single _ here = refl
subst-shrink-single _ (there x) = refl

subst-shrink-single-ext : ∀ {Δ} {l} {T′} → subst-shrink{Δ₁ = Δ}{Δ₂ = Δ} (singleₛ idₛ l T′) ≡ idₛ
subst-shrink-single-ext = refl

subst-to-env* : (σ : Sub Δ₁ Δ₂) → (η₂ : Env* Δ₂) → Env* Δ₁
subst-to-env* {Δ₁ = []} σ η₂ = []
subst-to-env* {Δ₁ = l ∷ Δ₁} σ η₂ = (⟦ σ l here ⟧ η₂) ∷ subst-to-env* {Δ₁ = Δ₁} (subst-shrink σ) η₂

subst-shrink-id : (x : l ∈ Δ) → subst-shrink{Δ₁ = Δ}{Δ₂ = l′ ∷ Δ} idₛ l x ≡ idₛ l (there x)
subst-shrink-id here = refl
subst-shrink-id (there x) = refl

subst-to-env*-id-ext : (η : Env* Δ) → (x : l ∈ Δ) → apply-env (subst-to-env* idₛ η) x ≡ apply-env η x
subst-to-env*-id-ext η here = refl
subst-to-env*-id-ext η (there x) = {!!}

subst-to-env*-id : (η : Env* Δ) → subst-to-env* idₛ η ≡ω η
subst-to-env*-id η = {!!}

-- work zone

subst-env-ext-cancel-type : Setω
subst-env-ext-cancel-type = ∀ {Δ₁ Δ₂ l} → (σ : Sub Δ₁ Δ₂) (η₂ : Env* Δ₂) (α : Set l)
  → ∀ {l₁} → (x : l₁ ∈ Δ₁) → apply-env (subst-to-env* σ η₂) x ≡ apply-env (subst-to-env* (subst-shrink (extₛ σ l)) (α ∷ η₂)) x

subst-env-ext-cancel : subst-env-ext-cancel-type
subst-env-ext-cancel σ η₂ α here = {!!}
subst-env-ext-cancel σ η₂ α (there x) = {!!}

subst-var-preserves : (x  : l ∈ Δ₁) (σ  : Sub Δ₁ Δ₂) (η₂ : Env* Δ₂) → ⟦ σ l x ⟧ η₂ ≡ apply-env (subst-to-env* σ η₂) x
subst-var-preserves here σ η₂ = refl
subst-var-preserves (there x) σ η₂ = subst-var-preserves x (subst-shrink σ) η₂

subst-preserves-type : Setω
subst-preserves-type =
  ∀ {Δ₁ Δ₂}{l}{η₂ : Env* Δ₂}
  → (σ : Sub Δ₁ Δ₂) (T : Type Δ₁ l)
  → ⟦ subT σ T ⟧ η₂ ≡ ⟦ T ⟧ (subst-to-env* σ η₂)

subst-preserves : subst-preserves-type
subst-preserves {η₂ = η₂} σ (` x) = subst-var-preserves x σ η₂
subst-preserves{η₂ = η₂} σ (T₁ ⇒ T₂)
  rewrite subst-preserves{η₂ = η₂} σ T₁
  |  subst-preserves{η₂ = η₂} σ T₂ = refl
subst-preserves {η₂ = η₂} σ (`∀α l , T) =
  dependent-extensionality (λ α → {!subst-preserves {η₂ = α ∷ η₂}(extₛ σ l) T!})
--  dependent-extensionality λ α → {!subst-preserves {η₁ = α ∷ η₁}{η₂ = α ∷ η₂} (extₛ σ l) T!}
subst-preserves σ 𝟙 = refl

single-subst-preserves : ∀ (η : Env* Δ) (T′ : Type Δ l) (T : Type (l ∷ Δ) l′) → ⟦ T [ T′ ]T ⟧ η ≡ ⟦ T ⟧ (⟦ T′ ⟧ η ∷ η)
single-subst-preserves {Δ = Δ} {l = l}{l′ = l′} η T′ T = 
  begin
    ⟦ T [ T′ ]T ⟧ η
  ≡⟨ subst-preserves{Δ₁ = l ∷ Δ}{Δ₂ = Δ}{l = l′}{η₂ = η} (singleₛ idₛ l T′) T ⟩
    ⟦ T ⟧ (⟦ T′ ⟧ η ∷ subst-to-env* (subst-shrink (singleₛ idₛ l T′)) η)
  ≡⟨ cong (λ H → ⟦ T ⟧ (⟦ T′ ⟧ η ∷ subst-to-env* H η)) (subst-shrink-single-ext{_}{l}{T′}) ⟩
    ⟦ T ⟧ (⟦ T′ ⟧ η ∷ subst-to-env* idₛ η)
  ≡⟨ congω (λ H → ⟦ T ⟧ (⟦ T′ ⟧ η ∷ H)) (subst-to-env*-id η) ⟩
    ⟦ T ⟧ (⟦ T′ ⟧ η ∷ η)
  ∎

E⟦_⟧ : ∀ {T : Type Δ l}{Γ : TEnv Δ} → Expr Δ Γ T → (η : Env* Δ) → Env Δ Γ η → ⟦ T ⟧ η
E⟦ ` x ⟧ η γ = γ x
E⟦ ƛ_ e ⟧ η γ = λ v → E⟦ e ⟧ η (extend γ v)
E⟦ e₁ · e₂ ⟧ η γ = E⟦ e₁ ⟧ η γ (E⟦ e₂ ⟧ η γ)
E⟦ Λ l ⇒ e ⟧ η γ = λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ η) (extend-tskip γ)
E⟦ _∙_ {T = T} e T′ ⟧ η γ
  with E⟦ e ⟧ η γ (⟦ T′ ⟧ η)
... | v rewrite single-subst-preserves η T′ T = v 
