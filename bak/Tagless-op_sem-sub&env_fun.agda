module Tagless-op_sem-sub&env_fun where

open import Level
open import Data.Product using (_×_; Σ-syntax; ∃-syntax; _,_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; length; lookup; tabulate)
open import Data.Unit
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂; cong-app; icong; module ≡-Reasoning)
open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open ≡-Reasoning

variable l l′ l₁ l₂ : Level

----------------------------------------------------------------------

postulate
  fun-ext : ∀{a b} → Extensionality a b

dependent-extensionality : ∀ {a b}{A : Set a}{F G : (α : A) → Set b}
    → (∀ (α : A) → F α ≡ G α)
    → ((α : A) → F α) ≡ ((α : A) → G α) 
dependent-extensionality = ∀-extensionality fun-ext _ _

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

postulate 
  fun-ext-lvl : {B : (l : Level) → Set (suc l)} {f g : (x : Level) → B x} →
    (∀ x → f x ≡ g x) → f ≡ω g
  fun-ext-ωl : {A : Setω} {B : A → Set l} {f g : (x : A) → B x} →
    (∀ x → f x ≡ g x) → f ≡ω g
  fun-ext-lω : {A : Set l} {B : A → Setω} {f g : (x : A) → B x} →
    (∀ x → f x ≡ω g x) → f ≡ω g
  fun-ext-ωω : {A : Setω} {B : A → Setω} {f g : (x : A) → B x} →
    (∀ x → f x ≡ω g x) → f ≡ω g

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
  𝟙      : Type Δ zero

variable T T₁ T₂ : Type Δ l


-- level of type according to Leivant'91
level : Type Δ l → Level
level {l = l} T = l

-- semantic environments (mapping level l to an element of Set l)

{- data Env* : LEnv → Setω where
  []  : Env* []
  _∷_ : Set l → Env* Δ → Env* (l ∷ Δ)
   -}

Env* : LEnv → Setω
Env* Δ = ∀ l → l ∈ Δ → Set l

drop* : Env* (l ∷ Δ) → Env* Δ 
drop* η _ x = η _ (there x)

cons* : Set l → Env* Δ → Env* (l ∷ Δ)
cons* T η _ here = T
cons* T η _ (there x) = η _ x

-- the meaning of a stratified type in terms of Agda universes

⟦_⟧ : (T : Type Δ l) → Env* Δ → Set l
⟦ ` x ⟧ η =  η _ x
⟦ T₁ ⇒ T₂ ⟧ η = ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η
⟦ `∀α l , T ⟧ η = (α : Set l) → ⟦ T ⟧ (cons* α η)
⟦ 𝟙 ⟧ η = ⊤

-- renaming on types

TRen : LEnv → LEnv → Set
TRen Δ₁ Δ₂ = ∀ l → l ∈ Δ₁ → l ∈ Δ₂

Twkᵣ : TRen Δ (l ∷ Δ)
Twkᵣ _ = there

Tliftᵣ : TRen Δ₁ Δ₂ → TRen (l ∷ Δ₁) (l ∷ Δ₂)
Tliftᵣ ρ _ here = here
Tliftᵣ ρ _ (there x) = there (ρ _ x)

Tdropᵣ : TRen (l ∷ Δ₁) Δ₂ → TRen Δ₁ Δ₂
Tdropᵣ ρ _ x = ρ _ (there x)

Tren : TRen Δ₁ Δ₂ → (Type Δ₁ l → Type Δ₂ l)
Tren ρ (` x) = ` ρ _ x
Tren ρ (T₁ ⇒ T₂) = Tren ρ T₁ ⇒ Tren ρ T₂
Tren ρ (`∀α lev , T) = `∀α lev , Tren (Tliftᵣ ρ) T
Tren ρ 𝟙 = 𝟙 

Twk : Type Δ l′ → Type (l ∷ Δ) l′
Twk = Tren Twkᵣ


-- the action of renaming on semantic environments

TRen* : (ρ : TRen Δ₁ Δ₂) → (η₁ : Env* Δ₁) → (η₂ : Env* Δ₂) → Setω
TRen* {Δ₁} ρ η₁ η₂ = ∀ {l : Level} → (x : l ∈ Δ₁) → η₂ _ (ρ _ x) ≡ η₁ _ x

wkᵣ∈Ren* : ∀ (η : Env* Δ) (⟦α⟧ : Set l) → TRen* (Twkᵣ{Δ}{l}) η (cons* ⟦α⟧ η)
wkᵣ∈Ren* η ⟦α⟧ x = refl

Tren*-id : (η : Env* Δ) → TRen* (λ _ x → x) η η
Tren*-id η x = refl

Tren*-pop : (ρ : TRen (l ∷ Δ₁) Δ₂) (α : Set l) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂) → TRen* ρ (cons* α η₁) η₂ → TRen* (λ _ x → ρ _ (there x)) η₁ η₂
Tren*-pop ρ α η₁ η₂ Tren* x = Tren* (there x)

Tren*-ext : ∀ {ρ : TRen Δ₁ Δ₂}{η₁ : Env* Δ₁}{η₂ : Env* Δ₂} (α : Set l)
  → TRen* ρ η₁ η₂ → TRen* (Tliftᵣ ρ) (cons* α η₁) (cons* α η₂)
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
    Tren*-preserves-semantics{ρ = Tliftᵣ ρ}{cons* α η₁}{cons* α η₂} (Tren*-ext {ρ = ρ} α Tren*) T)
Tren*-preserves-semantics Tren* 𝟙 = refl

-- substitution on types

TSub : LEnv → LEnv → Set
TSub Δ₁ Δ₂ = ∀ l → l ∈ Δ₁ → Type Δ₂ l

Tidₛ : TSub Δ Δ
Tidₛ _ = `_

Twkₛ : TSub Δ₁ Δ₂ → TSub Δ₁ (l ∷ Δ₂)
Twkₛ σ _ x = Twk (σ _ x)

Tliftₛ : TSub Δ₁ Δ₂ → TSub (l ∷ Δ₁) (l ∷ Δ₂)
Tliftₛ σ _ here = ` here
Tliftₛ σ _ (there x) = Twk (σ _ x)

Tdropₛ : TSub (l ∷ Δ₁) Δ₂ → TSub Δ₁ Δ₂
Tdropₛ σ _ x = σ _ (there x)

Tsub : TSub Δ₁ Δ₂ → Type Δ₁ l → Type Δ₂ l
Tsub σ (` x) = σ _ x
Tsub σ (T₁ ⇒ T₂) = Tsub σ T₁ ⇒ Tsub σ T₂
Tsub σ (`∀α l , T) = `∀α l , Tsub (Tliftₛ σ) T
Tsub σ 𝟙 = 𝟙

Textₛ : TSub Δ₁ Δ₂ → Type Δ₂ l → TSub (l ∷ Δ₁) Δ₂
Textₛ σ T' _ here = T'
Textₛ σ T' _ (there x) = σ _ x

_[_]T : Type (l ∷ Δ) l′ → Type Δ l → Type Δ l′
_[_]T T T' = Tsub (Textₛ Tidₛ T') T

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
  → Env Δ Γ η → Env (l ∷ Δ) (l ◁* Γ) (cons* ⟦α⟧ η)
extend-tskip {η = η} {⟦α⟧ = ⟦α⟧} γ (tskip{T = T} x)
  rewrite Tren*-preserves-semantics {ρ = Twkᵣ}{η}{cons* ⟦α⟧ η} (wkᵣ∈Ren* η ⟦α⟧) T
  = γ x

subst-to-env* : (σ : TSub Δ₁ Δ₂) → (η : Env* Δ₂) → Env* Δ₁
subst-to-env* σ η _ x = ⟦ σ _ x ⟧ η

subst-to-env*-wk : (σ  : TSub Δ₁ Δ₂) → (α  : Set l) → (η : Env* Δ₂) → 
  subst-to-env* (Twkₛ σ) (cons* α η) ≡ω subst-to-env* σ η
subst-to-env*-wk {[]} σ α η = fun-ext-lvl λ l → fun-ext λ ()  
subst-to-env*-wk {l ∷ Δ₁} {l = l₁} σ α η = fun-ext-lvl λ l → fun-ext {!   !}

subst-to-env*-build : ∀ (ρ : TRen Δ₁ Δ₂) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂) → TRen* ρ η₁ η₂
  → subst-to-env* (build-Tidₛ Δ₁ ρ) η₂ ≡ω η₁
subst-to-env*-build ρ [] η₂ Tren* = refl
subst-to-env*-build {Δ₁ = _ ∷ Δ₁} ρ (α ∷ η₁) η₂ Tren* = 
  transω (congωω (λ H → apply-env η₂ (ρ _ here) ∷ H) (subst-to-env*-build (λ _ x → ρ _ (there x)) η₁ η₂ (Tren*-pop ρ α η₁ η₂ Tren*)))
         (conglω (_∷ η₁) (Tren* here))

subst-to-env*-id : (η : Env* Δ) → subst-to-env* Tidₛ η ≡ω η
subst-to-env*-id {Δ} η = subst-to-env*-build {Δ₁ = Δ} (λ _ x → x) η η (Tren*-id η)

subst-preserves-type : Setω
subst-preserves-type =
  ∀ {Δ₁ Δ₂}{l}{η₂ : Env* Δ₂}
  → (σ : TSub Δ₁ Δ₂) (T : Type Δ₁ l)
  → ⟦ Tsub σ T ⟧ η₂ ≡ ⟦ T ⟧ (subst-to-env* σ η₂)

subst-preserves : subst-preserves-type
subst-preserves {η₂ = η₂} σ (` x) = refl
subst-preserves {η₂ = η₂} σ (T₁ ⇒ T₂)
  rewrite subst-preserves{η₂ = η₂} σ T₁
  |  subst-preserves{η₂ = η₂} σ T₂ = refl
subst-preserves {η₂ = η₂} σ (`∀α l , T) =
  dependent-extensionality (λ α →
    trans (subst-preserves {η₂ = α ∷ η₂} (Tliftₛ σ) T)
          (congωl (λ H → ⟦ T ⟧ (α ∷ H)) (subst-to-env*-wk σ α η₂)))
subst-preserves σ 𝟙 = refl

single-subst-preserves : ∀ (η : Env* Δ) (T′ : Type Δ l) (T : Type (l ∷ Δ) l′) → ⟦ T [ T′ ]T ⟧ η ≡ ⟦ T ⟧ (⟦ T′ ⟧ η ∷ η)
single-subst-preserves {Δ = Δ} {l = l}{l′ = l′} η T′ T =
  trans (subst-preserves (Textₛ Tidₛ T′) T)
        (congωl (λ H → ⟦ T ⟧ (⟦ T′ ⟧ η ∷ H)) (subst-to-env*-id η))

E⟦_⟧ : ∀ {T : Type Δ l}{Γ : TEnv Δ} → Expr Δ Γ T → (η : Env* Δ) → Env Δ Γ η → ⟦ T ⟧ η
E⟦ ` x ⟧ η γ = γ x
E⟦ ƛ_ e ⟧ η γ = λ v → E⟦ e ⟧ η (extend γ v)
E⟦ e₁ · e₂ ⟧ η γ = E⟦ e₁ ⟧ η γ (E⟦ e₂ ⟧ η γ)
E⟦ Λ l ⇒ e ⟧ η γ = λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ η) (extend-tskip γ)
E⟦ _∙_ {T = T} e T′ ⟧ η γ rewrite single-subst-preserves η T′ T = E⟦ e ⟧ η γ (⟦ T′ ⟧ η)

-- type in expr substitution


-- composition of renamings and substituions

_σσ→σ_ : TSub Δ₁ Δ₂ → TSub Δ₂ Δ₃ → TSub Δ₁ Δ₃
[] σσ→σ σ₂ = []
(T ∷ σ₁) σσ→σ σ₂ = Tsub σ₂ T ∷ σ₁ σσ→σ σ₂

_ρρ→ρ_ : TRen Δ₁ Δ₂ → TRen Δ₂ Δ₃ → TRen Δ₁ Δ₃
(ρ₁ ρρ→ρ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

_ρσ→σ_ : TRen Δ₁ Δ₂ → TSub Δ₂ Δ₃ → TSub Δ₁ Δ₃
ρ ρσ→σ σ = build-Tidₛ _ ρ σσ→σ σ

_σρ→σ_ : TSub Δ₁ Δ₂ → TRen Δ₂ Δ₃ → TSub Δ₁ Δ₃
[] σρ→σ ρ = []
(T ∷ σ) σρ→σ ρ = Tren ρ T ∷ σ σρ→σ ρ


-- interaction of renamings and substituions

sub↑-dist-ren↑ : ∀ l (ρ : TRen Δ₁ Δ₂) (σ : TSub Δ₂ Δ₃) →
  Tliftᵣ {l = l} ρ ρσ→σ Tliftₛ σ ≡ Tliftₛ (ρ ρσ→σ σ) 
sub↑-dist-ren↑ l ρ [] = {!   !}
sub↑-dist-ren↑ l ρ (x ∷ σ) = {!   !}

mutual 
  assoc-sub↑-ren↑ : ∀ (T : Type (l ∷ Δ₁) l′) (ρ : TRen Δ₁ Δ₂) (σ : TSub Δ₂ Δ₃) →
    Tsub (Tliftₛ σ) (Tren (Tliftᵣ ρ) T) ≡ Tsub (Tliftₛ (ρ ρσ→σ σ)) T
  assoc-sub↑-ren↑ T ρ σ = begin
      Tsub (Tliftₛ σ) (Tren (Tliftᵣ ρ) T) 
    ≡⟨ assoc-sub-ren T (Tliftᵣ ρ) (Tliftₛ σ) ⟩
      Tsub (Tliftᵣ ρ ρσ→σ Tliftₛ σ) T
    ≡⟨ cong (λ σ → Tsub σ T) (sub↑-dist-ren↑ _ ρ σ) ⟩
      Tsub (Tliftₛ (ρ ρσ→σ σ)) T
    ∎

  assoc-sub-ren : ∀ (T : Type Δ₁ l) (ρ : TRen Δ₁ Δ₂) (σ : TSub Δ₂ Δ₃) →
    Tsub σ (Tren ρ T) ≡ Tsub (ρ ρσ→σ σ) T
  assoc-sub-ren (` x) ρ σ = {!   !}
  assoc-sub-ren (T₁ ⇒ T₂) ρ σ = cong₂ _⇒_ (assoc-sub-ren T₁ ρ σ) (assoc-sub-ren T₂ ρ σ)
  assoc-sub-ren (`∀α l , T) ρ σ = cong (`∀α l ,_) (assoc-sub↑-ren↑ T ρ σ)
  assoc-sub-ren 𝟙 ρ σ = refl

ren↑-dist-ren↑ : ∀ l (ρ₁ : TRen Δ₁ Δ₂) (ρ₂ : TRen Δ₂ Δ₃) →
  ((Tliftᵣ {l = l} ρ₁) ρρ→ρ (Tliftᵣ ρ₂)) ≡ Tliftᵣ (ρ₁ ρρ→ρ ρ₂)
ren↑-dist-ren↑ l ρ₁ ρ₂ = {!   !}  

mutual 
  assoc-ren↑-ren↑ : ∀ (T : Type (l ∷ Δ₁) l′) (ρ₁ : TRen Δ₁ Δ₂) (ρ₂ : TRen Δ₂ Δ₃) →
    Tren (Tliftᵣ ρ₂) (Tren (Tliftᵣ ρ₁) T) ≡ Tren (Tliftᵣ (ρ₁ ρρ→ρ ρ₂)) T
  assoc-ren↑-ren↑ {l = l} T ρ₁ ρ₂ =
      Tren (Tliftᵣ ρ₂) (Tren (Tliftᵣ ρ₁) T) 
    ≡⟨ assoc-ren-ren T (Tliftᵣ ρ₁) (Tliftᵣ ρ₂) ⟩
      Tren (Tliftᵣ ρ₁ ρρ→ρ Tliftᵣ ρ₂) T
    ≡⟨ cong (λ ρ → Tren ρ T) (ren↑-dist-ren↑ l ρ₁ ρ₂)  ⟩
      Tren (Tliftᵣ (ρ₁ ρρ→ρ ρ₂)) T
    ∎

  assoc-ren-ren : ∀ (T : Type Δ₁ l) (ρ₁ : TRen Δ₁ Δ₂) (ρ₂ : TRen Δ₂ Δ₃) →
    Tren ρ₂ (Tren ρ₁ T) ≡ Tren (ρ₁ ρρ→ρ ρ₂) T
  assoc-ren-ren (` x) ρ₁ ρ₂ = {!   !}
  assoc-ren-ren (T₁ ⇒ T₂) ρ₁ ρ₂ = cong₂ _⇒_ (assoc-ren-ren T₁ ρ₁ ρ₂) (assoc-ren-ren T₂ ρ₁ ρ₂)
  assoc-ren-ren (`∀α l , T) ρ₁ ρ₂ = cong (`∀α l ,_) (assoc-ren↑-ren↑ T ρ₁ ρ₂)
  assoc-ren-ren 𝟙 ρ₁ ρ₂ = refl

ren↑-dist-sub↑ : ∀ l (σ : TSub Δ₁ Δ₂) (ρ : TRen Δ₂ Δ₃) →
  (Tliftₛ σ σρ→σ Tliftᵣ ρ) ≡ Tliftₛ (σ σρ→σ ρ) {l = l} 
ren↑-dist-sub↑ l σ ρ = {!   !}

mutual 
  assoc-ren↑-sub↑ : ∀ (T : Type (l ∷ Δ₁) l′) (σ : TSub Δ₁ Δ₂) (ρ : TRen Δ₂ Δ₃) →
    Tren (Tliftᵣ ρ) (Tsub (Tliftₛ σ) T) ≡ Tsub (Tliftₛ (σ σρ→σ ρ)) T
  assoc-ren↑-sub↑ {l = l} T σ ρ = begin 
      Tren (Tliftᵣ ρ) (Tsub (Tliftₛ σ) T)
    ≡⟨ assoc-ren-sub T (Tliftₛ σ) (Tliftᵣ ρ ) ⟩
      Tsub (Tliftₛ σ σρ→σ Tliftᵣ ρ) T
    ≡⟨ cong (λ σ → Tsub σ T) (ren↑-dist-sub↑ l σ ρ) ⟩
      Tsub (Tliftₛ (σ σρ→σ ρ)) T
    ∎ 

  assoc-ren-sub : ∀ (T : Type Δ₁ l) (σ : TSub Δ₁ Δ₂) (ρ : TRen Δ₂ Δ₃) →
    Tren ρ (Tsub σ T) ≡ Tsub (σ σρ→σ ρ) T
  assoc-ren-sub (` x) ρ σ = {!   !}
  assoc-ren-sub (T₁ ⇒ T₂) ρ σ = cong₂ _⇒_ (assoc-ren-sub T₁ ρ σ) (assoc-ren-sub T₂ ρ σ)
  assoc-ren-sub (`∀α l , T) ρ σ = cong (`∀α l ,_) (assoc-ren↑-sub↑ T ρ σ)
  assoc-ren-sub 𝟙 ρ σ = refl

sub↑-dist-sub↑ : ∀ l (σ₁ : TSub Δ₁ Δ₂) (σ₂ : TSub Δ₂ Δ₃) →
  (Tliftₛ σ₁ {l = l} σσ→σ Tliftₛ σ₂) ≡ Tliftₛ (σ₁ σσ→σ σ₂) 
sub↑-dist-sub↑ l σ₁ σ₂ = {!   !}

mutual 
  assoc-sub↑-sub↑ : ∀ (T : Type (l ∷ Δ₁) l′) (σ₁ : TSub Δ₁ Δ₂) (σ₂ : TSub Δ₂ Δ₃) →
    Tsub (Tliftₛ σ₂) (Tsub (Tliftₛ σ₁) T) ≡ Tsub (Tliftₛ (σ₁ σσ→σ σ₂)) T
  assoc-sub↑-sub↑ {l = l} T σ₁ σ₂ = begin 
      Tsub (Tliftₛ σ₂) (Tsub (Tliftₛ σ₁) T)
    ≡⟨ assoc-sub-sub T (Tliftₛ σ₁) (Tliftₛ σ₂) ⟩
      Tsub (Tliftₛ σ₁ σσ→σ Tliftₛ σ₂) T
    ≡⟨ cong (λ σ → Tsub σ T) (sub↑-dist-sub↑ l σ₁ σ₂) ⟩
      Tsub (Tliftₛ (σ₁ σσ→σ σ₂)) T
    ∎ 

  assoc-sub-sub : ∀ (T : Type Δ₁ l) (σ₁ : TSub Δ₁ Δ₂) (σ₂ : TSub Δ₂ Δ₃) →
    Tsub σ₂ (Tsub σ₁ T) ≡ Tsub (σ₁ σσ→σ σ₂) T
  assoc-sub-sub (` x) σ₁ σ₂ = {!   !}
  assoc-sub-sub (T₁ ⇒ T₂) σ₁ σ₂ = cong₂ _⇒_ (assoc-sub-sub T₁ σ₁ σ₂) (assoc-sub-sub T₂ σ₁ σ₂)
  assoc-sub-sub (`∀α l , T) σ₁ σ₂ = cong (`∀α l ,_) (assoc-sub↑-sub↑ T σ₁ σ₂)
  assoc-sub-sub 𝟙 σ₁ σ₂ = refl

-- type in expr renamings

Tren-Γ : TRen Δ₁ Δ₂ → TEnv Δ₁ → TEnv Δ₂
Tren-Γ ρ (T ◁ Γ) = Tren ρ T ◁ Tren-Γ ρ Γ
Tren-Γ ρ (l ◁* Γ) = Tren-Γ (Tdropᵣ ρ) Γ
Tren-Γ {Δ₂ = []} ρ ∅ = ∅
Tren-Γ {Δ₂ = l ∷ Δ₂} ρ ∅ = l ◁* (Tren-Γ (λ _ ()) ∅)

Tdropᵣρ·T≡ρ·TwkT : (ρ : TRen (l ∷ Δ₁) Δ₂) → Tren (Tdropᵣ ρ) T ≡ Tren ρ (Twk T)
Tdropᵣρ·T≡ρ·TwkT {T = ` x} ρ = refl
Tdropᵣρ·T≡ρ·TwkT {T = T₁ ⇒ T₂} ρ = cong₂ _⇒_ (Tdropᵣρ·T≡ρ·TwkT ρ) (Tdropᵣρ·T≡ρ·TwkT ρ)
Tdropᵣρ·T≡ρ·TwkT {T = `∀α l , T} ρ = cong (`∀α l ,_) {!   !}
Tdropᵣρ·T≡ρ·TwkT {T = 𝟙} ρ = refl

TdropᵣTliftᵣΓ≡l◁*Γ : ∀ {ρ : TRen Δ₁ Δ₂}(Γ : TEnv  Δ₁) → 
  Tren-Γ (Tdropᵣ (Tliftᵣ ρ)) Γ ≡ (l ◁* Tren-Γ ρ Γ)
TdropᵣTliftᵣΓ≡l◁*Γ = {!   !} 

ρ[T]≡[ρT]ρ↑ : ∀ (T : Type Δ₁ l) (ρ : TRen Δ₁ Δ₂) →
  Textₛ Tidₛ T σρ→σ ρ ≡ (Tliftᵣ ρ) ρσ→σ Textₛ Tidₛ (Tren ρ T)
ρ[T]≡[ρT]ρ↑ = {!   !}

ρT[T′]≡ρT[ρ↑T′] : ∀ (ρ : TRen Δ₁ Δ₂) (T : Type (l ∷ Δ₁) l′) (T′ : Type Δ₁ l) →
  Tren ρ (T [ T′ ]T) ≡ Tren (Tliftᵣ ρ) T [ Tren ρ T′ ]T 
ρT[T′]≡ρT[ρ↑T′] ρ T T′ = begin 
    Tren ρ (T [ T′ ]T)
  ≡⟨ assoc-ren-sub T (Textₛ Tidₛ T′) ρ ⟩
    Tsub (Textₛ Tidₛ T′ σρ→σ ρ) T
  ≡⟨ cong (λ σ → Tsub σ T) (ρ[T]≡[ρT]ρ↑ T′ ρ) ⟩
    Tsub ((Tliftᵣ ρ) ρσ→σ (Textₛ Tidₛ (Tren ρ T′))) T
  ≡⟨ sym (assoc-sub-ren T (Tliftᵣ ρ) (Textₛ Tidₛ (Tren ρ T′))) ⟩
    Tsub (Textₛ Tidₛ (Tren ρ T′)) (Tren (Tliftᵣ ρ) T)
  ∎

ETren-x : (ρ : TRen Δ₁ Δ₂) → inn T Γ → inn (Tren ρ T) (Tren-Γ ρ Γ)
ETren-x ρ here = here
ETren-x ρ (there x) = there (ETren-x ρ x)
ETren-x {T = T} {Γ = Γ} ρ (tskip x) = 
  subst (λ T → inn T (Tren-Γ ρ Γ)) (Tdropᵣρ·T≡ρ·TwkT ρ) (ETren-x (Tdropᵣ ρ) x)

ETren : (ρ : TRen Δ₁ Δ₂) → Expr Δ₁ Γ T → Expr Δ₂ (Tren-Γ ρ Γ) (Tren ρ T)
ETren ρ (` x) = ` ETren-x ρ x
ETren ρ (ƛ e) = ƛ ETren ρ e
ETren ρ (e₁ · e₂) = ETren ρ e₁ · ETren ρ e₂
ETren {Δ₂ = Δ₂} {Γ = Γ} {T = .(`∀α l , T)} ρ (Λ_⇒_ l {T} e) = Λ l ⇒ 
  subst (λ Γ → Expr (l ∷ Δ₂) Γ (Tren (Tliftᵣ ρ) T)) (TdropᵣTliftᵣΓ≡l◁*Γ Γ) (ETren (Tliftᵣ ρ) e)
ETren {Δ₂ = Δ₂} {Γ = Γ} ρ (_∙_ {T = T} e T′) = subst (λ T → Expr Δ₂ (Tren-Γ ρ Γ) T) (sym (ρT[T′]≡ρT[ρ↑T′] ρ T T′)) (ETren ρ e ∙ Tren ρ T′)

TwkᵣΓ≡l◁*Γ : ∀ (Γ : TEnv Δ) → Tren-Γ Twkᵣ Γ ≡ (l ◁* Γ)
TwkᵣΓ≡l◁*Γ ∅ = refl
TwkᵣΓ≡l◁*Γ (_◁_ {l = l} T Γ) = {!   !}
TwkᵣΓ≡l◁*Γ (l ◁* Γ) = {!   !}

Tsub-Γ : TSub Δ₁ Δ₂ → TEnv Δ₁ → TEnv Δ₂
Tsub-Γ σ (T ◁ Γ) = Tsub σ T ◁ Tsub-Γ σ Γ
Tsub-Γ (T ∷ σ) (l ◁* Γ) = Tsub-Γ σ Γ
Tsub-Γ {Δ₂ = []} [] ∅ = ∅
Tsub-Γ {Δ₂ = l ∷ Δ₂} [] ∅ = l ◁* Tsub-Γ [] ∅

TwkₛΓ≡l◁*Γ : ∀ {σ : TSub Δ₁ Δ₂}(Γ : TEnv  Δ₁) → Tsub-Γ (Twkₛ σ) Γ ≡ (l ◁* Tsub-Γ σ Γ)
TwkₛΓ≡l◁*Γ = {!   !} 

σ[T]≡[σT]σ↑ : ∀ (T : Type Δ₁ l) (σ : TSub Δ₁ Δ₂) →
  (Textₛ Tidₛ T σσ→σ σ) ≡ ((Tliftₛ σ) σσ→σ (Textₛ Tidₛ (Tsub σ T)))
σ[T]≡[σT]σ↑ T σ = {!   !}

σT[T′]≡σ↑T[σT'] : ∀ (σ : TSub Δ₁ Δ₂) (T : Type (l ∷ Δ₁) l′) (T′ : Type Δ₁ l) →
  Tsub σ (T [ T′ ]T) ≡ (Tsub (Tliftₛ σ) T) [ Tsub σ T′ ]T  
σT[T′]≡σ↑T[σT'] σ T T′ = 
  begin 
    Tsub σ (T [ T′ ]T) 
  ≡⟨ assoc-sub-sub T (Textₛ Tidₛ T′) σ ⟩
    Tsub (Textₛ Tidₛ T′ σσ→σ σ) T
  ≡⟨ cong (λ σ → Tsub σ T) (σ[T]≡[σT]σ↑ T′ σ) ⟩
    Tsub (Tliftₛ σ σσ→σ Textₛ Tidₛ (Tsub σ T′)) T
  ≡⟨ sym (assoc-sub-sub T (Tliftₛ σ) (Textₛ Tidₛ (Tsub σ T′))) ⟩
    (Tsub (Tliftₛ σ) T) [ Tsub σ T′ ]T
  ∎

ETsub-x : (σ : TSub Δ₁ Δ₂) → inn T Γ → inn (Tsub σ T) (Tsub-Γ σ Γ)
ETsub-x σ here = here
ETsub-x σ (there x) = there (ETsub-x σ x)
ETsub-x σ (tskip x) = {!   !}

ETsub : (σ : TSub Δ₁ Δ₂) → Expr Δ₁ Γ T → Expr Δ₂ (Tsub-Γ σ Γ) (Tsub σ T)
ETsub σ (` x) = ` ETsub-x σ x
ETsub σ (ƛ e) = ƛ ETsub σ e
ETsub σ (e₁ · e₂) = ETsub σ e₁ · ETsub σ e₂
ETsub {Δ₂ = Δ₂} {Γ = Γ} {T = .(`∀α l , T)} σ (Λ_⇒_ l {T} e) = Λ l ⇒ 
  subst (λ Γ → Expr (l ∷ Δ₂) Γ (Tsub (Tliftₛ σ) T)) (TwkₛΓ≡l◁*Γ Γ) (ETsub (Tliftₛ σ) e)
ETsub {Δ₂ = Δ₂} {Γ = Γ} σ (_∙_ {T = T} e T′) = subst (λ T → Expr Δ₂ (Tsub-Γ σ Γ) T) (sym (σT[T′]≡σ↑T[σT'] σ T T′)) (ETsub σ e ∙ Tsub σ T′) 

-- type in expr substituions

{- σ₁x≡σ₂x→↑σ₁x≡↑σ₂x : ∀ {σ₁ σ₂ : TSub Δ₁ Δ₂} → 
 (∀ {l} (x : l ∈ Δ₁) → apply-TSub x σ₁ ≡ apply-TSub x σ₂) → 
 (∀ {l} (x : l ∈ (l′ ∷ Δ₁)) → apply-TSub x (Tliftₛ σ₁) ≡ apply-TSub x (Tliftₛ σ₂))
σ₁x≡σ₂x→↑σ₁x≡↑σ₂x σ₁≡σ₂ here = refl
σ₁x≡σ₂x→↑σ₁x≡↑σ₂x {σ₁ = σ₁} σ₁≡σ₂ (there x) with σ₁≡σ₂ x
... | eq = {!    !}

σ₁x≡σ₂x : ∀ {σ₁ σ₂ : TSub Δ₁ Δ₂} (T : Type Δ₁ l) → 
  (∀ {l} (x : l ∈ Δ₁) → apply-TSub x σ₁ ≡ apply-TSub x σ₂) → 
  Tsub σ₁ T ≡ Tsub σ₂ T
σ₁x≡σ₂x (` x) σ₁≡σ₂ = σ₁≡σ₂ x
σ₁x≡σ₂x (T₁ ⇒ T₂) σ₁≡σ₂ = cong₂ _⇒_ (σ₁x≡σ₂x T₁ σ₁≡σ₂) (σ₁x≡σ₂x T₂ σ₁≡σ₂)
σ₁x≡σ₂x (`∀α l , T) σ₁≡σ₂ = cong (`∀α l ,_) (σ₁x≡σ₂x T (σ₁x≡σ₂x→↑σ₁x≡↑σ₂x σ₁≡σ₂))
σ₁x≡σ₂x 𝟙 σ₁≡σ₂ = refl -}

{- TliftₛTidₛ≡Tidₛ : ∀{Δ l} 
  (Tliftₛ Tidₛ) ≡ Tidₛ
TliftₛTidₛ≡Tidₛ here = refl
TliftₛTidₛ≡Tidₛ (there x) = {!   !} -}
 
Tidₛx≡`x : ∀ (x : l ∈ Δ) → apply-TSub x Tidₛ ≡ (` x)
Tidₛx≡`x here = refl
Tidₛx≡`x (there x) with Tidₛx≡`x x 
... | a = {!   !}

TidₛT≡T : ∀ (T : Type Δ l) → Tsub Tidₛ T ≡ T
TidₛT≡T (` x) = Tidₛx≡`x x
TidₛT≡T (T₁ ⇒ T₂) = cong₂ _⇒_ (TidₛT≡T T₁) (TidₛT≡T T₂)
TidₛT≡T {Δ = Δ} (`∀α_,_ {l′ = l′} l T) = cong (`∀α l ,_) (trans {!   !} (TidₛT≡T T))
TidₛT≡T 𝟙 = refl

TidₛΓ≡Γ : ∀ (Γ : TEnv Δ) → Tsub-Γ Tidₛ Γ ≡ Γ
TidₛΓ≡Γ ∅ = refl
TidₛΓ≡Γ (T ◁ Γ) = cong₂ _◁_ (TidₛT≡T T) (TidₛΓ≡Γ Γ)
TidₛΓ≡Γ (l ◁* Γ) = {!  !}

_[_]ET : Expr (l ∷ Δ) (l ◁* Γ) T → (T′ : Type Δ l) → Expr Δ Γ (T [ T′ ]T)
_[_]ET {Δ = Δ} {Γ = Γ} {T = T} e T′ = subst (λ Γ → Expr Δ Γ (T [ T′ ]T)) (TidₛΓ≡Γ Γ) (ETsub (Textₛ Tidₛ T′) e)

Ewk-l : Expr Δ Γ T → Expr (l ∷ Δ) (l ◁* Γ) (Twk T)  
Ewk-l {Δ = Δ} {Γ = Γ} {T = T} {l = l} e = subst (λ Γ → Expr (l ∷ Δ) Γ (Twk T)) (TwkᵣΓ≡l◁*Γ Γ) (ETren Twkᵣ e)

-- expr in expr substitution

ERen : TEnv Δ → TEnv Δ → Set
ERen {Δ} Γ₁ Γ₂ = ∀ {l} {T : Type Δ l} → inn T Γ₁ → inn T Γ₂

Ewkᵣ : ERen Γ (T ◁ Γ) 
Ewkᵣ = there

Eliftᵣ : ERen Γ₁ Γ₂ → ERen (T ◁ Γ₁) (T ◁ Γ₂)
Eliftᵣ ρ here = here
Eliftᵣ ρ (there x) = there (ρ x)

Eliftᵣ-l : ERen Γ₁ Γ₂ → ERen (l ◁* Γ₁) (l ◁* Γ₂)
Eliftᵣ-l ρ (tskip x) = tskip (ρ x) 

Eren : ERen Γ₁ Γ₂ → (Expr Δ Γ₁ T → Expr Δ Γ₂ T)
Eren ρ (` x) = ` ρ x
Eren ρ (ƛ e) = ƛ Eren (Eliftᵣ ρ) e
Eren ρ (e₁ · e₂) = Eren ρ e₁ · Eren ρ e₂
Eren ρ (Λ l ⇒ e) = Λ l ⇒ Eren (Eliftᵣ-l ρ) e
Eren ρ (e ∙ T′) = Eren ρ e ∙ T′

Ewk : Expr Δ Γ T → Expr Δ (T₁ ◁ Γ) T 
Ewk = Eren Ewkᵣ

ESub : TEnv Δ → TEnv Δ → Set
ESub {Δ} Γ₁ Γ₂ = ∀ {l} {T : Type Δ l} → inn T Γ₁ → Expr Δ Γ₂ T

Eidₛ : ESub Γ Γ
Eidₛ = `_

Ewkₛ : ESub Γ₁ Γ₂ → ESub Γ₁ (T ◁ Γ₂)
Ewkₛ σ x = Ewk (σ x)

Eliftₛ : ESub Γ₁ Γ₂ → ESub (T ◁ Γ₁) (T ◁ Γ₂)
Eliftₛ σ here = ` here
Eliftₛ σ (there x) = Ewk (σ x)

Eliftₛ-l : ESub Γ₁ Γ₂ → ESub (l ◁* Γ₁) (l ◁* Γ₂)
Eliftₛ-l σ (tskip x) = Ewk-l (σ x)

Esub : ESub Γ₁ Γ₂ → Expr Δ Γ₁ T → Expr Δ Γ₂ T
Esub σ (` x) = σ x
Esub σ (ƛ e) = ƛ Esub (Eliftₛ σ) e
Esub σ (e₁ · e₂) = Esub σ e₁ · Esub σ e₂
Esub σ (Λ l ⇒ e) = Λ l ⇒ Esub (Eliftₛ-l σ) e
Esub σ (e ∙ T) = Esub σ e ∙ T

Eextₛ : ESub Γ₁ Γ₂ → Expr Δ Γ₂ T → ESub (T ◁ Γ₁) Γ₂
Eextₛ σ e' here = e'
Eextₛ σ e' (there x) = σ x

_[_]E : Expr Δ (T₁ ◁ Γ) T₂ → Expr Δ Γ T₁ → Expr Δ Γ T₂
_[_]E e e' = Esub (Eextₛ Eidₛ e') e

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

adequacy : ∀ {e₁ e₂ : Expr [] ∅ T} → e₁ ↪ e₂ → E⟦ e₁ ⟧ [] (λ()) ≡ E⟦ e₂ ⟧ [] (λ())
adequacy (β-ƛ v₂) = {!   !}
adequacy β-Λ = {!   !}
adequacy (ξ-·₁ e₁↪e) = cong-app (adequacy e₁↪e) _
adequacy (ξ-·₂ {e₁ = e₁} e₂↪e v₁) = icong {f = E⟦ e₁ ⟧ [] λ ()} (adequacy e₂↪e)
adequacy (ξ-∙ e₁↪e₂) = {!   !}     