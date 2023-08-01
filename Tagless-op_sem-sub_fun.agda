module Tagless-op_sem-sub_fun where

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

----------------------------------------------------------------------

postulate
  fun-ext : ∀{a b} → Extensionality a b

fun-ext₂ : ∀ {A₁ : Set l₁} {A₂ : A₁ → Set l₂} {B : (x : A₁) → A₂ x → Set l₃}
             {f g : (x : A₁) → (y : A₂ x) → B x y} →
    (∀ (x : A₁) (y : A₂ x) → f x y ≡ g x y) →
    f ≡ g
fun-ext₂ h = fun-ext λ x → fun-ext λ y → h x y

dep-ext : ∀ {a b}{A : Set a}{F G : (α : A) → Set b}
    → (∀ (α : A) → F α ≡ G α)
    → ((α : A) → F α) ≡ ((α : A) → G α) 
dep-ext = ∀-extensionality fun-ext _ _

-- equality for Setω

data _≡ω_ {A : Setω} (x : A) : A → Setω where
  refl : x ≡ω x

postulate
  fun-ext-lvl : {B : (l : Level) → Set l} {f g : (x : Level) → B x} →
    (∀ x → f x ≡ g x) → f ≡ω g

congωl : ∀ {b} {A : Setω} {B : Set b} (f : A → B) {x y : A} → x ≡ω y → f x ≡ f y
congωl f refl = refl

conglω : ∀ {a} {A : Set a} {B : Setω} (f : A → B) {x y : A} → x ≡ y → f x ≡ω f y
conglω f refl = refl

congωω : ∀ {A : Setω} {B : Setω} (f : A → B) {x y : A} → x ≡ω y → f x ≡ω f y
congωω f refl = refl

-- conglωω : ∀ {a} {A : Set a} {B : Setω} {C : Setω} (f : A → B → C) {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≡ x₂ → y₁ ≡ω y₂ → f x₁ y₁ ≡ω f x₂ y₂
-- conglωω f refl refl = refl

transω : ∀ {A : Setω} {x y z : A} → x ≡ω y → y ≡ω z → x ≡ω z
transω refl refl = refl

symω : ∀ {A : Setω} {x y : A} → x ≡ω y → y ≡ω x
symω refl = refl

substω : ∀ {b}{A : Setω} → (F : (x : A) → Set b) →
  ∀ {x y : A} → x ≡ω y → F x → F y
substω f refl x = x

----------------------------------------------------------------------

-- level environments

{- 
-- Set l instead of Setω?
data LEnv′ (l : Level) : Set l where 
  []  : LEnv′ l
  _∷_[_] : (l′ : Level) → LEnv′ l → l′ ⊔ l ≡ l → LEnv′ l 
-}
   
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
  ρ ρ₁ ρ₂ : TRen Δ₁ Δ₂

Tidᵣ : TRen Δ Δ
Tidᵣ _ = id

Tdropᵣ : TRen (l ∷ Δ₁) Δ₂ → TRen Δ₁ Δ₂
Tdropᵣ ρ _ x = ρ _ (there x)

Twkᵣ : TRen Δ₁ Δ₂ → TRen Δ₁ (l ∷ Δ₂)
Twkᵣ ρ _ x = there (ρ _ x) 

Tliftᵣ : TRen Δ₁ Δ₂ → (l : Level) → TRen (l ∷ Δ₁) (l ∷ Δ₂)
Tliftᵣ ρ _ _ here = here
Tliftᵣ ρ _ _ (there x) = there (ρ _ x)

Tren : TRen Δ₁ Δ₂ → (Type Δ₁ l → Type Δ₂ l)
Tren ρ (` x) = ` ρ _ x
Tren ρ (T₁ ⇒ T₂) = Tren ρ T₁ ⇒ Tren ρ T₂
Tren ρ (`∀α l , T) = `∀α l , Tren (Tliftᵣ ρ l) T
Tren ρ `ℕ = `ℕ

Twk : Type Δ l′ → Type (l ∷ Δ) l′
Twk = Tren (Twkᵣ Tidᵣ)

-- the action of renaming on semantic environments

TRen* : (ρ : TRen Δ₁ Δ₂) → (η₁ : Env* Δ₁) → (η₂ : Env* Δ₂) → Setω
TRen* {Δ₁} ρ η₁ η₂ = ∀ {l : Level} → (x : l ∈ Δ₁) → apply-env η₂ (ρ _ x) ≡ apply-env η₁ x

wkᵣ∈Ren* : ∀ (η : Env* Δ) (⟦α⟧ : Set l) → TRen* (Twkᵣ {Δ₁ = Δ}{l = l} Tidᵣ) η (⟦α⟧ ∷ η)
wkᵣ∈Ren* η ⟦α⟧ x = refl

Tren*-id : (η : Env* Δ) → TRen* (λ _ x → x) η η
Tren*-id η x = refl

Tren*-pop : (ρ : TRen (l ∷ Δ₁) Δ₂) (α : Set l) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂) → 
  TRen* ρ (α ∷ η₁) η₂ → TRen* (λ _ x → ρ _ (there x)) η₁ η₂
Tren*-pop ρ α η₁ η₂ Tren* x = Tren* (there x)

Tren*-lift : ∀ {ρ : TRen Δ₁ Δ₂}{η₁ : Env* Δ₁}{η₂ : Env* Δ₂} (α : Set l)
  → TRen* ρ η₁ η₂ → TRen* (Tliftᵣ ρ _) (α ∷ η₁) (α ∷ η₂)
Tren*-lift α Tren* here = refl
Tren*-lift α Tren* (there x) = Tren* x

Tren*-preserves-semantics : ∀ {ρ : TRen Δ₁ Δ₂}{η₁ : Env* Δ₁}{η₂ : Env* Δ₂}
  → (Tren* : TRen* ρ η₁ η₂) → (T : Type Δ₁ l) →  ⟦ Tren ρ T ⟧ η₂ ≡ ⟦ T ⟧ η₁
Tren*-preserves-semantics {ρ = ρ} {η₁} {η₂} Tren* (` x) = Tren* x
Tren*-preserves-semantics {ρ = ρ} {η₁} {η₂} Tren* (T₁ ⇒ T₂)
  rewrite Tren*-preserves-semantics {ρ = ρ} {η₁} {η₂} Tren* T₁
  | Tren*-preserves-semantics {ρ = ρ} {η₁} {η₂} Tren* T₂
  = refl
Tren*-preserves-semantics {ρ = ρ} {η₁} {η₂} Tren* (`∀α l , T) = dep-ext λ where 
  α → Tren*-preserves-semantics{ρ = Tliftᵣ ρ _}{α ∷ η₁}{α ∷ η₂} (Tren*-lift {ρ = ρ} α Tren*) T
Tren*-preserves-semantics Tren* `ℕ = refl

-- substitution on types

TSub : LEnv → LEnv → Set
TSub Δ₁ Δ₂ = ∀ l → l ∈ Δ₁ → Type Δ₂ l

variable 
  σ σ₁ σ₂ : TSub Δ₁ Δ₂
 
Tidₛ : TSub Δ Δ
Tidₛ _ = `_

Tdropₛ : TSub (l ∷ Δ₁) Δ₂ → TSub Δ₁ Δ₂
Tdropₛ σ _ x = σ _ (there x)

Twkₛ : TSub Δ₁ Δ₂ → TSub Δ₁ (l ∷ Δ₂)
Twkₛ σ _ x = Twk (σ _ x)

Tliftₛ : TSub Δ₁ Δ₂ → (l : Level) → TSub (l ∷ Δ₁) (l ∷ Δ₂)
Tliftₛ σ _ _ here = ` here
Tliftₛ σ _ _ (there x) = Twk (σ _ x)

Tsub : TSub Δ₁ Δ₂ → Type Δ₁ l → Type Δ₂ l
Tsub σ (` x) = σ _ x
Tsub σ (T₁ ⇒ T₂) = Tsub σ T₁ ⇒ Tsub σ T₂
Tsub σ (`∀α l , T) = `∀α l , Tsub (Tliftₛ σ _) T
Tsub σ `ℕ = `ℕ

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
  = subst Function.id (sym (Tren*-preserves-semantics {ρ = Twkᵣ Tidᵣ} {η} {⟦α⟧ ∷ η} (wkᵣ∈Ren* η ⟦α⟧) T)) (γ _ _ x) -- γ _ _ x 
  
subst-to-env* : TSub Δ₁ Δ₂ → Env* Δ₂ → Env* Δ₁
subst-to-env* {[]} σ η₂ = []
subst-to-env* {x ∷ Δ₁} σ η₂ = ⟦ σ _ here ⟧ η₂ ∷ subst-to-env* (Tdropₛ σ) η₂

subst-var-preserves : (x  : l ∈ Δ₁) (σ  : TSub Δ₁ Δ₂) (η₂ : Env* Δ₂) → ⟦ σ _ x ⟧ η₂ ≡ apply-env (subst-to-env* σ η₂) x
subst-var-preserves here σ η₂ = refl
subst-var-preserves (there x) σ η₂ = subst-var-preserves x (Tdropₛ σ) η₂

subst-to-env*-wk : (σ  : TSub Δ₁ Δ₂) → (α  : Set l) → (η₂ : Env* Δ₂) → 
  subst-to-env* (Twkₛ σ) (α ∷ η₂) ≡ω subst-to-env* σ η₂
subst-to-env*-wk {Δ₁ = []} σ α η₂ = refl
subst-to-env*-wk {Δ₁ = l ∷ Δ₁} σ α η₂
  rewrite Tren*-preserves-semantics {ρ = Twkᵣ Tidᵣ}{η₂}{α ∷ η₂} (wkᵣ∈Ren* η₂ α) (σ _ here)
  = congωω (⟦ (σ _ here) ⟧ η₂ ∷_) (subst-to-env*-wk (Tdropₛ σ) α η₂) -- easier?

subst-to-env*-build : ∀ (ρ : TRen Δ₁ Δ₂) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂) → TRen* ρ η₁ η₂
  → subst-to-env* (λ _ x → ` ρ _ x) η₂ ≡ω η₁
subst-to-env*-build ρ [] η₂ Tren* = refl
subst-to-env*-build {Δ₁ = _ ∷ Δ₁} ρ (α ∷ η₁) η₂ Tren* = 
  transω (congωω (λ H → apply-env η₂ (ρ _ here) ∷ H) (subst-to-env*-build (λ _ x → ρ _ (there x)) η₁ η₂ (Tren*-pop ρ α η₁ η₂ Tren*)))
         (conglω (_∷ η₁) (Tren* here))

subst-to-env*-id : (η : Env* Δ) → subst-to-env* Tidₛ η ≡ω η
subst-to-env*-id {Δ = Δ} η = subst-to-env*-build {Δ₁ = Δ} (λ _ x → x) η η (Tren*-id η)

subst-preserves-type : Setω
subst-preserves-type =
  ∀ {Δ₁ Δ₂}{l}{η₂ : Env* Δ₂}
  → (σ : TSub Δ₁ Δ₂) (T : Type Δ₁ l)
  → ⟦ Tsub σ T ⟧ η₂ ≡ ⟦ T ⟧ (subst-to-env* σ η₂)

subst-preserves : subst-preserves-type
subst-preserves {η₂ = η₂} σ (` x) = subst-var-preserves x σ η₂
subst-preserves {η₂ = η₂} σ (T₁ ⇒ T₂)
  rewrite subst-preserves{η₂ = η₂} σ T₁
  |  subst-preserves{η₂ = η₂} σ T₂ = refl
subst-preserves {η₂ = η₂} σ (`∀α l , T) =
  dep-ext (λ ⟦α⟧ →
    trans (subst-preserves {η₂ = ⟦α⟧ ∷ η₂} (Tliftₛ σ _) T)
          (congωl (λ H → ⟦ T ⟧ (⟦α⟧ ∷ H)) (subst-to-env*-wk σ ⟦α⟧ η₂)))
subst-preserves σ `ℕ = refl
 
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
E⟦ _∙_ {T = T} e T′ ⟧ η γ rewrite Tsingle-subst-preserves η T′ T = E⟦ e ⟧ η γ (⟦ T′ ⟧ η)

-- type in expr substitution

-- composition of renamings and substituions

_∘ₛₛ_ : TSub Δ₁ Δ₂ → TSub Δ₂ Δ₃ → TSub Δ₁ Δ₃
(σ₁ ∘ₛₛ σ₂) _ x = Tsub σ₂ (σ₁ _ x)

_∘ᵣᵣ_ : TRen Δ₁ Δ₂ → TRen Δ₂ Δ₃ → TRen Δ₁ Δ₃
(ρ₁ ∘ᵣᵣ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

_∘ᵣₛ_ : TRen Δ₁ Δ₂ → TSub Δ₂ Δ₃ → TSub Δ₁ Δ₃
(ρ ∘ᵣₛ σ) _ x = σ _ (ρ _ x)

_∘ₛᵣ_ : TSub Δ₁ Δ₂ → TRen Δ₂ Δ₃ → TSub Δ₁ Δ₃
(σ ∘ₛᵣ ρ) _ x = Tren ρ (σ _ x)

-- interaction of renamings and substituions

sub↑-dist-∘ᵣₛ : ∀ l (ρ : TRen Δ₁ Δ₂) (σ : TSub Δ₂ Δ₃) →
  Tliftₛ (ρ ∘ᵣₛ σ) _ ≡ Tliftᵣ ρ l ∘ᵣₛ Tliftₛ σ _ 
sub↑-dist-∘ᵣₛ l ρ σ = fun-ext₂ λ where 
  _ here → refl
  _ (there x) → refl

mutual 
  assoc-sub↑-ren↑ : ∀ (T : Type (l ∷ Δ₁) l′) (ρ : TRen Δ₁ Δ₂) (σ : TSub Δ₂ Δ₃) →
    Tsub (Tliftₛ σ _) (Tren (Tliftᵣ ρ _) T) ≡ Tsub (Tliftₛ (ρ ∘ᵣₛ σ) _) T
  assoc-sub↑-ren↑ T ρ σ = begin
      Tsub (Tliftₛ σ _) (Tren (Tliftᵣ ρ _) T) 
    ≡⟨ assoc-sub-ren T (Tliftᵣ ρ _) (Tliftₛ σ _) ⟩
      Tsub (Tliftᵣ ρ _ ∘ᵣₛ Tliftₛ σ _) T
    ≡⟨ cong (λ σ → Tsub σ T) (sym (sub↑-dist-∘ᵣₛ _ ρ σ)) ⟩
      Tsub (Tliftₛ (ρ ∘ᵣₛ σ) _) T
    ∎

  assoc-sub-ren : ∀ (T : Type Δ₁ l) (ρ : TRen Δ₁ Δ₂) (σ : TSub Δ₂ Δ₃) →
    Tsub σ (Tren ρ T) ≡ Tsub (ρ ∘ᵣₛ σ) T
  assoc-sub-ren (` x) ρ σ = refl
  assoc-sub-ren (T₁ ⇒ T₂) ρ σ = cong₂ _⇒_ (assoc-sub-ren T₁ ρ σ) (assoc-sub-ren T₂ ρ σ)
  assoc-sub-ren (`∀α l , T) ρ σ = cong (`∀α l ,_) (assoc-sub↑-ren↑ T ρ σ)
  assoc-sub-ren `ℕ ρ σ = refl

ren↑-dist-∘ᵣᵣ : ∀ l (ρ₁ : TRen Δ₁ Δ₂) (ρ₂ : TRen Δ₂ Δ₃) →
  Tliftᵣ (ρ₁ ∘ᵣᵣ ρ₂) _ ≡ ((Tliftᵣ ρ₁ l) ∘ᵣᵣ (Tliftᵣ ρ₂ _)) 
ren↑-dist-∘ᵣᵣ l ρ₁ ρ₂ = fun-ext₂ λ where 
  _ here → refl
  _ (there x) → refl

mutual 
  assoc-ren↑-ren↑ : ∀ (T : Type (l ∷ Δ₁) l′) (ρ₁ : TRen Δ₁ Δ₂) (ρ₂ : TRen Δ₂ Δ₃) →
    Tren (Tliftᵣ ρ₂ _) (Tren (Tliftᵣ ρ₁ _) T) ≡ Tren (Tliftᵣ (ρ₁ ∘ᵣᵣ ρ₂) _) T
  assoc-ren↑-ren↑ {l = l} T ρ₁ ρ₂ =
      Tren (Tliftᵣ ρ₂ _) (Tren (Tliftᵣ ρ₁ _) T) 
    ≡⟨ assoc-ren-ren T (Tliftᵣ ρ₁ _) (Tliftᵣ ρ₂ _) ⟩
      Tren (Tliftᵣ ρ₁ _ ∘ᵣᵣ Tliftᵣ ρ₂ _) T
    ≡⟨ cong (λ ρ → Tren ρ T) (sym (ren↑-dist-∘ᵣᵣ l ρ₁ ρ₂))  ⟩
      Tren (Tliftᵣ (ρ₁ ∘ᵣᵣ ρ₂) _) T
    ∎

  assoc-ren-ren : ∀ (T : Type Δ₁ l) (ρ₁ : TRen Δ₁ Δ₂) (ρ₂ : TRen Δ₂ Δ₃) →
    Tren ρ₂ (Tren ρ₁ T) ≡ Tren (ρ₁ ∘ᵣᵣ ρ₂) T
  assoc-ren-ren (` x) ρ₁ ρ₂ = refl
  assoc-ren-ren (T₁ ⇒ T₂) ρ₁ ρ₂ = cong₂ _⇒_ (assoc-ren-ren T₁ ρ₁ ρ₂) (assoc-ren-ren T₂ ρ₁ ρ₂)
  assoc-ren-ren (`∀α l , T) ρ₁ ρ₂ = cong (`∀α l ,_) (assoc-ren↑-ren↑ T ρ₁ ρ₂)
  assoc-ren-ren `ℕ ρ₁ ρ₂ = refl

↑ρ-TwkT≡Twk-ρT : ∀ (T : Type Δ₁ l′) (ρ : TRen Δ₁ Δ₂) →
  Tren (Tliftᵣ ρ l) (Twk T) ≡ Twk (Tren ρ T) 
↑ρ-TwkT≡Twk-ρT {l = l} T ρ = 
  begin 
    Tren (Tliftᵣ ρ _) (Tren (Twkᵣ Tidᵣ) T)
  ≡⟨ assoc-ren-ren T (Twkᵣ Tidᵣ) (Tliftᵣ ρ _) ⟩
    Tren ((Twkᵣ Tidᵣ) ∘ᵣᵣ Tliftᵣ ρ _) T
  ≡⟨ sym (assoc-ren-ren T ρ (Twkᵣ Tidᵣ)) ⟩
    Tren (Twkᵣ Tidᵣ) (Tren ρ T)
  ∎

ren↑-dist-∘ₛᵣ : ∀ l (σ : TSub Δ₁ Δ₂) (ρ : TRen Δ₂ Δ₃) →
  Tliftₛ (σ ∘ₛᵣ ρ) l ≡ (Tliftₛ σ l ∘ₛᵣ Tliftᵣ ρ _)
ren↑-dist-∘ₛᵣ l σ ρ = fun-ext₂ λ where 
   _ here → refl
   _ (there x) → sym (↑ρ-TwkT≡Twk-ρT (σ _ x) ρ)

mutual 
  assoc-ren↑-sub↑ : ∀ (T : Type (l ∷ Δ₁) l′) (σ : TSub Δ₁ Δ₂) (ρ : TRen Δ₂ Δ₃) →
    Tren (Tliftᵣ ρ _) (Tsub (Tliftₛ σ _) T) ≡ Tsub (Tliftₛ (σ ∘ₛᵣ ρ) _) T
  assoc-ren↑-sub↑ {l = l} T σ ρ = begin 
      Tren (Tliftᵣ ρ _) (Tsub (Tliftₛ σ _) T)
    ≡⟨ assoc-ren-sub T (Tliftₛ σ _) (Tliftᵣ ρ _) ⟩
      Tsub (Tliftₛ σ _ ∘ₛᵣ Tliftᵣ ρ _) T
    ≡⟨ cong (λ σ → Tsub σ T) (sym (ren↑-dist-∘ₛᵣ l σ ρ)) ⟩
      Tsub (Tliftₛ (σ ∘ₛᵣ ρ) _) T
    ∎ 

  assoc-ren-sub : ∀ (T : Type Δ₁ l) (σ : TSub Δ₁ Δ₂) (ρ : TRen Δ₂ Δ₃) →
    Tren ρ (Tsub σ T) ≡ Tsub (σ ∘ₛᵣ ρ) T
  assoc-ren-sub (` x) ρ σ = refl
  assoc-ren-sub (T₁ ⇒ T₂) ρ σ = cong₂ _⇒_ (assoc-ren-sub T₁ ρ σ) (assoc-ren-sub T₂ ρ σ)
  assoc-ren-sub (`∀α l , T) ρ σ = cong (`∀α l ,_) (assoc-ren↑-sub↑ T ρ σ)
  assoc-ren-sub `ℕ ρ σ = refl

σ↑-TwkT≡Twk-σT : ∀ {l} (σ : TSub Δ₁ Δ₂) (T : Type Δ₁ l′) →
  Tsub (Tliftₛ σ _) (Twk {l = l} T) ≡ Twk (Tsub σ T)
σ↑-TwkT≡Twk-σT σ T = 
  begin 
    Tsub (Tliftₛ σ _) (Twk T) 
  ≡⟨ assoc-sub-ren T (Twkᵣ Tidᵣ) (Tliftₛ σ _) ⟩
    Tsub (σ ∘ₛᵣ λ _ → there) T
  ≡⟨ sym (assoc-ren-sub T σ (Twkᵣ Tidᵣ)) ⟩
    Tren (Twkᵣ Tidᵣ) (Tsub σ T)
  ∎


sub↑-dist-∘ₛₛ : ∀ l (σ₁ : TSub Δ₁ Δ₂) (σ₂ : TSub Δ₂ Δ₃) →
  Tliftₛ (σ₁ ∘ₛₛ σ₂) _  ≡ (Tliftₛ σ₁ l ∘ₛₛ Tliftₛ σ₂ _)
sub↑-dist-∘ₛₛ l σ₁ σ₂ = fun-ext₂ λ where 
  _ here → refl
  l′ (there x) → begin 
        (Tliftₛ (σ₁ ∘ₛₛ σ₂) l) l′ (there x) 
      ≡⟨ sym (σ↑-TwkT≡Twk-σT {l = l} σ₂ (σ₁ l′ x)) ⟩
        (Tliftₛ σ₁ _ ∘ₛₛ Tliftₛ σ₂ _) l′ (there x)
      ∎

mutual 
  assoc-sub↑-sub↑ : ∀ (T : Type (l ∷ Δ₁) l′) (σ₁ : TSub Δ₁ Δ₂) (σ₂ : TSub Δ₂ Δ₃) →
    Tsub (Tliftₛ σ₂ _) (Tsub (Tliftₛ σ₁ _) T) ≡ Tsub (Tliftₛ (σ₁ ∘ₛₛ σ₂) _) T
  assoc-sub↑-sub↑ {l = l} T σ₁ σ₂ = begin 
      Tsub (Tliftₛ σ₂ _) (Tsub (Tliftₛ σ₁ _) T)
    ≡⟨ assoc-sub-sub T (Tliftₛ σ₁ _) (Tliftₛ σ₂ _) ⟩
      Tsub (Tliftₛ σ₁ _ ∘ₛₛ Tliftₛ σ₂ _) T
    ≡⟨ cong (λ σ → Tsub σ T) (sym (sub↑-dist-∘ₛₛ l σ₁ σ₂)) ⟩
      Tsub (Tliftₛ (σ₁ ∘ₛₛ σ₂) _) T
    ∎ 

  assoc-sub-sub : ∀ (T : Type Δ₁ l) (σ₁ : TSub Δ₁ Δ₂) (σ₂ : TSub Δ₂ Δ₃) →
    Tsub σ₂ (Tsub σ₁ T) ≡ Tsub (σ₁ ∘ₛₛ σ₂) T
  assoc-sub-sub (` x) σ₁ σ₂ = refl
  assoc-sub-sub (T₁ ⇒ T₂) σ₁ σ₂ = cong₂ _⇒_ (assoc-sub-sub T₁ σ₁ σ₂) (assoc-sub-sub T₂ σ₁ σ₂)
  assoc-sub-sub (`∀α l , T) σ₁ σ₂ = cong (`∀α l ,_) (assoc-sub↑-sub↑ T σ₁ σ₂)
  assoc-sub-sub `ℕ σ₁ σ₂ = refl

-- type in expr renamings

TliftᵣTidᵣ≡Tidᵣ : ∀ Δ l →
  (Tliftᵣ {Δ₁ = Δ} Tidᵣ l) ≡ Tidᵣ
TliftᵣTidᵣ≡Tidᵣ _ _ = fun-ext₂ λ where
  _ here → refl
  _ (there x) → refl

TidᵣT≡T : ∀ (T : Type Δ l) → Tren Tidᵣ T ≡ T
TidᵣT≡T (` x) = refl
TidᵣT≡T (T₁ ⇒ T₂) = cong₂ _⇒_ (TidᵣT≡T T₁) (TidᵣT≡T T₂)
TidᵣT≡T {Δ = Δ} (`∀α l , T) rewrite TliftᵣTidᵣ≡Tidᵣ Δ l = cong (`∀α l ,_) (TidᵣT≡T T)
TidᵣT≡T `ℕ = refl

ρ[T]≡[ρT]ρ↑ : ∀ (T : Type Δ₁ l) (ρ : TRen Δ₁ Δ₂) →
  Textₛ Tidₛ T ∘ₛᵣ ρ ≡ (Tliftᵣ ρ _) ∘ᵣₛ Textₛ Tidₛ (Tren ρ T)
ρ[T]≡[ρT]ρ↑ T ρ = fun-ext₂ λ where 
  _ here → refl
  _ (there x) → refl

ρT[T′]≡ρT[ρ↑T′] : ∀ (ρ : TRen Δ₁ Δ₂) (T : Type (l ∷ Δ₁) l′) (T′ : Type Δ₁ l) →
  Tren ρ (T [ T′ ]T) ≡ Tren (Tliftᵣ ρ _) T [ Tren ρ T′ ]T 
ρT[T′]≡ρT[ρ↑T′] ρ T T′ = begin 
    Tren ρ (T [ T′ ]T)
  ≡⟨ assoc-ren-sub T (Textₛ Tidₛ T′) ρ ⟩
    Tsub (Textₛ Tidₛ T′ ∘ₛᵣ ρ) T
  ≡⟨ cong (λ σ → Tsub σ T) (ρ[T]≡[ρT]ρ↑ T′ ρ) ⟩
    Tsub ((Tliftᵣ ρ _) ∘ᵣₛ (Textₛ Tidₛ (Tren ρ T′))) T
  ≡⟨ sym (assoc-sub-ren T (Tliftᵣ ρ _) (Textₛ Tidₛ (Tren ρ T′))) ⟩
    Tsub (Textₛ Tidₛ (Tren ρ T′)) (Tren (Tliftᵣ ρ _) T)
  ∎

data OPE : TRen Δ₁ Δ₂ → TEnv Δ₁ → TEnv Δ₂ → Set where
  ope-id : ∀ {Δ} {Γ : TEnv Δ} →
    OPE Tidᵣ Γ Γ
  ope-lift-l : ∀ {l} {Δ₁} {Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {ρ : TRen Δ₁ Δ₂} →
    (ope : OPE ρ Γ₁ Γ₂) → OPE (Tliftᵣ ρ _) (l ◁* Γ₁) (l ◁* Γ₂)
  ope-wk : ∀ {l} {Δ₁} {Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {ρ : TRen Δ₁ Δ₂} →
    (ope : OPE ρ Γ₁ Γ₂) → OPE (Twkᵣ ρ) Γ₁ (l ◁* Γ₂)
  ope-lift-T : ∀ {l} {Δ₁} {Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {T : Type Δ₁ l} {ρ : TRen Δ₁ Δ₂}
    (ope : OPE ρ Γ₁ Γ₂) → OPE ρ (T ◁ Γ₁) (Tren ρ T ◁ Γ₂) 
  
ETren-x : {ρ : TRen Δ₁ Δ₂} → (ope : OPE ρ Γ₁ Γ₂) → inn T Γ₁ → inn (Tren ρ T) Γ₂
ETren-x {T = T} {ρ = ρ} ope-id x rewrite TidᵣT≡T T = x
ETren-x {ρ = .(Tliftᵣ _ _)} (ope-lift-l ope) (tskip x) = 
  subst (λ T → inn T _) (sym (↑ρ-TwkT≡Twk-ρT _ _)) (tskip (ETren-x ope x))
ETren-x {ρ = .(Twkᵣ _)} (ope-wk ope) x = subst (λ T → inn T _) (assoc-ren-ren _ _ (Twkᵣ Tidᵣ)) (tskip (ETren-x ope x))
ETren-x {ρ = ρ} (ope-lift-T ope) here = here
ETren-x {ρ = ρ} (ope-lift-T ope) (there x) = there (ETren-x ope x)

ETren : {ρ : TRen Δ₁ Δ₂} → (ope : OPE ρ Γ₁ Γ₂) → Expr Δ₁ Γ₁ T → Expr Δ₂ Γ₂ (Tren ρ T)
ETren ope (# n) = # n
ETren ope (` x) = ` ETren-x ope x
ETren ope (ƛ e) = ƛ ETren (ope-lift-T ope) e
ETren ope (e₁ · e₂) = ETren ope e₁ · ETren ope e₂
ETren {ρ = ρ} ope (Λ l ⇒ e) = Λ l ⇒ ETren (ope-lift-l ope) e
ETren {Δ₂ = Δ₂} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {ρ = ρ}  ope (_∙_ {T = T} e T′) = 
  subst (λ T → Expr Δ₂ Γ₂ T) (sym (ρT[T′]≡ρT[ρ↑T′] ρ T T′)) (ETren ope e ∙ Tren ρ T′) 

Ewk-l : Expr Δ Γ T → Expr (l ∷ Δ) (l ◁* Γ) (Twk T)  
Ewk-l {Δ = Δ} {Γ = Γ} {T = T} {l = l} e = ETren (ope-wk ope-id) e

-- type in expr substituions

data Sub : TSub Δ₁ Δ₂ → TEnv Δ₁ → TEnv Δ₂ → Set where
  sub-id : ∀ {Δ} {Γ : TEnv Δ} →
    Sub Tidₛ Γ Γ
  sub-lift-l : ∀ {l} {Δ₁} {Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {σ : TSub Δ₁ Δ₂} →
    (sub : Sub σ Γ₁ Γ₂) → Sub (Tliftₛ σ _) (l ◁* Γ₁) (l ◁* Γ₂)
  sub-ext : ∀ {l} {Δ₁} {Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {σ : TSub Δ₁ Δ₂} {T : Type Δ₂ l} →
    (sub : Sub σ Γ₁ Γ₂) → Sub (Textₛ σ T) (l ◁* Γ₁) Γ₂
  sub-lift-T : ∀ {l} {Δ₁} {Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {σ : TSub Δ₁ Δ₂} {T : Type Δ₁ l} →
    (sub : Sub σ Γ₁ Γ₂) → Sub σ (T ◁ Γ₁) (Tsub σ T ◁ Γ₂)

TliftₛTidₛ≡Tidₛ : ∀ Δ l →                         
  (Tliftₛ {Δ₁ = Δ} Tidₛ l) ≡ Tidₛ
TliftₛTidₛ≡Tidₛ _ _ = fun-ext₂ λ where
  _ here → refl
  _ (there x) → refl             

TidₛT≡T : ∀ (T : Type Δ l) → Tsub Tidₛ T ≡ T       
TidₛT≡T (` x) = refl
TidₛT≡T (T₁ ⇒ T₂) = cong₂ _⇒_ (TidₛT≡T T₁) (TidₛT≡T T₂)
TidₛT≡T {Δ = Δ} (`∀α l , T) rewrite TliftₛTidₛ≡Tidₛ Δ l = cong (`∀α l ,_) (TidₛT≡T T)
TidₛT≡T `ℕ = refl

σ[T]≡[σT]σ↑ : ∀ (T : Type Δ₁ l) (σ : TSub Δ₁ Δ₂) →
  (Textₛ Tidₛ T ∘ₛₛ σ) ≡ ((Tliftₛ σ _) ∘ₛₛ (Textₛ Tidₛ (Tsub σ T)))
σ[T]≡[σT]σ↑ T σ = fun-ext₂ λ where
  _ here → refl
  _ (there x) → begin 
        σ _ x
      ≡⟨ sym (TidₛT≡T (σ _ x)) ⟩
        Tsub Tidₛ (σ _ x)
      ≡⟨ sym (assoc-sub-ren (σ _ x) (Twkᵣ Tidᵣ) (Textₛ Tidₛ (Tsub σ T))) ⟩
        Tsub (Textₛ Tidₛ (Tsub σ T)) (Twk (σ _ x))
      ∎

σT[T′]≡σ↑T[σT'] : ∀ (σ : TSub Δ₁ Δ₂) (T : Type (l ∷ Δ₁) l′) (T′ : Type Δ₁ l) →
  Tsub σ (T [ T′ ]T) ≡ (Tsub (Tliftₛ σ _) T) [ Tsub σ T′ ]T  
σT[T′]≡σ↑T[σT'] σ T T′ = 
  begin 
    Tsub σ (T [ T′ ]T) 
  ≡⟨ assoc-sub-sub T (Textₛ Tidₛ T′) σ ⟩
    Tsub (Textₛ Tidₛ T′ ∘ₛₛ σ) T
  ≡⟨ cong (λ σ → Tsub σ T) (σ[T]≡[σT]σ↑ T′ σ) ⟩
    Tsub (Tliftₛ σ _ ∘ₛₛ Textₛ Tidₛ (Tsub σ T′)) T
  ≡⟨ sym (assoc-sub-sub T (Tliftₛ σ _) (Textₛ Tidₛ (Tsub σ T′))) ⟩
    (Tsub (Tliftₛ σ _) T) [ Tsub σ T′ ]T
  ∎

σT≡TextₛσTwkT : {T′ : Type Δ₂ l′} (σ : TSub Δ₁ Δ₂) (T : Type Δ₁ l) → Tsub (Textₛ σ T′) (Twk T) ≡ Tsub σ T
σT≡TextₛσTwkT {T′ = T′} σ T = begin 
    Tsub (Textₛ σ _) (Twk T)
  ≡⟨ assoc-sub-ren T (Twkᵣ Tidᵣ) (Textₛ σ _) ⟩
    Tsub (Twkᵣ Tidᵣ ∘ᵣₛ Textₛ σ T′) T
  ≡⟨ sym (assoc-sub-sub T _ σ) ⟩
    Tsub σ (Tsub Tidₛ T)
  ≡⟨ cong (λ T → Tsub σ T) (TidₛT≡T T) ⟩
    Tsub σ T
  ∎

ETsub-x : {σ : TSub Δ₁ Δ₂} → Sub σ Γ₁ Γ₂ → inn T Γ₁ → inn (Tsub σ T) Γ₂
ETsub-x {T = T} sub-id x rewrite TidₛT≡T T = x
ETsub-x {T = .(Twk T)} {σ = .(Tliftₛ _ _)} (sub-lift-l sub) (tskip {T = T} x) = 
  subst (λ T → inn T _) (sym (σ↑-TwkT≡Twk-σT _ T)) (tskip (ETsub-x sub x))
ETsub-x {T = .(Twk T)} (sub-ext sub) (tskip {T = T} x) = 
  subst (λ T → inn T _) (sym (σT≡TextₛσTwkT _ T)) (ETsub-x sub x)
ETsub-x (sub-lift-T sub) here = here
ETsub-x (sub-lift-T sub) (there x) = there (ETsub-x sub x)

ETsub : {σ : TSub Δ₁ Δ₂} → Sub σ Γ₁ Γ₂ → Expr Δ₁ Γ₁ T → Expr Δ₂ Γ₂ (Tsub σ T)
ETsub sub (# n) = # n
ETsub sub (` x) = ` ETsub-x sub x
ETsub sub (ƛ e) = ƛ ETsub (sub-lift-T sub) e
ETsub sub (e₁ · e₂) = ETsub sub e₁ · ETsub sub e₂
ETsub sub (Λ l ⇒ e) = Λ l ⇒ ETsub (sub-lift-l sub) e
ETsub {Δ₂ = Δ₂} {Γ₂ = Γ₂} {σ = σ} sub (_∙_ {T = T} e T′) = 
  subst (λ T → Expr Δ₂ Γ₂ T) (sym (σT[T′]≡σ↑T[σT'] σ T T′)) (ETsub sub e ∙ Tsub σ T′)

_[_]ET : Expr (l ∷ Δ) (l ◁* Γ) T → (T′ : Type Δ l) → Expr Δ Γ (T [ T′ ]T)
e [ T ]ET = ETsub (sub-ext sub-id) e 

-- expr in expr substitution
module extended where

  -- expression renamings

  ERen : TRen Δ₁ Δ₂ → TEnv Δ₁ → TEnv Δ₂ → Set
  ERen {Δ₁}{Δ₂} ρ* Γ₁ Γ₂ = ∀ {l} {T : Type Δ₁ l} → inn T Γ₁ → inn (Tren ρ* T) Γ₂

  Eidᵣ : ERen Tidᵣ Γ Γ 
  Eidᵣ {T = T} x rewrite TidᵣT≡T T = x

  Edropᵣ : (ρ* : TRen Δ₁ Δ₂) → ERen ρ* (T ◁ Γ₁) Γ₂ → ERen ρ* Γ₁ Γ₂
  Edropᵣ ρ* ρ x = ρ (there x)

  Ewkᵣ : (ρ* : TRen Δ₁ Δ₂) →  ERen ρ* Γ₁ Γ₂ → ERen ρ* Γ₁ (T ◁ Γ₂) 
  Ewkᵣ ρ* ρ x = there (ρ x) 

  Eliftᵣ : {ρ* : TRen Δ₁ Δ₂} → ERen ρ* Γ₁ Γ₂ → ERen ρ* (T ◁ Γ₁) (Tren ρ* T ◁ Γ₂)
  Eliftᵣ ρ here = here
  Eliftᵣ ρ (there x) = there (ρ x)

  Eliftᵣ-l : {ρ* : TRen Δ₁ Δ₂} → ERen ρ* Γ₁ Γ₂ → ERen (Tliftᵣ ρ* l) (l ◁* Γ₁) (l ◁* Γ₂)
  Eliftᵣ-l {Γ₂ = Γ₂} {l = l} {ρ* = ρ*} ρ (tskip x) = subst id (cong (λ T → inn T (l ◁* Γ₂)) (sym (↑ρ-TwkT≡Twk-ρT _ ρ*))) (tskip (ρ x))

  Eren : {ρ* : TRen Δ₁ Δ₂} → ERen ρ* Γ₁ Γ₂ → Expr Δ₁ Γ₁ T → Expr Δ₂ Γ₂ (Tren ρ* T)
  Eren ρ (# n) = # n
  Eren ρ (` x) = ` ρ x
  Eren ρ (ƛ e) = ƛ Eren (Eliftᵣ ρ) e
  Eren ρ (e₁ · e₂) = Eren ρ e₁ · Eren ρ e₂
  Eren ρ (Λ l ⇒ e) = Λ l ⇒ Eren (Eliftᵣ-l ρ) e
  Eren {Δ₂ = Δ₂} {Γ₂ = Γ₂} {T = .(T [ T′ ]T)} {ρ* = ρ*} ρ (_∙_ {T = T} e T′) = subst (Expr Δ₂ Γ₂) (sym (ρT[T′]≡ρT[ρ↑T′] ρ* T T′)) (Eren ρ e ∙ Tren ρ* T′)
  
  Ewk : Expr Δ Γ T → Expr Δ (T₁ ◁ Γ) (T) 
  Ewk {T = T} e = subst (λ T → Expr _ _ T) (TidᵣT≡T T) (Eren (Ewkᵣ Tidᵣ Eidᵣ) e)

  -- expression substitutions

  ESub : TSub Δ₁ Δ₂ → TEnv Δ₁ → TEnv Δ₂ → Set
  ESub {Δ₁ = Δ₁} {Δ₂ = Δ₂} σ* Γ₁ Γ₂ = ∀ {l} {T : Type Δ₁ l} → inn T Γ₁ → Expr Δ₂ Γ₂ (Tsub σ* T)
  
  Eidₛ : ESub Tidₛ Γ Γ
  Eidₛ {T = T} rewrite TidₛT≡T T = `_
  
  Ewkₛ : (σ* : TSub Δ₁ Δ₂) → ESub σ* Γ₁ Γ₂ → ESub σ* Γ₁ (T ◁ Γ₂)
  Ewkₛ σ* σ {T = T} x = Ewk (σ x)
  
  Edropₛ : (σ* : TSub Δ₁ Δ₂) → ESub σ* (T ◁ Γ₁) Γ₂ → ESub σ* Γ₁ Γ₂
  Edropₛ σ* σ x = σ (there x)
  
  Eliftₛ : (σ* : TSub Δ₁ Δ₂) → ESub σ* Γ₁ Γ₂ → ESub σ* (T ◁ Γ₁) ((Tsub σ* T) ◁ Γ₂)
  Eliftₛ _ σ here = ` here
  Eliftₛ _ σ (there x) = Ewk (σ x)
  
  Eliftₛ-l : (σ* : TSub Δ₁ Δ₂) → ESub σ* Γ₁ Γ₂ → ESub (Tliftₛ σ* _) (l ◁* Γ₁) (l ◁* Γ₂)
  Eliftₛ-l σ* σ (tskip x) = subst (Expr _ _) (sym {!!}) (Ewk-l (σ x))
  
  Esub : (σ* : TSub Δ₁ Δ₂) → ESub σ* Γ₁ Γ₂ → Expr Δ₁ Γ₁ T → Expr Δ₂ Γ₂ (Tsub σ* T)
  Esub σ* σ (# n) = # n
  Esub σ* σ (` x) = σ x
  Esub σ* σ (ƛ e) = ƛ Esub σ* (Eliftₛ σ* σ) e
  Esub σ* σ (e₁ · e₂) = Esub σ* σ e₁ · Esub σ* σ e₂
  Esub σ* σ (Λ l ⇒ e) = Λ l ⇒ Esub (Tliftₛ σ* _) (Eliftₛ-l σ* σ) e
  Esub σ* σ (_∙_ {T = T} e T′) = subst (Expr _ _) (sym {!!}) (Esub σ* σ e ∙ (Tsub σ* T′))
  -- Esub σ* σ (_∙_ {T = T} e T′) = subst (Expr _ _) (sym (ρT[T′]≡ρT[ρ↑T′] σ* T T′)) (Esub σ* σ e ∙ (Tren σ* T′))
  
  Eextₛ : (σ* : TSub Δ₁ Δ₂) → ESub σ* Γ₁ Γ₂ → Expr Δ₂ Γ₂ (Tsub σ* T) → ESub σ* (T ◁ Γ₁) Γ₂
  Eextₛ σ* σ e' here = e'
  Eextₛ σ* σ e' (there x) = σ x

  _[_]E : Expr Δ (T₁ ◁ Γ) T₂ → Expr Δ Γ T₁ → Expr Δ Γ T₂
  _[_]E {T₁ = T₁} {T₂ = T₂} e e′ = subst (Expr _ _) (TidₛT≡T T₂) (Esub Tidₛ (Eextₛ Tidₛ Eidₛ (subst (Expr _ _) (sym (TidₛT≡T T₁)) e′)) e)

ERen : TEnv Δ → TEnv Δ → Set
ERen {Δ} Γ₁ Γ₂ = ∀ {l} {T : Type Δ l} → inn T Γ₁ → inn T Γ₂

Eidᵣ : ERen Γ Γ 
Eidᵣ = id

Edropᵣ : ERen (T ◁ Γ₁) Γ₂ → ERen Γ₁ Γ₂
Edropᵣ ρ x = ρ (there x)

Ewkᵣ : ERen Γ₁ Γ₂ → ERen Γ₁ (T ◁ Γ₂) 
Ewkᵣ ρ x = there (ρ x) 

Eliftᵣ : ERen Γ₁ Γ₂ → ERen (T ◁ Γ₁) (T ◁ Γ₂)
Eliftᵣ ρ here = here
Eliftᵣ ρ (there x) = there (ρ x)

Eliftᵣ-l : ERen Γ₁ Γ₂ → ERen (l ◁* Γ₁) (l ◁* Γ₂)
Eliftᵣ-l ρ (tskip x) = tskip (ρ x) 

Eren : ERen Γ₁ Γ₂ → (Expr Δ Γ₁ T → Expr Δ Γ₂ T)
Eren ρ (# n) = # n
Eren ρ (` x) = ` ρ x
Eren ρ (ƛ e) = ƛ Eren (Eliftᵣ ρ) e
Eren ρ (e₁ · e₂) = Eren ρ e₁ · Eren ρ e₂
Eren ρ (Λ l ⇒ e) = Λ l ⇒ Eren (Eliftᵣ-l ρ) e
Eren ρ (e ∙ T′) = Eren ρ e ∙ T′

Ewk : Expr Δ Γ T → Expr Δ (T₁ ◁ Γ) T 
Ewk = Eren (Ewkᵣ Eidᵣ)

ESub : TEnv Δ → TEnv Δ → Set
ESub {Δ} Γ₁ Γ₂ = ∀ {l} {T : Type Δ l} → inn T Γ₁ → Expr Δ Γ₂ T
 
Eidₛ : ESub Γ Γ
Eidₛ = `_

Ewkₛ : ESub Γ₁ Γ₂ → ESub Γ₁ (T ◁ Γ₂)
Ewkₛ σ x = Ewk (σ x)

Edropₛ :  ESub (T ◁ Γ₁) Γ₂ → ESub Γ₁ Γ₂
Edropₛ σ x = σ (there x)

Eliftₛ : ESub Γ₁ Γ₂ → ESub (T ◁ Γ₁) (T ◁ Γ₂)
Eliftₛ σ here = ` here
Eliftₛ σ (there x) = Ewk (σ x)

Eliftₛ-l : ESub Γ₁ Γ₂ → ESub (l ◁* Γ₁) (l ◁* Γ₂)
Eliftₛ-l σ (tskip x) = Ewk-l (σ x)

Esub : ESub Γ₁ Γ₂ → Expr Δ Γ₁ T → Expr Δ Γ₂ T
Esub σ (# n) = # n
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
  v-n : Val {Δ}{Γ} (# n)
  v-ƛ : Val (ƛ e)
  v-Λ : Val (Λ l ⇒ e)


data _↪_ : Expr Δ Γ T → Expr Δ Γ T → Set where
  β-ƛ : 
     Val e₂ →
     ((ƛ e₁) · e₂) ↪ (e₁ [ e₂ ]E)
  β-Λ : ∀  {l l′ : Level} {T : Type Δ l} {T′ : Type (l ∷ Δ) l′} {e : Expr (l ∷ Δ) (l ◁* Γ) T′} →
     ((Λ l ⇒ e) ∙ T) ↪ (e [ T ]ET)
  ξ-·₁ :
    e₁ ↪ e →
    (e₁ · e₂) ↪ (e · e₂)
  ξ-·₂ : 
    e₂ ↪ e → 
    Val e₁ →
    (e₁ · e₂) ↪ (e₁ · e)
  ξ-∙ : ∀ {l l′ : Level} {T′ : Type Δ l′} {T : Type (l′ ∷ Δ) l} {e₁ e₂ : Expr Δ Γ (`∀α l′ , T)} →
    e₁ ↪ e₂ →
    (e₁ ∙ T′) ↪ (e₂ ∙ T′)

-- small-step continued

Sub-to-env : ∀{σ′ : TSub Δ₁ Δ₂} → Sub σ′ Γ₁ Γ₂ → Env Δ₂ Γ₂ η₂ → Env Δ₁ Γ₁ (subst-to-env* σ′ η₂)
Sub-to-env {η₂ = η₂} {σ′ = .Tidₛ} sub-id γ _ T x = 
  substω (λ η → ⟦ T ⟧ η) (symω (subst-to-env*-id η₂)) (γ _ _ x)
Sub-to-env {σ′ = .(Tliftₛ _ _)} (sub-lift-l σ) γ _ T x = {!   !}
Sub-to-env {σ′ = .(Textₛ _ _)} (sub-ext σ) γ _ T x = {!   !}
Sub-to-env {σ′ = σ′} (sub-lift-T σ) γ = {!   !}

ETRen* : {ρ′ : TRen Δ₁ Δ₂} (ρ : OPE ρ′ Γ₁ Γ₂) → (γ₁ : Env Δ₁ Γ₁ η₁) → (γ₂ : Env Δ₂ Γ₂ η₂) → (Tren* : TRen* ρ′ η₁ η₂)  → Setω
ETRen* {Δ₁ = Δ₁} {Γ₁ = Γ₁} {ρ′ = ρ′} ρ γ₁ γ₂ Tren* = ∀ {l} {T : Type Δ₁ l} → 
  (x : inn T Γ₁) → γ₂ l (Tren ρ′ T) (ETren-x ρ x) ≡ subst id (sym (Tren*-preserves-semantics Tren* T)) (γ₁ l T x)

ETren*-lift-T : {ρ′ : TRen Δ₁ Δ₂} {γ₁ : Env Δ₁ Γ₁ η₁} → {γ₂ : Env Δ₂ Γ₂ η₂} {Tren* : TRen* ρ′ η₁ η₂} → {T : Type Δ₁ l} 
  (⟦e⟧ : ⟦ Tren ρ′ T ⟧ η₂) → (ρ : OPE ρ′ Γ₁ Γ₂) → ETRen* ρ γ₁ γ₂ Tren* → 
  ETRen* (ope-lift-T {T = T} ρ) (extend γ₁ (subst id (Tren*-preserves-semantics Tren* T) ⟦e⟧)) (extend γ₂ ⟦e⟧) Tren*
ETren*-lift-T ⟦e⟧ ρ ETren* here = {!   !}
ETren*-lift-T ⟦e⟧ ρ ETren* (there x) = {!   !} 

ETren*-preserves-semantics : ∀ {T : Type Δ₁ l} {ρ′ : TRen Δ₁ Δ₂} {ρ : OPE ρ′ Γ₁ Γ₂}
  {γ₁ : Env Δ₁ Γ₁ η₁} {γ₂ : Env Δ₂ Γ₂ η₂} →
  (Tren* : TRen* ρ′ η₁ η₂) →
  (ETren* : ETRen* {ρ′ = ρ′} ρ γ₁ γ₂ Tren*) → (e : Expr Δ₁ Γ₁ T) → 
  E⟦ ETren ρ e ⟧ η₂ γ₂ ≡ subst id (sym (Tren*-preserves-semantics Tren* T)) (E⟦ e ⟧ η₁ γ₁)
ETren*-preserves-semantics Tren* ETren* (# n) = refl
ETren*-preserves-semantics Tren* ETren* (` x) = ETren* x
ETren*-preserves-semantics {ρ = ρ} Tren* ETren* (ƛ e) = fun-ext λ ⟦e⟧ → 
  {! ETren*-preserves-semantics {ρ = ope-lift-T ρ} Tren* (ETren*-lift-T ⟦e⟧ ρ ?) e !}
ETren*-preserves-semantics Tren* ETren* (e₁ · e₂) = {!   !}
ETren*-preserves-semantics Tren* ETren* (Λ l ⇒ e) = {!   !}
ETren*-preserves-semantics Tren* ETren* (e ∙ T′) = {!   !}

ETsubst-preserves : ∀ {T : Type Δ₁ l} {σ′ : TSub Δ₁ Δ₂} 
  (η₂ : Env* Δ₂) (γ₂ : Env Δ₂ Γ₂ η₂) → (σ : Sub σ′ Γ₁ Γ₂) → (e : Expr Δ₁ Γ₁ T) → 
  E⟦ ETsub σ e ⟧ η₂ γ₂ ≡ subst id (sym (subst-preserves σ′ T)) (E⟦ e ⟧ (subst-to-env* σ′ η₂) (Sub-to-env σ γ₂))
ETsubst-preserves η₂ γ₂ σ (# n) = refl
ETsubst-preserves η₂ γ₂ σ (` x) = {!   !}
ETsubst-preserves η₂ γ₂ σ (ƛ e) = {!   !}
ETsubst-preserves η₂ γ₂ σ (e · e₁) = {!   !}
ETsubst-preserves η₂ γ₂ σ (Λ l ⇒ e) = {!   !}
ETsubst-preserves η₂ γ₂ σ (e ∙ T′) = {!   !}

ERen* : (ρ : ERen Γ₁ Γ₂) → (γ₁ : Env Δ Γ₁ η) → (γ₂ : Env Δ Γ₂ η) → Setω
ERen* {Δ = Δ} {Γ₁ = Γ₁} ρ γ₁ γ₂ = ∀ {l} {T : Type Δ l} → 
  (x : inn T Γ₁) → γ₂ _ _ (ρ x) ≡ γ₁ _ _ x

Ewkᵣ∈ERen* : {T : Type Δ l} (⟦e⟧ : ⟦ T ⟧ η) → ERen* (Ewkᵣ {T = T} Eidᵣ) γ (extend γ ⟦e⟧)
Ewkᵣ∈ERen* ⟦e⟧ x = refl

Eren*-id : (γ : Env Δ Γ η) → ERen* Eidᵣ γ γ
Eren*-id γ x = refl

Eren*-lift : ∀ {ρ : ERen Γ₁ Γ₂} {T : Type Δ l} (⟦e⟧ : ⟦ T ⟧ η) → 
  ERen* ρ γ₁ γ₂ → ERen* (Eliftᵣ {T = T} ρ) (extend γ₁ ⟦e⟧) (extend γ₂ ⟦e⟧)
Eren*-lift ⟦e⟧ Eren* here = refl
Eren*-lift ⟦e⟧ Eren* (there x) = Eren* x

Eren*-lift-l : ∀ {ρ : ERen Γ₁ Γ₂} {γ₁ : Env Δ Γ₁ η} {γ₂ : Env Δ Γ₂ η} {l : Level} (⟦α⟧ : Set l) → 
  ERen* ρ γ₁ γ₂ → ERen* (Eliftᵣ-l {l = l} ρ) (extend-tskip {⟦α⟧ = ⟦α⟧} γ₁) (extend-tskip {⟦α⟧ = ⟦α⟧} γ₂)
Eren*-lift-l {η = η} ⟦α⟧ Eren* (tskip {T = T} x) 
  rewrite Tren*-preserves-semantics {ρ = Twkᵣ Tidᵣ} {η} {⟦α⟧ ∷ η} (wkᵣ∈Ren* η ⟦α⟧) T = Eren* x

Eren*-preserves-semantics : {ρ : ERen Γ₁ Γ₂} {γ₁ : Env Δ Γ₁ η} {γ₂ : Env Δ Γ₂ η} →
  (Eren* : ERen* ρ γ₁ γ₂) → (e : Expr Δ Γ₁ T) → E⟦ Eren ρ e ⟧ η γ₂ ≡ E⟦ e ⟧ η γ₁
Eren*-preserves-semantics Eren* (# n) = refl
Eren*-preserves-semantics Eren* (` x) = Eren* x
Eren*-preserves-semantics Eren* (ƛ e) = fun-ext λ ⟦e⟧ → 
  Eren*-preserves-semantics (Eren*-lift ⟦e⟧ Eren*) e
Eren*-preserves-semantics {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Eren* (e₁ · e₂) 
  rewrite Eren*-preserves-semantics {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Eren* e₁ |
          Eren*-preserves-semantics {ρ = ρ} {γ₁ = γ₁} {γ₂ = γ₂} Eren* e₂   
          = refl
Eren*-preserves-semantics Eren* (Λ l ⇒ e) = fun-ext λ ⟦α⟧ → 
  Eren*-preserves-semantics (Eren*-lift-l ⟦α⟧ Eren*) e
Eren*-preserves-semantics {η = η} Eren* (_∙_ {T = T} e T′) 
  rewrite Tsingle-subst-preserves η T′ T = cong-app (Eren*-preserves-semantics Eren* e) (⟦ T′ ⟧ η)

subst-to-env : ESub Γ₁ Γ₂ → Env Δ Γ₂ η → Env Δ Γ₁ η
subst-to-env {η = η} σ γ₂ _ _ x = E⟦ σ x ⟧ η γ₂

ste-dist-ext : ∀ (σ : ESub Γ₁ Γ₂) (T : Type Δ l) (⟦e⟧ : ⟦ T ⟧ η) (γ : Env Δ Γ₂ η) → 
  subst-to-env (Eliftₛ {T = T} σ) (extend {T = T} γ ⟦e⟧) ≡ω extend {T = T} (subst-to-env σ γ) ⟦e⟧
ste-dist-ext σ T ⟦e⟧ γ = fun-ext-lvl λ _ → fun-ext₂ λ where 
  _ here → refl
  _ (there x) → Eren*-preserves-semantics {ρ = Ewkᵣ Eidᵣ} (Ewkᵣ∈ERen* {γ = γ} {T = T} ⟦e⟧) (σ x)

ste-dist-ext-tskip : ∀ (σ : ESub Γ₁ Γ₂) (l : Level) (⟦α⟧ : Set l) (γ : Env Δ Γ₂ η) → 
  subst-to-env (Eliftₛ-l {l = l} σ) (extend-tskip {⟦α⟧ = ⟦α⟧} γ) ≡ω (extend-tskip {⟦α⟧ = ⟦α⟧} (subst-to-env σ γ))   
ste-dist-ext-tskip {Δ = Δ} {Γ₁ = Γ₁} {η = η} σ l ⟦α⟧ γ = fun-ext-lvl λ _ → fun-ext₂ λ { _ (tskip x) → 
  ETren*-preserves-semantics (wkᵣ∈Ren* η ⟦α⟧) {!   !} (σ x) }

Esubst-preserves : ∀ (γ : Env Δ Γ₂ η) → (σ : ESub Γ₁ Γ₂) (e : Expr Δ Γ₁ T)
  → E⟦ Esub σ e ⟧ η γ ≡ E⟦ e ⟧ η (subst-to-env σ γ)
Esubst-preserves γ σ (# n) = refl
Esubst-preserves γ σ (` x) = refl
Esubst-preserves {η = η} γ σ (ƛ_ {T = T} e) = fun-ext λ ⟦e⟧ → 
  trans (Esubst-preserves (extend γ ⟦e⟧) (Eliftₛ σ) e) 
        (congωl (E⟦ e ⟧ η) (ste-dist-ext σ T ⟦e⟧ γ))
Esubst-preserves γ σ (e₂ · e₁) rewrite Esubst-preserves γ σ e₁ | Esubst-preserves γ σ e₂ = refl
Esubst-preserves {η = η} γ σ (Λ l ⇒ e) = fun-ext λ ⟦α⟧ → 
  trans (Esubst-preserves (extend-tskip γ) (Eliftₛ-l σ) e) 
        (congωl (E⟦ e ⟧ (⟦α⟧ ∷ η)) (ste-dist-ext-tskip σ l ⟦α⟧ γ))
Esubst-preserves {η = η} γ σ (_∙_ {T = T} e T′) 
  rewrite Tsingle-subst-preserves η T′ T = cong-app (Esubst-preserves γ σ e) (⟦ T′ ⟧ η)

{-
E⟦ Esub (Eextₛ `_ e₂) e₁ ⟧ η γ ≡
      E⟦ e₁ ⟧ η (extend γ (E⟦ e₂ ⟧ η γ))
Have
E⟦ Esub (Eextₛ `_ e₂) e₁ ⟧ η γ ≡
      E⟦ e₁ ⟧ η (λ z z₁ x → E⟦ Eextₛ `_ e₂ x ⟧ η γ)
-}
Esingle-subst-preserves : ∀ (γ : Env Δ Γ η) (e₁ : Expr Δ (T′ ◁ Γ) T) (e₂ : Expr Δ Γ T′) →
  E⟦ e₁ [ e₂ ]E ⟧ η γ ≡ E⟦ e₁ ⟧ η (extend γ (E⟦ e₂ ⟧ η γ))  
Esingle-subst-preserves {η = η} γ e₁ e₂ = 
  substω (λ γ′ → E⟦ Esub (Eextₛ `_ e₂) e₁ ⟧ η γ ≡ E⟦ e₁ ⟧ η γ′) {! refl  !} 
  (Esubst-preserves γ (Eextₛ Eidₛ e₂) e₁)

adequacy : ∀ {e₁ e₂ : Expr Δ Γ T} → e₁ ↪ e₂ → E⟦ e₁ ⟧ η γ ≡ E⟦ e₂ ⟧ η γ
adequacy {γ = γ} (β-ƛ {e₂ = e₂} {e₁ = e₁} v₂) = sym (Esingle-subst-preserves γ e₁ e₂)
adequacy {η = η} (β-Λ {T = T} {T′ = T′}) = {!   !}
  -- rewrite Tsingle-subst-preserves η T T′ = ?
adequacy {η = η} {γ = γ} (ξ-·₁ {e₂ = e₂} e₁↪e) = cong-app (adequacy e₁↪e) (E⟦ e₂ ⟧ η γ)
adequacy {η = η} {γ = γ} (ξ-·₂ {e₁ = e₁} e₂↪e v₁) = cong (E⟦ e₁ ⟧ η γ) (adequacy e₂↪e)
adequacy {η = η} {γ = γ} (ξ-∙ {T′ = T′} {T = T} e₁↪e₂) 
  rewrite Tsingle-subst-preserves η T′ T = cong-app (adequacy e₁↪e₂) (⟦ T′ ⟧ η)  

----------------------------------------------------------------------

-- big step call by value semantics (analogous to Benton et al)

data Value : Type [] l → Set where
  V-ℕ : (n : ℕ) → Value `ℕ
  V-ƛ : ∀ {T : Type [] l}{T′ : Type [] l′} → Expr [] (T ◁ ∅) T′ → Value (T ⇒ T′)
  V-Λ : ∀ (l : Level) → {T : Type (l ∷ []) l′} → Expr (l ∷ []) (l ◁* ∅) T → Value (`∀α l , T)

variable v v₂ : Value T

exp : Value T → Expr [] ∅ T
exp (V-ℕ n) = # n
exp (V-ƛ e) = ƛ e
exp (V-Λ l e) = Λ l ⇒ e

-- connection to previous definition of value

Value-is-Val : (v : Value T) → Val (exp v)
Value-is-Val (V-ℕ x) = v-n
Value-is-Val (V-ƛ x) = v-ƛ
Value-is-Val (V-Λ l x) = v-Λ

Val-is-Value : Val e → ∃[ v ] exp v ≡ e
Val-is-Value {e = # n} v-n = V-ℕ n , refl
Val-is-Value {e = (ƛ e)} v-ƛ = (V-ƛ e) , refl
Val-is-Value {e = (Λ l ⇒ e)} v-Λ = (V-Λ l e) , refl

-- big step semantics

infix 15 _⇓_
data _⇓_ : Expr [] ∅ T → Value T → Set where
  ⇓-n : ∀ {n} → (# n) ⇓ V-ℕ n
  ⇓-ƛ : (ƛ e) ⇓ V-ƛ e
  ⇓-· : e₁ ⇓ V-ƛ e → e₂ ⇓ v₂ → (e [ exp v₂ ]E) ⇓ v → (e₁ · e₂) ⇓ v
  ⇓-Λ : (Λ l ⇒ e) ⇓ V-Λ l e
  ⇓-∙ : e₁ ⇓ V-Λ l e → (e [ T ]ET) ⇓ v → (e₁ ∙ T) ⇓ v

exp-v⇓v : ∀ (v : Value T) → exp v ⇓ v
exp-v⇓v (V-ℕ x) = ⇓-n
exp-v⇓v (V-ƛ x) = ⇓-ƛ
exp-v⇓v (V-Λ l x) = ⇓-Λ

variable v′ v′₂ : Expr [] ∅ T
infix 15 _⇓′_
data _⇓′_ : Expr [] ∅ T → Expr [] ∅ T → Set where
  ⇓-ƛ : ƛ e ⇓′ ƛ e
  ⇓-· : e₁ ⇓′ ƛ e → e₂ ⇓′ v′₂ → (e [ v′₂ ]E) ⇓′ v′ → (e₁ · e₂) ⇓′ v′
  ⇓-Λ : Λ l ⇒ e ⇓′ Λ l ⇒ e
  ⇓-∙ : e₁ ⇓′ Λ l ⇒ e → e [ T ]ET ⇓′ v′ → (e₁ ∙ T) ⇓′ v′

⇓-value : e ⇓′ v′ → Val v′
⇓-value ⇓-ƛ = v-ƛ
⇓-value (⇓-· e⇓′v′ e⇓′v′₁ e⇓′v′₂) = ⇓-value e⇓′v′₂
⇓-value ⇓-Λ = v-Λ
⇓-value (⇓-∙ e⇓′v′ e⇓′v′₁) = ⇓-value e⇓′v′₁

-- soundness

zero-env : Env [] ∅ []
zero-env l T ()

soundness : e ⇓ v → E⟦ e ⟧ [] zero-env ≡ E⟦ exp v ⟧ [] zero-env
soundness ⇓-n = refl
soundness ⇓-ƛ = refl
soundness (⇓-· {e = e} {v₂ = v₂} p p₁ p₂)
  with soundness p | soundness p₁
... | sound-p | sound-p₁
  rewrite sound-p | sound-p₁
  with soundness p₂
... | sound-p₂ = trans (sym (Esingle-subst-preserves zero-env e (exp v₂))) sound-p₂
soundness ⇓-Λ = refl
soundness (⇓-∙ p p₁)
  with soundness p | soundness p₁
... | sound-p | sound-p₁ = trans {! !} sound-p₁

-- adequacy

infixl 10 _∧_
_∧_ = _×_

-- logical relation

REL : Type [] l → Set (suc l)
REL {l} T = Value T → ⟦ T ⟧ [] → Set l 

RelEnv : LEnv → Setω
RelEnv Δ = ∀ l → l ∈ Δ → Σ (Type [] l) REL

REdrop : RelEnv (l ∷ Δ) → RelEnv Δ
REdrop ρ l x = ρ l (there x)

REext : RelEnv Δ → (Σ (Type [] l) REL) → RelEnv (l ∷ Δ)
REext ρ R _ here = R
REext ρ R _ (there x) = ρ _ x

subst←RE : RelEnv Δ → TSub Δ []
subst←RE ρ l x = proj₁ (ρ l x)

subst←RE-ext : ∀ (ρ : RelEnv Δ) (T : Type [] l) (R : REL T) (l′ : Level) (x : l′ ∈ (l ∷ Δ)) → subst←RE (REext ρ (T , R)) l′ x ≡ Textₛ (subst←RE ρ) T l′ x
subst←RE-ext ρ T R l here = refl
subst←RE-ext ρ T R l (there x) = refl

subst←RE-ext-ext : ∀ (ρ : RelEnv Δ) (T : Type [] l) (R : REL T) → subst←RE (REext ρ (T , R)) ≡ Textₛ (subst←RE ρ) T
subst←RE-ext-ext ρ T R = fun-ext₂ (subst←RE-ext ρ T R)


subst←RE-drop : ∀ (ρ : RelEnv (l ∷ Δ)) →
  (l′ : Level) (x : l′ ∈ Δ) → (subst←RE (REdrop ρ)) l′ x ≡ (Tdropₛ (subst←RE ρ)) l′ x
subst←RE-drop ρ l′ here = refl
subst←RE-drop ρ l′ (there x) = refl

subst←RE-drop-ext : ∀ (ρ : RelEnv (l ∷ Δ)) →
  (subst←RE (REdrop ρ)) ≡ (Tdropₛ (subst←RE ρ))
subst←RE-drop-ext ρ = fun-ext₂ (subst←RE-drop ρ)

-- special case of composition sub o ren

sublemma : (σ : TSub Δ []) → (Textₛ σ T) ≡ Tliftₛ σ _ ∘ₛₛ Textₛ Tidₛ T
sublemma {T = T} σ = fun-ext₂ λ where 
  _ here → refl
  _ (there x) → begin 
        σ _ x
      ≡⟨ sym (TidₛT≡T (σ _ x)) ⟩
        Tsub Tidₛ (σ _ x)
      ≡⟨ sym (assoc-sub-ren (σ _ x) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T)) ⟩
        Tsub (Textₛ Tidₛ T) (Twk (σ _ x)) 
      ∎

lemma2 : (σ : TSub Δ []) → (T  : Type (l ∷ Δ) l′) → (T′ : Type [] l)
  → Tsub (Tliftₛ σ l) T [ T′ ]T ≡ Tsub (Textₛ σ T′) T
lemma2 σ T T′ = begin 
    Tsub (Textₛ Tidₛ T′) (Tsub (Tliftₛ σ _) T)
  ≡⟨ assoc-sub-sub T (Tliftₛ σ _) (Textₛ Tidₛ T′) ⟩
    Tsub (Tliftₛ σ _ ∘ₛₛ Textₛ Tidₛ T′) T
  ≡⟨ cong (λ σ → Tsub σ T) (sym (sublemma σ)) ⟩
    Tsub (Textₛ σ T′) T
  ∎
   

lemma1 : (ρ  : RelEnv Δ) → (T  : Type (l ∷ Δ) l′) → (T′ : Type [] l) → (R  : REL T′)
  → Tsub (Tliftₛ (subst←RE ρ) l) T [ T′ ]T ≡ Tsub (subst←RE (REext ρ (T′ , R))) T
lemma1 {l = l} ρ T T′ R =
  begin
    Tsub (Tliftₛ (subst←RE ρ) l) T [ T′ ]T
    ≡⟨ lemma2 (subst←RE ρ) T T′ ⟩
    Tsub (Textₛ (subst←RE ρ) T′) T
    ≡⟨ cong (λ G → Tsub G T) (sym (subst←RE-ext-ext ρ T′ R)) ⟩
    Tsub (subst←RE (REext ρ (T′ , R))) T
    ∎

-- stratified logical relation

LRV : (T : Type Δ l) → (ρ : RelEnv Δ) → Value (Tsub (subst←RE ρ) T) → ⟦ T ⟧ (subst-to-env* (subst←RE ρ) []) → Set l
LRV `ℕ ρ (V-ℕ n) x =
  n ≡ x
LRV (` α) ρ v x =
  proj₂ (ρ _ α) v (subst id (sym (subst-var-preserves α (subst←RE ρ) [])) x)
LRV (T ⇒ T′)    ρ (V-ƛ e)    f =
  ∀ (w : Value (Tsub (subst←RE ρ) T)) →
  ∀ (x : ⟦ T ⟧ (subst-to-env* (subst←RE ρ) [])) →
  LRV T ρ w x →
  ∃[ v ] (e [ exp w ]E ⇓ v)
       ∧ LRV T′ ρ v (f x)
LRV (`∀α l , T) ρ (V-Λ .l e) F =
  ∀ (T′ : Type [] l) →
  ∀ (R : REL T′) →
  ∃[ v ] (e [ T′ ]ET ⇓ v)
       ∧ let ρ′ = REext ρ (T′ , R)
         in LRV T ρ′ (subst Value (lemma1 ρ T T′ R) v) (F (⟦ T′ ⟧ []))

-- closing value substitution

module extended2 where
  open extended

  variable σ* : TSub Δ []

  VSub : {Γ₁ : TEnv Δ₁} → extended.ESub σ* Γ₁ Γ₂ → Set
  VSub {Δ₁ = Δ₁} {Γ₁ = Γ₁} σ = ∀ {l} {T : Type Δ₁ l} → (x : inn T Γ₁) → Val (σ x)

  CSub : TSub Δ [] → TEnv Δ → Set
  CSub {Δ} σ* Γ = Σ (extended.ESub σ* Γ ∅) VSub

  Csub : {Γ : TEnv Δ} {σ* : TSub Δ []} → CSub σ* Γ → Expr Δ Γ T → Expr [] ∅ (Tsub σ* T)
  Csub {σ* = σ*} ( χ₁ , χ₂ ) e = extended.Esub σ* χ₁ e

  Cdrop : CSub σ* (T ◁ Γ) → CSub σ* Γ
  Cdrop (χ₁ , χ₂) = (χ₁ ∘ there , χ₂ ∘ there)
  
  Cdropt : {Γ : TEnv Δ} → CSub σ (l ◁* Γ) → CSub (Tdropₛ σ) Γ
  Cdropt {σ = σ} (χ₁ , χ₂) = (λ {l} {T} x → {!!}) , {!!}

  ----------

  CSub′ : TSub Δ [] → TEnv Δ → Set
  CSub′ {Δ} σ* Γ = ∀ {l} {T : Type Δ l} → inn T Γ → Σ (Expr [] ∅ (Tsub σ* T)) Val

  Csub′ : {Γ : TEnv Δ} {σ* : TSub Δ []} → CSub′ σ* Γ → Expr Δ Γ T → Expr [] ∅ (Tsub σ* T)
  Csub′ {σ* = σ*} χ e = extended.Esub σ* (proj₁ ∘ χ) e

  Cdrop′ : CSub′ σ* (T ◁ Γ) → CSub′ σ* Γ
  Cdrop′ χ = χ ∘ there
  
  Cdropt′ : {Γ : TEnv Δ} → CSub′ σ* (l ◁* Γ) → CSub′ (Tdropₛ σ*) Γ
  Cdropt′ {σ* = σ*} χ {l}{T} x = subst (λ T → Σ (Expr [] ∅ T) Val) (assoc-sub-ren T (Twkᵣ Tidᵣ) σ*) (χ (tskip x))

  Cextt′ : ∀{l} → CSub′ σ* Γ → (T′ : Type [] l) → CSub′ (Textₛ σ* T′) (l ◁* Γ)
  Cextt′ {σ* = σ*} χ T′ (tskip {T = T} x) = subst (λ T → Σ (Expr [] ∅ T) Val) (sym (σT≡TextₛσTwkT σ* T)) (χ x)


CSub : TSub Δ [] → TEnv Δ → Set
CSub {Δ} σ Γ = ∀ {l} {T : Type Δ l} → inn T Γ → Value (Tsub σ T)

-- doesn't work
Csub : {Γ : TEnv Δ} → CSub σ Γ → Expr Δ Γ T → Expr [] ∅ (Tsub σ T)
Csub χ (# n) = # n
Csub χ (` x) = exp (χ x)
Csub χ (ƛ e) = ƛ {!!}
Csub χ (e₁ · e₂) = Csub χ e₁ · Csub χ e₂
Csub χ (Λ l ⇒ e) = {!!}
Csub χ (e ∙ T′) = {!!}

Cdrop : CSub σ (T ◁ Γ) → CSub σ Γ
Cdrop χ x = χ (there x)

Cdropt : {Γ : TEnv Δ} → CSub σ (l ◁* Γ) → CSub (Tdropₛ σ) Γ
Cdropt {σ = σ} χ {l} {T} x = subst Value (assoc-sub-ren T (Twkᵣ Tidᵣ) σ) (χ (tskip x))

Cextt : ∀{l} → CSub σ Γ → (T′ : Type [] l) → CSub (Textₛ σ T′) (l ◁* Γ)
Cextt {σ = σ} χ T′ (tskip {T = T} x) = subst Value (sym (σT≡TextₛσTwkT σ T)) (χ x)

Gdropt : (σ : TSub (l ∷ Δ) [])
  → Env (l ∷ Δ) (l ◁* Γ) (subst-to-env* σ [])
  → Env Δ Γ (subst-to-env* (Tdropₛ σ) [])
Gdropt σ γ l T x =
  let r = γ l (Twk T) (tskip x) in
  subst id (Tren*-preserves-semantics {ρ = Twkᵣ Tidᵣ} {subst-to-env* (Tdropₛ σ) []} {subst-to-env* σ []} (wkᵣ∈Ren* (subst-to-env* (Tdropₛ σ) []) (⟦ σ _ here ⟧ [])) T) r

exprTy : {T : Type Δ l} → Expr Δ Γ T → Type Δ l
exprTy {T = T} e = T

levelTy : Type Δ l → Level
levelTy {l = l} T = l

levelEnv : TEnv Δ → Level
levelEnv ∅ = zero
levelEnv (T ◁ Γ) = levelTy T ⊔ levelEnv Γ
levelEnv (l ◁* Γ) = levelEnv Γ

ENVdrop : (Γ : TEnv Δ) → (η : Env* Δ) → Env Δ (T ◁ Γ) η → Env Δ Γ η
ENVdrop Γ η γ l T x = γ l T (there x)

-- extended LR on environments

LRG : (Γ : TEnv Δ) → (ρ : RelEnv Δ) → CSub (subst←RE ρ) Γ → let η = subst-to-env* (subst←RE ρ) [] in Env Δ Γ η → Set (levelEnv Γ)
LRG ∅ ρ χ γ = ⊤
LRG (T ◁ Γ) ρ χ γ = LRV T ρ (χ here) (γ _ T here) ∧  LRG Γ ρ (Cdrop χ) (ENVdrop Γ _ γ)
LRG (l ◁* Γ) ρ χ γ
  rewrite sym (subst←RE-drop-ext ρ) = LRG Γ (REdrop ρ) (Cdropt χ) (Gdropt (subst←RE ρ) γ)

LRV←LRG : (Γ : TEnv Δ) (ρ : RelEnv Δ) (χ : CSub (subst←RE ρ) Γ) (γ : Env Δ Γ (subst-to-env* (subst←RE ρ) [])) (T : Type Δ l) → LRG Γ ρ χ γ →
  (x : inn T Γ) → LRV T ρ (χ x) (γ l T x)
LRV←LRG .(T ◁ _) ρ χ γ T (lrv , lrg) here = lrv
LRV←LRG (_ ◁ Γ) ρ χ γ T (lrv , lrg) (there x) = LRV←LRG _ ρ (Cdrop χ) (ENVdrop Γ _ γ) T lrg x
LRV←LRG {l = l} (_ ◁* Γ) ρ χ γ Tw lrg (tskip x)
  rewrite sym (subst←RE-drop-ext ρ) = LRV←LRG {l = l} Γ (REdrop ρ) (Cdropt χ) (Gdropt (subst←RE ρ) γ) {!!} lrg {!x!}

-- fundamental theorem
-- need function to apply closing substitution χ to expression e

fundamental : ∀ (Γ : TEnv Δ) (ρ : RelEnv Δ) (χ : CSub (subst←RE ρ) Γ) → let η = subst-to-env* (subst←RE ρ) [] in (γ : Env Δ Γ η) →
  ∀ (T : Type Δ l) (e : Expr Δ Γ T) →
  LRG Γ ρ χ γ → ∃[ v ] (Csub χ e ⇓ v) ∧ LRV T ρ v (E⟦ e ⟧ η γ)
fundamental Γ ρ χ γ T (` x) lrg = χ x , exp-v⇓v (χ x) , {!!}
fundamental Γ ρ χ γ `ℕ (# n) lrg = V-ℕ n , ⇓-n , refl
fundamental Γ ρ χ γ (T ⇒ T′) (ƛ e) lrg =
  V-ƛ {!!} ,
  ⇓-ƛ ,
  (λ w x lrv-w-x → fundamental (T ◁ Γ) ρ {!!} (extend γ x) T′ e (lrv-w-x , lrg))
fundamental Γ ρ χ γ T (_·_ {T = T₂}{T′ = .T} e₁ e₂) lrg
  with fundamental Γ ρ χ γ (T₂ ⇒ T) e₁ lrg | fundamental Γ ρ χ γ T₂ e₂ lrg
... | V-ƛ e₃ , e₁⇓v₁ , lrv₁ | v₂ , e₂⇓v₂ , lrv₂
  with lrv₁ v₂ (E⟦ e₂ ⟧ (subst-to-env* (subst←RE ρ) []) γ) lrv₂
... | v₃ , e₃[]⇓v₃ , lrv₃
  = v₃ , (⇓-· e₁⇓v₁ e₂⇓v₂ e₃[]⇓v₃) , lrv₃
fundamental Γ ρ χ γ (`∀α l , T) (Λ .l ⇒ e) lrg =
  V-Λ l {!!} ,
  ⇓-Λ ,
  λ T′ R → fundamental (l ◁* Γ)
                       (REext ρ (T′ , R))
                       (subst (λ σ → CSub σ (l ◁* Γ)) (sym (subst←RE-ext-ext ρ T′ R)) (Cextt χ T′))
                       {!!}
                       {!T!}
                       {!e!}
                       {!!}
fundamental Γ ρ χ γ .(_ [ T′ ]T) (_∙_ {T = T} e T′) lrg = {!!}
