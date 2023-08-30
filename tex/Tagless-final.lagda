\begin{code}[hide]
module Tagless-final where

open import Level
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ) renaming (zero to zeroℕ; suc to sucℕ)
open import Data.List using (List; []; _∷_; _++_; length; lookup; tabulate)
open import Data.Unit
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

----------------------------------------------------------------------
postulate
\end{code}
\newcommand\TFDependentExt{%
\begin{code}
  ∀-extensionality :
    ∀ {a b}{A : Set a}{F G : (α : A) → Set b}
    → (∀ (α : A) → F α ≡ G α)
    → ((α : A) → F α) ≡ ((α : A) → G α)
\end{code}}
\begin{code}[hide]
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

variable Δ Δ₁ Δ₂ : List Level
variable l l′ ℓ ℓ′ : Level

-- types
module systemf where
\end{code}
\newcommand\SFType{%
\begin{code}
  data Type (Δ : ℕ) : Set where
    nat : Type Δ
    _⇒_ : Type Δ → Type Δ → Type Δ
    `_  : Fin Δ → Type Δ
    `∀  : Type (sucℕ Δ) → Type Δ
\end{code}}
\begin{code}[hide]
LEnv = List Level
\end{code}
\newcommand\TFType{%
\begin{code}
data Type (Δ : List Level) : Level → Set where
  nat : Type Δ zero
  _⇒_ : Type Δ ℓ → Type Δ ℓ′ → Type Δ (ℓ ⊔ ℓ′)
  `_  : ℓ ∈ Δ → Type Δ ℓ
  `∀  : ∀ ℓ → Type (ℓ ∷ Δ) ℓ′ → Type Δ (suc ℓ ⊔ ℓ′)
\end{code}}
\newcommand\TFlevel{%
\begin{code}
-- level of type according to Leivant'91
level : Type Δ ℓ → Level
level {ℓ = ℓ} T = ℓ
\end{code}}
\begin{code}[hide]
-- semantic environments (mapping level ℓ to an element of Set ℓ)
\end{code}
\newcommand\TFTEnv{%
\begin{code}
data DEnv : List Level → Setω where
  []  : DEnv []
  _∷_ : Set ℓ → DEnv Δ → DEnv (ℓ ∷ Δ)
\end{code}}
\newcommand\TFTEnvP{%
\begin{code}
-- meaning of a type variable α
DEnv′ : List Level → Setω
DEnv′ Δ = ∀ {ℓ} → (α : ℓ ∈ Δ) → Set ℓ
\end{code}}
\begin{code}[hide]
apply-env : DEnv Δ → ℓ ∈ Δ → Set ℓ
apply-env [] ()
apply-env (x ∷ _) here = x
apply-env (_ ∷ η) (there x) = apply-env η x

ext-env : Set ℓ → DEnv Δ → DEnv (ℓ ∷ Δ)
ext-env D η = D ∷ η

ext-env′ : Set ℓ → DEnv′ Δ → DEnv′ (ℓ ∷ Δ)
ext-env′ D η here = D
ext-env′ D η (there α) = η α

-- the meaning of a stratified type in terms of Agda universes
\end{code}
\newcommand\TFTSem{%
\begin{code}
𝓣⟦_⟧ : Type Δ ℓ → DEnv Δ → Set ℓ
𝓣⟦ nat ⟧ η = ℕ
𝓣⟦ T₁ ⇒ T₂ ⟧ η = 𝓣⟦ T₁ ⟧ η → 𝓣⟦ T₂ ⟧ η
𝓣⟦ ` α ⟧ η = apply-env η α
𝓣⟦ `∀ ℓ T ⟧ η = (D : Set ℓ) → 𝓣⟦ T ⟧ (ext-env D η)
\end{code}}
\newcommand\TFTSemP{%
\begin{code}
-- meaning of a type
𝓣′⟦_⟧ : Type Δ ℓ → DEnv′ Δ → Set ℓ
𝓣′⟦ nat ⟧ η = ℕ
𝓣′⟦ T₁ ⇒ T₂ ⟧ η = 𝓣′⟦ T₁ ⟧ η → 𝓣′⟦ T₂ ⟧ η
𝓣′⟦ ` α ⟧ η = η α
𝓣′⟦ `∀ ℓ T ⟧ η = (D : Set ℓ) → 𝓣′⟦ T ⟧ (ext-env′ D η)
\end{code}}
\begin{code}[hide]
-- renaming on types

TRen : LEnv → LEnv → Set
TRen Δ₁ Δ₂ = ∀ {ℓ} → ℓ ∈ Δ₁ → ℓ ∈ Δ₂

wkᵣ : TRen Δ (ℓ ∷ Δ)
wkᵣ = there

extᵣ : TRen Δ₁ Δ₂ → TRen (ℓ ∷ Δ₁) (ℓ ∷ Δ₂)
extᵣ ρ here = here
extᵣ ρ (there x) = there (ρ x)

Tren : TRen Δ₁ Δ₂ → (Type Δ₁ ℓ → Type Δ₂ ℓ)
Tren ρ (` x) = ` ρ x
Tren ρ (T₁ ⇒ T₂) = Tren ρ T₁ ⇒ Tren ρ T₂
Tren ρ (`∀ lev T) = `∀ lev (Tren (extᵣ ρ) T)
Tren ρ nat = nat

Tweaken : Type Δ ℓ′ → Type (ℓ ∷ Δ) ℓ′
Tweaken = Tren wkᵣ

-- the action of renaming on semantic environments

TRen* : (ρ : TRen Δ₁ Δ₂) → (η₁ : DEnv Δ₁) → (η₂ : DEnv Δ₂) → Setω
TRen* {Δ₁} ρ η₁ η₂ = ∀ {ℓ : Level} → (x : ℓ ∈ Δ₁) → apply-env η₂ (ρ x) ≡ apply-env η₁ x

wkᵣ∈TRen* : ∀ (η : DEnv Δ) (D : Set ℓ)
  → TRen* (wkᵣ{Δ}{ℓ}) η (D ∷ η)
wkᵣ∈TRen* η D x = refl

ren*-id : (η : DEnv Δ) → TRen* id η η
ren*-id η x = refl

ren*-pop : (ρ : TRen (ℓ ∷ Δ₁) Δ₂) (α : Set ℓ) (η₁ : DEnv Δ₁) (η₂ : DEnv Δ₂)
  → TRen* ρ (α ∷ η₁) η₂
  → TRen* (ρ ∘ there) η₁ η₂
ren*-pop ρ α η₁ η₂ ren* x = ren* (there x)

ren*-ext : ∀ {ρ : TRen Δ₁ Δ₂}{η₁ : DEnv Δ₁}{η₂ : DEnv Δ₂} (D : Set ℓ)
  → TRen* ρ η₁ η₂
  → TRen* (extᵣ ρ) (D ∷ η₁) (D ∷ η₂)
ren*-ext D ren* here = refl
ren*-ext D ren* (there x) = ren* x
\end{code}
\newcommand\TFRenPreserverSemanticsType{%
\begin{code}
ren*-preserves-semantics :
  ∀ {ρ : TRen Δ₁ Δ₂}{η₁ : DEnv Δ₁}{η₂ : DEnv Δ₂}
  → (ren* : TRen* ρ η₁ η₂) → (T : Type Δ₁ ℓ)
  → 𝓣⟦ Tren ρ T ⟧ η₂ ≡ 𝓣⟦ T ⟧ η₁
\end{code}}
\begin{code}[hide]
ren*-preserves-semantics ren* nat = refl
ren*-preserves-semantics ren* (` x) = ren* x
ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* (T₁ ⇒ T₂)
  = cong₂ (λ t₁ t₂ → (t₁ → t₂))
          (ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* T₁)
          (ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* T₂)
ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* (`∀ ℓ T) =
  ∀-extensionality (λ α →
    ren*-preserves-semantics{ρ = extᵣ ρ}{α ∷ η₁}{α ∷ η₂} (ren*-ext{ρ = ρ} α ren*) T)

postulate 
  problematic-goal : 
    ∀ {ℓ′}{Δ₁ Δ₂ : LEnv}{ρ : TRen Δ₁ Δ₂}{η₁ : DEnv Δ₁}{η₂ : DEnv Δ₂}
    → (ren* : TRen* ρ η₁ η₂) →
\end{code}
\newcommand\TFProblematicGoal{%
\begin{code}
    (T : Type (ℓ ∷ Δ₁) ℓ′) →
    ((D : Set ℓ) → 𝓣⟦ Tren (extᵣ ρ) T ⟧ (D ∷ η₂)) ≡
       ((D : Set ℓ) → 𝓣⟦ T ⟧ (D ∷ η₁))
\end{code}}
\begin{code}[hide]
-- substitution on types

data Sub : LEnv → LEnv → Set where
  []  : Sub [] Δ₂
  _∷_ : Type Δ₂ ℓ → Sub Δ₁ Δ₂ → Sub (ℓ ∷ Δ₁) Δ₂

apply-sub : Sub Δ₁ Δ₂ → ℓ ∈ Δ₁ → Type Δ₂ ℓ
apply-sub (T ∷ _) here = T
apply-sub (_ ∷ σ) (there x) = apply-sub σ x

build-id : (Δ₁ : LEnv) → TRen Δ₁ Δ → Sub Δ₁ Δ
build-id [] ρ = []
build-id (ℓ ∷ Δ₁) ρ = (` ρ here) ∷ build-id Δ₁ (ρ ∘ there)

idₛ : Sub Δ Δ
idₛ {Δ} = build-id Δ id

wkₛ : Sub Δ₁ Δ₂ → Sub Δ₁ (ℓ ∷ Δ₂)
wkₛ [] = []
wkₛ (T ∷ σ) = Tweaken T ∷ wkₛ σ

extₛ : Sub Δ₁ Δ₂ → ∀ {ℓ} → Sub (ℓ ∷ Δ₁) (ℓ ∷ Δ₂)
extₛ σ = ` here ∷ wkₛ σ

subT : Sub Δ₁ Δ₂ → Type Δ₁ ℓ → Type Δ₂ ℓ
subT σ nat = nat
subT σ (` α) = apply-sub σ α
subT σ (T₁ ⇒ T₂) = subT σ T₁ ⇒ subT σ T₂
subT σ (`∀ ℓ T) = `∀ ℓ (subT (extₛ σ) T)

singleₛ : Sub Δ₁ Δ₂ → ∀ {ℓ} → Type Δ₂ ℓ → Sub (ℓ ∷ Δ₁) Δ₂
singleₛ σ T' = T' ∷ σ

_[_]T : Type (ℓ ∷ Δ) ℓ′ → Type Δ ℓ → Type Δ ℓ′
_[_]T T T' = subT (singleₛ idₛ T') T

-- type environments
\end{code}
\newcommand\TFTVEnv{%
\begin{code}
data TEnv : List Level → Set where
  ∅    : TEnv []
  _◁_  : Type Δ ℓ → TEnv Δ → TEnv Δ  -- type binding
  _◁*_ : ∀ ℓ → TEnv Δ → TEnv (ℓ ∷ Δ) -- level binding
\end{code}}
\begin{code}[hide]
module cleaner-expressions where
  variable
    T : Type Δ ℓ
    T′ : Type Δ ℓ′
    Γ : TEnv Δ
\end{code}
\newcommand\TFCleanerinn{%
\begin{code}
  -- term variables
  data inn : Type Δ ℓ → TEnv Δ → Set where
    here  : inn T (T ◁ Γ)
    there : inn T Γ → inn T (T′ ◁ Γ)
    tskip : inn T Γ → inn (Tweaken T) (ℓ′ ◁* Γ)
\end{code}}
\newcommand\TFCleanExpr{%
\begin{code}
  data Expr {Δ} (Γ : TEnv Δ) : Type Δ ℓ → Set where

    Λ    : ∀ (ℓ : Level)
         → {T : Type (ℓ ∷ Δ) ℓ′}
         → Expr (ℓ ◁* Γ) T
           ---------------------
         → Expr Γ (`∀ ℓ T)

    _∙_  : ∀ {T : Type (ℓ ∷ Δ) ℓ′}
         → Expr Γ (`∀ ℓ T)
         → (T′ : Type Δ ℓ)
           -----------------------
         → Expr Γ (T [ T′ ]T)
\end{code}}
\newcommand\TFinn{%
\begin{code}
data inn : Type Δ ℓ → TEnv Δ → Set where
  here  : ∀ {T : Type Δ ℓ}{Γ}
        → inn T (T ◁ Γ)
  there : ∀ {T : Type Δ ℓ}{T′ : Type Δ ℓ′}{Γ}
        → inn T Γ → inn T (T′ ◁ Γ)
  tskip : ∀ {T : Type Δ ℓ}{Γ}
        → inn T Γ → inn (Tweaken T) (ℓ′ ◁* Γ)
\end{code}}
\newcommand\TFExpr{%
\begin{code}
data Expr {Δ : List Level} (Γ : TEnv Δ) : Type Δ ℓ → Set where
  #_   : ∀ (n : ℕ) → Expr Γ nat
  `_   : ∀ {T : Type Δ ℓ}
       → inn T Γ → Expr Γ T
  ƛ_   : ∀ {T : Type Δ ℓ}{T′ : Type Δ ℓ′}
       → Expr (T ◁ Γ) T′ → Expr Γ (T ⇒ T′)
  _·_  : ∀ {T : Type Δ ℓ}{T′ : Type Δ ℓ′}
       → Expr Γ (T ⇒ T′) → Expr Γ T → Expr Γ T′
  Λ    : ∀ (ℓ : Level) → {T : Type (ℓ ∷ Δ) ℓ′}
       → Expr (ℓ ◁* Γ) T → Expr Γ (`∀ ℓ T)
  _∙_  : ∀ {T : Type (ℓ ∷ Δ) ℓ′}
       → Expr Γ (`∀ ℓ T) → (T′ : Type Δ ℓ)
       → Expr Γ (T [ T′ ]T)
\end{code}}
\begin{code}[hide]
-- value environments
\end{code}
\newcommand\TFVEnv{%
\begin{code}
Env : ∀ {Δ : List Level} → TEnv Δ → DEnv Δ → Setω
Env {Δ} Γ η = ∀ {ℓ}{T : Type Δ ℓ} → inn T Γ → 𝓣⟦ T ⟧ η
\end{code}}
\begin{code}[hide]
extend : ∀ {T : Type Δ ℓ}{Γ : TEnv Δ}{η : DEnv Δ}
  → Env Γ η
  → 𝓣⟦ T ⟧ η
  → Env (T ◁ Γ) η
extend γ v here = v
extend γ v (there x) = γ x
\end{code}
\newcommand\TFExtendTskip{%
\begin{code}
extend-tskip : ∀ {Δ : LEnv}{Γ : TEnv Δ}{η : DEnv Δ}{D : Set ℓ}
  → Env Γ η → Env (ℓ ◁* Γ) (D ∷ η)
extend-tskip {η = η} {D = D} γ (tskip{T = T} x) =
  subst id (sym (ren*-preserves-semantics {ρ = wkᵣ}{η}{D ∷ η}
                (wkᵣ∈TRen* η D) T))
           (γ x)
\end{code}}
\begin{code}[hide]
subst-to-env* : (σ : Sub Δ₁ Δ₂) → (η₂ : DEnv Δ₂) → DEnv Δ₁
subst-to-env* [] η₂ = []
subst-to-env* (T ∷ σ) η₂ = 𝓣⟦ T ⟧ η₂ ∷ subst-to-env* σ η₂

subst-var-preserves : (α : ℓ ∈ Δ₁) (σ : Sub Δ₁ Δ₂) (η₂ : DEnv Δ₂)
  → 𝓣⟦ apply-sub σ α ⟧ η₂ ≡ apply-env (subst-to-env* σ η₂) α
subst-var-preserves here (T ∷ σ) η₂ = refl
subst-var-preserves (there α) (_ ∷ σ) η₂ = subst-var-preserves α σ η₂

subst-to-env*-wk : (σ : Sub Δ₁ Δ₂) (D : Set ℓ) (η₂ : DEnv Δ₂)
  → subst-to-env* (wkₛ σ) (D ∷ η₂) ≡ω subst-to-env* σ η₂
subst-to-env*-wk [] D η₂ = refl
subst-to-env*-wk (T ∷ σ) D η₂
  rewrite ren*-preserves-semantics {ρ = wkᵣ}{η₂}{D ∷ η₂} (wkᵣ∈TRen* η₂ D) T
  = congωω (𝓣⟦ T ⟧ η₂ ∷_) (subst-to-env*-wk σ D η₂)

subst-to-env*-build : ∀ (ρ : TRen Δ₁ Δ₂) (η₁ : DEnv Δ₁) (η₂ : DEnv Δ₂)
  → TRen* ρ η₁ η₂
  → subst-to-env* (build-id Δ₁ ρ) η₂ ≡ω η₁
subst-to-env*-build ρ [] η₂ ren* = refl
subst-to-env*-build {Δ₁ = _ ∷ Δ₁} ρ (D ∷ η₁) η₂ ren* = 
  transω (congωω (apply-env η₂ (ρ here) ∷_) (subst-to-env*-build (ρ ∘ there) η₁ η₂ (ren*-pop ρ D η₁ η₂ ren*)))
         (conglω (_∷ η₁) (ren* here))

subst-to-env*-id : (η : DEnv Δ) → subst-to-env* idₛ η ≡ω η
subst-to-env*-id {Δ} η = subst-to-env*-build {Δ₁ = Δ} id η η (ren*-id η)

subst-preserves : 
  ∀ {Δ₁ Δ₂}{ℓ}{η₂ : DEnv Δ₂}
  → (σ : Sub Δ₁ Δ₂) (T : Type Δ₁ ℓ)
  → 𝓣⟦ subT σ T ⟧ η₂ ≡ 𝓣⟦ T ⟧ (subst-to-env* σ η₂)
subst-preserves σ nat = refl
subst-preserves {η₂ = η₂} σ (` α) = subst-var-preserves α σ η₂
subst-preserves{η₂ = η₂} σ (T₁ ⇒ T₂) =
  cong₂ (λ t₁ t₂ → t₁ → t₂) (subst-preserves{η₂ = η₂} σ T₁) (subst-preserves{η₂ = η₂} σ T₂)
subst-preserves {η₂ = η₂} σ (`∀ ℓ T) =
  ∀-extensionality (λ D →
    trans (subst-preserves {η₂ = D ∷ η₂} (extₛ σ) T)
          (congωl (λ H → 𝓣⟦ T ⟧ (D ∷ H)) (subst-to-env*-wk σ D η₂)))
\end{code}
\newcommand\TFSingleSubstPreserves{%
\begin{code}
single-subst-preserves :
  ∀ {η : DEnv Δ} (T′ : Type Δ ℓ) (T : Type (ℓ ∷ Δ) ℓ′)
  → 𝓣⟦ T [ T′ ]T ⟧ η ≡ 𝓣⟦ T ⟧ (𝓣⟦ T′ ⟧ η ∷ η)
\end{code}}
\begin{code}[hide]
single-subst-preserves {Δ = Δ} {ℓ = ℓ}{ℓ′ = ℓ′}{η = η} T′ T =
  trans (subst-preserves (singleₛ idₛ T′) T)
        (congωl (λ H → 𝓣⟦ T ⟧ (𝓣⟦ T′ ⟧ η ∷ H)) (subst-to-env*-id η))
\end{code}
\newcommand\TFExprSem{%
\begin{code}
𝓔⟦_⟧ : ∀ {T : Type Δ ℓ}{Γ : TEnv Δ}
  → Expr Γ T → (η : DEnv Δ) → Env Γ η → 𝓣⟦ T ⟧ η
𝓔⟦ # n ⟧ η γ = n
𝓔⟦ ` x ⟧ η γ = γ x
𝓔⟦ ƛ_ e ⟧ η γ = λ v → 𝓔⟦ e ⟧ η (extend γ v)
𝓔⟦ e₁ · e₂ ⟧ η γ = 𝓔⟦ e₁ ⟧ η γ (𝓔⟦ e₂ ⟧ η γ)
𝓔⟦ Λ ℓ e ⟧ η γ = λ D → 𝓔⟦ e ⟧ (ext-env D η) (extend-tskip γ)
𝓔⟦ _∙_ {T = T} e T′ ⟧ η γ =
  subst id (sym (single-subst-preserves T′ T))
    (𝓔⟦ e ⟧ η γ (𝓣⟦ T′ ⟧ η))
\end{code}}
