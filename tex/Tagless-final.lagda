\begin{code}[hide]
module Tagless-final where

open import Level
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_; length; lookup; tabulate)
open import Data.Unit
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; resp₂)

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
variable l l′ : Level

-- types
\end{code}
\newcommand\TFType{%
\begin{code}
LEnv = List Level
data Type (Δ : LEnv) : Level → Set where
  nat : Type Δ zero
  `_  : l ∈ Δ → Type Δ l
  _⇒_ : Type Δ l → Type Δ l′ → Type Δ (l ⊔ l′)
  `∀  : ∀ l → Type (l ∷ Δ) l′ → Type Δ (suc l ⊔ l′)
\end{code}}
\begin{code}[hide]
-- level of type according to Leivant'91
level : Type Δ l → Level
level {l = l} T = l

-- semantic environments (mapping level l to an element of Set l)
\end{code}
\newcommand\TFTEnv{%
\begin{code}
data DEnv : LEnv → Setω where
  []  : DEnv []
  _∷_ : Set l → DEnv Δ → DEnv (l ∷ Δ)
\end{code}}
\begin{code}[hide]
apply-env : DEnv Δ → l ∈ Δ → Set l
apply-env [] ()
apply-env (x ∷ _) here = x
apply-env (_ ∷ η) (there x) = apply-env η x

-- the meaning of a stratified type in terms of Agda universes
\end{code}
\newcommand\TFTSem{%
\begin{code}
𝓣⟦_⟧ : Type Δ l → DEnv Δ → Set l
𝓣⟦ nat ⟧ η = ℕ
𝓣⟦ ` α ⟧ η = apply-env η α
𝓣⟦ T₁ ⇒ T₂ ⟧ η = 𝓣⟦ T₁ ⟧ η → 𝓣⟦ T₂ ⟧ η
𝓣⟦ `∀ l T ⟧ η = (⟦α⟧ : Set l) → 𝓣⟦ T ⟧ (⟦α⟧ ∷ η)
\end{code}}
\begin{code}[hide]
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
renT ρ (`∀ lev T) = `∀ lev (renT (extᵣ ρ) T)
renT ρ nat = nat

wkT : Type Δ l′ → Type (l ∷ Δ) l′
wkT = renT wkᵣ

-- the action of renaming on semantic environments

Ren* : (ρ : Ren Δ₁ Δ₂) → (η₁ : DEnv Δ₁) → (η₂ : DEnv Δ₂) → Setω
Ren* {Δ₁} ρ η₁ η₂ = ∀ {l : Level} → (x : l ∈ Δ₁) → apply-env η₂ (ρ x) ≡ apply-env η₁ x

wkᵣ∈Ren* : ∀ (η : DEnv Δ) (⟦α⟧ : Set l)
  → Ren* (wkᵣ{Δ}{l}) η (⟦α⟧ ∷ η)
wkᵣ∈Ren* η ⟦α⟧ x = refl

ren*-id : (η : DEnv Δ) → Ren* id η η
ren*-id η x = refl

ren*-pop : (ρ : Ren (l ∷ Δ₁) Δ₂) (α : Set l) (η₁ : DEnv Δ₁) (η₂ : DEnv Δ₂)
  → Ren* ρ (α ∷ η₁) η₂
  → Ren* (ρ ∘ there) η₁ η₂
ren*-pop ρ α η₁ η₂ ren* x = ren* (there x)

ren*-ext : ∀ {ρ : Ren Δ₁ Δ₂}{η₁ : DEnv Δ₁}{η₂ : DEnv Δ₂} (⟦α⟧ : Set l)
  → Ren* ρ η₁ η₂
  → Ren* (extᵣ ρ) (⟦α⟧ ∷ η₁) (⟦α⟧ ∷ η₂)
ren*-ext ⟦α⟧ ren* here = refl
ren*-ext ⟦α⟧ ren* (there x) = ren* x
\end{code}
\newcommand\TFRenPreserverSemanticsType{%
\begin{code}
ren*-preserves-semantics :
  ∀ {ρ : Ren Δ₁ Δ₂}{η₁ : DEnv Δ₁}{η₂ : DEnv Δ₂}
  → (ren* : Ren* ρ η₁ η₂) → (T : Type Δ₁ l)
  → 𝓣⟦ renT ρ T ⟧ η₂ ≡ 𝓣⟦ T ⟧ η₁
\end{code}}
\begin{code}[hide]
ren*-preserves-semantics ren* nat = refl
ren*-preserves-semantics ren* (` x) = ren* x
ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* (T₁ ⇒ T₂)
  rewrite ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* T₁
  | ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* T₂
  = refl
ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* (`∀ l T) =
  ∀-extensionality (λ α →
    ren*-preserves-semantics{ρ = extᵣ ρ}{α ∷ η₁}{α ∷ η₂} (ren*-ext{ρ = ρ} α ren*) T)

postulate 
  problematic-goal : 
    ∀ {l′}{Δ₁ Δ₂ : LEnv}{ρ : Ren Δ₁ Δ₂}{η₁ : DEnv Δ₁}{η₂ : DEnv Δ₂}
    → (ren* : Ren* ρ η₁ η₂) →
\end{code}
\newcommand\TFProblematicGoal{%
\begin{code}
    (T : Type (l ∷ Δ₁) l′) →
    ((⟦α⟧ : Set l) → 𝓣⟦ renT (extᵣ ρ) T ⟧ (⟦α⟧ ∷ η₂)) ≡
       ((⟦α⟧ : Set l) → 𝓣⟦ T ⟧ (⟦α⟧ ∷ η₁))
\end{code}}
\begin{code}[hide]
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
subT σ nat = nat
subT σ (` α) = apply-sub σ α
subT σ (T₁ ⇒ T₂) = subT σ T₁ ⇒ subT σ T₂
subT σ (`∀ l T) = `∀ l (subT (extₛ σ) T)

singleₛ : Sub Δ₁ Δ₂ → ∀ {l} → Type Δ₂ l → Sub (l ∷ Δ₁) Δ₂
singleₛ σ T' = T' ∷ σ

_[_]T : Type (l ∷ Δ) l′ → Type Δ l → Type Δ l′
_[_]T T T' = subT (singleₛ idₛ T') T

-- type environments
\end{code}
\newcommand\TFTVEnv{%
\begin{code}
data TEnv : LEnv → Set where
  ∅    : TEnv []
  _◁_  : Type Δ l → TEnv Δ → TEnv Δ  -- term variable
  _◁*_ : ∀ l → TEnv Δ → TEnv (l ∷ Δ) -- type variable
\end{code}}
\newcommand\TFinn{%
\begin{code}
data inn : Type Δ l → TEnv Δ → Set where
  here  : ∀ {T : Type Δ l}{Γ}
        → inn T (T ◁ Γ)
  there : ∀ {T : Type Δ l}{T′ : Type Δ l′}{Γ}
        → inn T Γ → inn T (T′ ◁ Γ)
  tskip : ∀ {T : Type Δ l}{Γ}
        → inn T Γ → inn (wkT T) (l′ ◁* Γ)
\end{code}}
\newcommand\TFExpr{%
\begin{code}
data Expr (Δ : LEnv) (Γ : TEnv Δ) : Type Δ l → Set where
  #_   : ∀ (n : ℕ) → Expr Δ Γ nat
  `_   : ∀ {T : Type Δ l}
       → inn T Γ → Expr Δ Γ T
  ƛ_   : ∀ {T : Type Δ l}{T′ : Type Δ l′}
       → Expr Δ (T ◁ Γ) T′ → Expr Δ Γ (T ⇒ T′)
  _·_  : ∀ {T : Type Δ l}{T′ : Type Δ l′}
       → Expr Δ Γ (T ⇒ T′) → Expr Δ Γ T → Expr Δ Γ T′
  Λ    : ∀ (l : Level) → {T : Type (l ∷ Δ) l′}
       → Expr (l ∷ Δ) (l ◁* Γ) T → Expr Δ Γ (`∀ l T)
  _∙_  : ∀ {T : Type (l ∷ Δ) l′}
       → Expr Δ Γ (`∀ l T) → (T′ : Type Δ l)
       → Expr Δ Γ (T [ T′ ]T)
\end{code}}
\begin{code}[hide]
-- value environments
\end{code}
\newcommand\TFVEnv{%
\begin{code}
Env : (Δ : LEnv) → TEnv Δ → DEnv Δ → Setω
Env Δ Γ η = ∀ {l}{T : Type Δ l} → inn T Γ → 𝓣⟦ T ⟧ η
\end{code}}
\begin{code}[hide]
extend : ∀ {T : Type Δ l}{Γ : TEnv Δ}{η : DEnv Δ}
  → Env Δ Γ η
  → 𝓣⟦ T ⟧ η
  → Env Δ (T ◁ Γ) η
extend γ v here = v
extend γ v (there x) = γ x
\end{code}
\newcommand\TFExtendTskip{%
\begin{code}
extend-tskip : ∀ {Δ : LEnv}{Γ : TEnv Δ}{η : DEnv Δ}{⟦α⟧ : Set l}
  → Env Δ Γ η → Env (l ∷ Δ) (l ◁* Γ) (⟦α⟧ ∷ η)
extend-tskip {η = η} {⟦α⟧ = ⟦α⟧} γ (tskip{T = T} x)
  rewrite ren*-preserves-semantics {ρ = wkᵣ}{η}{⟦α⟧ ∷ η}
            (wkᵣ∈Ren* η ⟦α⟧) T
  = γ x
\end{code}}
\begin{code}[hide]
subst-to-env* : (σ : Sub Δ₁ Δ₂) → (η₂ : DEnv Δ₂) → DEnv Δ₁
subst-to-env* [] η₂ = []
subst-to-env* (T ∷ σ) η₂ = 𝓣⟦ T ⟧ η₂ ∷ subst-to-env* σ η₂

subst-var-preserves : (α : l ∈ Δ₁) (σ : Sub Δ₁ Δ₂) (η₂ : DEnv Δ₂)
  → 𝓣⟦ apply-sub σ α ⟧ η₂ ≡ apply-env (subst-to-env* σ η₂) α
subst-var-preserves here (T ∷ σ) η₂ = refl
subst-var-preserves (there α) (_ ∷ σ) η₂ = subst-var-preserves α σ η₂

subst-to-env*-wk : (σ : Sub Δ₁ Δ₂) (⟦α⟧ : Set l) (η₂ : DEnv Δ₂)
  → subst-to-env* (wkₛ σ) (⟦α⟧ ∷ η₂) ≡ω subst-to-env* σ η₂
subst-to-env*-wk [] ⟦α⟧ η₂ = refl
subst-to-env*-wk (T ∷ σ) ⟦α⟧ η₂
  rewrite ren*-preserves-semantics {ρ = wkᵣ}{η₂}{⟦α⟧ ∷ η₂} (wkᵣ∈Ren* η₂ ⟦α⟧) T
  = congωω (𝓣⟦ T ⟧ η₂ ∷_) (subst-to-env*-wk σ ⟦α⟧ η₂)

subst-to-env*-build : ∀ (ρ : Ren Δ₁ Δ₂) (η₁ : DEnv Δ₁) (η₂ : DEnv Δ₂)
  → Ren* ρ η₁ η₂
  → subst-to-env* (build-id Δ₁ ρ) η₂ ≡ω η₁
subst-to-env*-build ρ [] η₂ ren* = refl
subst-to-env*-build {Δ₁ = _ ∷ Δ₁} ρ (⟦α⟧ ∷ η₁) η₂ ren* = 
  transω (congωω (apply-env η₂ (ρ here) ∷_) (subst-to-env*-build (ρ ∘ there) η₁ η₂ (ren*-pop ρ ⟦α⟧ η₁ η₂ ren*)))
         (conglω (_∷ η₁) (ren* here))

subst-to-env*-id : (η : DEnv Δ) → subst-to-env* idₛ η ≡ω η
subst-to-env*-id {Δ} η = subst-to-env*-build {Δ₁ = Δ} id η η (ren*-id η)

subst-preserves : 
  ∀ {Δ₁ Δ₂}{l}{η₂ : DEnv Δ₂}
  → (σ : Sub Δ₁ Δ₂) (T : Type Δ₁ l)
  → 𝓣⟦ subT σ T ⟧ η₂ ≡ 𝓣⟦ T ⟧ (subst-to-env* σ η₂)
subst-preserves σ nat = refl
subst-preserves {η₂ = η₂} σ (` α) = subst-var-preserves α σ η₂
subst-preserves{η₂ = η₂} σ (T₁ ⇒ T₂)
  rewrite subst-preserves{η₂ = η₂} σ T₁
  |  subst-preserves{η₂ = η₂} σ T₂ = refl
subst-preserves {η₂ = η₂} σ (`∀ l T) =
  ∀-extensionality (λ ⟦α⟧ →
    trans (subst-preserves {η₂ = ⟦α⟧ ∷ η₂} (extₛ σ) T)
          (congωl (λ H → 𝓣⟦ T ⟧ (⟦α⟧ ∷ H)) (subst-to-env*-wk σ ⟦α⟧ η₂)))
\end{code}
\newcommand\TFSingleSubstPreserves{%
\begin{code}
single-subst-preserves :
  ∀ (η : DEnv Δ) (T′ : Type Δ l) (T : Type (l ∷ Δ) l′)
  → 𝓣⟦ T [ T′ ]T ⟧ η ≡ 𝓣⟦ T ⟧ (𝓣⟦ T′ ⟧ η ∷ η)
\end{code}}
\begin{code}[hide]
single-subst-preserves {Δ = Δ} {l = l}{l′ = l′} η T′ T =
  trans (subst-preserves (singleₛ idₛ T′) T)
        (congωl (λ H → 𝓣⟦ T ⟧ (𝓣⟦ T′ ⟧ η ∷ H)) (subst-to-env*-id η))
\end{code}
\newcommand\TFExprSem{%
\begin{code}
𝓔⟦_⟧ : ∀ {T : Type Δ l}{Γ : TEnv Δ}
  → Expr Δ Γ T → (η : DEnv Δ) → Env Δ Γ η → 𝓣⟦ T ⟧ η
𝓔⟦ # n ⟧ η γ = n
𝓔⟦ ` x ⟧ η γ = γ x
𝓔⟦ ƛ_ e ⟧ η γ = λ v → 𝓔⟦ e ⟧ η (extend γ v)
𝓔⟦ e₁ · e₂ ⟧ η γ = 𝓔⟦ e₁ ⟧ η γ (𝓔⟦ e₂ ⟧ η γ)
𝓔⟦ Λ l e ⟧ η γ = λ ⟦α⟧ → 𝓔⟦ e ⟧ (⟦α⟧ ∷ η) (extend-tskip γ)
𝓔⟦ _∙_ {T = T} e T′ ⟧ η γ =
  subst id (sym (single-subst-preserves η T′ T))
    (𝓔⟦ e ⟧ η γ (𝓣⟦ T′ ⟧ η))
\end{code}}
