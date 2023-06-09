module Tagless-steroid where

open import Level renaming (_⊔_ to _⊔′_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; length; lookup; tabulate)
open import Data.Unit
open import Data.Maybe
open import Function using (_∘_)
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

-- elements of a list

variable A : Set
variable a a′ : A
variable Δ Δ₁ Δ₂ : List A

data _∈_ (a : A) : List A → Set where
  here  : a ∈ (a ∷ Δ)
  there : a ∈ Δ → a ∈ (a′ ∷ Δ)

-- types

data Levelω : Set where
  just  : Level → Levelω
  omega : Levelω
variable l l′ : Levelω

_⊔_ : Levelω → Levelω → Levelω
just x ⊔ just y = just (x ⊔′ y)
just x ⊔ omega  = omega
omega  ⊔ just x = omega
omega  ⊔ omega  = omega

lsuc : Levelω → Levelω
lsuc (just x) = just (suc x)
lsuc omega = omega

-- grammar
--   λ ::= level variable
--   ℓ ::= l | λ
--   α ::= type variable
--   T ::= 𝟙
--       | ∀ᴸ λ . T
--       | ∀ⱽ α : ℓ . T
--       | T ⇒ T
--       | α

-- Δ ⊢ 𝟙 : lzero

-- Δ ⊢ S : ℓˢ
-- Δ ⊢ T : ℓᵗ
-- ------------------
-- Δ ⊢ S ⇒ T : ℓˢ ⊔ ℓᵗ

-- Δ, α : ℓ ⊢ T : ℓᵗ
-- -----------------------------
-- Δ ⊢ ∀ⱽ α : ℓ . T : suc ℓ ⊔ ℓᵗ

-- Δ, λ ⊢ T : ℓᵗ
-- ----------------
-- Δ ⊢ ∀ᴸ λ . T : ω


data Kind : Set where
  LV : Kind
  TV : Kind

data LVL (Δ : List Kind) : Set where
  lcn : Level → LVL Δ
  omg : LVL Δ
  lvr : LV ∈ Δ → LVL Δ
  lub : LVL Δ → LVL Δ → LVL Δ
  lsc : LVL Δ → LVL Δ

data Telescope : (Δ : List Kind) → Set where
  [] : Telescope []
  *ᴸ_ : ∀ {Δ} → Telescope Δ → Telescope (LV ∷ Δ)
  _∷_ : LVL Δ → Telescope Δ → Telescope (TV ∷ Δ)

-- some renaming style lemmas

weak-lv : ∀ {Δ} → LVL Δ → LVL (LV ∷ Δ)
weak-lv = {!!}

weak-tv : ∀ {Δ} → LVL Δ → LVL (TV ∷ Δ)
weak-tv = {!!}

strong-tv : ∀ {Δ} → LVL (TV ∷ Δ) → LVL Δ
strong-tv = {!!}

level-of-tv : {Δ : List Kind} → Telescope Δ → TV ∈ Δ → LVL Δ
level-of-tv [] ()
level-of-tv (*ᴸ Θ) (there α) = weak-lv (level-of-tv Θ α)
level-of-tv (x ∷ Θ) here = weak-tv x
level-of-tv (x ∷ Θ) (there α) = weak-tv (level-of-tv Θ α)

data Type {Δ : List Kind} : Telescope Δ → LVL Δ → Set where
  𝟙      : ∀ {Θ} → Type Θ (lcn zero)
  `_     : ∀ {Θ} → (l : TV ∈ Δ) → Type Θ (level-of-tv Θ l)
  _⇒_    : ∀ {Θ l l′} → Type Θ l → Type Θ l′ → Type Θ (lub l l′)
  `∀α_,_ : ∀ {Θ l′} → (l : LVL Δ) → Type (l ∷ Θ) l′ → Type Θ (lub (lsc l) (strong-tv l′))
  ∀ᴸ_    : ∀ {Θ l} → Type (*ᴸ Θ) l → Type Θ omg


-- semantic environments (mapping level l to an element of Set l)

module alternative where

  data SemLeveled : Levelω → Setω₁ where
    AtLev : ∀ {l} → Set l → SemLeveled (just l)
    Omega : Setω → SemLeveled omega


  data Env* : ∀ {Δ} → Telescope Δ → Setω₂
  level-of-lv : {Δ : List Kind} → (Θ : Telescope Δ) → Env* Θ → LV ∈ Δ → Level
  eval-lv : ∀ {Δ}{Θ : Telescope Δ} → LVL Δ → Env* Θ → Levelω

  data Env* where
    []  : Env* []
    _∷ᴸ_ : ∀ {Δ}{Θ : Telescope Δ} → Env* Θ → Level → Env* (*ᴸ Θ)
    _▷_ : ∀ {Δ}{Θ : Telescope Δ}{l : LVL Δ} → (η : Env* Θ) → SemLeveled (eval-lv l η) → Env* (l ∷ Θ)

  level-of-lv [] [] ()
  level-of-lv (*ᴸ Θ) (η ∷ᴸ x) here = x
  level-of-lv (*ᴸ Θ) (η ∷ᴸ x) (there lv) = level-of-lv Θ η lv
  level-of-lv (x ∷ Θ) (η ▷ x₁) (there lv) = level-of-lv Θ η lv

  eval-lv (lcn x) η = just x
  eval-lv omg η = omega
  eval-lv {Δ}{Θ} (lvr x) η = just (level-of-lv Θ η x)
  eval-lv (lub lv lv₁) η = eval-lv lv η ⊔ eval-lv lv₁ η
  eval-lv (lsc lv) η = lsuc (eval-lv lv η)

  --- end inductive recursive definition

  level-of-tv′ : ∀ {Δ}{Θ : Telescope Δ} → Env* Θ → TV ∈ Δ → Levelω
  level-of-tv′ [] ()
  level-of-tv′ (η ∷ᴸ x) (there α) = level-of-tv′ η α
  level-of-tv′ (_▷_ {l = lvl} η x) here = eval-lv lvl η
  level-of-tv′ (η ▷ x) (there α) = level-of-tv′ η α

  level-of-tv-≡ : ∀ {Δ}{Θ : Telescope Δ} → (η : Env* Θ) → (α : TV ∈ Δ) → level-of-tv′ η α ≡ eval-lv (level-of-tv Θ α) η
  level-of-tv-≡ [] ()
  level-of-tv-≡ (η ∷ᴸ x) (there α) = {!!}
  level-of-tv-≡ (η ▷ x) here = {!!}
  level-of-tv-≡ (η ▷ x) (there α) = {!!}

  apply-env : ∀ {Δ}{Θ : Telescope Δ} → (η : Env* Θ) → (α : TV ∈ Δ) → SemLeveled (level-of-tv′ η α)
  apply-env [] ()
  apply-env (η ∷ᴸ _) (there α) = apply-env η α
  apply-env (η ▷ x) here = x
  apply-env (η ▷ _) (there α) = apply-env η α

  ⟦_⟧ : ∀ {Δ}{Θ : Telescope Δ}{l} → Type Θ l → (η : Env* Θ) → SemLeveled (eval-lv l η)
  ⟦ 𝟙 ⟧ η = AtLev ⊤
  ⟦ ` α ⟧ η rewrite sym (level-of-tv-≡ η α) = apply-env η α
  ⟦ _⇒_ {l = l}{l′ = l′} T₁ T₂ ⟧ η
    with eval-lv l η | ⟦ T₁ ⟧ η | eval-lv l′ η | ⟦ T₂ ⟧ η
  ... | just l₁ | AtLev D₁ | just l₂ | AtLev D₂ = AtLev (D₁ → D₂)
  ... | just l₁ | AtLev D₁ | omega | Omega D₂ = Omega (D₁ → D₂)
  ... | omega | Omega D₁ | just l₂ | AtLev D₂ = Omega (D₁ → D₂)
  ... | omega | Omega D₁ | omega | Omega D₂ = Omega (D₁ → D₂)
  ⟦ `∀α_,_ {l′ = l′} l T ⟧ η
    with eval-lv l η in eq₁ | eval-lv (strong-tv l′) η
  ... | just l₁ | just l₂ = AtLev ((⟦α⟧ : Set l₁) → {!⟦ T ⟧ (η ▷ (subst SemLeveled ? (AtLev ⟦α⟧)))!})
  ... | just x | omega = {!!}
  ... | omega | just x = {!!}
  ... | omega | omega = {!!}
  ⟦ ∀ᴸ T ⟧ η = Omega ({!!})


-- SemLeveled₀ : Maybe Level → Setω₁
-- SemLeveled₀ (just x) = {!Set x!}
-- SemLeveled₀ nothing = Setω

data SemLeveled : Setω₁ where
  Leveled  : ∀ {l} → (A : Set l) → SemLeveled
  Omega : (A : Setω) → SemLeveled

data SemLeveled₁ : Levelω → Setω₁ where
  Leveled : ∀ {l} → Set l → SemLeveled₁ (just l)
  Omega : Setω → SemLeveled₁ omega

data Liftω : Setω₁ where
  liftω : ∀ {l} → Set l → Liftω

data Env* : ∀  {Δ} → Telescope Δ → Setω where
  []  : Env* []
  _∷ᴸ_ : ∀ {Δ}{Θ : Telescope Δ} → Level → Env* Θ → Env* (*ᴸ Θ)
  _∷_ : ∀ {Δ}{Θ : Telescope Δ}{l : LVL Δ} → {!!} → Env* Θ → Env* (l ∷ Θ)

level-of-lv : {Δ : List Kind} → (Θ : Telescope Δ) → Env* Θ → LV ∈ Δ → Level
level-of-lv [] [] ()
level-of-lv (*ᴸ Θ) (x ∷ᴸ η) here = x
level-of-lv (*ᴸ Θ) (x ∷ᴸ η) (there lv) = level-of-lv Θ η lv
level-of-lv (x ∷ Θ) (x₁ ∷ η) (there lv) = level-of-lv Θ η lv

eval-lv :  ∀ {Δ}{Θ : Telescope Δ} → LVL Δ → Env* Θ → Levelω
eval-lv (lcn x) η = just x
eval-lv omg η = omega
eval-lv {Δ}{Θ} (lvr x) η = just (level-of-lv Θ η x)
eval-lv (lub lv lv₁) η = eval-lv lv η ⊔ eval-lv lv₁ η
eval-lv (lsc lv) η = lsuc (eval-lv lv η)

⟦_⟧ᴸ : ∀ {Δ}{Θ : Telescope Δ} → (lv : LVL Δ) → (η : Env* Θ) → SemLeveled₁ (eval-lv lv η)
⟦ lcn x ⟧ᴸ η = Leveled {!!}
⟦ omg ⟧ᴸ η = Omega {!!}
⟦ lvr x ⟧ᴸ η = {!!}
⟦ lub l l₁ ⟧ᴸ η = {!!}
⟦ lsc l ⟧ᴸ η = {!!}


-- apply-env : Env* Δ → l ∈ Δ → Set l
-- apply-env [] ()
-- apply-env (x ∷ _) here = x
-- apply-env (_ ∷ η) (there x) = apply-env η x

-- -- the meaning of a stratified type in terms of Agda universes

-- ⟦_⟧ : (T : Type Δ l) → Env* Δ → Set l
-- ⟦ ` x ⟧ η = apply-env η x
-- ⟦ T₁ ⇒ T₂ ⟧ η = ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η
-- ⟦ `∀α l , T ⟧ η = (α : Set l) → ⟦ T ⟧ (α ∷ η)
-- ⟦ 𝟙 ⟧ η = ⊤

-- -- renaming on types

-- Ren : LEnv → LEnv → Set
-- Ren Δ₁ Δ₂ = ∀ {l} → l ∈ Δ₁ → l ∈ Δ₂

-- wkᵣ : Ren Δ (l ∷ Δ)
-- wkᵣ = there

-- extᵣ : Ren Δ₁ Δ₂ → Ren (l ∷ Δ₁) (l ∷ Δ₂)
-- extᵣ ρ here = here
-- extᵣ ρ (there x) = there (ρ x)

-- renT : Ren Δ₁ Δ₂ → (Type Δ₁ l → Type Δ₂ l)
-- renT ρ (` x) = ` ρ x
-- renT ρ (T₁ ⇒ T₂) = renT ρ T₁ ⇒ renT ρ T₂
-- renT ρ (`∀α lev , T) = `∀α lev , renT (extᵣ ρ) T
-- renT ρ 𝟙 = 𝟙 

-- wkT : Type Δ l′ → Type (l ∷ Δ) l′
-- wkT = renT wkᵣ

-- -- the action of renaming on semantic environments

-- Ren* : (ρ : Ren Δ₁ Δ₂) → (η₁ : Env* Δ₁) → (η₂ : Env* Δ₂) → Setω
-- Ren* {Δ₁} ρ η₁ η₂ = ∀ {l : Level} → (x : l ∈ Δ₁) → apply-env η₂ (ρ x) ≡ apply-env η₁ x

-- wkᵣ∈Ren* : ∀ (η : Env* Δ) (⟦α⟧ : Set l)
--   → Ren* (wkᵣ{Δ}{l}) η (⟦α⟧ ∷ η)
-- wkᵣ∈Ren* η ⟦α⟧ x = refl

-- ren*-id : (η : Env* Δ) → Ren* (λ x → x) η η
-- ren*-id η x = refl

-- ren*-pop : (ρ : Ren (l ∷ Δ₁) Δ₂) (α : Set l) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂)
--   → Ren* ρ (α ∷ η₁) η₂
--   → Ren* (ρ ∘ there) η₁ η₂
-- ren*-pop ρ α η₁ η₂ ren* x = ren* (there x)

-- ren*-ext : ∀ {ρ : Ren Δ₁ Δ₂}{η₁ : Env* Δ₁}{η₂ : Env* Δ₂} (α : Set l)
--   → Ren* ρ η₁ η₂
--   → Ren* (extᵣ ρ) (α ∷ η₁) (α ∷ η₂)
-- ren*-ext α ren* here = refl
-- ren*-ext α ren* (there x) = ren* x

-- ren*-preserves-semantics : ∀ {ρ : Ren Δ₁ Δ₂}{η₁ : Env* Δ₁}{η₂ : Env* Δ₂}
--   → (ren* : Ren* ρ η₁ η₂) → (T : Type Δ₁ l)
--   → ⟦ renT ρ T ⟧ η₂ ≡ ⟦ T ⟧ η₁
-- ren*-preserves-semantics ren* (` x) = ren* x
-- ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* (T₁ ⇒ T₂)
--   rewrite ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* T₁
--   | ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* T₂
--   = refl
-- ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* (`∀α l , T) =
--   dependent-extensionality (λ α →
--     ren*-preserves-semantics{ρ = extᵣ ρ}{α ∷ η₁}{α ∷ η₂} (ren*-ext{ρ = ρ} α ren*) T)
-- ren*-preserves-semantics ren* 𝟙 = refl

-- -- substitution on types

-- data Sub : LEnv → LEnv → Set where
--   []  : Sub [] Δ₂
--   _∷_ : Type Δ₂ l → Sub Δ₁ Δ₂ → Sub (l ∷ Δ₁) Δ₂

-- apply-sub : l ∈ Δ₁ → Sub Δ₁ Δ₂ → Type Δ₂ l
-- apply-sub here (T ∷ _) = T
-- apply-sub (there x) (_ ∷ σ) = apply-sub x σ

-- build-id : (Δ₁ : LEnv) → Ren Δ₁ Δ → Sub Δ₁ Δ
-- build-id [] ρ = []
-- build-id (l ∷ Δ₁) ρ = (` ρ here) ∷ build-id Δ₁ (ρ ∘ there)

-- idₛ : Sub Δ Δ
-- idₛ {Δ} = build-id Δ (λ x → x)

-- wkₛ : Sub Δ₁ Δ₂ → Sub Δ₁ (l ∷ Δ₂)
-- wkₛ [] = []
-- wkₛ (T ∷ σ) = wkT T ∷ wkₛ σ

-- extₛ : Sub Δ₁ Δ₂ → ∀ {l} → Sub (l ∷ Δ₁) (l ∷ Δ₂)
-- extₛ σ = ` here ∷ wkₛ σ

-- subT : Sub Δ₁ Δ₂ → Type Δ₁ l → Type Δ₂ l
-- subT σ (` x) = apply-sub x σ
-- subT σ (T₁ ⇒ T₂) = subT σ T₁ ⇒ subT σ T₂
-- subT σ (`∀α l , T) = `∀α l , subT (extₛ σ) T
-- subT σ 𝟙 = 𝟙

-- singleₛ : Sub Δ₁ Δ₂ → ∀ {l} → Type Δ₂ l → Sub (l ∷ Δ₁) Δ₂
-- singleₛ σ T' = T' ∷ σ

-- _[_]T : Type (l ∷ Δ) l′ → Type Δ l → Type Δ l′
-- _[_]T T T' = subT (singleₛ idₛ T') T

-- -- type environments

-- data TEnv : LEnv → Set where
--   ∅    : TEnv []
--   _◁_  : Type Δ l → TEnv Δ → TEnv Δ
--   _◁*_ : (l : Level) → TEnv Δ → TEnv (l ∷ Δ)

-- data inn : Type Δ l → TEnv Δ → Set where
--   here  : ∀ {T Γ} → inn {Δ}{l} T (T ◁ Γ)
--   there : ∀ {T : Type Δ l}{T′ : Type Δ l′}{Γ} → inn {Δ}{l} T Γ → inn {Δ} T (T′ ◁ Γ)
--   tskip : ∀ {T l Γ} → inn {Δ}{l′} T Γ → inn (wkT T) (l ◁* Γ)

-- data Expr (Δ : LEnv) (Γ : TEnv Δ) : Type Δ l → Set where
--   `_   : ∀ {T : Type Δ l} → inn T Γ → Expr Δ Γ T
--   ƛ_   : ∀ {T : Type Δ l}{T′ : Type Δ l′} → Expr Δ (T ◁ Γ) T′ → Expr Δ Γ (T ⇒ T′)
--   _·_  : ∀ {T : Type Δ l}{T′ : Type Δ l′} → Expr Δ Γ (T ⇒ T′) → Expr Δ Γ T → Expr Δ Γ T′
--   Λ_⇒_ : ∀ (l : Level) → {T : Type (l ∷ Δ) l′} → Expr (l ∷ Δ) (l ◁* Γ) T → Expr Δ Γ (`∀α l , T)
--   _∙_  : ∀ {T : Type (l ∷ Δ) l′} → Expr Δ Γ (`∀α l , T) → (T′ : Type Δ l) → Expr Δ Γ (T [ T′ ]T)

-- -- value environments

-- Env : (Δ : LEnv) → TEnv Δ → Env* Δ → Setω
-- Env Δ Γ η = ∀ {l}{T : Type Δ l} → (x : inn T Γ) → ⟦ T ⟧ η

-- extend : ∀ {T : Type Δ l}{Γ : TEnv Δ}{η : Env* Δ}
--   → Env Δ Γ η → ⟦ T ⟧ η
--   → Env Δ (T ◁ Γ) η
-- extend γ v here = v
-- extend γ v (there x) = γ x

-- extend-tskip : ∀ {Δ : LEnv}{Γ : TEnv Δ}{η : Env* Δ}{⟦α⟧ : Set l}
--   → Env Δ Γ η
--   → Env (l ∷ Δ) (l ◁* Γ) (⟦α⟧ ∷ η)
-- extend-tskip {η = η} {⟦α⟧ = ⟦α⟧} γ (tskip{T = T} x)
--   rewrite ren*-preserves-semantics {ρ = wkᵣ}{η}{⟦α⟧ ∷ η} (wkᵣ∈Ren* η ⟦α⟧) T
--   = γ x

-- subst-to-env* : (σ : Sub Δ₁ Δ₂) → (η₂ : Env* Δ₂) → Env* Δ₁
-- subst-to-env* [] η₂ = []
-- subst-to-env* (T ∷ σ) η₂ = ⟦ T ⟧ η₂ ∷ subst-to-env* σ η₂

-- subst-var-preserves : (x  : l ∈ Δ₁) (σ  : Sub Δ₁ Δ₂) (η₂ : Env* Δ₂)
--   → ⟦ apply-sub x σ ⟧ η₂ ≡ apply-env (subst-to-env* σ η₂) x
-- subst-var-preserves here (T ∷ σ) η₂ = refl
-- subst-var-preserves (there x) (_ ∷ σ) η₂ = subst-var-preserves x σ η₂

-- subst-to-env*-wk : (σ  : Sub Δ₁ Δ₂) (α  : Set l) (η₂ : Env* Δ₂)
--   → subst-to-env* (wkₛ σ) (α ∷ η₂) ≡ω subst-to-env* σ η₂
-- subst-to-env*-wk [] α η₂ = refl
-- subst-to-env*-wk (T ∷ σ) α η₂
--   rewrite ren*-preserves-semantics {ρ = wkᵣ}{η₂}{α ∷ η₂} (wkᵣ∈Ren* η₂ α) T
--   = congωω (⟦ T ⟧ η₂ ∷_) (subst-to-env*-wk σ α η₂)

-- subst-to-env*-build : ∀ (ρ : Ren Δ₁ Δ₂) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂)
--   → Ren* ρ η₁ η₂
--   → subst-to-env* (build-id Δ₁ ρ) η₂ ≡ω η₁
-- subst-to-env*-build ρ [] η₂ ren* = refl
-- subst-to-env*-build {Δ₁ = _ ∷ Δ₁} ρ (α ∷ η₁) η₂ ren* = 
--   transω (congωω (apply-env η₂ (ρ here) ∷_) (subst-to-env*-build (ρ ∘ there) η₁ η₂ (ren*-pop ρ α η₁ η₂ ren*)))
--          (conglω (_∷ η₁) (ren* here))

-- subst-to-env*-id : (η : Env* Δ) → subst-to-env* idₛ η ≡ω η
-- subst-to-env*-id {Δ} η = subst-to-env*-build {Δ₁ = Δ} (λ x → x) η η (ren*-id η)

-- subst-preserves-type : Setω
-- subst-preserves-type =
--   ∀ {Δ₁ Δ₂}{l}{η₂ : Env* Δ₂}
--   → (σ : Sub Δ₁ Δ₂) (T : Type Δ₁ l)
--   → ⟦ subT σ T ⟧ η₂ ≡ ⟦ T ⟧ (subst-to-env* σ η₂)

-- subst-preserves : subst-preserves-type
-- subst-preserves {η₂ = η₂} σ (` x) = subst-var-preserves x σ η₂
-- subst-preserves{η₂ = η₂} σ (T₁ ⇒ T₂)
--   rewrite subst-preserves{η₂ = η₂} σ T₁
--   |  subst-preserves{η₂ = η₂} σ T₂ = refl
-- subst-preserves {η₂ = η₂} σ (`∀α l , T) =
--   dependent-extensionality (λ α →
--     trans (subst-preserves {η₂ = α ∷ η₂} (extₛ σ) T)
--           (congωl (λ H → ⟦ T ⟧ (α ∷ H)) (subst-to-env*-wk σ α η₂)))
-- subst-preserves σ 𝟙 = refl

-- single-subst-preserves : ∀ (η : Env* Δ) (T′ : Type Δ l) (T : Type (l ∷ Δ) l′)
--   → ⟦ T [ T′ ]T ⟧ η ≡ ⟦ T ⟧ (⟦ T′ ⟧ η ∷ η)
-- single-subst-preserves {Δ = Δ} {l = l}{l′ = l′} η T′ T =
--   trans (subst-preserves (singleₛ idₛ T′) T)
--         (congωl (λ H → ⟦ T ⟧ (⟦ T′ ⟧ η ∷ H)) (subst-to-env*-id η))

-- E⟦_⟧ : ∀ {T : Type Δ l}{Γ : TEnv Δ} → Expr Δ Γ T → (η : Env* Δ) → Env Δ Γ η → ⟦ T ⟧ η
-- E⟦ ` x ⟧ η γ = γ x
-- E⟦ ƛ_ e ⟧ η γ = λ v → E⟦ e ⟧ η (extend γ v)
-- E⟦ e₁ · e₂ ⟧ η γ = E⟦ e₁ ⟧ η γ (E⟦ e₂ ⟧ η γ)
-- E⟦ Λ l ⇒ e ⟧ η γ = λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ η) (extend-tskip γ)
-- E⟦ _∙_ {T = T} e T′ ⟧ η γ
--   with E⟦ e ⟧ η γ (⟦ T′ ⟧ η)
-- ... | v rewrite single-subst-preserves η T′ T = v 
