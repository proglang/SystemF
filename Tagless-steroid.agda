module Tagless-steroid where

open import Level renaming (_⊔_ to _⊔′_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; length; lookup; tabulate)
open import Data.Unit
open import Data.Empty
open import Data.Maybe
open import Data.Product
open import Data.Sum
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

data _≡ω₁_ {A : Setω₁} (x : A) : A → Setω₂ where
  refl : x ≡ω₁ x

substω : ∀ {a}{A : Set a} → (F : (x : A) → Setω₁) →
  ∀ {x y : A} → x ≡ y → F x → F y
substω f refl x = x

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

-- expressions
--   x ::= term variable
--   M, N ::= x
--       | λ x . M
--       | M N
--       | Λ α : ℓ . M
--       | M T
--       | Λᴸ λ . M
--       | M ℓ

data Kind : Set where
  LV : Kind
  TV : Kind


data LAN Δ : Set where
  lacn : Level → LAN Δ
  lavr : LV ∈ Δ → LAN Δ

data LVL (Δ : List Kind) : Set where
  lan : LAN Δ → LVL Δ
  omg : LVL Δ
  lub : LVL Δ → LVL Δ → LVL Δ
  lsc : LVL Δ → LVL Δ

data Telescope : (Δ : List Kind) → Set where
  [] : Telescope []
  *ᴸ_ : ∀ {Δ} → Telescope Δ → Telescope (LV ∷ Δ)
  _∷_ : LAN Δ → Telescope Δ → Telescope (TV ∷ Δ)

-- some renaming style lemmas

weak-lv : ∀ {Δ} → LAN Δ → LAN (LV ∷ Δ)
weak-lv (lacn x) = lacn x
weak-lv (lavr x) = lavr (there x)

weak-tv : ∀ {Δ} → LAN Δ → LAN (TV ∷ Δ)
weak-tv (lacn x) = lacn x
weak-tv (lavr x) = lavr (there x)

strong-tv-lan : ∀ {Δ} → LAN (TV ∷ Δ) → LAN Δ
strong-tv-lan (lacn x) = lacn x
strong-tv-lan (lavr (there x)) = lavr x

strong-tv : ∀ {Δ} → LVL (TV ∷ Δ) → LVL Δ
strong-tv (lan x) = lan (strong-tv-lan x)
strong-tv omg = omg
strong-tv (lub lv lv₁) = lub (strong-tv lv) (strong-tv lv₁)
strong-tv (lsc lv) = lsc (strong-tv lv)

level-of-tv : {Δ : List Kind} → Telescope Δ → TV ∈ Δ → LAN Δ
level-of-tv [] ()
level-of-tv (*ᴸ Θ) (there α) = weak-lv (level-of-tv Θ α)
level-of-tv (x ∷ Θ) here = weak-tv x
level-of-tv (x ∷ Θ) (there α) = weak-tv (level-of-tv Θ α)

data Type {Δ : List Kind} : Telescope Δ → LVL Δ → Set where
  𝟙      : ∀ {Θ} → Type Θ (lan (lacn zero))
  `_     : ∀ {Θ} → (l : TV ∈ Δ) → Type Θ (lan (level-of-tv Θ l))
  _⇒_    : ∀ {Θ l l′} → Type Θ l → Type Θ l′ → Type Θ (lub l l′)
  `∀α_,_ : ∀ {Θ l′} → (l : LAN Δ) → Type (l ∷ Θ) l′ → Type Θ (lub (lsc (lan l)) (strong-tv l′))
  ∀ᴸ_    : ∀ {Θ l} → Type (*ᴸ Θ) l → Type Θ omg


-- semantic environments (mapping level l to an element of Set l)

data SemLeveled : Levelω → Setω₁ where
  AtLev : ∀ {l} → Set l → SemLeveled (just l)
  Omega : Setω → SemLeveled omega

fromLev : ∀ {l lω} → SemLeveled lω → lω ≡ just l → Set l
fromLev (AtLev x) refl = x

fromOmega : ∀ {lω} → SemLeveled lω → lω ≡ omega → Setω
fromOmega (Omega x) refl = x

data Env* : ∀ {Δ} → Telescope Δ → Setω
level-of-lv : {Δ : List Kind} {Θ : Telescope Δ} → Env* Θ → LV ∈ Δ → Level
eval-lan :  ∀ {Δ}{Θ : Telescope Δ} → LAN Δ → Env* Θ → Level

data Env* where
  []  : Env* []
  _▷ᴸ_ : ∀ {Δ}{Θ : Telescope Δ} → Env* Θ → Level → Env* (*ᴸ Θ)
  _▷_ : ∀ {Δ}{Θ : Telescope Δ}{l : LAN Δ} → (η : Env* Θ) → Set (eval-lan l η) → Env* (l ∷ Θ)

level-of-lv [] ()
level-of-lv (η ▷ᴸ x) here = x
level-of-lv (η ▷ᴸ x) (there lv) = level-of-lv η lv
level-of-lv (η ▷ x₁) (there lv) = level-of-lv η lv

eval-lan (lacn x) η = x
eval-lan (lavr x) η = level-of-lv η x

eval-lv : ∀ {Δ}{Θ : Telescope Δ} → LVL Δ → Env* Θ → Levelω
eval-lv (lan x) η = just (eval-lan x η)
eval-lv omg η = omega
eval-lv (lub lv lv₁) η = eval-lv lv η ⊔ eval-lv lv₁ η
eval-lv (lsc lv) η = lsuc (eval-lv lv η)

--- end inductive recursive definition

--- abstract levels

data ALevelω : Set where
  ALevel AOmega : ALevelω

_∼⊔_ : ALevelω → ALevelω → ALevelω
ALevel ∼⊔ ALevel = ALevel
ALevel ∼⊔ AOmega = AOmega
AOmega ∼⊔ ALevel = AOmega
AOmega ∼⊔ AOmega = AOmega

∼⊔-reflects-ALevel : ∀ {x}{y} → (x ∼⊔ y) ≡ ALevel → x ≡ ALevel × y ≡ ALevel
∼⊔-reflects-ALevel {ALevel} {ALevel} refl = refl , refl
∼⊔-reflects-ALevel {ALevel} {AOmega} ()

∼⊔-reflects-AOmega : ∀ {x}{y} → (x ∼⊔ y) ≡ AOmega → (x ≡ AOmega) ⊎ (y ≡ AOmega)
∼⊔-reflects-AOmega {ALevel} {AOmega} refl = inj₂ refl
∼⊔-reflects-AOmega {AOmega} {ALevel} refl = inj₁ refl
∼⊔-reflects-AOmega {AOmega} {AOmega} refl = inj₁ refl

a-eval-lv : ∀ {Δ}{Θ : Telescope Δ} → LVL Δ → Env* Θ → ALevelω
a-eval-lv (lan _) η = ALevel
a-eval-lv omg η = AOmega
a-eval-lv (lub lvl lvl₁) η = a-eval-lv lvl η ∼⊔ a-eval-lv lvl₁ η
a-eval-lv (lsc lvl) η = a-eval-lv lvl η

a-eval-lv-≡ : ∀ {Δ}{Θ : Telescope Δ} → (η η′ : Env* Θ) → (lv : LVL Δ) → a-eval-lv lv η ≡ a-eval-lv lv η′
a-eval-lv-≡ η η′ (lan x) = refl
a-eval-lv-≡ η η′ omg = refl
a-eval-lv-≡ η η′ (lub lv lv₁) rewrite a-eval-lv-≡ η η′ lv | a-eval-lv-≡ η η′ lv₁ = refl
a-eval-lv-≡ η η′ (lsc lv) rewrite a-eval-lv-≡ η η′ lv = refl

_~<_ : Levelω → ALevelω → Set
just x ~< ALevel = ⊤
just x ~< AOmega = ⊥
omega ~< ALevel = ⊥
omega ~< AOmega = ⊤

eval~<a-eval : ∀ {Δ}{Θ : Telescope Δ} → (lv : LVL Δ) → (η : Env* Θ) → eval-lv lv η ~< a-eval-lv lv η
eval~<a-eval (lan x) η = tt
eval~<a-eval omg η = tt
eval~<a-eval (lub lv lv₁) η
  with eval-lv lv η | a-eval-lv lv η | eval~<a-eval lv η | eval-lv lv₁ η | a-eval-lv lv₁ η | eval~<a-eval lv₁ η
... | just x | ALevel | tt | just x₁ | ALevel | tt = tt
... | just x | ALevel | tt | just x₁ | AOmega | ()
... | just x | ALevel | tt | omega | ALevel | ()
... | just x | ALevel | tt | omega | AOmega | tt = tt
... | just x | AOmega | () | elv₁ | alv₁ | ea~<₁
... | omega | ALevel | () | elv₁ | alv₁ | ea~<₁
... | omega | AOmega | tt | just x | ALevel | tt = tt
... | omega | AOmega | tt | just x | AOmega | ()
... | omega | AOmega | tt | omega | ALevel | ()
... | omega | AOmega | tt | omega | AOmega | tt = tt
eval~<a-eval (lsc lv) η
  with eval-lv lv η | a-eval-lv lv η | eval~<a-eval lv η
... | just x | ALevel | tt = tt
... | just x | AOmega | ()
... | omega | ALevel | ()
... | omega | AOmega | tt = tt

a-eval-level-just : ∀ {Δ}{Θ : Telescope Δ} → (lv : LVL Δ) → (η : Env* Θ) → a-eval-lv lv η ≡ ALevel → ∃[ l ] eval-lv lv η ≡ just l
a-eval-level-just (lan (lacn l)) η refl = l , refl
a-eval-level-just (lan (lavr x)) η refl = level-of-lv η x , refl
a-eval-level-just (lub lv lv₁) η aeval≡ALevel
  with ∼⊔-reflects-ALevel aeval≡ALevel
... | ae≡ , ae≡₁
  with a-eval-level-just lv η ae≡ | a-eval-level-just lv₁ η ae≡₁ 
... | l , e≡j | l₁ , e≡j₁ rewrite e≡j | e≡j₁ = (l Level.⊔ l₁) , refl
a-eval-level-just (lsc lv) η aeval≡ALevel
  with a-eval-level-just lv η aeval≡ALevel
... | l , eval≡just rewrite eval≡just = suc l , refl

a-eval-level-omega : ∀ {Δ}{Θ : Telescope Δ} → (lv : LVL Δ) → (η : Env* Θ) → a-eval-lv lv η ≡ AOmega → eval-lv lv η ≡ omega
a-eval-level-omega omg η refl = refl
a-eval-level-omega (lub lv lv₁) η ae-lub≡
  with ∼⊔-reflects-AOmega ae-lub≡
... | inj₁ ae≡
  rewrite a-eval-level-omega lv η ae≡
    with eval-lv lv₁ η
... | just x = refl
... | omega = refl
a-eval-level-omega (lub lv lv₁) η ae-lub≡ | inj₂ ae≡₁
  rewrite a-eval-level-omega lv₁ η ae≡₁
    with eval-lv lv η
... | just x = refl
... | omega = refl
a-eval-level-omega (lsc lv) η ae≡
  rewrite a-eval-level-omega lv η ae≡ = refl


level-of-tv′ : ∀ {Δ}{Θ : Telescope Δ} → Env* Θ → TV ∈ Δ → Level
level-of-tv′ [] ()
level-of-tv′ (η ▷ᴸ x) (there α) = level-of-tv′ η α
level-of-tv′ (_▷_ {l = ln} η x) here = eval-lan ln η
level-of-tv′ (η ▷ x) (there α) = level-of-tv′ η α

level-weak : ∀ {Δ}{Θ : Telescope Δ} → (l : LAN Δ) → (η : Env* Θ) (x : Set (eval-lan l η))
  → eval-lan (weak-tv l) (_▷_ {l = l} η x) ≡ eval-lan l η
level-weak (lacn x₁) η x = refl
level-weak (lavr x₁) η x = refl

eval-lan-weak-ext : ∀ {Δ}{Θ : Telescope Δ}{ln : LAN Δ} → (η : Env* Θ) → (α : TV ∈ Δ) → (x : Set (eval-lan ln η))
  → eval-lan (weak-tv (level-of-tv Θ α)) (_▷_ {l = ln} η  x) ≡ eval-lan (level-of-tv Θ α) η
eval-lan-weak-ext {Θ = Θ} η α x
  with level-of-tv Θ α
... | lacn x = refl
... | lavr x = refl

eval-lan-weak-ext-lv : ∀ {Δ}{Θ : Telescope Δ} → (η : Env* Θ) → (α : TV ∈ Δ) → (lev : Level)
  → eval-lan (weak-lv (level-of-tv Θ α)) (η ▷ᴸ lev) ≡ eval-lan (level-of-tv Θ α) η
eval-lan-weak-ext-lv {Θ = Θ} η α lev
  with level-of-tv Θ α
... | lacn x = refl
... | lavr x = refl

level-of-tv-≡ : ∀ {Δ}{Θ : Telescope Δ} → (η : Env* Θ) → (α : TV ∈ Δ)
  → eval-lan (level-of-tv Θ α) η ≡ level-of-tv′ η α
level-of-tv-≡ [] ()
level-of-tv-≡ (η ▷ᴸ lev) (there α) = trans (eval-lan-weak-ext-lv η α lev) (level-of-tv-≡ η α)
level-of-tv-≡ (_▷_ {l = l} η  x) here = level-weak l η x
level-of-tv-≡ {Θ = ln ∷ Θ} (η ▷ x) (there α) = trans (eval-lan-weak-ext {ln = ln} η α x) (level-of-tv-≡ η α)

apply-env : ∀ {Δ}{Θ : Telescope Δ} → (η : Env* Θ) → (α : TV ∈ Δ) → Set (level-of-tv′ η α)
apply-env [] ()
apply-env (η ▷ᴸ _) (there α) = apply-env η α
apply-env (η ▷ x) here = x
apply-env (η ▷ _) (there α) = apply-env η α

eval-strong-lan-≡ : ∀ {Δ}{Θ : Telescope Δ}{l : LAN Δ}
  → (x : LAN (TV ∷ Δ)) (η : Env* Θ) (⟦α⟧ : Set (eval-lan l η))
  → eval-lan x (_▷_ {l = l} η ⟦α⟧) ≡ eval-lan (strong-tv-lan x) η
eval-strong-lan-≡ (lacn x) η ⟦α⟧ = refl
eval-strong-lan-≡ (lavr (there x)) η ⟦α⟧ = refl

eval-strong-≡ : ∀ {Δ}{Θ : Telescope Δ}{l : LAN Δ}
  → (l′ : LVL (TV ∷ Δ)) (η : Env* Θ) (⟦α⟧ : Set (eval-lan l η))
  → eval-lv l′ (_▷_ {l = l} η ⟦α⟧) ≡ eval-lv (strong-tv l′) η
eval-strong-≡ {l = l} (lan x) η ⟦α⟧ = cong just (eval-strong-lan-≡ {l = l} x η ⟦α⟧)
eval-strong-≡ omg η ⟦α⟧ = refl
eval-strong-≡ (lub lv lv₁) η ⟦α⟧ = cong₂ _⊔_ (eval-strong-≡ lv η ⟦α⟧) (eval-strong-≡ lv₁ η ⟦α⟧)
eval-strong-≡ (lsc lv) η ⟦α⟧ = cong lsuc (eval-strong-≡ lv η ⟦α⟧)

⟦_⟧ : ∀ {Δ}{Θ : Telescope Δ}{l : LVL Δ} → Type Θ l → (η : Env* Θ) → SemLeveled (eval-lv l η)
⟦ 𝟙 ⟧ η = AtLev ⊤
⟦ ` α ⟧ η rewrite level-of-tv-≡ η α = AtLev (apply-env η α)
⟦ _⇒_ {l = l}{l′ = l′} T₁ T₂ ⟧ η
  with eval-lv l η | ⟦ T₁ ⟧ η | eval-lv l′ η | ⟦ T₂ ⟧ η
... | just l₁ | AtLev D₁ | just l₂ | AtLev D₂ = AtLev (D₁ → D₂)
... | just l₁ | AtLev D₁ | omega | Omega D₂ = Omega (D₁ → D₂)
... | omega | Omega D₁ | just l₂ | AtLev D₂ = Omega (D₁ → D₂)
... | omega | Omega D₁ | omega | Omega D₂ = Omega (D₁ → D₂)
⟦ `∀α_,_ {l′ = l′} l T ⟧ η
  with eval-lv (strong-tv l′) η in eq₂
... | just l₂ =
  AtLev ((⟦α⟧ : Set (eval-lan l η)) →
        fromLev (⟦ T ⟧ (η ▷ ⟦α⟧)) (trans (eval-strong-≡ l′ η ⟦α⟧) eq₂))
... | omega =
  Omega ((⟦α⟧ : Set (eval-lan l η)) →
        fromOmega (⟦ T ⟧ (η ▷ ⟦α⟧)) (trans (eval-strong-≡ l′ η ⟦α⟧) eq₂))
⟦_⟧ {Δ} (∀ᴸ_ {l = l} T) η
  with a-eval-lv l (η ▷ᴸ zero) in eq
... | ALevel = Omega (∀ (a : Level) → let l , elj = a-eval-level-just l (η ▷ᴸ a) (trans (a-eval-lv-≡ (η ▷ᴸ a) (η ▷ᴸ zero) l) eq)
                                      in  fromLev (⟦ T ⟧ (η ▷ᴸ a)) elj)
... | AOmega = Omega (∀ (a : Level) → let elo = a-eval-level-omega l (η ▷ᴸ a) (trans (a-eval-lv-≡ (η ▷ᴸ a) (η ▷ᴸ zero) l) eq)
                                      in  fromOmega (⟦ T ⟧ (η ▷ᴸ a)) elo)

-- -- apply-env : Env* Δ → l ∈ Δ → Set l
-- -- apply-env [] ()
-- -- apply-env (x ∷ _) here = x
-- -- apply-env (_ ∷ η) (there x) = apply-env η x

-- -- -- the meaning of a stratified type in terms of Agda universes

-- -- ⟦_⟧ : (T : Type Δ l) → Env* Δ → Set l
-- -- ⟦ ` x ⟧ η = apply-env η x
-- -- ⟦ T₁ ⇒ T₂ ⟧ η = ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η
-- -- ⟦ `∀α l , T ⟧ η = (α : Set l) → ⟦ T ⟧ (α ∷ η)
-- -- ⟦ 𝟙 ⟧ η = ⊤

-- -- -- renaming on types

-- -- Ren : LEnv → LEnv → Set
-- -- Ren Δ₁ Δ₂ = ∀ {l} → l ∈ Δ₁ → l ∈ Δ₂

-- -- wkᵣ : Ren Δ (l ∷ Δ)
-- -- wkᵣ = there

-- -- extᵣ : Ren Δ₁ Δ₂ → Ren (l ∷ Δ₁) (l ∷ Δ₂)
-- -- extᵣ ρ here = here
-- -- extᵣ ρ (there x) = there (ρ x)

-- -- renT : Ren Δ₁ Δ₂ → (Type Δ₁ l → Type Δ₂ l)
-- -- renT ρ (` x) = ` ρ x
-- -- renT ρ (T₁ ⇒ T₂) = renT ρ T₁ ⇒ renT ρ T₂
-- -- renT ρ (`∀α lev , T) = `∀α lev , renT (extᵣ ρ) T
-- -- renT ρ 𝟙 = 𝟙 

-- -- wkT : Type Δ l′ → Type (l ∷ Δ) l′
-- -- wkT = renT wkᵣ

-- -- -- the action of renaming on semantic environments

-- -- Ren* : (ρ : Ren Δ₁ Δ₂) → (η₁ : Env* Δ₁) → (η₂ : Env* Δ₂) → Setω
-- -- Ren* {Δ₁} ρ η₁ η₂ = ∀ {l : Level} → (x : l ∈ Δ₁) → apply-env η₂ (ρ x) ≡ apply-env η₁ x

-- -- wkᵣ∈Ren* : ∀ (η : Env* Δ) (⟦α⟧ : Set l)
-- --   → Ren* (wkᵣ{Δ}{l}) η (⟦α⟧ ∷ η)
-- -- wkᵣ∈Ren* η ⟦α⟧ x = refl

-- -- ren*-id : (η : Env* Δ) → Ren* (λ x → x) η η
-- -- ren*-id η x = refl

-- -- ren*-pop : (ρ : Ren (l ∷ Δ₁) Δ₂) (α : Set l) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂)
-- --   → Ren* ρ (α ∷ η₁) η₂
-- --   → Ren* (ρ ∘ there) η₁ η₂
-- -- ren*-pop ρ α η₁ η₂ ren* x = ren* (there x)

-- -- ren*-ext : ∀ {ρ : Ren Δ₁ Δ₂}{η₁ : Env* Δ₁}{η₂ : Env* Δ₂} (α : Set l)
-- --   → Ren* ρ η₁ η₂
-- --   → Ren* (extᵣ ρ) (α ∷ η₁) (α ∷ η₂)
-- -- ren*-ext α ren* here = refl
-- -- ren*-ext α ren* (there x) = ren* x

-- -- ren*-preserves-semantics : ∀ {ρ : Ren Δ₁ Δ₂}{η₁ : Env* Δ₁}{η₂ : Env* Δ₂}
-- --   → (ren* : Ren* ρ η₁ η₂) → (T : Type Δ₁ l)
-- --   → ⟦ renT ρ T ⟧ η₂ ≡ ⟦ T ⟧ η₁
-- -- ren*-preserves-semantics ren* (` x) = ren* x
-- -- ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* (T₁ ⇒ T₂)
-- --   rewrite ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* T₁
-- --   | ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* T₂
-- --   = refl
-- -- ren*-preserves-semantics {ρ = ρ}{η₁}{η₂} ren* (`∀α l , T) =
-- --   dependent-extensionality (λ α →
-- --     ren*-preserves-semantics{ρ = extᵣ ρ}{α ∷ η₁}{α ∷ η₂} (ren*-ext{ρ = ρ} α ren*) T)
-- -- ren*-preserves-semantics ren* 𝟙 = refl

-- -- -- substitution on types

-- -- data Sub : LEnv → LEnv → Set where
-- --   []  : Sub [] Δ₂
-- --   _∷_ : Type Δ₂ l → Sub Δ₁ Δ₂ → Sub (l ∷ Δ₁) Δ₂

-- -- apply-sub : l ∈ Δ₁ → Sub Δ₁ Δ₂ → Type Δ₂ l
-- -- apply-sub here (T ∷ _) = T
-- -- apply-sub (there x) (_ ∷ σ) = apply-sub x σ

-- -- build-id : (Δ₁ : LEnv) → Ren Δ₁ Δ → Sub Δ₁ Δ
-- -- build-id [] ρ = []
-- -- build-id (l ∷ Δ₁) ρ = (` ρ here) ∷ build-id Δ₁ (ρ ∘ there)

-- -- idₛ : Sub Δ Δ
-- -- idₛ {Δ} = build-id Δ (λ x → x)

-- -- wkₛ : Sub Δ₁ Δ₂ → Sub Δ₁ (l ∷ Δ₂)
-- -- wkₛ [] = []
-- -- wkₛ (T ∷ σ) = wkT T ∷ wkₛ σ

-- -- extₛ : Sub Δ₁ Δ₂ → ∀ {l} → Sub (l ∷ Δ₁) (l ∷ Δ₂)
-- -- extₛ σ = ` here ∷ wkₛ σ

-- -- subT : Sub Δ₁ Δ₂ → Type Δ₁ l → Type Δ₂ l
-- -- subT σ (` x) = apply-sub x σ
-- -- subT σ (T₁ ⇒ T₂) = subT σ T₁ ⇒ subT σ T₂
-- -- subT σ (`∀α l , T) = `∀α l , subT (extₛ σ) T
-- -- subT σ 𝟙 = 𝟙

-- -- singleₛ : Sub Δ₁ Δ₂ → ∀ {l} → Type Δ₂ l → Sub (l ∷ Δ₁) Δ₂
-- -- singleₛ σ T' = T' ∷ σ

-- -- _[_]T : Type (l ∷ Δ) l′ → Type Δ l → Type Δ l′
-- -- _[_]T T T' = subT (singleₛ idₛ T') T

-- type environments

data TEnv : {Δ : List Kind} → Telescope Δ → Set where
  ∅    : TEnv []
  _▷_  : ∀{Δ}{Θ : Telescope Δ}{l : LVL Δ} → TEnv Θ → Type Θ l → TEnv Θ
  _▷*_ : ∀{Δ}{Θ : Telescope Δ}{l : LVL Δ} → TEnv Θ → (la : LAN Δ) → TEnv (la ∷ Θ)
  _▷ℓ : ∀{Δ}{Θ : Telescope Δ}{l : LVL Δ} → TEnv Θ → TEnv (*ᴸ Θ)

data inn : ∀ {Δ} {l : LVL Δ} {Θ : Telescope Δ} → Type Θ l → TEnv Θ → Set where
  here  : ∀{Δ}{l}{Θ : Telescope Δ}{T : Type Θ l}{Γ} → inn T (Γ ▷ T)
  there : ∀{Δ}{l}{Θ : Telescope Δ}{T T′ : Type Θ l}{Γ} → inn T Γ → inn T (Γ ▷ T′)
  tskip : ∀{Δ}{l}{Θ : Telescope Δ}{T : Type Θ l}{Γ}{l′} → inn T Γ → inn {!!} (Γ ▷* l′)
  lskip : ∀{Δ}{l}{Θ : Telescope Δ}{T : Type Θ l}{Γ} → inn T Γ → inn {!!} (Γ ▷ℓ)

-- -- data Expr (Δ : LEnv) (Γ : TEnv Δ) : Type Δ l → Set where
-- --   `_   : ∀ {T : Type Δ l} → inn T Γ → Expr Δ Γ T
-- --   ƛ_   : ∀ {T : Type Δ l}{T′ : Type Δ l′} → Expr Δ (T ◁ Γ) T′ → Expr Δ Γ (T ⇒ T′)
-- --   _·_  : ∀ {T : Type Δ l}{T′ : Type Δ l′} → Expr Δ Γ (T ⇒ T′) → Expr Δ Γ T → Expr Δ Γ T′
-- --   Λ_⇒_ : ∀ (l : Level) → {T : Type (l ∷ Δ) l′} → Expr (l ∷ Δ) (l ◁* Γ) T → Expr Δ Γ (`∀α l , T)
-- --   _∙_  : ∀ {T : Type (l ∷ Δ) l′} → Expr Δ Γ (`∀α l , T) → (T′ : Type Δ l) → Expr Δ Γ (T [ T′ ]T)

-- -- -- value environments

-- -- Env : (Δ : LEnv) → TEnv Δ → Env* Δ → Setω
-- -- Env Δ Γ η = ∀ {l}{T : Type Δ l} → (x : inn T Γ) → ⟦ T ⟧ η

-- -- extend : ∀ {T : Type Δ l}{Γ : TEnv Δ}{η : Env* Δ}
-- --   → Env Δ Γ η → ⟦ T ⟧ η
-- --   → Env Δ (T ◁ Γ) η
-- -- extend γ v here = v
-- -- extend γ v (there x) = γ x

-- -- extend-tskip : ∀ {Δ : LEnv}{Γ : TEnv Δ}{η : Env* Δ}{⟦α⟧ : Set l}
-- --   → Env Δ Γ η
-- --   → Env (l ∷ Δ) (l ◁* Γ) (⟦α⟧ ∷ η)
-- -- extend-tskip {η = η} {⟦α⟧ = ⟦α⟧} γ (tskip{T = T} x)
-- --   rewrite ren*-preserves-semantics {ρ = wkᵣ}{η}{⟦α⟧ ∷ η} (wkᵣ∈Ren* η ⟦α⟧) T
-- --   = γ x

-- -- subst-to-env* : (σ : Sub Δ₁ Δ₂) → (η₂ : Env* Δ₂) → Env* Δ₁
-- -- subst-to-env* [] η₂ = []
-- -- subst-to-env* (T ∷ σ) η₂ = ⟦ T ⟧ η₂ ∷ subst-to-env* σ η₂

-- -- subst-var-preserves : (x  : l ∈ Δ₁) (σ  : Sub Δ₁ Δ₂) (η₂ : Env* Δ₂)
-- --   → ⟦ apply-sub x σ ⟧ η₂ ≡ apply-env (subst-to-env* σ η₂) x
-- -- subst-var-preserves here (T ∷ σ) η₂ = refl
-- -- subst-var-preserves (there x) (_ ∷ σ) η₂ = subst-var-preserves x σ η₂

-- -- subst-to-env*-wk : (σ  : Sub Δ₁ Δ₂) (α  : Set l) (η₂ : Env* Δ₂)
-- --   → subst-to-env* (wkₛ σ) (α ∷ η₂) ≡ω subst-to-env* σ η₂
-- -- subst-to-env*-wk [] α η₂ = refl
-- -- subst-to-env*-wk (T ∷ σ) α η₂
-- --   rewrite ren*-preserves-semantics {ρ = wkᵣ}{η₂}{α ∷ η₂} (wkᵣ∈Ren* η₂ α) T
-- --   = congωω (⟦ T ⟧ η₂ ∷_) (subst-to-env*-wk σ α η₂)

-- -- subst-to-env*-build : ∀ (ρ : Ren Δ₁ Δ₂) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂)
-- --   → Ren* ρ η₁ η₂
-- --   → subst-to-env* (build-id Δ₁ ρ) η₂ ≡ω η₁
-- -- subst-to-env*-build ρ [] η₂ ren* = refl
-- -- subst-to-env*-build {Δ₁ = _ ∷ Δ₁} ρ (α ∷ η₁) η₂ ren* = 
-- --   transω (congωω (apply-env η₂ (ρ here) ∷_) (subst-to-env*-build (ρ ∘ there) η₁ η₂ (ren*-pop ρ α η₁ η₂ ren*)))
-- --          (conglω (_∷ η₁) (ren* here))

-- -- subst-to-env*-id : (η : Env* Δ) → subst-to-env* idₛ η ≡ω η
-- -- subst-to-env*-id {Δ} η = subst-to-env*-build {Δ₁ = Δ} (λ x → x) η η (ren*-id η)

-- -- subst-preserves-type : Setω
-- -- subst-preserves-type =
-- --   ∀ {Δ₁ Δ₂}{l}{η₂ : Env* Δ₂}
-- --   → (σ : Sub Δ₁ Δ₂) (T : Type Δ₁ l)
-- --   → ⟦ subT σ T ⟧ η₂ ≡ ⟦ T ⟧ (subst-to-env* σ η₂)

-- -- subst-preserves : subst-preserves-type
-- -- subst-preserves {η₂ = η₂} σ (` x) = subst-var-preserves x σ η₂
-- -- subst-preserves{η₂ = η₂} σ (T₁ ⇒ T₂)
-- --   rewrite subst-preserves{η₂ = η₂} σ T₁
-- --   |  subst-preserves{η₂ = η₂} σ T₂ = refl
-- -- subst-preserves {η₂ = η₂} σ (`∀α l , T) =
-- --   dependent-extensionality (λ α →
-- --     trans (subst-preserves {η₂ = α ∷ η₂} (extₛ σ) T)
-- --           (congωl (λ H → ⟦ T ⟧ (α ∷ H)) (subst-to-env*-wk σ α η₂)))
-- -- subst-preserves σ 𝟙 = refl

-- -- single-subst-preserves : ∀ (η : Env* Δ) (T′ : Type Δ l) (T : Type (l ∷ Δ) l′)
-- --   → ⟦ T [ T′ ]T ⟧ η ≡ ⟦ T ⟧ (⟦ T′ ⟧ η ∷ η)
-- -- single-subst-preserves {Δ = Δ} {l = l}{l′ = l′} η T′ T =
-- --   trans (subst-preserves (singleₛ idₛ T′) T)
-- --         (congωl (λ H → ⟦ T ⟧ (⟦ T′ ⟧ η ∷ H)) (subst-to-env*-id η))

-- -- E⟦_⟧ : ∀ {T : Type Δ l}{Γ : TEnv Δ} → Expr Δ Γ T → (η : Env* Δ) → Env Δ Γ η → ⟦ T ⟧ η
-- -- E⟦ ` x ⟧ η γ = γ x
-- -- E⟦ ƛ_ e ⟧ η γ = λ v → E⟦ e ⟧ η (extend γ v)
-- -- E⟦ e₁ · e₂ ⟧ η γ = E⟦ e₁ ⟧ η γ (E⟦ e₂ ⟧ η γ)
-- -- E⟦ Λ l ⇒ e ⟧ η γ = λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ η) (extend-tskip γ)
-- -- E⟦ _∙_ {T = T} e T′ ⟧ η γ
-- --   with E⟦ e ⟧ η γ (⟦ T′ ⟧ η)
-- -- ... | v rewrite single-subst-preserves η T′ T = v 
