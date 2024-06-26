module StratF.Expressions where

open import Level renaming (suc to lsuc; zero to lzero)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong; module ≡-Reasoning)
open ≡-Reasoning

open import StratF.TypeSubstPropertiesSem
open import StratF.TypeSubstitution
open import StratF.Types

--! TF >

-- type environments

--! TVEnv 
data Ctx : LEnv → Set where
  ∅     : Ctx []
  _◁_   : Type Δ l → Ctx Δ → Ctx Δ          
  _◁*_  : (l : Level) → Ctx Δ → Ctx (l ∷ Δ) 

variable Γ Γ₁ Γ₂ Γ₂₁ Γ₂₂ : Ctx Δ

--! inn
data inn : Type Δ l → Ctx Δ → Set where
  here   : inn T (T ◁ Γ)
  there  : inn T Γ → inn T (T′ ◁ Γ)
  tskip  : inn T Γ → inn (Twk T) (l ◁* Γ)

data Expr (Δ : LEnv) (Γ : Ctx Δ) : Type Δ l → Set where
  #_    : (n : ℕ) → Expr Δ Γ `ℕ
  `suc  : Expr Δ Γ `ℕ → Expr Δ Γ `ℕ
  `_    : ∀ {T : Type Δ l} → inn T Γ → Expr Δ Γ T
  ƛ_    : ∀ {T : Type Δ l} {T′ : Type Δ l′} → Expr Δ (T ◁ Γ) T′ → Expr Δ Γ (T ⇒ T′)
  _·_   : ∀ {T : Type Δ l} {T′ : Type Δ l′} → Expr Δ Γ (T ⇒ T′) → Expr Δ Γ T → Expr Δ Γ T′
  Λ_⇒_  : ∀ (l : Level) → {T : Type (l ∷ Δ) l′} → Expr (l ∷ Δ) (l ◁* Γ) T → Expr Δ Γ (`∀α l , T)
  _∙_   : ∀ {T : Type (l ∷ Δ) l′} → Expr Δ Γ (`∀α l , T) → (T′ : Type Δ l) → Expr Δ Γ (T [ T′ ]T)

variable e e₁ e₂ e₃ : Expr Δ Γ T
variable n : ℕ

-- value environments

--! VEnv
Env : (Δ : LEnv) → Ctx Δ → Env* Δ → Setω
Env Δ Γ η = ∀ l (T : Type Δ l) → (x : inn T Γ) → ⟦ T ⟧ η

variable 
  γ γ₁ γ₂ : Env Δ Γ η

extend : ∀ {T : Type Δ l}{Γ : Ctx Δ}{η : Env* Δ}
  → Env Δ Γ η → ⟦ T ⟧ η → Env Δ (T ◁ Γ) η
extend γ v _ _ here = v
extend γ v _ _ (there x) = γ _ _ x

--! ExtendTskip
extend-tskip :  ∀ {⟦α⟧ : Set l} → Env Δ Γ η → 
                Env (l ∷ Δ) (l ◁* Γ) (⟦α⟧ ∷ η)
extend-tskip {⟦α⟧ = ⟦α⟧} γ _ _ (tskip {T = T} x) = subst 
  id (sym (Tren*-preserves-semantics (wkᵣ∈Ren* _ ⟦α⟧) T)) 
  (γ _ _ x)

--! ExprSem
E⟦_⟧ : Expr Δ Γ T → (η : Env* Δ) → Env Δ Γ η → ⟦ T ⟧ η
E⟦ # n ⟧ η γ = n
E⟦ `suc e ⟧ η γ = suc (E⟦ e ⟧ η γ)
E⟦ ` x ⟧ η γ = γ _ _ x
E⟦ ƛ_ e ⟧ η γ = λ v → E⟦ e ⟧ η (extend γ v)
E⟦ e₁ · e₂ ⟧ η γ = E⟦ e₁ ⟧ η γ (E⟦ e₂ ⟧ η γ)
E⟦ Λ l ⇒ e ⟧ η γ = λ ⟦α⟧ → E⟦ e ⟧ (⟦α⟧ ∷ η) (extend-tskip γ)
E⟦ _∙_ {T = T} e T′ ⟧ η γ = subst id 
  (sym (Tsingle-subst-preserves η T′ T)) (E⟦ e ⟧ η γ (⟦ T′ ⟧ η))

-- auxiliary

levelTy : Type Δ l → Level
levelTy {l = l} T = l

levelEnv : Ctx Δ → Level
levelEnv ∅ = lzero
levelEnv (T ◁ Γ) = levelTy T ⊔ levelEnv Γ
levelEnv (l ◁* Γ) = levelEnv Γ

-- compatibility

TEnv = Ctx
