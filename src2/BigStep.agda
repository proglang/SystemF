module BigStep where

open import Level using (Level)
open import Data.List using (List; []; [_])
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import Prelude
open import Type
open import Expr
import ExprSub as E
import ExprTypeSub as ET

Type : KindCtx → Level → Set
Type = _⊢_

-- closed types
CType : Level → Set
CType = Type []

Expr : (Δ : KindCtx) → TypeCtx Δ → Type Δ l → Set
Expr = _⍮_⊢_

-- closed expressions
CExpr : CType l → Set
CExpr T = Expr [] [] T

-- values

data isValue : ∀{l} {T : CType l} → CExpr T → Set where
  -- V-#
  V-ƛ : ∀ {T₁ : CType l₁}{T₂ : CType l₂}{e : Expr [] (T₁ ∷ []) T₂}
    → isValue (λx e)
  V-Λ : ∀ {T′ : Type [ l₁ ] l₂}{e : Expr [ l₁ ] (l₁ ∷⋆ []) T′}
    → isValue (Λ[α∶ l₁ ] e)

Value : CType l → Set
Value T = Σ (CExpr T) isValue

variable
  T : Type Δ l
  v v₂ : Value T

exp : ∀ {T : CType l} → Value T → CExpr T
exp = proj₁

-- big step semantics

infix 15 _⇓_
data _⇓_ : CExpr T → Value T → Set where
  -- ⇓-n : # n ⇓ (# n , V-♯)
  ⇓-ƛ : λx e ⇓ (λx e , V-ƛ)
  ⇓-· : e₁ ⇓ (λx e , V-ƛ)
      → e₂ ⇓ v₂
      → e E.[ exp v₂ ] ⇓ v
      → (e₁ · e₂) ⇓ v
  ⇓-Λ : Λ[α∶ l ] e ⇓ (Λ[α∶ l ] e , V-Λ)
  ⇓-∙ : e₁ ⇓ (Λ[α∶ l ] e , V-Λ)
      → (e ET.[ T ]) ⇓ v
      → (e₁ ∙ T) ⇓ v
