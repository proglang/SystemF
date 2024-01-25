module BigStep where

open import Level using (Level)
open import Data.List using (List; []; [_])
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import Prelude
open import Type
open import Expr
import ExprSub as E
import ExprTypeSub as ET

open import Notation

-- values

data isValue : ∀{l} {T : CType l} → CExpr T → Set where
  V-♯ : ∀ {n}
    → isValue (# n)
  V-ƛ : ∀ {T₁ : CType l₁}{T₂ : CType l₂}{e : Expr [] (T₁ ∷ []) T₂}
    → isValue (λx e)
  V-Λ : ∀ {T′ : Type [ l₁ ] l₂}{e : Expr [ l₁ ] (l₁ ∷⋆ []) T′}
    → isValue (Λ[α∶ l₁ ] e)

record Value (T : CType l) : Set where
  constructor _,_
  field
    exp : CExpr T
    isv : isValue exp
open Value

variable
  T : Type Δ l
  v v₂ : Value T

-- big step semantics

infix 15 _⇓_
data _⇓_ : CExpr T → Value T → Set where
  ⇓-n : # n ⇓ (# n , V-♯)
  ⇓-ƛ : λx e ⇓ (λx e , V-ƛ)
  ⇓-· : e₁ ⇓ (λx e , V-ƛ)
      → e₂ ⇓ v₂
      → e E.[ exp v₂ ] ⇓ v
      → (e₁ · e₂) ⇓ v
  ⇓-Λ : Λ[α∶ l ] e ⇓ (Λ[α∶ l ] e , V-Λ)
  ⇓-∙ : e₁ ⇓ (Λ[α∶ l ] e , V-Λ)
      → (e ET.[ T ]) ⇓ v
      → (e₁ ∙ T) ⇓ v

-- values evaluate to themselves

Value-⇓ : ∀ {T : CType l} → (v : Value T) → exp v ⇓ v
Value-⇓ ((# n) , V-♯) = ⇓-n
Value-⇓ ((` x) , ())
Value-⇓ ((λx e) , V-ƛ) = ⇓-ƛ
Value-⇓ ((Λ[α∶ l ] e) , V-Λ) = ⇓-Λ
Value-⇓ ((e · e₁) , ())
Value-⇓ ((e ∙ t') , ())
