module BigStep where

open import Data.List using (List; []; _∷_; [_])
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)

open import Types
open import Expressions
open import ExprSubstitution

----------------------------------------------------------------------
--! BigStep >

-- big step call by value semantics (analogous to Benton et al)

--! CExpr
CExpr : Type [] l → Set
CExpr T = Expr [] ∅ T

--! isValue
data isValue : ∀ {l}{T : Type [] l} → CExpr T → Set where
  V-♯ : ∀ {n}
    → isValue (# n)
  V-ƛ : ∀ {l₁ l₂}{T₁ : Type [] l₁}{T₂ : Type [] l₂}{e : Expr [] (T₁ ◁ ∅) T₂}
    → isValue (ƛ e)
  V-Λ : ∀ {l₁ l₂}{T′ : Type (l₁ ∷ []) l₂}{e : Expr (l₁ ∷ []) (l₁ ◁* ∅) T′}
    → isValue (Λ l₁ ⇒ e)

--! Value
record CValue (T : Type [] l) : Set where
  constructor _,_
  field
    exp : CExpr T
    prf : isValue exp

open CValue public

-- big step semantics

variable v v₂ : CValue T
infix 15 _⇓_
--! Semantics
data _⇓_ : CExpr T → CValue T → Set where
  ⇓-n : # n ⇓ (# n , V-♯)
  ⇓-s : e ⇓ (# n , V-♯)
      → `suc e ⇓ (# suc n , V-♯)
  ⇓-ƛ : ƛ e ⇓ (ƛ e , V-ƛ)
  ⇓-· : e₁ ⇓ (ƛ e , V-ƛ)
      → e₂ ⇓ v₂
      → (e [ exp v₂ ]E) ⇓ v
      → (e₁ · e₂) ⇓ v
  ⇓-Λ : Λ l ⇒ e ⇓ (Λ l ⇒ e , V-Λ)
  ⇓-∙ : e₁ ⇓ (Λ l ⇒ e , V-Λ)
      → (e [ T ]ET) ⇓ v
      → (e₁ ∙ T) ⇓ v

--! ValueReduceSelf
Value-⇓ : ∀ {l} {T : Type [] l} → (v : CValue T) → exp v ⇓ v
Value-⇓ (.(# _) ,     V-♯) = ⇓-n
Value-⇓ (.(ƛ _) ,     V-ƛ) = ⇓-ƛ
Value-⇓ (.(Λ _ ⇒ _) , V-Λ) = ⇓-Λ

----------------------------------------------------------------------
-- compatibility

Value = CValue
