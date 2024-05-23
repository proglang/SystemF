module StratF.Evaluation where

open import Data.List using (List; []; _∷_; [_])
open import Data.Nat using (ℕ; suc)

open import StratF.ExprSubstitution
open import StratF.Expressions
open import StratF.Types

--! BigStep >

-- big step call by value semantics (analogous to Benton et al)

--! CExpr
CExpr : Type [] l → Set
CExpr T = Expr [] ∅ T

--! isValue
data isValue : Expr Δ Γ T → Set where
  V-♯  : isValue {Δ} {Γ} (# n)
  V-ƛ  : isValue (ƛ e)
  V-Λ  : isValue (Λ l ⇒ e)


--! Value
record CValue (T : Type [] l) : Set where
  constructor _,_
  field  exp : CExpr T
         prf : isValue exp

open CValue public

-- general evaluation API

variable v v₂ : CValue T


record Eval : Set₁ where
  infix 15 _↓_ 
  field
    _↓_ : ∀ {T : Type [] l} → CExpr T → CValue T → Set
    ↓-n : (# n) ↓ ((# n) , V-♯)
    ↓-s : e ↓ ((# n) , V-♯) → `suc e ↓ ((# suc n) , V-♯)
    ↓-ƛ : (ƛ e) ↓ ((ƛ e) , V-ƛ)
    ↓-· : e₁ ↓ ((ƛ e) , V-ƛ) → e₂ ↓ v₂ → (e [ exp v₂ ]E) ↓ v → (e₁ · e₂) ↓ v
    ↓-Λ : (Λ l ⇒ e) ↓ ((Λ l ⇒ e) , V-Λ)
    ↓-∙ : e₁ ↓ ((Λ l ⇒ e) , V-Λ) → (e [ T ]ET) ↓ v → (e₁ ∙ T) ↓ v
    Value-↓ : ∀ {T : Type [] l} → (v : CValue T) → exp v ↓ v


-- compatibility

Value = CValue
