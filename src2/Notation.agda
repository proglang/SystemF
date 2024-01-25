module Notation where

open import Level using (Level)
open import Data.List using ([])

open import Prelude
open import Type
open import Expr


Type : KindCtx → Level → Set
Type = _⊢_

-- closed types
CType : Level → Set
CType = [] ⊢_

Expr : (Δ : KindCtx) → TypeCtx Δ → Type Δ l → Set
Expr = _⍮_⊢_

-- closed expressions
CExpr : CType l → Set
CExpr = [] ⍮ [] ⊢_
