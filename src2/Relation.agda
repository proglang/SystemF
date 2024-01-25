module Relation where

open import Level using (Level; Setω; suc)
open import Data.List using (List; []; [_])
open import Data.Product using (Σ; _×_; ∃-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Prelude
open import Type
import TypeSub as T
open import Expr
import ExprSub as E
import ExprTypeSub as ET

open import Denotational
open import Notation
open import BigStep

-- relation between a syntactic value and a semantic value

REL : ∀ {l : Level} → CType l → Set (Level.suc l)
REL {l} T = Value T → ⟦ T ⟧ₜ []⋆ → Set l 

RelEnv : KindCtx → Setω
RelEnv Δ = ∀ l → Δ ∋ l → Σ (Type [] l) REL

subst←RE : RelEnv Δ → Δ T.⇒ₛ []
subst←RE ρ l x = proj₁ (ρ l x)


𝓥⟦_⟧ : (t : Type Δ l) → (ρ : RelEnv Δ)
  → let σ = (subst←RE ρ)
  in  Value (t T.⋯ₛ σ) → Value (t T.⋯ₛ σ) → Set l
𝓥⟦ `ℕ ⟧ ρ = λ v₁ v₂ → ∃[ n ] (v₁ ≡ (# n , V-♯) × v₂ ≡ (# n , V-♯))
𝓥⟦ ` α ⟧ ρ = {!!}
𝓥⟦ ∀[α∶ l ] t ⟧ ρ = {!!}
𝓥⟦ t ⇒ t₁ ⟧ ρ = {!!}


