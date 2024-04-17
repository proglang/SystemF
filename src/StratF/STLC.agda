module StratF.STLC where

open import Data.Nat  using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)

--! STLC >

--! Type
data Type : Set where
  nat  : Type
  _⇒_  : Type → Type → Type

--! TypeDenot
𝓣⟦_⟧ : Type → Set
𝓣⟦ nat    ⟧ = ℕ
𝓣⟦ S ⇒ T  ⟧ = 𝓣⟦ S ⟧ → 𝓣⟦ T ⟧

--! TypeEnv
Env = List Type

--! Var
data Var : Env → Type → Set where
  here   : ∀ {T Γ} →             Var (T ∷ Γ) T
  there  : ∀ {S T Γ} → Var Γ T → Var (S ∷ Γ) T

--! Expr
data Expr (Γ : Env) : Type → Set where
  #_   : ℕ → Expr Γ nat
  `_   : ∀ {T} → Var Γ T → Expr Γ T
  λx   : ∀ {S T} → Expr (S ∷ Γ) T → Expr Γ (S ⇒ T)
  _·_  : ∀ {S T} → Expr Γ (S ⇒ T) → Expr Γ S → Expr Γ T

--! ExprEnv
data 𝓖⟦_⟧ : Env → Set where
  []   : 𝓖⟦ [] ⟧
  _∷_  : ∀ {T Γ} → 𝓣⟦ T ⟧ → 𝓖⟦ Γ ⟧ → 𝓖⟦ T ∷ Γ ⟧

--! Lookup
lookup : ∀ {T Γ} → Var Γ T → 𝓖⟦ Γ ⟧ → 𝓣⟦ T ⟧
lookup here       (v ∷ _)  = v
lookup (there x)  (_ ∷ γ)  = lookup x γ

--! ExprDenot
𝓔⟦_⟧ : ∀ {Γ T} → Expr Γ T → 𝓖⟦ Γ ⟧ → 𝓣⟦ T ⟧
𝓔⟦ # n      ⟧ γ = n
𝓔⟦ ` x      ⟧ γ = lookup x γ
𝓔⟦ λx e      ⟧ γ = λ v → 𝓔⟦ e ⟧ (v ∷ γ)
𝓔⟦ e₁ · e₂  ⟧ γ = 𝓔⟦ e₁ ⟧ γ (𝓔⟦ e₂ ⟧ γ)