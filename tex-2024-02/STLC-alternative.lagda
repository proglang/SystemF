\begin{code}
module STLC-alternative where

open import Data.Nat  using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)

data Type : Set where
  nat : Type
  _⇒_ : Type → Type → Type

𝓣⟦_⟧ : Type → Set
𝓣⟦ nat ⟧   = ℕ
𝓣⟦ S ⇒ T ⟧ = 𝓣⟦ S ⟧ → 𝓣⟦ T ⟧

Env = List Type

data Var : Env → Type → Set where
  here  : ∀ {T Γ} →             Var (T ∷ Γ) T
  there : ∀ {S T Γ} → Var Γ T → Var (S ∷ Γ) T

data Expr (Γ : Env) : Type → Set where
  con : ℕ → Expr Γ nat
  var : ∀ {T} → Var Γ T → Expr Γ T
  lam : ∀ {S T} → Expr (S ∷ Γ) T → Expr Γ (S ⇒ T)
  app : ∀ {S T} → Expr Γ (S ⇒ T) → Expr Γ S → Expr Γ T

module alt where
  open import Data.Unit using (⊤; tt)
  open import Data.Product
  
  𝓖⟦_⟧ : Env → Set
  𝓖⟦ [] ⟧ = ⊤
  𝓖⟦ T ∷ Γ ⟧ = 𝓣⟦ T ⟧ × 𝓖⟦ Γ ⟧

  extend : ∀ {T}{Γ} → 𝓣⟦ T ⟧ → 𝓖⟦ Γ ⟧ → 𝓖⟦ T ∷ Γ ⟧
  extend v γ = v , γ

  lookup : ∀ {T Γ} → Var Γ T → 𝓖⟦ Γ ⟧ → 𝓣⟦ T ⟧
  lookup here (v , _) = v
  lookup (there x) (_ , γ) = lookup x γ
    

𝓖⟦_⟧ : Env → Set
𝓖⟦ Γ ⟧ = ∀ {T} → Var Γ T → 𝓣⟦ T ⟧

extend : ∀ {T}{Γ} → 𝓣⟦ T ⟧ → 𝓖⟦ Γ ⟧ → 𝓖⟦ T ∷ Γ ⟧
extend v γ here = v
extend v γ (there x) = γ x

𝓔⟦_⟧ : ∀ {Γ T} → Expr Γ T → 𝓖⟦ Γ ⟧ → 𝓣⟦ T ⟧
𝓔⟦ con n ⟧ γ     = n
𝓔⟦ var x ⟧ γ     = γ x
𝓔⟦ lam e ⟧ γ     = λ v → 𝓔⟦ e ⟧ (extend v γ)
𝓔⟦ app e₁ e₂ ⟧ γ = 𝓔⟦ e₁ ⟧ γ (𝓔⟦ e₂ ⟧ γ)
\end{code}
\begin{code}[hide]
_ : Expr [] (nat ⇒ nat)
_ = lam (con zero)

_ : Expr [] (nat ⇒ nat)
_ = lam (var here)
\end{code}
