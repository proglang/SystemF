\begin{code}
module STLC where

open import Data.Nat  using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)

data Type : Set where
  nat : Type
  _⇒_ : Type → Type → Type

𝓣⟦_⟧ : Type → Set
𝓣⟦ nat ⟧ = ℕ
𝓣⟦ S ⇒ T ⟧ = 𝓣⟦ S ⟧ → 𝓣⟦ T ⟧

Env = List Type

data _∈_ : Type → Env → Set where
  here  : ∀ {T Γ} → T ∈ (T ∷ Γ)
  there : ∀ {S T Γ} → S ∈ Γ → S ∈ (T ∷ Γ)

data Expr (Γ : Env) : Type → Set where
  con : ℕ → Expr Γ nat
  var : ∀ {T} → T ∈ Γ → Expr Γ T
  lam : ∀ {S T} → Expr (S ∷ Γ) T → Expr Γ (S ⇒ T)
  app : ∀ {S T} → Expr Γ (S ⇒ T) → Expr Γ S → Expr Γ T

data ⟦_⟧ : Env → Set where
  []  : ⟦ [] ⟧
  _∷_ : ∀ {T Γ} → 𝓣⟦ T ⟧ → ⟦ Γ ⟧ → ⟦ T ∷ Γ ⟧

lookup : ∀ {T Γ} → (T ∈ Γ) → ⟦ Γ ⟧ → 𝓣⟦ T ⟧
lookup here (x ∷ _) = x
lookup (there x) (_ ∷ γ) = lookup x γ

𝓔⟦_⟧ : ∀ {Γ T} → Expr Γ T → ⟦ Γ ⟧ → 𝓣⟦ T ⟧
𝓔⟦ con n ⟧ γ = n
𝓔⟦ var x ⟧ γ = lookup x γ
𝓔⟦ lam e ⟧ γ = λ v → 𝓔⟦ e ⟧ (v ∷ γ)
𝓔⟦ app e₁ e₂ ⟧ γ = 𝓔⟦ e₁ ⟧ γ (𝓔⟦ e₂ ⟧ γ)
\end{code}
\begin{code}[hide]

_ : Expr [] (nat ⇒ nat)
_ = lam (con zero)

_ : Expr [] (nat ⇒ nat)
_ = lam (var here)
\end{code}
