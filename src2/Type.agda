open import Level using (Level; zero; suc; _⊔_)
open import Data.List using (List; []; _∷_)

open import Prelude hiding (zero; suc)

module Type where

KindCtx : Set
KindCtx = List Level

variable
  l l₁ l₂ l₃ l' l₁' l₂' l₃' : Level
  Δ Δ₁ Δ₂ Δ₃ Δ' Δ₁' Δ₂' Δ₃' : KindCtx
  α α₁ α₂ α₃ α' α₁' α₂' α₃' : Δ ∋ l

data _⊢_ : KindCtx → Level → Set where
  `ℕ : Δ ⊢ zero
  `_      :
    Δ ∋ l →
    Δ ⊢ l
  ∀[α∶_]_ :
    (l : Level) →
    (l ∷ Δ) ⊢ l' →
    Δ ⊢ (suc l ⊔ l')
  _⇒_ :
    Δ ⊢ l →
    Δ ⊢ l' →
    Δ ⊢ (l ⊔ l')
    
variable
  t t₁ t₂ t₃ t' t₁' t₂' t₃' : Δ ⊢ l
  
data TypeCtx : KindCtx → Set where
  []   : TypeCtx Δ
  _∷_  : Δ ⊢ l → TypeCtx Δ → TypeCtx Δ
  _∷⋆_ : (l : Level) → TypeCtx Δ → TypeCtx (l ∷ Δ)

variable
  Γ Γ₁ Γ₂ Γ₃ Γ' Γ₁' Γ₂' Γ₃' : TypeCtx Δ
