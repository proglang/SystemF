module TypeSub where

open import Data.List using (List; []; _∷_)

open import Prelude
open import Type

_⇒ᵣ_ : KindCtx → KindCtx → Set
Δ₁ ⇒ᵣ Δ₂ = ∀ l → Δ₁ ∋ l → Δ₂ ∋ l

_⇒ₛ_ : KindCtx → KindCtx → Set
Δ₁ ⇒ₛ Δ₂ = ∀ l → Δ₁ ∋ l → Δ₂ ⊢ l

_↑ᵣ_ : Δ₁ ⇒ᵣ Δ₂ → ∀ l → (l ∷ Δ₁) ⇒ᵣ (l ∷ Δ₂)
(ρ ↑ᵣ k) _ zero    = zero
(ρ ↑ᵣ k) _ (suc x) = suc (ρ _ x)

_⋯ᵣ_ : Δ₁ ⊢ l → Δ₁ ⇒ᵣ Δ₂ → Δ₂ ⊢ l
`ℕ           ⋯ᵣ ρ = `ℕ
(` x)        ⋯ᵣ ρ = ` ρ _ x
(∀[α∶ l ] t) ⋯ᵣ ρ = ∀[α∶ l ] (t ⋯ᵣ (ρ ↑ᵣ l))
(t₁ ⇒ t₂)    ⋯ᵣ ρ = (t₁ ⋯ᵣ ρ) ⇒ (t₂ ⋯ᵣ ρ)

idᵣ : Δ ⇒ᵣ Δ
idᵣ _ x = x 

wkᵣ' : ∀ l → Δ₁ ⇒ᵣ Δ₂ → Δ₁ ⇒ᵣ (l ∷ Δ₂)
wkᵣ' l ρ _ x = suc (ρ _  x)

wkᵣ : ∀ l → Δ ⇒ᵣ (l ∷ Δ)
wkᵣ l _ x = suc x

_↑ₛ_ : Δ₁ ⇒ₛ Δ₂ → ∀ l → (l ∷ Δ₁) ⇒ₛ (l ∷ Δ₂)
(σ ↑ₛ k) _ zero    = ` zero
(σ ↑ₛ k) _ (suc x) = σ _ x ⋯ᵣ wkᵣ _

_⋯ₛ_ : Δ₁ ⊢ l → Δ₁ ⇒ₛ Δ₂ → Δ₂ ⊢ l
`ℕ           ⋯ₛ σ = `ℕ
(` x)        ⋯ₛ σ = σ _ x
(∀[α∶ l ] t) ⋯ₛ σ = ∀[α∶ l ] (t ⋯ₛ (σ ↑ₛ l))
(t₁ ⇒ t₂)    ⋯ₛ σ = (t₁ ⋯ₛ σ) ⇒ (t₂ ⋯ₛ σ)

idₛ : Δ ⇒ₛ Δ
idₛ _ x = ` x 

extₛ : Δ₂ ⊢ l → Δ₁ ⇒ₛ Δ₂ → (l ∷ Δ₁) ⇒ₛ Δ₂
extₛ t σ _ zero = t
extₛ t σ _ (suc x) = σ _ x

⦅_⦆ₛ : Δ ⊢ l → (l ∷ Δ) ⇒ₛ Δ
⦅ t ⦆ₛ = extₛ t idₛ 
