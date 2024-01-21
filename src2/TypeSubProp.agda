module TypeSubProp where

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Prelude
open import Type
open import TypeSub

_ᵣ·ᵣ_ : Δ₁ ⇒ᵣ Δ₂ → Δ₂ ⇒ᵣ Δ₃ → Δ₁ ⇒ᵣ Δ₃
(ρ₁ ᵣ·ᵣ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

↑ᵣ-dist-ᵣ·ᵣ : ∀ (ρ₁ : Δ₁ ⇒ᵣ Δ₂) (ρ₂ : Δ₂ ⇒ᵣ Δ₃) →
  (ρ₁ ↑ᵣ l) ᵣ·ᵣ (ρ₂ ↑ᵣ l) ≡ (ρ₁ ᵣ·ᵣ ρ₂) ↑ᵣ l
↑ᵣ-dist-ᵣ·ᵣ ρ₁ ρ₂ = fun-ext λ _ → fun-ext λ where
  zero    → refl
  (suc x) → refl

⋯ᵣᵣ-fusion : ∀ (t : Δ₁ ⊢ l) (ρ₁ : Δ₁ ⇒ᵣ Δ₂) (ρ₂ : Δ₂ ⇒ᵣ Δ₃) →
  (t ⋯ᵣ ρ₁) ⋯ᵣ ρ₂ ≡ t ⋯ᵣ (ρ₁ ᵣ·ᵣ ρ₂)
⋯ᵣᵣ-fusion (` x)        ρ₁ ρ₂ = refl
⋯ᵣᵣ-fusion (t₁ ⇒ t₂)    ρ₁ ρ₂ = cong₂ _⇒_ (⋯ᵣᵣ-fusion t₁ ρ₁ ρ₂) (⋯ᵣᵣ-fusion t₂ ρ₁ ρ₂)
⋯ᵣᵣ-fusion (∀[α∶ l ] t) ρ₁ ρ₂ = cong ∀[α∶ l ]_ (
  begin
    (t ⋯ᵣ (ρ₁ ↑ᵣ l)) ⋯ᵣ (ρ₂ ↑ᵣ l)
  ≡⟨ ⋯ᵣᵣ-fusion t (ρ₁ ↑ᵣ l) (ρ₂ ↑ᵣ l) ⟩
    t ⋯ᵣ ((ρ₁ ↑ᵣ l) ᵣ·ᵣ (ρ₂ ↑ᵣ l))
  ≡⟨ cong (t ⋯ᵣ_) (↑ᵣ-dist-ᵣ·ᵣ ρ₁ ρ₂) ⟩
    t ⋯ᵣ ((ρ₁ ᵣ·ᵣ ρ₂) ↑ᵣ l)
  ∎)


_ᵣ·ₛ_ : Δ₁ ⇒ᵣ Δ₂ → Δ₂ ⇒ₛ Δ₃ → Δ₁ ⇒ₛ Δ₃
(ρ₁ ᵣ·ₛ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

↑ₛ-dist-ᵣ·ₛ : ∀ (ρ₁ : Δ₁ ⇒ᵣ Δ₂) (ρ₂ : Δ₂ ⇒ₛ Δ₃) →
  (ρ₁ ↑ᵣ l) ᵣ·ₛ (ρ₂ ↑ₛ l) ≡ (ρ₁ ᵣ·ₛ ρ₂) ↑ₛ l
↑ₛ-dist-ᵣ·ₛ ρ₁ ρ₂ = fun-ext λ _ → fun-ext λ where
  zero    → refl
  (suc x) → refl

⋯ᵣₛ-fusion : ∀ (t : Δ₁ ⊢ l) (ρ₁ : Δ₁ ⇒ᵣ Δ₂) (ρ₂ : Δ₂ ⇒ₛ Δ₃) →
  (t ⋯ᵣ ρ₁) ⋯ₛ ρ₂ ≡ t ⋯ₛ (ρ₁ ᵣ·ₛ ρ₂)
⋯ᵣₛ-fusion (` x)        ρ₁ ρ₂ = refl
⋯ᵣₛ-fusion (t₁ ⇒ t₂)    ρ₁ ρ₂ = cong₂ _⇒_ (⋯ᵣₛ-fusion t₁ ρ₁ ρ₂) (⋯ᵣₛ-fusion t₂ ρ₁ ρ₂)
⋯ᵣₛ-fusion (∀[α∶ l ] t) ρ₁ ρ₂ = cong ∀[α∶ l ]_ (
  begin
    (t ⋯ᵣ (ρ₁ ↑ᵣ l)) ⋯ₛ (ρ₂ ↑ₛ l)
  ≡⟨ ⋯ᵣₛ-fusion t (ρ₁ ↑ᵣ l) (ρ₂ ↑ₛ l) ⟩
    t ⋯ₛ ((ρ₁ ↑ᵣ l) ᵣ·ₛ (ρ₂ ↑ₛ l))
  ≡⟨ cong (t ⋯ₛ_) (↑ₛ-dist-ᵣ·ₛ ρ₁ ρ₂) ⟩
    t ⋯ₛ ((ρ₁ ᵣ·ₛ ρ₂) ↑ₛ l)
  ∎)


_ₛ·ᵣ_ : Δ₁ ⇒ₛ Δ₂ → Δ₂ ⇒ᵣ Δ₃ → Δ₁ ⇒ₛ Δ₃
(ρ₁ ₛ·ᵣ ρ₂) _ x = ρ₁ _ x ⋯ᵣ ρ₂

↑ₛ-dist-ₛ·ᵣ : ∀ (ρ₁ : Δ₁ ⇒ₛ Δ₂) (ρ₂ : Δ₂ ⇒ᵣ Δ₃) →
  (ρ₁ ↑ₛ l) ₛ·ᵣ (ρ₂ ↑ᵣ l) ≡ (ρ₁ ₛ·ᵣ ρ₂) ↑ₛ l
↑ₛ-dist-ₛ·ᵣ {l = l} ρ₁ ρ₂ = fun-ext λ _ → fun-ext λ where
  zero    → refl
  (suc x) →
    begin
      ((ρ₁ ↑ₛ l) ₛ·ᵣ (ρ₂ ↑ᵣ l)) _ (suc x)
    ≡⟨⟩
      (ρ₁ _ x ⋯ᵣ wkᵣ l idᵣ) ⋯ᵣ (ρ₂ ↑ᵣ l)
    ≡⟨ ⋯ᵣᵣ-fusion (ρ₁ _ x) (wkᵣ l idᵣ) (ρ₂ ↑ᵣ l) ⟩
      ρ₁ _ x ⋯ᵣ (wkᵣ l idᵣ ᵣ·ᵣ (ρ₂ ↑ᵣ l))
    ≡⟨ cong (ρ₁ _ x ⋯ᵣ_) refl ⟩
      ρ₁ _ x ⋯ᵣ (ρ₂ ᵣ·ᵣ wkᵣ l idᵣ)
    ≡⟨ sym (⋯ᵣᵣ-fusion (ρ₁ _ x) ρ₂ (wkᵣ l idᵣ)) ⟩
      (ρ₁ _ x ⋯ᵣ ρ₂) ⋯ᵣ wkᵣ l idᵣ
    ≡⟨⟩
      ((ρ₁ ₛ·ᵣ ρ₂) _ x ⋯ᵣ wkᵣ l idᵣ)
    ∎

⋯ₛᵣ-fusion : ∀ (t : Δ₁ ⊢ l) (ρ₁ : Δ₁ ⇒ₛ Δ₂) (ρ₂ : Δ₂ ⇒ᵣ Δ₃) →
  (t ⋯ₛ ρ₁) ⋯ᵣ ρ₂ ≡ t ⋯ₛ (ρ₁ ₛ·ᵣ ρ₂)
⋯ₛᵣ-fusion (` x)        ρ₁ ρ₂ = refl
⋯ₛᵣ-fusion (t₁ ⇒ t₂)    ρ₁ ρ₂ = cong₂ _⇒_ (⋯ₛᵣ-fusion t₁ ρ₁ ρ₂) (⋯ₛᵣ-fusion t₂ ρ₁ ρ₂)
⋯ₛᵣ-fusion (∀[α∶ l ] t) ρ₁ ρ₂ = cong ∀[α∶ l ]_ (
  begin
    (t ⋯ₛ (ρ₁ ↑ₛ l)) ⋯ᵣ (ρ₂ ↑ᵣ l)
  ≡⟨ ⋯ₛᵣ-fusion t (ρ₁ ↑ₛ l) (ρ₂ ↑ᵣ l) ⟩
    t ⋯ₛ ((ρ₁ ↑ₛ l) ₛ·ᵣ (ρ₂ ↑ᵣ l))
  ≡⟨ cong (t ⋯ₛ_) (↑ₛ-dist-ₛ·ᵣ ρ₁ ρ₂) ⟩
    t ⋯ₛ ((ρ₁ ₛ·ᵣ ρ₂) ↑ₛ l)
  ∎)


_ₛ·ₛ_ : Δ₁ ⇒ₛ Δ₂ → Δ₂ ⇒ₛ Δ₃ → Δ₁ ⇒ₛ Δ₃
(ρ₁ ₛ·ₛ ρ₂) _ x = ρ₁ _ x ⋯ₛ ρ₂

↑ₛ-dist-ₛ·ₛ : ∀ (ρ₁ : Δ₁ ⇒ₛ Δ₂) (ρ₂ : Δ₂ ⇒ₛ Δ₃) →
  (ρ₁ ↑ₛ l) ₛ·ₛ (ρ₂ ↑ₛ l) ≡ (ρ₁ ₛ·ₛ ρ₂) ↑ₛ l
↑ₛ-dist-ₛ·ₛ {l = l} ρ₁ ρ₂ = fun-ext λ _ → fun-ext λ where
  zero    → refl
  (suc x) →
    begin
      ((ρ₁ ↑ₛ l) ₛ·ₛ (ρ₂ ↑ₛ l)) _ (suc x)
    ≡⟨⟩
      (ρ₁ _ x ⋯ᵣ wkᵣ l idᵣ) ⋯ₛ (ρ₂ ↑ₛ l)
    ≡⟨ ⋯ᵣₛ-fusion (ρ₁ _ x) (wkᵣ l idᵣ) (ρ₂ ↑ₛ l) ⟩
      ρ₁ _ x ⋯ₛ (wkᵣ l idᵣ ᵣ·ₛ (ρ₂ ↑ₛ l))
    ≡⟨ cong (ρ₁ _ x ⋯ₛ_) refl ⟩
      ρ₁ _ x ⋯ₛ (ρ₂ ₛ·ᵣ wkᵣ l idᵣ)
    ≡⟨ sym (⋯ₛᵣ-fusion (ρ₁ _ x) ρ₂ (wkᵣ l idᵣ)) ⟩
      (ρ₁ _ x ⋯ₛ ρ₂) ⋯ᵣ wkᵣ l idᵣ
    ≡⟨⟩
      ((ρ₁ ₛ·ₛ ρ₂) _ x ⋯ᵣ wkᵣ l idᵣ)
    ∎

⋯ₛₛ-fusion : ∀ (t : Δ₁ ⊢ l) (ρ₁ : Δ₁ ⇒ₛ Δ₂) (ρ₂ : Δ₂ ⇒ₛ Δ₃) →
  (t ⋯ₛ ρ₁) ⋯ₛ ρ₂ ≡ t ⋯ₛ (ρ₁ ₛ·ₛ ρ₂)
⋯ₛₛ-fusion (` x)        ρ₁ ρ₂ = refl
⋯ₛₛ-fusion (t₁ ⇒ t₂)    ρ₁ ρ₂ = cong₂ _⇒_ (⋯ₛₛ-fusion t₁ ρ₁ ρ₂) (⋯ₛₛ-fusion t₂ ρ₁ ρ₂)
⋯ₛₛ-fusion (∀[α∶ l ] t) ρ₁ ρ₂ = cong ∀[α∶ l ]_ (
  begin
    (t ⋯ₛ (ρ₁ ↑ₛ l)) ⋯ₛ (ρ₂ ↑ₛ l)
  ≡⟨ ⋯ₛₛ-fusion t (ρ₁ ↑ₛ l) (ρ₂ ↑ₛ l) ⟩
    t ⋯ₛ ((ρ₁ ↑ₛ l) ₛ·ₛ (ρ₂ ↑ₛ l))
  ≡⟨ cong (t ⋯ₛ_) (↑ₛ-dist-ₛ·ₛ ρ₁ ρ₂) ⟩
    t ⋯ₛ ((ρ₁ ₛ·ₛ ρ₂) ↑ₛ l)
  ∎)


wkᵣ-↑ᵣ : ∀ (t : Δ₁ ⊢ l') (ρ : Δ₁ ⇒ᵣ Δ₂) →
  (t ⋯ᵣ ρ) ⋯ᵣ wkᵣ l idᵣ ≡ (t ⋯ᵣ wkᵣ l idᵣ) ⋯ᵣ (ρ ↑ᵣ l)
wkᵣ-↑ᵣ {Δ₁} {k'} {Δ₂} {l} t ρ =
  begin
    (t ⋯ᵣ ρ) ⋯ᵣ wkᵣ l idᵣ
  ≡⟨ ⋯ᵣᵣ-fusion t ρ (wkᵣ l idᵣ) ⟩
    t ⋯ᵣ (ρ ᵣ·ᵣ wkᵣ l idᵣ)
  ≡⟨⟩
    t ⋯ᵣ (wkᵣ l idᵣ ᵣ·ᵣ (ρ ↑ᵣ l))
  ≡⟨ sym (⋯ᵣᵣ-fusion t (wkᵣ l idᵣ) (ρ ↑ᵣ l)) ⟩
    (t ⋯ᵣ wkᵣ l idᵣ) ⋯ᵣ (ρ ↑ᵣ l)
  ∎

wkᵣ-↑ₛ : ∀ (t : Δ₁ ⊢ l') (ρ : Δ₁ ⇒ₛ Δ₂) →
  (t ⋯ₛ ρ) ⋯ᵣ wkᵣ l idᵣ ≡ (t ⋯ᵣ wkᵣ l idᵣ) ⋯ₛ (ρ ↑ₛ l)
wkᵣ-↑ₛ {Δ₁} {k'} {Δ₂} {l} t ρ =
  begin
    (t ⋯ₛ ρ) ⋯ᵣ wkᵣ l idᵣ
  ≡⟨ ⋯ₛᵣ-fusion t ρ (wkᵣ l idᵣ) ⟩
    t ⋯ₛ (ρ ₛ·ᵣ wkᵣ l idᵣ)
  ≡⟨⟩
    t ⋯ₛ (wkᵣ l idᵣ ᵣ·ₛ (ρ ↑ₛ l))
  ≡⟨ sym (⋯ᵣₛ-fusion t (wkᵣ l idᵣ) (ρ ↑ₛ l)) ⟩
    (t ⋯ᵣ wkᵣ l idᵣ) ⋯ₛ (ρ ↑ₛ l)
  ∎

idₛ-↑ₛ : idₛ ↑ₛ l ≡ idₛ {Δ = l ∷ Δ}
idₛ-↑ₛ = fun-ext λ _ → fun-ext λ where
  zero    → refl
  (suc x) → refl

⋯ₛ-id : ∀ (t : Δ ⊢ l) →
  t ⋯ₛ idₛ ≡ t
⋯ₛ-id (` x)        = refl
⋯ₛ-id (∀[α∶ l ] t) = cong ∀[α∶ l ]_ (
  begin
     t ⋯ₛ (idₛ ↑ₛ l)
   ≡⟨ cong (t ⋯ₛ_) idₛ-↑ₛ ⟩
     t ⋯ₛ idₛ
   ≡⟨ ⋯ₛ-id t ⟩
     t
   ∎)
⋯ₛ-id (t₁ ⇒ t₂)    = cong₂ _⇒_ (⋯ₛ-id t₁) (⋯ₛ-id t₂)

wkᵣ-cancels-⦅⦆ₛ : ∀ (t' : Δ ⊢ l') (t : Δ ⊢ l) →
  (t' ⋯ᵣ wkᵣ l idᵣ) ⋯ₛ ⦅ t ⦆ₛ ≡ t'
wkᵣ-cancels-⦅⦆ₛ {Δ} {k'} {l} t' t =
  begin
    (t' ⋯ᵣ wkᵣ l idᵣ) ⋯ₛ ⦅ t ⦆ₛ
  ≡⟨ ⋯ᵣₛ-fusion t' (wkᵣ l idᵣ) ⦅ t ⦆ₛ ⟩
    t' ⋯ₛ (wkᵣ l idᵣ ᵣ·ₛ ⦅ t ⦆ₛ)
  ≡⟨⟩
    t' ⋯ₛ idₛ
  ≡⟨ ⋯ₛ-id t' ⟩
    t'
  ∎

⦅⦆ₛ-↑ᵣ' : ∀ (t : Δ₁ ⊢ l) (ρ : Δ₁ ⇒ᵣ Δ₂) →
  (ρ ↑ᵣ l) ᵣ·ₛ ⦅ t ⋯ᵣ ρ ⦆ₛ ≡ ⦅ t ⦆ₛ ₛ·ᵣ ρ
⦅⦆ₛ-↑ᵣ' {Δ₁} {l} {Δ₂} t ρ = fun-ext λ _ → fun-ext λ where
  zero    → refl
  (suc x) → refl

⦅⦆ₛ-↑ᵣ : ∀ (t : (l ∷ Δ₁) ⊢ l') (t' : Δ₁ ⊢ l) (ρ : Δ₁ ⇒ᵣ Δ₂) →
  (t ⋯ᵣ (ρ ↑ᵣ l)) ⋯ₛ ⦅ t' ⋯ᵣ ρ ⦆ₛ ≡ (t ⋯ₛ ⦅ t' ⦆ₛ) ⋯ᵣ ρ
⦅⦆ₛ-↑ᵣ {l} {Δ₁} {l'} {Δ₂} t t' ρ =
  begin
    (t ⋯ᵣ (ρ ↑ᵣ l)) ⋯ₛ ⦅ t' ⋯ᵣ ρ ⦆ₛ
  ≡⟨ ⋯ᵣₛ-fusion t (ρ ↑ᵣ l) ⦅ t' ⋯ᵣ ρ ⦆ₛ ⟩
    t ⋯ₛ ((ρ ↑ᵣ l) ᵣ·ₛ ⦅ t' ⋯ᵣ ρ ⦆ₛ)
  ≡⟨ cong (t ⋯ₛ_) (⦅⦆ₛ-↑ᵣ' t' ρ) ⟩
    t ⋯ₛ (⦅ t' ⦆ₛ ₛ·ᵣ ρ)
  ≡⟨ sym (⋯ₛᵣ-fusion t ⦅ t' ⦆ₛ ρ) ⟩
    (t ⋯ₛ ⦅ t' ⦆ₛ) ⋯ᵣ ρ
  ∎

⦅⦆ₛ-↑ₛ' : ∀ (t : Δ₁ ⊢ l) (ρ : Δ₁ ⇒ₛ Δ₂) →
  (ρ ↑ₛ l) ₛ·ₛ ⦅ t ⋯ₛ ρ ⦆ₛ ≡ ⦅ t ⦆ₛ ₛ·ₛ ρ
⦅⦆ₛ-↑ₛ' {Δ₁} {l} {Δ₂} t ρ = fun-ext λ _ → fun-ext λ where
  zero    → refl
  (suc x) → wkᵣ-cancels-⦅⦆ₛ ((⦅ t ⦆ₛ ₛ·ₛ ρ) _ (suc x)) (t ⋯ₛ ρ)

⦅⦆ₛ-↑ₛ : ∀ (t : (l ∷ Δ₁) ⊢ l') (t' : Δ₁ ⊢ l) (ρ : Δ₁ ⇒ₛ Δ₂) →
  (t ⋯ₛ (ρ ↑ₛ l)) ⋯ₛ ⦅ t' ⋯ₛ ρ ⦆ₛ ≡ (t ⋯ₛ ⦅ t' ⦆ₛ) ⋯ₛ ρ
⦅⦆ₛ-↑ₛ {l} {Δ₁} {k'} {Δ₂} t t' ρ =
  begin
    (t ⋯ₛ (ρ ↑ₛ l)) ⋯ₛ ⦅ t' ⋯ₛ ρ ⦆ₛ
  ≡⟨ ⋯ₛₛ-fusion t (ρ ↑ₛ l) ⦅ t' ⋯ₛ ρ ⦆ₛ ⟩
    t ⋯ₛ ((ρ ↑ₛ l) ₛ·ₛ ⦅ t' ⋯ₛ ρ ⦆ₛ)
  ≡⟨ cong (t ⋯ₛ_) (⦅⦆ₛ-↑ₛ' t' ρ) ⟩
    t ⋯ₛ (⦅ t' ⦆ₛ ₛ·ₛ ρ)
  ≡⟨ sym (⋯ₛₛ-fusion t ⦅ t' ⦆ₛ ρ) ⟩
    (t ⋯ₛ ⦅ t' ⦆ₛ) ⋯ₛ ρ
  ∎ 