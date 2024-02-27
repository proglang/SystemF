module SmallStepSoundness where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; [_])
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Function using (_∘_; id; _$_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; dcong₂; subst; subst₂; resp₂; cong-app; icong;
        subst-∘; subst-subst; subst-sym-subst; sym-cong;
        module ≡-Reasoning)
open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open ≡-Reasoning
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)
open import HeterogeneousSetωEquality as Hω using (_≅ω_; refl)
module Rω = Hω.≅ω-Reasoning

open import Ext
open import SetOmega
open import SubstProperties
open import Types
open import TypeSubstitution
open import TypeSubstProperties
open import TypeSubstPropertiesSem
open import Expressions
open import ExprSubstitution
open import ExprSubstPropertiesSem
open import ExprSubstFusion public
open import SmallStep
import HeterogeneousEqualityLemmas as HE

soundness : ∀ {e₁ e₂ : Expr Δ Γ T} → e₁ ↪ e₂ → E⟦ e₁ ⟧ η γ ≡ E⟦ e₂ ⟧ η γ
soundness β-suc = refl
soundness (ξ-suc e₁↪e₂) = cong ℕ.suc (soundness e₁↪e₂)
soundness {γ = γ} (β-ƛ {e₂ = e₂} {e₁ = e₁} v₂) = sym (EEsingle-subst-preserves γ e₁ e₂)
soundness {γ = γ} (β-Λ {T = T} {e = e}) = sym (ETsingle-subst-preserves γ e T)
soundness {η = η} {γ = γ} (ξ-·₁ {e₂ = e₂} e₁↪e) = cong-app (soundness e₁↪e) (E⟦ e₂ ⟧ η γ)
soundness {η = η} {γ = γ} (ξ-·₂ {e₁ = e₁} e₂↪e v₁) = cong (E⟦ e₁ ⟧ η γ) (soundness e₂↪e)
soundness {η = η} {γ = γ} (ξ-∙ {T′ = T′} {T = T} e₁↪e₂) 
  rewrite Tsingle-subst-preserves η T′ T = cong-app (soundness e₁↪e₂) (⟦ T′ ⟧ η)       