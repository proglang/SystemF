module StratF.SmallStepSoundness where

open import Data.List using (List; []; _∷_; [_])
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; dcong; dcong₂; subst; subst₂; resp₂; cong-app; icong;
        subst-∘; subst-subst; subst-sym-subst; sym-cong;
        module ≡-Reasoning)
open ≡-Reasoning

open import StratF.ExprSubstFusion public
open import StratF.ExprSubstPropertiesSem
open import StratF.ExprSubstitution
open import StratF.Expressions
open import StratF.SmallStep
open import StratF.TypeSubstProperties
open import StratF.TypeSubstPropertiesSem
open import StratF.TypeSubstitution
open import StratF.Types
open import StratF.Util.Extensionality
open import StratF.Util.HeterogeneousSetOmegaEquality as Hω using (_≅ω_; refl)
open import StratF.Util.PropositionalSetOmegaEquality
open import StratF.Util.SubstProperties
import StratF.Util.HeterogeneousEqualityLemmas as HE

--! SmallStep >

--! Soundness
soundness : ∀ {e₁ e₂ : Expr Δ Γ T} →
  e₁ ↪ e₂ →
  ∀ η γ → E⟦ e₁ ⟧ η γ ≡ E⟦ e₂ ⟧ η γ

--! SoundnessProof
soundness β-suc η γ = refl
soundness (ξ-suc e₁↪e₂) η γ = cong ℕ.suc (soundness e₁↪e₂ η γ)
soundness (β-ƛ {e₂ = e₂} {e₁ = e₁} v₂) η γ = sym (EEsingle-subst-preserves γ e₁ e₂)
soundness (β-Λ {T = T} {e = e}) η γ = sym (ETsingle-subst-preserves γ e T)
soundness (ξ-·₁ {e₂ = e₂} e₁↪e) η γ = cong-app (soundness e₁↪e η γ) (E⟦ e₂ ⟧ η γ)
soundness (ξ-·₂ {e₁ = e₁} e₂↪e v₁) η γ = cong (E⟦ e₁ ⟧ η γ) (soundness e₂↪e η γ)
soundness (ξ-∙ {T′ = T′} {T = T} e₁↪e₂) η γ
  rewrite Tsingle-subst-preserves η T′ T = cong-app (soundness e₁↪e₂ η γ) (⟦ T′ ⟧ η)
