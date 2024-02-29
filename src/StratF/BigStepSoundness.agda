-- This file proves that the big step semantics is sound wrt. the denotational semantics.

module StratF.BigStepSoundness where

open import Data.List using (List; []; _∷_; [_])
open import Data.Nat using (ℕ; suc)
open import Function using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; module ≡-Reasoning)
open ≡-Reasoning

open import StratF.BigStep
open import StratF.ExprSubstPropertiesSem using (EEsingle-subst-preserves; ETsingle-subst-preserves)
open import StratF.ExprSubstitution
open import StratF.Expressions
open import StratF.TypeSubstProperties
open import StratF.TypeSubstPropertiesSem
open import StratF.Types

--! BigStep >

γ₀ : Env [] ∅ []
γ₀ = λ l T ()

--! SoundnessType
soundness : ∀ {T : Type [] l} {e : CExpr T} {v : CValue T} →
  e ⇓ v →
  E⟦ e ⟧ [] γ₀ ≡ E⟦ exp v ⟧ [] γ₀

--! Soundness
soundness ⇓-n = refl
soundness (⇓-s e⇓v) = cong suc (soundness e⇓v)
soundness ⇓-ƛ = refl
soundness {e = e₁ · e₂}{v = v} (⇓-· {e = e}{v₂ = v₂} e₁⇓v₁ e₂⇓v₂ e[]⇓v) =
  begin
    E⟦ e₁ ⟧ [] γ₀ (E⟦ e₂ ⟧ [] γ₀)      ≡⟨ cong (λ H → H (E⟦ e₂ ⟧ [] γ₀)) (soundness e₁⇓v₁) ⟩
    E⟦ ƛ e ⟧ [] γ₀ (E⟦ e₂ ⟧ [] γ₀)     ≡⟨ cong (E⟦ ƛ e ⟧ [] γ₀) (soundness e₂⇓v₂) ⟩
    E⟦ ƛ e ⟧ [] γ₀ (E⟦ exp v₂ ⟧ [] γ₀) ≡⟨ sym (EEsingle-subst-preserves γ₀ e (exp v₂)) ⟩
    E⟦ e [ exp v₂ ]E ⟧ [] γ₀           ≡⟨ soundness e[]⇓v ⟩
    E⟦ exp v ⟧ [] γ₀
  ∎
soundness ⇓-Λ = refl
soundness {e =  _∙_ {T = T₁} e₁ T}{v = v} (⇓-∙ {e = e} e₁⇓v₁ e[]⇓v) =
  begin
    E⟦ e₁ ∙ T ⟧ [] γ₀
  ≡⟨ refl ⟩
    subst id (sym (Tsingle-subst-preserves [] T T₁))
      (E⟦ e₁ ⟧ [] γ₀ (⟦ T ⟧ []))
  ≡⟨ cong (λ H → subst id (sym (Tsingle-subst-preserves [] T T₁)) (H (⟦ T ⟧ [])))
          (soundness e₁⇓v₁) ⟩
    subst id (sym (Tsingle-subst-preserves [] T T₁))
      (E⟦ e ⟧ (⟦ T ⟧ [] ∷ []) (extend-tskip γ₀))
  ≡⟨ sym (ETsingle-subst-preserves γ₀ e T) ⟩
    E⟦ e [ T ]ET ⟧ [] γ₀
  ≡⟨ soundness e[]⇓v ⟩
    E⟦ exp v ⟧ [] γ₀
  ∎
