module BigStepSoundness where

open import Data.List using (List; []; _∷_; [_])
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym;
            module ≡-Reasoning)
open ≡-Reasoning
open import Function using (id)

open import Types
open import TypeSubstProperties
open import Expressions
open import ExprSubstitution

open import BigStep
open import Soundness using (EEsingle-subst-preserves; ETsingle-subst-preserves)

γ₀ : Env [] ∅ []
γ₀ = λ l T ()

soundness : ∀ {T : Type [] l} {e : CExpr T} {v : CValue T}
  → e ⇓ v
  → E⟦ e ⟧ [] γ₀ ≡ E⟦ exp v ⟧ [] γ₀
soundness ⇓-n = refl
soundness (⇓-s e⇓v) = cong suc (soundness e⇓v)
soundness ⇓-ƛ = refl
soundness {e = e₁ · e₂}{v = v} (⇓-· {e = e}{v₂ = v₂} e₁⇓v₁ e₂⇓v₂ e[]⇓v) =
  begin
    E⟦ e₁ ⟧ [] γ₀ (E⟦ e₂ ⟧ [] γ₀)
  ≡⟨ cong (λ H → H (E⟦ e₂ ⟧ [] γ₀)) (soundness e₁⇓v₁) ⟩
    E⟦ ƛ e ⟧ [] γ₀ (E⟦ e₂ ⟧ [] γ₀)
  ≡⟨ cong (E⟦ ƛ e ⟧ [] γ₀) (soundness e₂⇓v₂) ⟩
    E⟦ ƛ e ⟧ [] γ₀ (E⟦ exp v₂ ⟧ [] γ₀)
  ≡⟨ sym (EEsingle-subst-preserves γ₀ e (exp v₂)) ⟩
    E⟦ e [ exp v₂ ]E ⟧ [] γ₀
  ≡⟨ soundness e[]⇓v ⟩
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
