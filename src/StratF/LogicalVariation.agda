module StratF.LogicalVariation where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; [_])
open import Function using (_∘_; id; case_of_; _|>_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong;
        subst-∘; subst-application; subst-application′; subst-subst-sym; subst-sym-subst; subst-subst; -- Properties
        module ≡-Reasoning)
open ≡-Reasoning

open import StratF.BigStep
open import StratF.ExprSubstProperties
open import StratF.ExprSubstitution
open import StratF.Expressions
open import StratF.TypeSubstProperties
open import StratF.TypeSubstitution
open import StratF.TypeSubstPropertiesSem
open import StratF.Types
open import StratF.Util.Extensionality
open import StratF.Util.PropositionalSetOmegaEquality
open import StratF.Util.SubstProperties

----------------------------------------------------------------------
--! Logical >
--! Variation >

open import StratF.LogicalPrelim

-- stratified logical relation

π₁∘ext≡ext∘↑π₁ : ∀ (T : Type (l ∷ Δ) l′) (ρ : 𝓓⟦ Δ ⟧) (T′ : Type [] l) (R : REL T′)
    → let ρ′ = REext ρ (T′ , R) in 
    Tsub (π₁ ρ′) T ≡ Tsub (Tliftₛ (π₁ ρ) l) T [ T′ ]T
π₁∘ext≡ext∘↑π₁ T ρ T′ R = begin 
    Tsub (λ l₁ x → proj₁ (REext ρ (T′ , R) l₁ x)) T
  ≡⟨ cong (λ ■ → Tsub ■ T) (fun-ext λ l → fun-ext λ where
      here → refl
      (there x) → refl) ⟩ 
    Tsub (Textₛ (λ l₁ x → proj₁ (ρ l₁ x)) T′) T
  ≡⟨⟩ 
    Tsub (Textₛ (π₁ ρ) T′) T
  ≡⟨ sym (lemma2 (π₁ ρ) T T′) ⟩
    Tsub (Textₛ Tidₛ T′) (Tsub (Tliftₛ (π₁ ρ) _) T)
  ∎

⟦⟧∘ext≡ext∘⟦⟧ : ∀ (T : Type [ l ] l′) → (T′ : Type [] l)
  → ⟦ T [ T′ ]T ⟧ [] ≡ ⟦ T ⟧ (⟦ T′ ⟧ [] ∷ [])
⟦⟧∘ext≡ext∘⟦⟧ T T′ = Tsingle-subst-preserves [] T′ T

--! MCVType
𝓥′⟦_⟧ : (T : Type Δ l) → (ρ : 𝓓⟦ Δ ⟧) → REL (Tsub (π₁ ρ) T)

--! MCEType
𝓔′⟦_⟧ : (T : Type Δ l) → (ρ : 𝓓⟦ Δ ⟧)
  → CExpr (Tsub (π₁ ρ) T) → ⟦ Tsub (π₁ ρ) T ⟧ [] → Set l

--! MCVBody
𝓥′⟦ `ℕ ⟧ ρ u z =
  ∃[ n ] (exp u ≡ (# n)) ∧ (n ≡ z)
𝓥′⟦ T₁ ⇒ T₂ ⟧ ρ u f =
  ∃[ e ] (exp u ≡ ƛ e) ∧
  ∀ w z → 𝓥′⟦ T₁ ⟧ ρ w z → 𝓔′⟦ T₂ ⟧ ρ (e [ exp w ]E) (f z)

--! MCVBodyUniversal
𝓥′⟦ ` α ⟧ ρ v z =
  π₂ ρ _ α v z
𝓥′⟦ `∀α l , T ⟧ ρ u F =
  ∃[ e ] (exp u ≡ Λ l ⇒ e) ∧
  ∀ T′ R → let ρ′ = REext ρ (T′ , R) in 
  ∃[ v ] (subst CExpr (sym (π₁∘ext≡ext∘↑π₁ T ρ T′ R)) (e [ T′ ]ET) ⇓ v)
       ∧ 𝓥′⟦ T ⟧ ρ′ v (subst id (sym (trans (cong (λ t → ⟦ t ⟧ []) (π₁∘ext≡ext∘↑π₁ T ρ T′ R))
                                            (⟦⟧∘ext≡ext∘⟦⟧ (Tsub (Tliftₛ (π₁ ρ) l) T) T′)))
                               (F (⟦ T′ ⟧ [])))

--! MCE
𝓔′⟦ T ⟧ ρ e z = ∃[ v ] (e ⇓ v) ∧ 𝓥′⟦ T ⟧ ρ v z
