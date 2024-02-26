module ExprSubstFusion.SwapSub where

open import Level
open import Data.List using (List; []; _∷_; [_])
open import Function using (_∘_; id; _$_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)

open import Ext
open import Types
open import TypeSubstitution
open import TypeSubstProperties
open import Expressions
open import ExprSubstitution
open import HeterogeneousEqualityLemmas
open import ExprSubstFusion.SubRen
open import ExprSubstFusion.RenSub

-- Swap-Lemmas for Substitutions

swap-sub-Ewk :
  ∀ {ρ* : TSub Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂}
    (ρ : ESub ρ* Γ₁ Γ₂) (T : Type Δ₁ l) →
  Ewkᵣ {T = T} Tidᵣ Eidᵣ >>RS Eliftₛ ρ* ρ ≅
  ρ >>SR Ewkᵣ {T = Tsub ρ* T} Tidᵣ Eidᵣ
swap-sub-Ewk {Δ₁} {Δ₂} {l} {ρ*} {Γ₁} {Γ₂} ρ T =
  fun-ext-h-ESub (sym (∘ₛᵣ-neutralˡ ρ*)) refl λ l₁ T₁ x →
    let
      F₁ = (Expr Δ₂ (Tsub ρ* T ◁ Γ₂)) ; E₁ = (fusion-Tsub-Tren T₁ Tidᵣ ρ*)                  ; sub₁ = subst F₁ E₁
      F₂ = (Expr Δ₂ (Tsub ρ* T ◁ Γ₂)) ; E₂ = (TidᵣT≡T (Tsub ρ* (Tren (λ _ x₁ → x₁) T₁))) ; sub₂ = subst F₂ E₂
      F₃ = (λ T₂ → inn T₂ Γ₁)         ; E₃ = (sym (TidᵣT≡T T₁))                          ; sub₃ = subst F₃ E₃
      F₄ = (Expr Δ₂ (Tsub ρ* T ◁ Γ₂)) ; E₄ = (fusion-Tren-Tsub T₁ ρ* (λ _ x₁ → x₁))         ; sub₄ = subst F₄ E₄
    in
    R.begin
      (Ewkᵣ {T = T} Tidᵣ Eidᵣ >>RS Eliftₛ ρ* ρ) l₁ T₁ x
    R.≅⟨ refl ⟩
      sub₁ (sub₂ (Eren Tidᵣ (Ewkᵣ {T = Tsub ρ* T} Tidᵣ Eidᵣ) (ρ l₁ (Tren Tidᵣ T₁) (sub₃ x))))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      sub₂ (Eren Tidᵣ (Ewkᵣ {T = Tsub ρ* T} Tidᵣ Eidᵣ) (ρ l₁ (Tren Tidᵣ T₁) (sub₃ x)))
    R.≅⟨ H.≡-subst-removable F₂ E₂ _ ⟩
      Eren Tidᵣ (Ewkᵣ {T = Tsub ρ* T} Tidᵣ Eidᵣ) (ρ l₁ (Tren Tidᵣ T₁) (sub₃ x))
    R.≅⟨ H.cong₂ {B = λ ■ → inn ■ Γ₁} (λ ■₁ ■₂ → Eren Tidᵣ (Ewkᵣ {T = Tsub ρ* T} Tidᵣ Eidᵣ) (ρ l₁ ■₁ ■₂))
                 (H.≡-to-≅ (TidᵣT≡T T₁)) (H.≡-subst-removable F₃ E₃ _) ⟩
      Eren Tidᵣ (Ewkᵣ {T = Tsub ρ* T} Tidᵣ Eidᵣ) (ρ l₁ T₁ x)
    R.≅⟨ H.sym (H.≡-subst-removable F₄ E₄ _) ⟩
      sub₄ (Eren Tidᵣ (Ewkᵣ {T = Tsub ρ* T} Tidᵣ Eidᵣ) (ρ l₁ T₁ x))
    R.≅⟨ refl ⟩
      (ρ >>SR Ewkᵣ Tidᵣ Eidᵣ) l₁ T₁ x
    R.∎

swap-Esub-Ewk :
  ∀ {ρ* : TSub Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {T : Type Δ₁ l}
    (ρ : ESub ρ* Γ₁ Γ₂) (T′ : Type Δ₁ l′) (e : Expr Δ₁ Γ₁ T) →
  Esub ρ* (Eliftₛ {T = T′} ρ* ρ) (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) e) ≅
  Eren Tidᵣ (Ewkᵣ {T = Tsub ρ* T′} Tidᵣ Eidᵣ) (Esub ρ* ρ e)
swap-Esub-Ewk {Δ₁} {Δ₂} {l} {l′} {ρ*} {Γ₁} {Γ₂} {T} ρ T′ e =
  R.begin
    Esub ρ* (Eliftₛ ρ* ρ) (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) e)
  R.≅⟨ fusion-Esub-Eren' e (Ewkᵣ Tidᵣ Eidᵣ) (Eliftₛ ρ* ρ) ⟩
    Esub ρ* (Ewkᵣ {T = T′} Tidᵣ Eidᵣ >>RS Eliftₛ ρ* ρ) e
  R.≅⟨ H.cong₂ {B = λ ■ → ESub ■ Γ₁ (Tsub ρ* T′ ◁ Γ₂)} (λ ■₁ ■₂ → Esub ■₁ ■₂ e)
               (H.≡-to-≅ (sym (∘ₛᵣ-neutralˡ ρ*))) (swap-sub-Ewk ρ T′) ⟩
    Esub (ρ* ∘ₛᵣ Tidᵣ) (ρ >>SR Ewkᵣ {T = Tsub ρ* T′} Tidᵣ Eidᵣ) e
  R.≅⟨ H.sym (fusion-Eren-Esub' e ρ (Ewkᵣ Tidᵣ Eidᵣ)) ⟩
    Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (Esub ρ* ρ e)
  R.∎

swap-sub-Ewk-l :
  ∀ {ρ* : TSub Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂}
    (ρ : ESub ρ* Γ₁ Γ₂) (l : Level) →
  Ewkᵣ-l l >>RS Eliftₛ-l ρ* ρ ≅ ρ >>SR Ewkᵣ-l l
swap-sub-Ewk-l {Δ₁} {Δ₂} {ρ*} {Γ₁} {Γ₂} ρ l =
  fun-ext-h-ESub refl refl λ l₁ T₁ x →
    let
      F₁ = (Expr (l ∷ Δ₂) (l ◁* Γ₂)) ; E₁ = (fusion-Tsub-Tren T₁ (Twkᵣ Tidᵣ) (Tliftₛ ρ* l))              ; sub₁ = subst F₁ E₁
      F₂ = (Expr (l ∷ Δ₂) (l ◁* Γ₂)) ; E₂ = (sym (swap-Tsub-Twk ρ* T₁)) ; sub₂ = subst F₂ E₂
      F₃ = (Expr (l ∷ Δ₂) (l ◁* Γ₂)) ; E₃ = (fusion-Tren-Tsub T₁ ρ* (Twkᵣ Tidᵣ))                         ; sub₃ = subst F₃ E₃
    in
    R.begin
      (Ewkᵣ-l l >>RS Eliftₛ-l ρ* ρ) l₁ T₁ x
    R.≅⟨ refl ⟩
      sub₁ (sub₂ (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (ρ l₁ T₁ x)))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      sub₂ (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (ρ l₁ T₁ x))
    R.≅⟨ H.≡-subst-removable F₂ E₂ _ ⟩
      Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (ρ l₁ T₁ x)
    R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
      sub₃ (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (ρ l₁ T₁ x))
    R.≅⟨ refl ⟩
      (ρ >>SR Ewkᵣ-l l) l₁ T₁ x
    R.∎

swap-Esub-Ewk-l :
  ∀ {ρ* : TSub Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {T : Type Δ₁ l}
    (ρ : ESub ρ* Γ₁ Γ₂) (l′ : Level) (e : Expr Δ₁ Γ₁ T) →
  Esub (Tliftₛ ρ* l′) (Eliftₛ-l ρ* ρ) (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l′) e) ≅
  Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l′) (Esub ρ* ρ e)
swap-Esub-Ewk-l {Δ₁} {Δ₂} {l} {ρ*} {Γ₁} {Γ₂} {T} ρ l′ e =
  R.begin
    Esub (Tliftₛ ρ* l′) (Eliftₛ-l ρ* ρ) (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l′) e)
  R.≅⟨ fusion-Esub-Eren' e (Ewkᵣ-l l′) (Eliftₛ-l ρ* ρ) ⟩
    Esub (Twkᵣ Tidᵣ ∘ᵣₛ Tliftₛ ρ* l′) (Ewkᵣ-l l′ >>RS Eliftₛ-l ρ* ρ) e
  R.≅⟨ H.cong (λ ■ → Esub (Twkᵣ Tidᵣ ∘ᵣₛ Tliftₛ ρ* l′) ■ e) (swap-sub-Ewk-l ρ l′) ⟩
    Esub (ρ* ∘ₛᵣ Twkᵣ Tidᵣ) (ρ >>SR Ewkᵣ-l l′) e
  R.≅⟨ H.sym (fusion-Eren-Esub' e ρ (Ewkᵣ-l l′)) ⟩
    Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l′) (Esub ρ* ρ e)
  R.∎
