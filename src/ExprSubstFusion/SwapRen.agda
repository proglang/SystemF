module ExprSubstFusion.SwapRen where

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

open import ExprSubstFusion.RenRen

-- Swap-Lemmas for Renamings

swap-ren-Ewk :
  ∀ {ρ* : TRen Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂}
    (ρ : ERen ρ* Γ₁ Γ₂) (T : Type Δ₁ l) →
  Ewkᵣ {T = T} Tidᵣ Eidᵣ >>RR Eliftᵣ ρ* ρ ≅
  ρ >>RR Ewkᵣ {T = Tren ρ* T} Tidᵣ Eidᵣ
swap-ren-Ewk {Δ₁} {Δ₂} {l} {ρ*} {Γ₁} {Γ₂} ρ T =
  fun-ext-h-ERen refl refl λ l₁ T₁ x →
    let
      F₁ = (λ T₂ → inn T₂ (Tren ρ* T ◁ Γ₂)) ; E₁ = (fusion-Tren-Tren T₁ Tidᵣ ρ*)   ; sub₁ = subst F₁ E₁
      F₂ = (λ T₂ → inn T₂ Γ₁)               ; E₂ = (sym (TidᵣT≡T T₁))           ; sub₂ = subst F₂ E₂
      F₃ = (λ T₂ → inn T₂ (Tren ρ* T ◁ Γ₂)) ; E₃ = (fusion-Tren-Tren T₁ ρ* Tidᵣ)   ; sub₃ = subst F₃ E₃
      F₄ = (λ T₂ → inn T₂ Γ₂)               ; E₄ = (sym (TidᵣT≡T (Tren ρ* T₁))) ; sub₄ = subst F₄ E₄
    in
    R.begin
      (Ewkᵣ Tidᵣ Eidᵣ >>RR Eliftᵣ ρ* ρ) l₁ T₁ x
    R.≅⟨ refl ⟩
      sub₁ (there (ρ l₁ (Tren Tidᵣ T₁) (sub₂ x)))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      there (ρ l₁ (Tren Tidᵣ T₁) (sub₂ x))
    R.≅⟨ H.cong₂ {B = λ ■ → inn ■ Γ₁} (λ ■₁ ■₂ → inn.there (ρ l₁ ■₁ ■₂))
                 (H.≡-to-≅ (TidᵣT≡T T₁)) (H.≡-subst-removable F₂ E₂ _) ⟩
      there (ρ l₁ T₁ x)
    R.≅⟨ H.cong₂ {B = λ ■ → inn ■ Γ₂} (λ _ → inn.there)
                 (H.≡-to-≅ (sym (TidᵣT≡T (Tren ρ* T₁)))) (H.sym (H.≡-subst-removable F₄ E₄ _)) ⟩
      there (sub₄ (ρ l₁ T₁ x))
    R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
      sub₃ (there (sub₄ (ρ l₁ T₁ x)))
    R.≅⟨ refl ⟩
      (ρ >>RR Ewkᵣ Tidᵣ Eidᵣ) l₁ T₁ x
    R.∎

swap-Eren-Ewk :
  ∀ {ρ* : TRen Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {T : Type Δ₁ l}
    (ρ : ERen ρ* Γ₁ Γ₂) (T′ : Type Δ₁ l′) (e : Expr Δ₁ Γ₁ T) →
  Eren ρ* (Eliftᵣ {T = T′} ρ* ρ) (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) e) ≅
  Eren Tidᵣ (Ewkᵣ {T = Tren ρ* T′} Tidᵣ Eidᵣ) (Eren ρ* ρ e)
swap-Eren-Ewk {Δ₁} {Δ₂} {l} {l′} {ρ*} {Γ₁} {Γ₂} {T} ρ T′ e =
  R.begin
    Eren ρ* (Eliftᵣ ρ* ρ) (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) e)
  R.≅⟨ fusion-Eren-Eren' e (Ewkᵣ Tidᵣ Eidᵣ) (Eliftᵣ ρ* ρ) ⟩
    Eren ρ* (Ewkᵣ {T = T′} Tidᵣ Eidᵣ >>RR Eliftᵣ ρ* ρ) e
  R.≅⟨ H.cong (λ ■ → Eren ρ* ■ e) (swap-ren-Ewk ρ T′) ⟩
    Eren ρ* (ρ >>RR Ewkᵣ {T = Tren ρ* T′} Tidᵣ Eidᵣ) e
  R.≅⟨ H.sym (fusion-Eren-Eren' e ρ (Ewkᵣ Tidᵣ Eidᵣ)) ⟩
    Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (Eren ρ* ρ e)
  R.∎

swap-ren-Ewk-l :
  ∀ {ρ* : TRen Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂}
    (ρ : ERen ρ* Γ₁ Γ₂) (l : Level) →
  Ewkᵣ-l l >>RR Eliftᵣ-l ρ* ρ ≅ ρ >>RR Ewkᵣ-l l
swap-ren-Ewk-l {Δ₁} {Δ₂} {ρ*} {Γ₁} {Γ₂} ρ l =
  fun-ext-h-ERen refl refl λ l₁ T₁ x →
    let
      F₁ = (λ T → inn T (l ◁* Γ₂)) ; E₁ = (fusion-Tren-Tren T₁ (Twkᵣ Tidᵣ) (Tliftᵣ ρ* l))              ; sub₁ = subst F₁ E₁
      F₂ = id                      ; E₂ = (cong (λ T → inn T (l ◁* Γ₂)) (sym (swap-Tren-Twk ρ* _))) ; sub₂ = subst F₂ E₂
      F₃ = (λ T → inn T (l ◁* Γ₂)) ; E₃ = (fusion-Tren-Tren T₁ ρ* (Twkᵣ Tidᵣ))                         ; sub₃ = subst F₃ E₃
    in
    R.begin
      (Ewkᵣ-l l >>RR Eliftᵣ-l ρ* ρ) l₁ T₁ x
    R.≅⟨ refl ⟩
      sub₁ (sub₂ (tskip (ρ l₁ T₁ x)))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      sub₂ (tskip (ρ l₁ T₁ x))
    R.≅⟨ H.≡-subst-removable F₂ E₂ _ ⟩
      tskip (ρ l₁ T₁ x)
    R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
      sub₃ (tskip (ρ l₁ T₁ x))
    R.≅⟨ refl ⟩
      (ρ >>RR Ewkᵣ-l l) l₁ T₁ x
    R.∎

swap-Eren-Ewk-l :
  ∀ {ρ* : TRen Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {T : Type Δ₁ l}
    (ρ : ERen ρ* Γ₁ Γ₂) (l′ : Level) (e : Expr Δ₁ Γ₁ T) →
  Eren (Tliftᵣ ρ* l′) (Eliftᵣ-l ρ* ρ) (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l′) e) ≅
  Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l′) (Eren ρ* ρ e)
swap-Eren-Ewk-l {Δ₁} {Δ₂} {l} {ρ*} {Γ₁} {Γ₂} {T} ρ l′ e =
  R.begin
    Eren (Tliftᵣ ρ* l′) (Eliftᵣ-l ρ* ρ) (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l′) e)
  R.≅⟨ fusion-Eren-Eren' e (Ewkᵣ-l l′) (Eliftᵣ-l ρ* ρ) ⟩
    Eren (Twkᵣ ρ*) (Ewkᵣ-l l′ >>RR Eliftᵣ-l ρ* ρ) e
  R.≅⟨ H.cong (λ ■ → Eren (Twkᵣ ρ*) ■ e) (swap-ren-Ewk-l ρ l′) ⟩
    Eren (Twkᵣ ρ*) (ρ >>RR Ewkᵣ-l l′) e
  R.≅⟨ H.sym (fusion-Eren-Eren' e ρ (Ewkᵣ-l l′)) ⟩
    Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l′) (Eren ρ* ρ e)
  R.∎
