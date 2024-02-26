{-# OPTIONS --allow-unsolved-metas #-}

module ExprSubstFusion.SubSub where

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
open import ExprSubstFusion.SwapSub
open import ExprSubstFusion.RenRen
open import ExprSubstFusion.SubRen
open import ExprSubstFusion.RenSub

-- ∘ₛₛ Fusion

Esub↑-dist-∘ₛₛ :
  ∀ {σ* : TSub Δ₁ Δ₂} {ρ* : TSub Δ₂ Δ₃} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃} 
    (T : Type Δ₁ l)
    (σ : ESub σ* Γ₁ Γ₂) (ρ : ESub ρ* Γ₂ Γ₃) →
  Eliftₛ {T = T} σ* σ >>SS Eliftₛ ρ* ρ ≅ Eliftₛ {T = T} (σ* ∘ₛₛ ρ*) (σ >>SS ρ)
Esub↑-dist-∘ₛₛ {Δ₂ = Δ₂} {Δ₃ = Δ₃} {l = l'} {σ* = σ*} {ρ* = ρ*} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ₃ = Γ₃} T σ ρ =
  fun-ext-h-ESub refl (cong (_◁ Γ₃) (fusion-Tsub-Tsub T σ* ρ*)) λ l T′ → λ where
  here →
    let
      F₁ = (Expr _ (Tsub ρ* (Tsub σ* T) ◁ Γ₃)) ; E₁ = (fusion-Tsub-Tsub T σ* ρ*) ; sub₁ = subst F₁ E₁
    in
    R.begin
      sub₁ (` here)
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩ 
      ` here
    R.≅⟨ H.cong {B = λ ■ → Expr _ (■ ◁ Γ₃) ■} (λ ■ → `_ {Γ = ■ ◁ Γ₃} {T = ■} here) (H.≡-to-≅ (fusion-Tsub-Tsub T σ* ρ*)) ⟩ 
      ` here
    R.≅⟨ refl ⟩
      Eliftₛ (σ* ∘ₛₛ ρ*) (σ >>SS ρ) l' T here
    R.∎
  (there x) →
    let
      F₁ = (Expr _ (Tsub ρ* (Tsub σ* T) ◁ Γ₃))                  ; E₁ = (fusion-Tsub-Tsub T′ σ* ρ*)                         ; sub₁ = subst F₁ E₁
      F₂ = (Expr _ (Tsub σ* T ◁ _))                             ; E₂ = (TidᵣT≡T (Tsub σ* T′))                           ; sub₂ = subst F₂ E₂
      F₃ = (Expr Δ₃ (Tsub (λ z x₁ → Tsub ρ* (σ* z x₁)) T ◁ Γ₃)) ; E₃ = (TidᵣT≡T (Tsub (λ z x₁ → Tsub ρ* (σ* z x₁)) T′)) ; sub₃ = subst F₃ E₃
      F₄ = (Expr Δ₃ Γ₃)                                         ; E₄ = E₁                                               ; sub₄ = subst F₄ E₄
    in
    R.begin
      (Eliftₛ {T = T} σ* σ >>SS Eliftₛ ρ* ρ) l T′ (there x)
    R.≅⟨ refl ⟩
      sub₁ (Esub ρ* (Eliftₛ ρ* ρ) (sub₂ (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (σ l T′ x))))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      Esub ρ* (Eliftₛ ρ* ρ) (sub₂ (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (σ l T′ x)))
    R.≅⟨ H.cong₂ {B = Expr Δ₂ (Tsub σ* T ◁ Γ₂)} (λ _ → Esub ρ* (Eliftₛ ρ* ρ))
                 (H.≡-to-≅ (sym (TidᵣT≡T (Tsub σ* T′)))) (H.≡-subst-removable F₂ E₂ _) ⟩
      Esub ρ* (Eliftₛ ρ* ρ) (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (σ l T′ x))
    R.≅⟨ swap-Esub-Ewk ρ (Tsub σ* T) (σ l T′ x) ⟩
      Eren Tidᵣ (Ewkᵣ {T = Tsub ρ* (Tsub σ* T)} Tidᵣ Eidᵣ) (Esub ρ* ρ (σ l T′ x))
    R.≅⟨ H.cong (λ ■ → Eren Tidᵣ (Ewkᵣ {T = ■} Tidᵣ Eidᵣ) (Esub ρ* ρ (σ l T′ x)))
                (H.≡-to-≅ (fusion-Tsub-Tsub T σ* ρ*)) ⟩
      Eren Tidᵣ (Ewkᵣ {T = Tsub (σ* ∘ₛₛ ρ*) T} Tidᵣ Eidᵣ) (Esub ρ* ρ (σ l T′ x))
    R.≅⟨ H.cong₂ {B = Expr Δ₃ Γ₃} (λ _ → Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ))
                 (H.≡-to-≅ (fusion-Tsub-Tsub T′ σ* ρ*)) (H.sym (H.≡-subst-removable F₄ E₄ _)) ⟩
      Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (sub₄ (Esub ρ* ρ (σ l T′ x)))
    R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
      sub₃ (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (sub₄ (Esub ρ* ρ (σ l T′ x))))
    R.≅⟨ refl ⟩
      sub₃ (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) ((σ >>SS ρ) _ _ x))
    R.≅⟨ refl ⟩
      Ewk ((σ >>SS ρ) _ _ x)
    R.≅⟨ refl ⟩
      Eliftₛ {T = T} (σ* ∘ₛₛ ρ*) (σ >>SS ρ) l T′ (there x)
    R.∎

Esub↑-dist-∘ₛₛ-l :
  ∀ {σ* : TSub Δ₁ Δ₂} {ρ* : TSub Δ₂ Δ₃}
    {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃}
    {l : Level} (σ : ESub σ* Γ₁ Γ₂) (ρ : ESub ρ* Γ₂ Γ₃) →
  Eliftₛ-l {l = l} σ* σ >>SS Eliftₛ-l ρ* ρ ≅ Eliftₛ-l {l = l} (σ* ∘ₛₛ ρ*) (σ >>SS ρ)
Esub↑-dist-∘ₛₛ-l {Δ₁} {Δ₂} {Δ₃} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {l} σ ρ =
  fun-ext-h-ESub (sym (sub↑-dist-∘ₛₛ l σ* ρ*)) refl λ l′ T → λ where
    (tskip {T = T′} x) →
      let
        F₁ = (Expr (l ∷ Δ₃) (l ◁* Γ₃)) ; E₁ = (fusion-Tsub-Tsub (Tren (Twkᵣ Tidᵣ) T′) (Tliftₛ σ* l) (Tliftₛ ρ* l)) ; sub₁ = subst F₁ E₁
        F₂ = (Expr (l ∷ Δ₂) (l ◁* Γ₂)) ; E₂ = (sym (swap-Tsub-Twk σ* T′))                                       ; sub₂ = subst F₂ E₂
        F₃ = (Expr (l ∷ Δ₃) (l ◁* Γ₃)) ; E₃ = (sym (swap-Tsub-Twk (σ* ∘ₛₛ ρ*) T′))                              ; sub₃ = subst F₃ E₃
        F₄ = (Expr Δ₃ Γ₃)              ; E₄ = (fusion-Tsub-Tsub T′ σ* ρ*)                                          ; sub₄ = subst F₄ E₄
      in
      R.begin
        (Eliftₛ-l σ* σ >>SS Eliftₛ-l ρ* ρ) l′ (Twk T′) (tskip x)
      R.≅⟨ refl ⟩
        sub₁ (Esub (Tliftₛ ρ* l) (Eliftₛ-l ρ* ρ) (sub₂ (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (σ l′ T′ x))))
      R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
        Esub (Tliftₛ ρ* l) (Eliftₛ-l ρ* ρ) (sub₂ (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (σ l′ T′ x)))
      R.≅⟨ H.cong₂ {B = Expr (l ∷ Δ₂) (l ◁* Γ₂)} (λ _ → Esub (Tliftₛ ρ* l) (Eliftₛ-l ρ* ρ))
                   (H.≡-to-≅ (swap-Tsub-Twk σ* T′)) (H.≡-subst-removable F₂ E₂ _) ⟩
        Esub (Tliftₛ ρ* l) (Eliftₛ-l ρ* ρ) (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (σ l′ T′ x))
      R.≅⟨ swap-Esub-Ewk-l ρ l (σ l′ T′ x) ⟩
        Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (Esub ρ* ρ (σ l′ T′ x))
      R.≅⟨ H.cong₂ {B = Expr Δ₃ Γ₃} (λ _ → Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l))
                   (H.≡-to-≅ (fusion-Tsub-Tsub T′ σ* ρ*)) (H.sym (H.≡-subst-removable F₄ E₄ _)) ⟩
        Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (sub₄ (Esub ρ* ρ (σ l′ T′ x)))
      R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
        sub₃ (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (sub₄ (Esub ρ* ρ (σ l′ T′ x))))
      R.≅⟨ refl ⟩
        Eliftₛ-l (σ* ∘ₛₛ ρ*) (σ >>SS ρ) l′ (Twk T′) (tskip x)
      R.∎

mutual
  Eassoc-sub↑-sub↑-l :
    ∀ {σ* : TSub Δ₁ Δ₂} {ρ* : TSub Δ₂ Δ₃}
      {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃}
      {l′ : Level}
      {T : Type (l′ ∷ Δ₁) l}
      (e : Expr (l′ ∷ Δ₁) (l′ ◁* Γ₁) T)
      (σ : ESub σ* Γ₁ Γ₂) (ρ : ESub ρ* Γ₂ Γ₃) →
    Esub (Tliftₛ σ* l′ ∘ₛₛ Tliftₛ ρ* l′) (Eliftₛ-l σ* σ >>SS Eliftₛ-l ρ* ρ) e ≅
    Esub (Tliftₛ (σ* ∘ₛₛ ρ*) l′) (Eliftₛ-l (σ* ∘ₛₛ ρ*) (σ >>SS ρ)) e
  Eassoc-sub↑-sub↑-l {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {l′} {T} e σ ρ =
    R.begin
      Esub (Tliftₛ σ* l′ ∘ₛₛ Tliftₛ ρ* l′) (Eliftₛ-l σ* σ >>SS Eliftₛ-l ρ* ρ) e
    R.≅⟨ H.cong₂ (λ ■₁ ■₂ → Esub {Γ₂ = l′ ◁* Γ₃} ■₁ ■₂ e) (H.≡-to-≅ (sym (sub↑-dist-∘ₛₛ l′ σ* ρ*))) (Esub↑-dist-∘ₛₛ-l σ ρ) ⟩
      Esub (Tliftₛ (σ* ∘ₛₛ ρ*) l′) (Eliftₛ-l (σ* ∘ₛₛ ρ*) (σ >>SS ρ)) e
    R.∎

  Eassoc-sub↑-sub↑ :
    ∀ {σ* : TSub Δ₁ Δ₂} {ρ* : TSub Δ₂ Δ₃}
      {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
      {T : Type Δ₁ l}
      {T′ : Type Δ₁ l′}
      (e : Expr Δ₁ (T′ ◁  Γ₁) T)
      (σ : ESub σ* Γ₁ Γ₂) (ρ : ESub ρ* Γ₂ Γ₃) →
    Esub ρ* (Eliftₛ {T = Tsub σ* T′} ρ* ρ) (Esub σ* (Eliftₛ σ* σ) e) ≅
    Esub (σ* ∘ₛₛ ρ*) (Eliftₛ {T = T′} (σ* ∘ₛₛ ρ*) (σ >>SS ρ)) e
  Eassoc-sub↑-sub↑ {Δ₃ = Δ₃} {σ* = σ*} {ρ* = ρ*} {Γ₁ = Γ₁} {Γ₃ = Γ₃} {T = T} {T′ = T′} e σ ρ =
    R.begin
      Esub ρ* (Eliftₛ ρ* ρ) (Esub σ* (Eliftₛ σ* σ) e)
    R.≅⟨ fusion-Esub-Esub' e (Eliftₛ σ* σ) (Eliftₛ ρ* ρ) ⟩
      Esub (σ* ∘ₛₛ ρ*) ((Eliftₛ σ* σ) >>SS (Eliftₛ ρ* ρ)) e
    R.≅⟨ H.cong₂ {B = λ ■ → ESub (σ* ∘ₛₛ ρ*) (_ ◁ Γ₁) (■ ◁ Γ₃)}
                 (λ _ ■ → Esub (σ* ∘ₛₛ ρ*) ■ e)
                 (H.≡-to-≅ (fusion-Tsub-Tsub T′ σ* ρ*)) (Esub↑-dist-∘ₛₛ _ σ ρ) ⟩
      Esub (σ* ∘ₛₛ ρ*) (Eliftₛ (σ* ∘ₛₛ ρ*) (σ >>SS ρ)) e
    R.∎

  fusion-Esub-Esub' : 
      {σ* : TSub Δ₁ Δ₂} {ρ* : TSub Δ₂ Δ₃}
    → {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
    → {T : Type Δ₁ l}
    → (e : Expr Δ₁ Γ₁ T)
    → (σ : ESub σ* Γ₁ Γ₂) (ρ : ESub ρ* Γ₂ Γ₃)
    → Esub ρ* ρ (Esub σ* σ e) ≅ Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) e
  fusion-Esub-Esub' {Δ₁} {Δ₂} {Δ₃} {.zero} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {.`ℕ} (# n) σ ρ =
    refl
  fusion-Esub-Esub' {Δ₁} {Δ₂} {Δ₃} {.zero} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {.`ℕ} (`suc e) ρ σ =
    R.begin
      Esub σ* σ (Esub ρ* ρ (`suc e))
    R.≅⟨ refl ⟩
      `suc (Esub σ* σ (Esub ρ* ρ e))
    R.≅⟨ H.cong `suc (fusion-Esub-Esub' e ρ σ) ⟩
      `suc (Esub (ρ* ∘ₛₛ σ*) (ρ >>SS σ) e)
    R.≅⟨ refl ⟩
      Esub (ρ* ∘ₛₛ σ*) (ρ >>SS σ) (`suc e)
    R.∎
  fusion-Esub-Esub' {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {T} (` x) σ ρ =
    let F₁ = (Expr Δ₃ Γ₃) ; E₁ = (fusion-Tsub-Tsub T σ* ρ*) ; sub₁ = subst F₁ E₁ in
    R.begin
      Esub ρ* ρ (Esub σ* σ (` x))
    R.≅⟨ refl ⟩
      Esub ρ* ρ (σ l T x)
    R.≅⟨ H.sym (H.≡-subst-removable F₁ E₁ _) ⟩
      sub₁ (Esub ρ* ρ (σ l T x))
    R.≅⟨ refl ⟩
      Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) (` x)
    R.∎
  fusion-Esub-Esub' {Δ₁} {Δ₂} {Δ₃} {_} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {T₁ ⇒ T₂} (ƛ e) σ ρ =
    R.begin
      ƛ Esub ρ* (Eliftₛ ρ* ρ) (Esub σ* (Eliftₛ σ* σ) e)
    R.≅⟨ Hcong₃ {C = λ ■₁ ■₂ → Expr Δ₃ (■₁ ◁ Γ₃) ■₂} (λ _ _ ■ → ƛ ■)
                (H.≡-to-≅ (fusion-Tsub-Tsub T₁ σ* ρ*))
                (H.≡-to-≅ (fusion-Tsub-Tsub T₂ σ* ρ*))
                (Eassoc-sub↑-sub↑ e σ ρ)  ⟩
      ƛ (Esub (σ* ∘ₛₛ ρ*) (Eliftₛ (σ* ∘ₛₛ ρ*) (σ >>SS ρ)) e)
    R.≅⟨ refl ⟩
      Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) (ƛ e)
    R.∎
  fusion-Esub-Esub' {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {T} (_·_ {T = T₁} {T′ = T₂} e₁ e₂) σ ρ =
    R.begin
      Esub ρ* ρ (Esub σ* σ (e₁ · e₂))
    R.≅⟨ refl ⟩
      Esub ρ* ρ (Esub σ* σ e₁) · Esub ρ* ρ (Esub σ* σ e₂)
    R.≅⟨ Hcong₄ {C = λ ■₁ ■₂ → Expr Δ₃ Γ₃ (■₂ ⇒ ■₁)} {D = λ _ ■₂ _ → Expr Δ₃ Γ₃ ■₂} (λ _ _ → _·_)
                (H.≡-to-≅ (fusion-Tsub-Tsub T σ* ρ*)) (H.≡-to-≅ (fusion-Tsub-Tsub T₁ σ* ρ*))
                (fusion-Esub-Esub' e₁ σ ρ) (fusion-Esub-Esub' e₂ σ ρ) ⟩
      Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) e₁ · Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) e₂
    R.≅⟨ refl ⟩
      Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) (e₁ · e₂)
    R.∎
  fusion-Esub-Esub' {Δ₁} {Δ₂} {Δ₃} {_} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {`∀α l , T} (Λ l ⇒ e) σ ρ =
    R.begin
      Esub ρ* ρ (Esub σ* σ (Λ l ⇒ e))
    R.≅⟨ refl ⟩
      Λ l ⇒ Esub (Tliftₛ ρ* l) (Eliftₛ-l ρ* ρ) (Esub (Tliftₛ σ* l) (Eliftₛ-l σ* σ) e)
    R.≅⟨ H.cong₂ {B = Expr (l ∷ Δ₃) (l ◁* Γ₃)} (λ _ → Λ l ⇒_)
                 (H.≡-to-≅ (fusion-Tsub-Tsub T (Tliftₛ σ* _) (Tliftₛ ρ* _)))
                 (fusion-Esub-Esub' e (Eliftₛ-l σ* σ) (Eliftₛ-l ρ* ρ)) ⟩
      Λ l ⇒ Esub (Tliftₛ σ* l ∘ₛₛ Tliftₛ ρ* l) (Eliftₛ-l σ* σ >>SS Eliftₛ-l ρ* ρ) e
    R.≅⟨ H.cong₂ {B = Expr (l ∷ Δ₃) (l ◁* Γ₃)} (λ _ → Λ l ⇒_)
                 (H.≡-to-≅ (cong (λ σ → Tsub σ T) (sym (sub↑-dist-∘ₛₛ _ σ* ρ*))))
                 (Eassoc-sub↑-sub↑-l e σ ρ) ⟩
      Λ l ⇒ Esub (Tliftₛ (σ* ∘ₛₛ ρ*) l) (Eliftₛ-l (σ* ∘ₛₛ ρ*) (σ >>SS ρ)) e
    R.≅⟨ refl ⟩
      Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) (Λ l ⇒ e)
    R.∎
  fusion-Esub-Esub' {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {_} (_∙_ {T = T} e T′) σ ρ =
    let
      F₂ = Expr Δ₂ Γ₂ ; E₂ = sym (swap-Tsub-[] σ* T T′)                                ; sub₂ = subst F₂ E₂
      F₃ = Expr Δ₃ Γ₃ ; E₃ = sym (swap-Tsub-[] (σ* ∘ₛₛ ρ*) T T′)                       ; sub₃ = subst F₃ E₃
      F₅ = Expr Δ₃ Γ₃ ; E₅ = sym (swap-Tsub-[] ρ* (Tsub (Tliftₛ σ* _) T) (Tsub σ* T′)) ; sub₅ = subst F₅ E₅
    in
    R.begin
      Esub ρ* ρ (Esub σ* σ (e ∙ T′))
    R.≅⟨ refl ⟩
      Esub ρ* ρ (sub₂ (Esub σ* σ e ∙ Tsub σ* T′))
    R.≅⟨ H.cong₂ {B = Expr Δ₂ Γ₂} (λ _ ■ → Esub ρ* ρ ■) (H.≡-to-≅ (sym E₂)) (H.≡-subst-removable F₂ E₂ _) ⟩
      Esub ρ* ρ (Esub σ* σ e ∙ Tsub σ* T′)
    R.≅⟨ refl ⟩
      sub₅ (Esub ρ* ρ (Esub σ* σ e) ∙ Tsub ρ* (Tsub σ* T′))
    R.≅⟨ H.≡-subst-removable F₅ E₅ _ ⟩
      Esub ρ* ρ (Esub σ* σ e) ∙ Tsub ρ* (Tsub σ* T′)
    R.≅⟨ Hcong₃ {B = λ ■ → Expr Δ₃ Γ₃ (`∀α _ , ■)} {C = λ _ _ → Type Δ₃ _ } (λ _ ■₁ ■₂ → ■₁ ∙ ■₂)
         (H.≡-to-≅ (assoc-sub↑-sub↑ T σ* ρ*)) (fusion-Esub-Esub' e σ ρ) (H.≡-to-≅ (fusion-Tsub-Tsub T′ σ* ρ*)) ⟩
      Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) e ∙ Tsub (σ* ∘ₛₛ ρ*) T′
    R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
      sub₃ (Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) e ∙ (Tsub (σ* ∘ₛₛ ρ*) T′))
    R.≅⟨ refl ⟩
      Esub (σ* ∘ₛₛ ρ*) (σ >>SS ρ) (e ∙ T′)
    R.∎ 
