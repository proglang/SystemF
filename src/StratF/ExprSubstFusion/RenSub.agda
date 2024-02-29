module StratF.ExprSubstFusion.RenSub where

open import Data.List using (List; []; _∷_; [_])
open import Function using (_∘_; id; _$_)
open import Level
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning

open import StratF.ExprSubstitution
open import StratF.Expressions
open import StratF.TypeSubstProperties
open import StratF.TypeSubstitution
open import StratF.Types
open import StratF.Util.Extensionality
open import StratF.Util.HeterogeneousEqualityLemmas

open import StratF.ExprSubstFusion.SwapRen

-- ∘ₛᵣ Fusion

Esub↑-dist-∘ₛᵣ :
  ∀ {σ* : TSub Δ₁ Δ₂} {ρ* : TRen Δ₂ Δ₃} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃} 
    (T : Type Δ₁ l)
    (σ : ESub σ* Γ₁ Γ₂) (ρ : ERen ρ* Γ₂ Γ₃) →
  Eliftₛ {T = T} σ* σ >>SR Eliftᵣ ρ* ρ ≅ Eliftₛ {T = T} (σ* ∘ₛᵣ ρ*) (σ >>SR ρ)
Esub↑-dist-∘ₛᵣ {Δ₂ = Δ₂} {Δ₃ = Δ₃} {l = l'} {σ* = σ*} {ρ* = ρ*} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ₃ = Γ₃} T σ ρ =
  fun-ext-h-ESub refl (cong (_◁ Γ₃) (fusion-Tren-Tsub T σ* ρ*)) λ l T′ → λ where
  here →
    let
      F₁ = (Expr _ (Tren ρ* (Tsub σ* T) ◁ Γ₃)) ; E₁ = (fusion-Tren-Tsub T σ* ρ*) ; sub₁ = subst F₁ E₁
    in
    R.begin
      sub₁ (` here)
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩ 
      ` here
    R.≅⟨ H.cong {B = λ ■ → Expr _ (■ ◁ Γ₃) ■} (λ ■ → `_ {Γ = ■ ◁ Γ₃} {T = ■} here) (H.≡-to-≅ (fusion-Tren-Tsub T σ* ρ*)) ⟩ 
      ` here
    R.≅⟨ refl ⟩
      Eliftₛ (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) l' T here
    R.∎
  (there x) →
    let
      F₁ = (Expr _ (Tren ρ* (Tsub σ* T) ◁ Γ₃))                  ; E₁ = (fusion-Tren-Tsub T′ σ* ρ*)                         ; sub₁ = subst F₁ E₁
      F₂ = (Expr _ (Tsub σ* T ◁ _))                             ; E₂ = (TidᵣT≡T (Tsub σ* T′))                           ; sub₂ = subst F₂ E₂
      F₃ = (Expr Δ₃ (Tsub (λ z x₁ → Tren ρ* (σ* z x₁)) T ◁ Γ₃)) ; E₃ = (TidᵣT≡T (Tsub (λ z x₁ → Tren ρ* (σ* z x₁)) T′)) ; sub₃ = subst F₃ E₃
      F₄ = (Expr Δ₃ Γ₃)                                         ; E₄ = E₁                                               ; sub₄ = subst F₄ E₄
    in
    R.begin
      (Eliftₛ {T = T} σ* σ >>SR Eliftᵣ ρ* ρ) l T′ (there x)
    R.≅⟨ refl ⟩
      sub₁ (Eren ρ* (Eliftᵣ ρ* ρ) (sub₂ (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (σ l T′ x))))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      Eren ρ* (Eliftᵣ ρ* ρ) (sub₂ (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (σ l T′ x)))
    R.≅⟨ H.cong₂ {B = Expr Δ₂ (Tsub σ* T ◁ Γ₂)} (λ _ → Eren ρ* (Eliftᵣ ρ* ρ))
                 (H.≡-to-≅ (sym (TidᵣT≡T (Tsub σ* T′)))) (H.≡-subst-removable F₂ E₂ _) ⟩
      Eren ρ* (Eliftᵣ ρ* ρ) (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (σ l T′ x))
    R.≅⟨ swap-Eren-Ewk ρ (Tsub σ* T) (σ l T′ x) ⟩
      Eren Tidᵣ (Ewkᵣ {T = Tren ρ* (Tsub σ* T)} Tidᵣ Eidᵣ) (Eren ρ* ρ (σ l T′ x))
    R.≅⟨ H.cong (λ ■ → Eren Tidᵣ (Ewkᵣ {T = ■} Tidᵣ Eidᵣ) (Eren ρ* ρ (σ l T′ x)))
                (H.≡-to-≅ (fusion-Tren-Tsub T σ* ρ*)) ⟩
      Eren Tidᵣ (Ewkᵣ {T = Tsub (σ* ∘ₛᵣ ρ*) T} Tidᵣ Eidᵣ) (Eren ρ* ρ (σ l T′ x))
    R.≅⟨ H.cong₂ {B = Expr Δ₃ Γ₃} (λ _ → Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ))
                 (H.≡-to-≅ (fusion-Tren-Tsub T′ σ* ρ*)) (H.sym (H.≡-subst-removable F₄ E₄ _)) ⟩
      Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (sub₄ (Eren ρ* ρ (σ l T′ x)))
    R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
      sub₃ (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) (sub₄ (Eren ρ* ρ (σ l T′ x))))
    R.≅⟨ refl ⟩
      sub₃ (Eren Tidᵣ (Ewkᵣ Tidᵣ Eidᵣ) ((σ >>SR ρ) _ _ x))
    R.≅⟨ refl ⟩
      Ewk ((σ >>SR ρ) _ _ x)
    R.≅⟨ refl ⟩
      Eliftₛ {T = T} (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) l T′ (there x)
    R.∎

Esub↑-dist-∘ₛᵣ-l :
  ∀ {σ* : TSub Δ₁ Δ₂} {ρ* : TRen Δ₂ Δ₃}
    {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃}
    {l : Level} (σ : ESub σ* Γ₁ Γ₂) (ρ : ERen ρ* Γ₂ Γ₃) →
  Eliftₛ-l {l = l} σ* σ >>SR Eliftᵣ-l ρ* ρ ≅ Eliftₛ-l {l = l} (σ* ∘ₛᵣ ρ*) (σ >>SR ρ)
Esub↑-dist-∘ₛᵣ-l {Δ₁} {Δ₂} {Δ₃} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {l} σ ρ =
  fun-ext-h-ESub (sym (ren↑-dist-∘ₛᵣ l σ* ρ*)) refl λ l′ T → λ where
    (tskip {T = T′} x) →
      let
        F₁ = (Expr (l ∷ Δ₃) (l ◁* Γ₃)) ; E₁ = (fusion-Tren-Tsub (Tren (Twkᵣ Tidᵣ) T′) (Tliftₛ σ* l) (Tliftᵣ ρ* l)) ; sub₁ = subst F₁ E₁
        F₂ = (Expr (l ∷ Δ₂) (l ◁* Γ₂)) ; E₂ = (sym (swap-Tsub-Twk σ* T′))                                       ; sub₂ = subst F₂ E₂
        F₃ = (Expr (l ∷ Δ₃) (l ◁* Γ₃)) ; E₃ = (sym (swap-Tsub-Twk (σ* ∘ₛᵣ ρ*) T′))                              ; sub₃ = subst F₃ E₃
        F₄ = (Expr Δ₃ Γ₃)              ; E₄ = (fusion-Tren-Tsub T′ σ* ρ*)                                          ; sub₄ = subst F₄ E₄
      in
      R.begin
        (Eliftₛ-l σ* σ >>SR Eliftᵣ-l ρ* ρ) l′ (Twk T′) (tskip x)
      R.≅⟨ refl ⟩
        sub₁ (Eren (Tliftᵣ ρ* l) (Eliftᵣ-l ρ* ρ) (sub₂ (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (σ l′ T′ x))))
      R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
        Eren (Tliftᵣ ρ* l) (Eliftᵣ-l ρ* ρ) (sub₂ (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (σ l′ T′ x)))
      R.≅⟨ H.cong₂ {B = Expr (l ∷ Δ₂) (l ◁* Γ₂)} (λ _ → Eren (Tliftᵣ ρ* l) (Eliftᵣ-l ρ* ρ))
                   (H.≡-to-≅ (swap-Tsub-Twk σ* T′)) (H.≡-subst-removable F₂ E₂ _) ⟩
        Eren (Tliftᵣ ρ* l) (Eliftᵣ-l ρ* ρ) (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (σ l′ T′ x))
      R.≅⟨ swap-Eren-Ewk-l ρ l (σ l′ T′ x) ⟩
        Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (Eren ρ* ρ (σ l′ T′ x))
      R.≅⟨ H.cong₂ {B = Expr Δ₃ Γ₃} (λ _ → Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l))
                   (H.≡-to-≅ (fusion-Tren-Tsub T′ σ* ρ*)) (H.sym (H.≡-subst-removable F₄ E₄ _)) ⟩
        Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (sub₄ (Eren ρ* ρ (σ l′ T′ x)))
      R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
        sub₃ (Eren (Twkᵣ Tidᵣ) (Ewkᵣ-l l) (sub₄ (Eren ρ* ρ (σ l′ T′ x))))
      R.≅⟨ refl ⟩
        Eliftₛ-l (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) l′ (Twk T′) (tskip x)
      R.∎

mutual
  fusion-Eren-Esub-lift-l :
    ∀ {σ* : TSub Δ₁ Δ₂} {ρ* : TRen Δ₂ Δ₃}
      {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃}
      {l′ : Level}
      {T : Type (l′ ∷ Δ₁) l}
      (e : Expr (l′ ∷ Δ₁) (l′ ◁* Γ₁) T)
      (σ : ESub σ* Γ₁ Γ₂) (ρ : ERen ρ* Γ₂ Γ₃) →
    Esub (Tliftₛ σ* l′ ∘ₛᵣ Tliftᵣ ρ* l′) (Eliftₛ-l σ* σ >>SR Eliftᵣ-l ρ* ρ) e ≅
    Esub (Tliftₛ (σ* ∘ₛᵣ ρ*) l′) (Eliftₛ-l (σ* ∘ₛᵣ ρ*) (σ >>SR ρ)) e
  fusion-Eren-Esub-lift-l {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {l′} {T} e σ ρ =
    R.begin
      Esub (Tliftₛ σ* l′ ∘ₛᵣ Tliftᵣ ρ* l′) (Eliftₛ-l σ* σ >>SR Eliftᵣ-l ρ* ρ) e
    R.≅⟨ H.cong₂ (λ ■₁ ■₂ → Esub {Γ₂ = l′ ◁* Γ₃} ■₁ ■₂ e) (H.≡-to-≅ (sym (ren↑-dist-∘ₛᵣ l′ σ* ρ*))) (Esub↑-dist-∘ₛᵣ-l σ ρ) ⟩
      Esub (Tliftₛ (σ* ∘ₛᵣ ρ*) l′) (Eliftₛ-l (σ* ∘ₛᵣ ρ*) (σ >>SR ρ)) e
    R.∎

  fusion-Eren-Esub-lift :
    ∀ {σ* : TSub Δ₁ Δ₂} {ρ* : TRen Δ₂ Δ₃}
      {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
      {T : Type Δ₁ l}
      {T′ : Type Δ₁ l′}
      (e : Expr Δ₁ (T′ ◁  Γ₁) T)
      (σ : ESub σ* Γ₁ Γ₂) (ρ : ERen ρ* Γ₂ Γ₃) →
    Eren ρ* (Eliftᵣ {T = Tsub σ* T′} ρ* ρ) (Esub σ* (Eliftₛ σ* σ) e) ≅
    Esub (σ* ∘ₛᵣ ρ*) (Eliftₛ {T = T′} (σ* ∘ₛᵣ ρ*) (σ >>SR ρ)) e
  fusion-Eren-Esub-lift {Δ₃ = Δ₃} {σ* = σ*} {ρ* = ρ*} {Γ₁ = Γ₁} {Γ₃ = Γ₃} {T = T} {T′ = T′} e σ ρ =
    R.begin
      Eren ρ* (Eliftᵣ ρ* ρ) (Esub σ* (Eliftₛ σ* σ) e)
    R.≅⟨ fusion-Eren-Esub' e (Eliftₛ σ* σ) (Eliftᵣ ρ* ρ) ⟩
      Esub (σ* ∘ₛᵣ ρ*) ((Eliftₛ σ* σ) >>SR (Eliftᵣ ρ* ρ)) e
    R.≅⟨ H.cong₂ {B = λ ■ → ESub (σ* ∘ₛᵣ ρ*) (_ ◁ Γ₁) (■ ◁ Γ₃)}
                 (λ _ ■ → Esub (σ* ∘ₛᵣ ρ*) ■ e)
                 (H.≡-to-≅ (fusion-Tren-Tsub T′ σ* ρ*)) (Esub↑-dist-∘ₛᵣ _ σ ρ) ⟩
      Esub (σ* ∘ₛᵣ ρ*) (Eliftₛ (σ* ∘ₛᵣ ρ*) (σ >>SR ρ)) e
    R.∎

  fusion-Eren-Esub' : 
      {σ* : TSub Δ₁ Δ₂} {ρ* : TRen Δ₂ Δ₃}
    → {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
    → {T : Type Δ₁ l}
    → (e : Expr Δ₁ Γ₁ T)
    → (σ : ESub σ* Γ₁ Γ₂) (ρ : ERen ρ* Γ₂ Γ₃)
    → Eren ρ* ρ (Esub σ* σ e) ≅ Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) e
  fusion-Eren-Esub' {Δ₁} {Δ₂} {Δ₃} {.zero} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {.`ℕ} (# n) σ ρ =
    refl
  fusion-Eren-Esub' {Δ₁} {Δ₂} {Δ₃} {.zero} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {.`ℕ} (`suc e) ρ σ =
    R.begin
      Eren σ* σ (Esub ρ* ρ (`suc e))
    R.≅⟨ refl ⟩
      `suc (Eren σ* σ (Esub ρ* ρ e))
    R.≅⟨ H.cong `suc (fusion-Eren-Esub' e ρ σ) ⟩
      `suc (Esub (ρ* ∘ₛᵣ σ*) (ρ >>SR σ) e)
    R.≅⟨ refl ⟩
      Esub (ρ* ∘ₛᵣ σ*) (ρ >>SR σ) (`suc e)
    R.∎
  fusion-Eren-Esub' {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {T} (` x) σ ρ =
    let F₁ = (Expr Δ₃ Γ₃) ; E₁ = (fusion-Tren-Tsub T σ* ρ*) ; sub₁ = subst F₁ E₁ in
    R.begin
      Eren ρ* ρ (Esub σ* σ (` x))
    R.≅⟨ refl ⟩
      Eren ρ* ρ (σ l T x)
    R.≅⟨ H.sym (H.≡-subst-removable F₁ E₁ _) ⟩
      sub₁ (Eren ρ* ρ (σ l T x))
    R.≅⟨ refl ⟩
      Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) (` x)
    R.∎
  fusion-Eren-Esub' {Δ₁} {Δ₂} {Δ₃} {_} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {T₁ ⇒ T₂} (ƛ e) σ ρ =
    R.begin
      ƛ Eren ρ* (Eliftᵣ ρ* ρ) (Esub σ* (Eliftₛ σ* σ) e)
    R.≅⟨ Hcong₃ {C = λ ■₁ ■₂ → Expr Δ₃ (■₁ ◁ Γ₃) ■₂} (λ _ _ ■ → ƛ ■)
                (H.≡-to-≅ (fusion-Tren-Tsub T₁ σ* ρ*))
                (H.≡-to-≅ (fusion-Tren-Tsub T₂ σ* ρ*))
                (fusion-Eren-Esub-lift e σ ρ)  ⟩
      ƛ (Esub (σ* ∘ₛᵣ ρ*) (Eliftₛ (σ* ∘ₛᵣ ρ*) (σ >>SR ρ)) e)
    R.≅⟨ refl ⟩
      Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) (ƛ e)
    R.∎
  fusion-Eren-Esub' {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {T} (_·_ {T = T₁} {T′ = T₂} e₁ e₂) σ ρ =
    R.begin
      Eren ρ* ρ (Esub σ* σ (e₁ · e₂))
    R.≅⟨ refl ⟩
      Eren ρ* ρ (Esub σ* σ e₁) · Eren ρ* ρ (Esub σ* σ e₂)
    R.≅⟨ Hcong₄ {C = λ ■₁ ■₂ → Expr Δ₃ Γ₃ (■₂ ⇒ ■₁)} {D = λ _ ■₂ _ → Expr Δ₃ Γ₃ ■₂} (λ _ _ → _·_)
                (H.≡-to-≅ (fusion-Tren-Tsub T σ* ρ*)) (H.≡-to-≅ (fusion-Tren-Tsub T₁ σ* ρ*))
                (fusion-Eren-Esub' e₁ σ ρ) (fusion-Eren-Esub' e₂ σ ρ) ⟩
      Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) e₁ · Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) e₂
    R.≅⟨ refl ⟩
      Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) (e₁ · e₂)
    R.∎
  fusion-Eren-Esub' {Δ₁} {Δ₂} {Δ₃} {_} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {`∀α l , T} (Λ l ⇒ e) σ ρ =
    R.begin
      Eren ρ* ρ (Esub σ* σ (Λ l ⇒ e))
    R.≅⟨ refl ⟩
      Λ l ⇒ Eren (Tliftᵣ ρ* l) (Eliftᵣ-l ρ* ρ) (Esub (Tliftₛ σ* l) (Eliftₛ-l σ* σ) e)
    R.≅⟨ H.cong₂ {B = Expr (l ∷ Δ₃) (l ◁* Γ₃)} (λ _ → Λ l ⇒_)
                 (H.≡-to-≅ (fusion-Tren-Tsub T (Tliftₛ σ* _) (Tliftᵣ ρ* _)))
                 (fusion-Eren-Esub' e (Eliftₛ-l σ* σ) (Eliftᵣ-l ρ* ρ)) ⟩
      Λ l ⇒ Esub (Tliftₛ σ* l ∘ₛᵣ Tliftᵣ ρ* l) (Eliftₛ-l σ* σ >>SR Eliftᵣ-l ρ* ρ) e
    R.≅⟨ H.cong₂ {B = Expr (l ∷ Δ₃) (l ◁* Γ₃)} (λ _ → Λ l ⇒_)
                 (H.≡-to-≅ (cong (λ σ → Tsub σ T) (sym (ren↑-dist-∘ₛᵣ _ σ* ρ*))))
                 (fusion-Eren-Esub-lift-l e σ ρ) ⟩
      Λ l ⇒ Esub (Tliftₛ (σ* ∘ₛᵣ ρ*) l) (Eliftₛ-l (σ* ∘ₛᵣ ρ*) (σ >>SR ρ)) e
    R.≅⟨ refl ⟩
      Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) (Λ l ⇒ e)
    R.∎
  fusion-Eren-Esub' {Δ₁} {Δ₂} {Δ₃} {l} {σ*} {ρ*} {Γ₁} {Γ₂} {Γ₃} {_} (_∙_ {T = T} e T′) σ ρ =
    let
      F₂ = Expr Δ₂ Γ₂ ; E₂ = sym (swap-Tsub-[] σ* T T′)                                ; sub₂ = subst F₂ E₂
      F₃ = Expr Δ₃ Γ₃ ; E₃ = sym (swap-Tsub-[] (σ* ∘ₛᵣ ρ*) T T′)                       ; sub₃ = subst F₃ E₃
      F₅ = Expr Δ₃ Γ₃ ; E₅ = sym (swap-Tren-[] ρ* (Tsub (Tliftₛ σ* _) T) (Tsub σ* T′)) ; sub₅ = subst F₅ E₅
    in
    R.begin
      Eren ρ* ρ (Esub σ* σ (e ∙ T′))
    R.≅⟨ refl ⟩
      Eren ρ* ρ (sub₂ (Esub σ* σ e ∙ Tsub σ* T′))
    R.≅⟨ H.cong₂ {B = Expr Δ₂ Γ₂} (λ _ ■ → Eren ρ* ρ ■) (H.≡-to-≅ (sym E₂)) (H.≡-subst-removable F₂ E₂ _) ⟩
      Eren ρ* ρ (Esub σ* σ e ∙ Tsub σ* T′)
    R.≅⟨ refl ⟩
      sub₅ (Eren ρ* ρ (Esub σ* σ e) ∙ Tren ρ* (Tsub σ* T′))
    R.≅⟨ H.≡-subst-removable F₅ E₅ _ ⟩
      Eren ρ* ρ (Esub σ* σ e) ∙ Tren ρ* (Tsub σ* T′)
    R.≅⟨ Hcong₃ {B = λ ■ → Expr Δ₃ Γ₃ (`∀α _ , ■)} {C = λ _ _ → Type Δ₃ _ } (λ _ ■₁ ■₂ → ■₁ ∙ ■₂)
         (H.≡-to-≅ (fusion-Tren-Tsub-lift T σ* ρ*)) (fusion-Eren-Esub' e σ ρ) (H.≡-to-≅ (fusion-Tren-Tsub T′ σ* ρ*)) ⟩
      Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) e ∙ Tsub (σ* ∘ₛᵣ ρ*) T′
    R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
      sub₃ (Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) e ∙ (Tsub (σ* ∘ₛᵣ ρ*) T′))
    R.≅⟨ refl ⟩
      Esub (σ* ∘ₛᵣ ρ*) (σ >>SR ρ) (e ∙ T′)
    R.∎ 
