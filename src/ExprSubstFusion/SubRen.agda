module ExprSubstFusion.SubRen where

open import Level
open import Data.List using (List; []; _∷_; [_])
open import Function using (_∘_; id; _$_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)

open import Extensionality
open import Types
open import TypeSubstitution
open import TypeSubstProperties
open import Expressions
open import ExprSubstitution
open import HeterogeneousEqualityLemmas

-- ∘ᵣₛ Fusion

Esub↑-dist-∘ᵣₛ :
  ∀ {ρ* : TRen Δ₁ Δ₂}{σ* : TSub Δ₂ Δ₃} {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃} 
    (T : Type Δ₁ l)
    (ρ : ERen ρ* Γ₁ Γ₂) → (σ : ESub σ* Γ₂ Γ₃) →
  Eliftᵣ {T = T} ρ* ρ >>RS Eliftₛ σ* σ ≅ Eliftₛ {T = T} (ρ* ∘ᵣₛ σ*) (ρ >>RS σ)
Esub↑-dist-∘ᵣₛ {Δ₃ = Δ₃} {l = l'} {ρ* = ρ*} {σ* = σ*} {Γ₁ = Γ₁} {Γ₃ = Γ₃} T ρ σ =
  fun-ext-h-ESub refl (cong (_◁ Γ₃) (fusion-Tsub-Tren T ρ* σ*)) λ l T′ → λ where
  here →
    let
      F₁ = (Expr _ (Tsub σ* (Tren ρ* T) ◁ Γ₃))          ; E₁ = (fusion-Tsub-Tren T ρ* σ*)            ; sub₁ = subst F₁ E₁
      F₃ = (Expr _ Γ₃)                                  ; E₃ = λ l₂ T₂ → (fusion-Tsub-Tren T₂ ρ* σ*) ; sub₃ = λ l₂ T₂ → subst F₃ (E₃ l₂ T₂)
    in
    R.begin
      sub₁ (` here)
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩ 
      ` here
    R.≅⟨ H.cong {B = λ ■ → Expr _ (■ ◁ Γ₃) ■} (λ ■ → `_ {Γ = ■ ◁ Γ₃} {T = ■} here) (H.≡-to-≅ (fusion-Tsub-Tren T ρ* σ*)) ⟩ 
      ` here
    R.≅⟨ refl ⟩
      Eliftₛ (ρ* ∘ᵣₛ σ*) (λ l₂ T₂ x → sub₃ l₂ T₂ (σ l₂ (Tren ρ* T₂) (ρ l₂ T₂ x))) _ T here
    R.∎
  (there x) →
    let
      F₁ = (Expr _ (Tsub σ* (Tren ρ* T) ◁ Γ₃))              ; E₁ = (fusion-Tsub-Tren T′ ρ* σ*)                      ; sub₁ = subst F₁ E₁
      F₂ = (Expr _ (Tsub σ* (Tren ρ* T) ◁ Γ₃))              ; E₂ = (TidᵣT≡T (Tsub σ* (Tren ρ* T′)))              ; sub₂ = subst F₂ E₂
      F₇ = (Expr _ (Tsub (λ z x₁ → σ* z (ρ* z x₁)) T ◁ Γ₃)) ; E₇ = (TidᵣT≡T (Tsub (λ z x₁ → σ* z (ρ* z x₁)) T′)) ; sub₇ = subst F₇ E₇
      F₈ = (Expr _ Γ₃)                                      ; E₈ = E₁                                            ; sub₈ = subst F₈ E₈
    in
    R.begin
      (Eliftᵣ {T = T} ρ* ρ >>RS Eliftₛ σ* σ) l T′ (there x)
    R.≅⟨ refl ⟩
      sub₁ (sub₂ (Eren Tidᵣ
        (λ l₁ T₂ x₁ → there (subst (λ T₃ → inn T₃ Γ₃) (sym (TidᵣT≡T T₂)) x₁))
        (σ l (Tren ρ* T′) (ρ l T′ x))))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      sub₂ (Eren Tidᵣ
        (λ l₁ T₂ x₁ → there (subst (λ T₃ → inn T₃ Γ₃) (sym (TidᵣT≡T T₂)) x₁))
        (σ l (Tren ρ* T′) (ρ l T′ x)))
    R.≅⟨ H.≡-subst-removable F₂ E₂ _ ⟩
      Eren {Γ₂ = Tsub σ* (Tren ρ* T) ◁ Γ₃} Tidᵣ
        (λ l₁ T₂ x₁ → there {T = Tren Tidᵣ T₂} (subst (λ T₃ → inn T₃ Γ₃) (sym (TidᵣT≡T T₂)) x₁))
        (σ l (Tren ρ* T′) (ρ l T′ x))
    R.≅⟨ H.cong (λ ■ → Eren {Γ₂ = ■ ◁ Γ₃} Tidᵣ
        (λ l₁ T₂ x₁ → there {T = Tren Tidᵣ T₂} (subst (λ T₃ → inn T₃ Γ₃) (sym (TidᵣT≡T T₂)) x₁))
        (σ l (Tren ρ* T′) (ρ l T′ x))) (H.≡-to-≅ (fusion-Tsub-Tren T ρ* σ*)) ⟩
      Eren {Γ₂ = Tsub (ρ* ∘ᵣₛ σ*) T ◁ Γ₃} Tidᵣ
        (λ l₁ T₂ x₁ → there {T = Tren Tidᵣ T₂} (subst (λ T₃ → inn T₃ Γ₃) (sym (TidᵣT≡T T₂)) x₁))
        (σ l (Tren ρ* T′) (ρ l T′ x))
    R.≅⟨ H.cong₂ {B = λ ■ → Expr Δ₃ Γ₃ ■}
                  (λ _ ■ → Eren Tidᵣ (λ l₁ T₂ x₁ → there {T = Tren Tidᵣ T₂} (subst (λ T₃ → inn T₃ Γ₃) (sym (TidᵣT≡T T₂)) x₁)) ■)
                  (H.≡-to-≅ E₈)
                  (H.sym (H.≡-subst-removable F₈ E₈ _)) ⟩
      Eren {Γ₂ = Tsub (ρ* ∘ᵣₛ σ*) T ◁ Γ₃} Tidᵣ
        (λ l₁ T₂ x₁ → there {T = Tren Tidᵣ T₂} (subst (λ T₃ → inn T₃ Γ₃) (sym (TidᵣT≡T T₂)) x₁))
        (sub₈ (σ l (Tren ρ* T′) (ρ l T′ x)))
    R.≅⟨ H.sym (H.≡-subst-removable F₇ E₇ _) ⟩
      sub₇ (Eren Tidᵣ
        (λ l₁ T₂ x₁ → there (subst (λ T₃ → inn T₃ Γ₃) (sym (TidᵣT≡T T₂)) x₁))
        (sub₈ (σ l (Tren ρ* T′) (ρ l T′ x))))
    R.≅⟨ refl ⟩
      Ewk ((ρ >>RS σ) _ _ x)
    R.≅⟨ refl ⟩
      Eliftₛ {T = T} (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) l T′ (there x)
    R.∎

Esub↑-dist-∘ᵣₛ-l :
  ∀ {ρ* : TRen Δ₁ Δ₂} {σ* : TSub Δ₂ Δ₃}
    {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃}
    {l : Level} (ρ : ERen ρ* Γ₁ Γ₂) (σ : ESub σ* Γ₂ Γ₃) →
  Eliftᵣ-l {l = l} ρ* ρ >>RS Eliftₛ-l σ* σ ≅ Eliftₛ-l (ρ* ∘ᵣₛ σ*) (ρ >>RS σ)
Esub↑-dist-∘ᵣₛ-l {Δ₁} {Δ₂} {Δ₃} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {l} ρ σ =
  fun-ext-h-ESub (sym (sub↑-dist-∘ᵣₛ l ρ* σ*)) refl λ l′ T → λ where
    (tskip {T = T′} x) →
      let
        F₂ = (Expr (l ∷ Δ₃) (l ◁* Γ₃)) ; E₂ = (fusion-Tsub-Tren T (Tliftᵣ ρ* l) (Tliftₛ σ* l))
                                       ; sub₂ = subst F₂ E₂
        F₃ = (λ x → x) ; E₃ = (cong (λ T → inn T (l ◁* Γ₂)) (sym (swap-Tren-Twk ρ* _)))
                       ; sub₃ = subst F₃ E₃
        F₅ = (Expr (l ∷ Δ₃) (l ◁* Γ₃)) ; E₅ = sym (swap-Tsub-Twk (ρ* ∘ᵣₛ σ*) T′) ; sub₅ = subst F₅ E₅
        F₇ = (Expr _ _) ; E₇ = (sym (swap-Tsub-Twk σ* (Tren ρ* T′))) ; sub₇ = subst F₇ E₇
        F₈ = (Expr Δ₃ Γ₃) ; E₈ = (fusion-Tsub-Tren T′ ρ* σ*) ; sub₈ = subst F₈ E₈
      in
      R.begin
        (Eliftᵣ-l ρ* ρ >>RS Eliftₛ-l σ* σ) l′ T (tskip x)
      R.≅⟨ refl ⟩
        sub₂ (Eliftₛ-l σ* σ _ _ (Eliftᵣ-l ρ* ρ _ _ (tskip x)))
      R.≅⟨ refl ⟩
        sub₂ (Eliftₛ-l σ* σ _ _ (sub₃ (tskip {T = Tren ρ* T′} (ρ _ _ x))))
      R.≅⟨ H.≡-subst-removable F₂ E₂ _ ⟩
        Eliftₛ-l σ* σ l′ (Tren (Tliftᵣ ρ* l) (Twk T′)) (sub₃ (tskip {T = Tren ρ* T′} (ρ _ _ x)))
      R.≅⟨ H.cong₂ (Eliftₛ-l σ* σ l′) (H.≡-to-≅ (swap-Tren-Twk ρ* _)) (H.≡-subst-removable F₃ E₃ _) ⟩
        Eliftₛ-l σ* σ l′ (Twk (Tren ρ* T′)) (tskip {T = Tren ρ* T′} (ρ _ _ x))
      R.≅⟨ refl ⟩
        sub₇ (Ewk-l (σ _ _ (ρ _ _ x)))
      R.≅⟨ H.≡-subst-removable F₇ E₇ _ ⟩
        Ewk-l {T = Tsub σ* (Tren ρ* T′)} (σ _ _ (ρ _ _ x))
      R.≅⟨ H.cong₂ {B = Expr Δ₃ Γ₃} (λ ■₁ ■₂ → Ewk-l ■₂) (H.≡-to-≅ E₈) (H.sym (H.≡-subst-removable F₈ E₈ _)) ⟩
        Ewk-l {T = Tsub (ρ* ∘ᵣₛ σ*) T′} (sub₈ (σ _ _ (ρ _ _ x)))
      R.≅⟨ refl ⟩
        Ewk-l ((ρ >>RS σ) l′ T′ x)
      R.≅⟨ H.sym (H.≡-subst-removable F₅ E₅ _) ⟩
        sub₅ (Ewk-l ((ρ >>RS σ) l′ T′ x))
      R.≅⟨ refl ⟩
        Eliftₛ-l (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) l′ T (tskip x)
      R.∎

mutual
  Eassoc-sub↑-ren↑-l :
    ∀ {ρ* : TRen Δ₁ Δ₂} {σ* : TSub Δ₂ Δ₃}
      {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃}
      {l′ : Level}
      {T : Type (l′ ∷ Δ₁) l}
      (e : Expr (l′ ∷ Δ₁) (l′ ◁* Γ₁) T)
      (ρ : ERen ρ* Γ₁ Γ₂) (σ : ESub σ* Γ₂ Γ₃) →
    Esub (Tliftᵣ ρ* l′ ∘ᵣₛ Tliftₛ σ* l′) (Eliftᵣ-l ρ* ρ >>RS Eliftₛ-l σ* σ) e ≅
    Esub (Tliftₛ (ρ* ∘ᵣₛ σ*) l′) (Eliftₛ-l (ρ* ∘ᵣₛ σ*) (ρ >>RS σ)) e
  Eassoc-sub↑-ren↑-l {Δ₁} {Δ₂} {Δ₃} {l} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {l′} {T} e ρ σ =
    R.begin
      Esub (Tliftᵣ ρ* l′ ∘ᵣₛ Tliftₛ σ* l′) (Eliftᵣ-l ρ* ρ >>RS Eliftₛ-l σ* σ) e
    R.≅⟨ H.cong₂ (λ ■₁ ■₂ → Esub {Γ₂ = l′ ◁* Γ₃} ■₁ ■₂ e) (H.≡-to-≅ (sym (sub↑-dist-∘ᵣₛ l′ ρ* σ*))) (Esub↑-dist-∘ᵣₛ-l ρ σ) ⟩
      Esub (Tliftₛ (ρ* ∘ᵣₛ σ*) l′) (Eliftₛ-l (ρ* ∘ᵣₛ σ*) (ρ >>RS σ)) e
    R.∎

  Eassoc-sub↑-ren↑ :
    ∀ {ρ* : TRen Δ₁ Δ₂} {σ* : TSub Δ₂ Δ₃}
      {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
      {T : Type Δ₁ l}
      {T′ : Type Δ₁ l′}
      (e : Expr Δ₁ (T′ ◁  Γ₁) T)
      (ρ : ERen ρ* Γ₁ Γ₂) (σ : ESub σ* Γ₂ Γ₃) →
    Esub σ* (Eliftₛ {T = Tren ρ* T′} σ* σ) (Eren ρ* (Eliftᵣ ρ* ρ) e) ≅
    Esub (ρ* ∘ᵣₛ σ*) (Eliftₛ {T = T′} (ρ* ∘ᵣₛ σ*) (ρ >>RS σ)) e
  Eassoc-sub↑-ren↑ {Δ₃ = Δ₃} {ρ* = ρ*} {σ* = σ*} {Γ₁ = Γ₁} {Γ₃ = Γ₃} {T = T} {T′ = T′} e ρ σ =
    R.begin
      Esub σ* (Eliftₛ σ* σ) (Eren ρ* (Eliftᵣ ρ* ρ) e)
    R.≅⟨ fusion-Esub-Eren' e (Eliftᵣ ρ* ρ) (Eliftₛ σ* σ) ⟩
      Esub (ρ* ∘ᵣₛ σ*) ((Eliftᵣ ρ* ρ) >>RS (Eliftₛ σ* σ)) e
    R.≅⟨ H.cong₂ {B = λ ■ → ESub (ρ* ∘ᵣₛ σ*) (_ ◁ Γ₁) (■ ◁ Γ₃)}
                 (λ _ ■ → Esub (ρ* ∘ᵣₛ σ*) ■ e)
                 (H.≡-to-≅ (fusion-Tsub-Tren T′ ρ* σ*)) (Esub↑-dist-∘ᵣₛ _ ρ σ) ⟩
      Esub (ρ* ∘ᵣₛ σ*) (Eliftₛ (ρ* ∘ᵣₛ σ*) (ρ >>RS σ)) e
    R.∎

  fusion-Esub-Eren' : 
      {ρ* : TRen Δ₁ Δ₂} {σ* : TSub Δ₂ Δ₃}
    → {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
    → {T : Type Δ₁ l}
    → (e : Expr Δ₁ Γ₁ T)
    → (ρ : ERen ρ* Γ₁ Γ₂) (σ : ESub σ* Γ₂ Γ₃)
    → Esub σ* σ (Eren ρ* ρ e) ≅ Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) e
  fusion-Esub-Eren' {Δ₁} {Δ₂} {Δ₃} {.zero} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {.`ℕ} (# n) ρ σ =
    refl
  fusion-Esub-Eren' {Δ₁} {Δ₂} {Δ₃} {.zero} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {.`ℕ} (`suc e) ρ σ =
    R.begin
      Esub σ* σ (Eren ρ* ρ (`suc e))
    R.≅⟨ refl ⟩
      `suc (Esub σ* σ (Eren ρ* ρ e))
    R.≅⟨ H.cong `suc (fusion-Esub-Eren' e ρ σ) ⟩
      `suc (Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) e)
    R.≅⟨ refl ⟩
      Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) (`suc e)
    R.∎
  fusion-Esub-Eren' {Δ₁} {Δ₂} {Δ₃} {l} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {T} (` x) ρ σ =
    let F₁ = (Expr Δ₃ Γ₃) ; E₁ = (fusion-Tsub-Tren T ρ* σ*) ; sub₁ = subst F₁ E₁ in
    R.begin
      Esub σ* σ (Eren ρ* ρ (` x))
    R.≅⟨ refl ⟩
      σ l (Tren ρ* T) (ρ l T x)
    R.≅⟨ H.sym (H.≡-subst-removable F₁ E₁ _) ⟩
      sub₁ (σ l (Tren ρ* T) (ρ l T x))
    R.≅⟨ refl ⟩
      Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) (` x)
    R.∎
  fusion-Esub-Eren' {Δ₁} {Δ₂} {Δ₃} {_} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {T₁ ⇒ T₂} (ƛ e) ρ σ =
    R.begin
      ƛ Esub σ* (Eliftₛ σ* σ) (Eren ρ* (Eliftᵣ ρ* ρ) e)
    R.≅⟨ Hcong₃ {C = λ ■₁ ■₂ → Expr Δ₃ (■₁ ◁ Γ₃) ■₂} (λ _ _ ■ → ƛ ■)
                (H.≡-to-≅ (fusion-Tsub-Tren T₁ ρ* σ*))
                (H.≡-to-≅ (fusion-Tsub-Tren T₂ ρ* σ*))
                (Eassoc-sub↑-ren↑ e ρ σ)  ⟩
      ƛ (Esub (ρ* ∘ᵣₛ σ*) (Eliftₛ (ρ* ∘ᵣₛ σ*) (ρ >>RS σ)) e)
    R.≅⟨ refl ⟩
      Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) (ƛ e)
    R.∎
  fusion-Esub-Eren' {Δ₁} {Δ₂} {Δ₃} {l} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {T} (_·_ {T = T₁} {T′ = T₂} e₁ e₂) ρ σ =
    R.begin
      Esub σ* σ (Eren ρ* ρ (e₁ · e₂))
    R.≅⟨ refl ⟩
      Esub σ* σ (Eren ρ* ρ e₁) · Esub σ* σ (Eren ρ* ρ e₂)
    R.≅⟨ Hcong₄ {C = λ ■₁ ■₂ → Expr Δ₃ Γ₃ (■₂ ⇒ ■₁)} {D = λ _ ■₂ _ → Expr Δ₃ Γ₃ ■₂} (λ _ _ → _·_)
                (H.≡-to-≅ (fusion-Tsub-Tren T ρ* σ*)) (H.≡-to-≅ (fusion-Tsub-Tren T₁ ρ* σ*))
                (fusion-Esub-Eren' e₁ ρ σ) (fusion-Esub-Eren' e₂ ρ σ) ⟩
      Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) e₁ · Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) e₂
    R.≅⟨ refl ⟩
      Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) (e₁ · e₂)
    R.∎
  fusion-Esub-Eren' {Δ₁} {Δ₂} {Δ₃} {_} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {`∀α l , T} (Λ l ⇒ e) ρ σ =
    R.begin
      Esub σ* σ (Eren ρ* ρ (Λ l ⇒ e))
    R.≅⟨ refl ⟩
      Λ l ⇒ Esub (Tliftₛ σ* l) (Eliftₛ-l σ* σ) (Eren (Tliftᵣ ρ* l) (Eliftᵣ-l ρ* ρ) e)
    R.≅⟨ H.cong₂ {B = Expr (l ∷ Δ₃) (l ◁* Γ₃)} (λ _ → Λ l ⇒_)
                 (H.≡-to-≅ (fusion-Tsub-Tren T (Tliftᵣ ρ* _) (Tliftₛ σ* _)))
                 (fusion-Esub-Eren' e (Eliftᵣ-l ρ* ρ) (Eliftₛ-l σ* σ)) ⟩
      Λ l ⇒ Esub (Tliftᵣ ρ* l ∘ᵣₛ Tliftₛ σ* l) (Eliftᵣ-l ρ* ρ >>RS Eliftₛ-l σ* σ) e
    R.≅⟨ H.cong₂ {B = Expr (l ∷ Δ₃) (l ◁* Γ₃)} (λ _ → Λ l ⇒_)
                 (H.≡-to-≅ (cong (λ σ → Tsub σ T) (sym (sub↑-dist-∘ᵣₛ _ ρ* σ*))))
                 (Eassoc-sub↑-ren↑-l e ρ σ) ⟩
      Λ l ⇒ Esub (Tliftₛ (ρ* ∘ᵣₛ σ*) l) (Eliftₛ-l (ρ* ∘ᵣₛ σ*) (ρ >>RS σ)) e
    R.≅⟨ refl ⟩
      Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) (Λ l ⇒ e)
    R.∎
  fusion-Esub-Eren' {Δ₁} {Δ₂} {Δ₃} {l} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {_} (_∙_ {T = T} e T′) ρ σ =
    let
      F₂ = Expr Δ₂ Γ₂ ; E₂ = sym (swap-Tren-[] ρ* T T′)                                ; sub₂ = subst F₂ E₂
      F₃ = Expr Δ₃ Γ₃ ; E₃ = sym (swap-Tsub-[] (ρ* ∘ᵣₛ σ*) T T′)                       ; sub₃ = subst F₃ E₃
      F₅ = Expr Δ₃ Γ₃ ; E₅ = sym (swap-Tsub-[] σ* (Tren (Tliftᵣ ρ* _) T) (Tren ρ* T′)) ; sub₅ = subst F₅ E₅
    in
    R.begin
      Esub σ* σ (Eren ρ* ρ (e ∙ T′))
    R.≅⟨ refl ⟩
      Esub σ* σ (sub₂ (Eren ρ* ρ e ∙ Tren ρ* T′))
    R.≅⟨ H.cong₂ {B = Expr Δ₂ Γ₂} (λ _ ■ → Esub σ* σ ■) (H.≡-to-≅ (sym E₂)) (H.≡-subst-removable F₂ E₂ _) ⟩
      Esub σ* σ (Eren ρ* ρ e ∙ Tren ρ* T′)
    R.≅⟨ refl ⟩
      sub₅ (Esub σ* σ (Eren ρ* ρ e) ∙ Tsub σ* (Tren ρ* T′))
    R.≅⟨ H.≡-subst-removable F₅ E₅ _ ⟩
      Esub σ* σ (Eren ρ* ρ e) ∙ Tsub σ* (Tren ρ* T′)
    R.≅⟨ Hcong₃ {B = λ ■ → Expr Δ₃ Γ₃ (`∀α _ , ■)} {C = λ _ _ → Type Δ₃ _ } (λ _ ■₁ ■₂ → ■₁ ∙ ■₂)
         (H.≡-to-≅ (assoc-sub↑-ren↑ T ρ* σ*)) (fusion-Esub-Eren' e ρ σ) (H.≡-to-≅ (fusion-Tsub-Tren T′ ρ* σ*)) ⟩
      Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) e ∙ Tsub (ρ* ∘ᵣₛ σ*) T′
    R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
      sub₃ (Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) e ∙ (Tsub (ρ* ∘ᵣₛ σ*) T′))
    R.≅⟨ refl ⟩
      Esub (ρ* ∘ᵣₛ σ*) (ρ >>RS σ) (e ∙ T′)
    R.∎ 
