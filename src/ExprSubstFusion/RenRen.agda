{-# OPTIONS --allow-unsolved-metas #-}

module ExprSubstFusion.RenRen where

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

-- ∘ᵣᵣ Fusion

Eren↑-dist-∘ᵣᵣ :
  ∀ {ρ* : TRen Δ₁ Δ₂}{σ* : TRen Δ₂ Δ₃} {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃} 
    (T : Type Δ₁ l)
    (ρ : ERen ρ* Γ₁ Γ₂) → (σ : ERen σ* Γ₂ Γ₃) →
  Eliftᵣ {T = T} ρ* ρ >>RR Eliftᵣ σ* σ ≅ Eliftᵣ {T = T} (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ)
Eren↑-dist-∘ᵣᵣ {Δ₃ = Δ₃} {l = l'} {ρ* = ρ*} {σ* = σ*} {Γ₁ = Γ₁} {Γ₃ = Γ₃} T ρ σ =
  fun-ext-h-ERen refl (cong (_◁ Γ₃) (assoc-ren-ren T ρ* σ*)) λ l T′ → λ where
  here →
    let
      F₁ = (λ ■ → inn ■ (Tren σ* (Tren ρ* T) ◁ Γ₃)) ; E₁ = (assoc-ren-ren T ρ* σ*) ; sub₁ = subst F₁ E₁
    in
    R.begin
      sub₁ here
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩ 
      here
    R.≅⟨ H.cong {B = λ ■ → inn ■ (■ ◁ Γ₃)} (λ ■ → here) (H.≡-to-≅ (assoc-ren-ren T ρ* σ*)) ⟩ 
      here
    R.∎
  (there x) →
    let
      F₁ = (λ ■ → inn ■ (Tren σ* (Tren ρ* T) ◁ Γ₃)) ; E₁ = (assoc-ren-ren T′ ρ* σ*) ; sub₁ = subst F₁ E₁
      F₈ = (λ ■ → inn ■ Γ₃)                         ; E₈ = E₁                       ; sub₈ = subst F₈ E₈
    in
    R.begin
      (Eliftᵣ {T = T} ρ* ρ >>RR Eliftᵣ σ* σ) l T′ (there x)
    R.≅⟨ refl ⟩
      sub₁ (there (σ l (Tren ρ* T′) (ρ l T′ x)))
    R.≅⟨ H.≡-subst-removable F₁ E₁ _ ⟩
      there (σ l (Tren ρ* T′) (ρ l T′ x))
    R.≅⟨ Hcong₃ {C = λ ■ _ → inn ■ Γ₃} (λ ■₁ ■₂ ■₃ → there {T = ■₁} {T′ = ■₂} ■₃ )
                (H.≡-to-≅ E₈)
                (H.≡-to-≅ (assoc-ren-ren T ρ* σ*))
                (H.sym (H.≡-subst-removable F₈ E₈ _))
                ⟩
      there (sub₈ (σ l (Tren ρ* T′) (ρ l T′ x)))
    R.≅⟨ refl ⟩
      Eliftᵣ {T = T} (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) l T′ (there x)
    R.∎

Eren↑-dist-∘ᵣᵣ-l :
  ∀ {ρ* : TRen Δ₁ Δ₂} {σ* : TRen Δ₂ Δ₃}
    {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃}
    {l : Level} (ρ : ERen ρ* Γ₁ Γ₂) (σ : ERen σ* Γ₂ Γ₃) →
  Eliftᵣ-l {l = l} ρ* ρ >>RR Eliftᵣ-l σ* σ ≅ Eliftᵣ-l (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ)
Eren↑-dist-∘ᵣᵣ-l {Δ₁} {Δ₂} {Δ₃} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {l} ρ σ =
  fun-ext-h-ERen (sym (ren↑-dist-∘ᵣᵣ l ρ* σ*)) refl λ l′ T → λ where
    (tskip {T = T′} x) →
      let
        F₂ = (λ ■ → inn ■ (l ◁* Γ₃)) ; E₂ = (assoc-ren-ren T (Tliftᵣ ρ* l) (Tliftᵣ σ* l)) ; sub₂ = subst F₂ E₂
        F₃ = id ; E₃ = (cong (λ T → inn T (l ◁* Γ₂)) (sym (swap-Tren-Twk ρ* _))) ; sub₃ = subst F₃ E₃
        F₄ = id ; E₄ = (cong (λ T → inn T (l ◁* Γ₃)) (sym (swap-Tren-Twk σ* _))) ; sub₄ = subst F₄ E₄
        F₅ = id ; E₅ = (cong (λ T → inn T (l ◁* Γ₃)) (sym (swap-Tren-Twk (ρ* ∘ᵣᵣ σ*) _))); sub₅ = subst F₅ E₅
        F₆ = (λ T → inn T Γ₃) ; E₆ = (assoc-ren-ren T′ ρ* σ*) ; sub₆ = subst F₆ E₆
      in
      R.begin
        (Eliftᵣ-l ρ* ρ >>RR Eliftᵣ-l σ* σ) l′ T (tskip x)
      R.≅⟨ refl ⟩
        sub₂ (Eliftᵣ-l σ* σ _ _ (Eliftᵣ-l ρ* ρ _ _ (tskip x)))
      R.≅⟨ H.≡-subst-removable F₂ E₂ _ ⟩
        Eliftᵣ-l σ* σ _ _ (Eliftᵣ-l ρ* ρ _ _ (tskip x))
      R.≅⟨ refl ⟩
        Eliftᵣ-l σ* σ _ _ (sub₃ (tskip (ρ _ _ x)))
      R.≅⟨ H.cong₂ {B = λ ■ → inn ■ (l ◁* Γ₂)} (λ _ → Eliftᵣ-l σ* σ _ _) (H.≡-to-≅ (swap-Tren-Twk ρ* T′)) (H.≡-subst-removable F₃ E₃ _) ⟩
        Eliftᵣ-l σ* σ _ _ (tskip (ρ _ _ x))
      R.≅⟨ refl ⟩
        sub₄ (tskip (σ _ _ (ρ _ _ x)))
      R.≅⟨ H.≡-subst-removable F₄ E₄ _ ⟩
        tskip (σ _ _ (ρ _ _ x))
      R.≅⟨ H.cong₂ {B = λ ■ → inn ■ Γ₃} (λ _ → tskip) (H.≡-to-≅ (assoc-ren-ren T′ ρ* σ*)) (H.sym (H.≡-subst-removable F₆ E₆ _)) ⟩
        tskip (sub₆ (σ _ _ (ρ _ _ x)))
      R.≅⟨ refl ⟩
        tskip ((ρ >>RR σ) l′ T′ x)
      R.≅⟨ H.sym (H.≡-subst-removable F₅ E₅ _) ⟩
        sub₅ (tskip ((ρ >>RR σ) l′ T′ x))
      R.≅⟨ refl ⟩
        Eliftᵣ-l (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) l′ T (tskip x)
      R.∎

mutual
  Eassoc-ren↑-ren↑-l :
    ∀ {ρ* : TRen Δ₁ Δ₂} {σ* : TRen Δ₂ Δ₃}
      {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃}
      {l′ : Level}
      {T : Type (l′ ∷ Δ₁) l}
      (e : Expr (l′ ∷ Δ₁) (l′ ◁* Γ₁) T)
      (ρ : ERen ρ* Γ₁ Γ₂) (σ : ERen σ* Γ₂ Γ₃) →
    Eren (Tliftᵣ ρ* l′ ∘ᵣᵣ Tliftᵣ σ* l′) (Eliftᵣ-l ρ* ρ >>RR Eliftᵣ-l σ* σ) e ≅
    Eren (Tliftᵣ (ρ* ∘ᵣᵣ σ*) l′) (Eliftᵣ-l (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ)) e
  Eassoc-ren↑-ren↑-l {Δ₁} {Δ₂} {Δ₃} {l} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {l′} {T} e ρ σ =
    R.begin
      Eren (Tliftᵣ ρ* l′ ∘ᵣᵣ Tliftᵣ σ* l′) (Eliftᵣ-l ρ* ρ >>RR Eliftᵣ-l σ* σ) e
    R.≅⟨ H.cong₂ (λ ■₁ ■₂ → Eren {Γ₂ = l′ ◁* Γ₃} ■₁ ■₂ e) (H.≡-to-≅ (sym (ren↑-dist-∘ᵣᵣ l′ ρ* σ*))) (Eren↑-dist-∘ᵣᵣ-l ρ σ) ⟩
      Eren (Tliftᵣ (ρ* ∘ᵣᵣ σ*) l′) (Eliftᵣ-l (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ)) e
    R.∎

  Eassoc-ren↑-ren↑ :
    ∀ {ρ* : TRen Δ₁ Δ₂} {σ* : TRen Δ₂ Δ₃}
      {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
      {T : Type Δ₁ l}
      {T′ : Type Δ₁ l′}
      (e : Expr Δ₁ (T′ ◁  Γ₁) T)
      (ρ : ERen ρ* Γ₁ Γ₂) (σ : ERen σ* Γ₂ Γ₃) →
    Eren σ* (Eliftᵣ {T = Tren ρ* T′} σ* σ) (Eren ρ* (Eliftᵣ ρ* ρ) e) ≅
    Eren (ρ* ∘ᵣᵣ σ*) (Eliftᵣ {T = T′} (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ)) e
  Eassoc-ren↑-ren↑ {Δ₃ = Δ₃} {ρ* = ρ*} {σ* = σ*} {Γ₁ = Γ₁} {Γ₃ = Γ₃} {T = T} {T′ = T′} e ρ σ =
    R.begin
      Eren σ* (Eliftᵣ σ* σ) (Eren ρ* (Eliftᵣ ρ* ρ) e)
    R.≅⟨ Eassoc-ren-ren' e (Eliftᵣ ρ* ρ) (Eliftᵣ σ* σ) ⟩
      Eren (ρ* ∘ᵣᵣ σ*) ((Eliftᵣ ρ* ρ) >>RR (Eliftᵣ σ* σ)) e
    R.≅⟨ H.cong₂ {B = λ ■ → ERen (ρ* ∘ᵣᵣ σ*) (_ ◁ Γ₁) (■ ◁ Γ₃)}
                 (λ _ ■ → Eren (ρ* ∘ᵣᵣ σ*) ■ e)
                 (H.≡-to-≅ (assoc-ren-ren T′ ρ* σ*)) (Eren↑-dist-∘ᵣᵣ _ ρ σ) ⟩
      Eren (ρ* ∘ᵣᵣ σ*) (Eliftᵣ (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ)) e
    R.∎

  Eassoc-ren-ren' : 
      {ρ* : TRen Δ₁ Δ₂} {σ* : TRen Δ₂ Δ₃}
    → {Γ₁ : TEnv Δ₁}{Γ₂ : TEnv Δ₂}{Γ₃ : TEnv Δ₃}
    → {T : Type Δ₁ l}
    → (e : Expr Δ₁ Γ₁ T)
    → (ρ : ERen ρ* Γ₁ Γ₂) (σ : ERen σ* Γ₂ Γ₃)
    → Eren σ* σ (Eren ρ* ρ e) ≅ Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) e
  Eassoc-ren-ren' {Δ₁} {Δ₂} {Δ₃} {.zero} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {.`ℕ} (# n) ρ σ =
    refl
  Eassoc-ren-ren' {Δ₁} {Δ₂} {Δ₃} {.zero} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {.`ℕ} (`suc e) ρ σ =
    R.begin
      Eren σ* σ (Eren ρ* ρ (`suc e))
    R.≅⟨ refl ⟩
      `suc (Eren σ* σ (Eren ρ* ρ e))
    R.≅⟨ H.cong `suc (Eassoc-ren-ren' e ρ σ) ⟩
      `suc (Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) e)
    R.≅⟨ refl ⟩
      Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) (`suc e)
    R.∎
  Eassoc-ren-ren' {Δ₁} {Δ₂} {Δ₃} {l} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {T} (` x) ρ σ =
    let F₁ = (λ ■ → inn ■ Γ₃) ; E₁ = (assoc-ren-ren T ρ* σ*) ; sub₁ = subst F₁ E₁ in
    R.begin
      Eren σ* σ (Eren ρ* ρ (` x))
    R.≅⟨ refl ⟩
      ` σ l (Tren ρ* T) (ρ l T x)
    R.≅⟨ H.cong₂ {B = λ ■ → inn ■ Γ₃} {C = λ ■ _ → Expr Δ₃ Γ₃ ■} (λ ■ → `_ {Γ = Γ₃} {T = ■})
                 (H.≡-to-≅ (assoc-ren-ren T ρ* σ*)) (H.sym (H.≡-subst-removable F₁ E₁ _)) ⟩
      ` sub₁ (σ l (Tren ρ* T) (ρ l T x))
    R.≅⟨ refl ⟩
      Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) (` x)
    R.∎
  Eassoc-ren-ren' {Δ₁} {Δ₂} {Δ₃} {_} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {T₁ ⇒ T₂} (ƛ e) ρ σ =
    R.begin
      ƛ Eren σ* (Eliftᵣ σ* σ) (Eren ρ* (Eliftᵣ ρ* ρ) e)
    R.≅⟨ Hcong₃ {C = λ ■₁ ■₂ → Expr Δ₃ (■₁ ◁ Γ₃) ■₂} (λ _ _ ■ → ƛ ■)
                (H.≡-to-≅ (assoc-ren-ren T₁ ρ* σ*))
                (H.≡-to-≅ (assoc-ren-ren T₂ ρ* σ*))
                (Eassoc-ren↑-ren↑ e ρ σ)  ⟩
      ƛ (Eren (ρ* ∘ᵣᵣ σ*) (Eliftᵣ (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ)) e)
    R.≅⟨ refl ⟩
      Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) (ƛ e)
    R.∎
  Eassoc-ren-ren' {Δ₁} {Δ₂} {Δ₃} {l} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {T} (_·_ {T = T₁} {T′ = T₂} e₁ e₂) ρ σ =
    R.begin
      Eren σ* σ (Eren ρ* ρ (e₁ · e₂))
    R.≅⟨ refl ⟩
      Eren σ* σ (Eren ρ* ρ e₁) · Eren σ* σ (Eren ρ* ρ e₂)
    R.≅⟨ Hcong₄ {C = λ ■₁ ■₂ → Expr Δ₃ Γ₃ (■₂ ⇒ ■₁)} {D = λ _ ■₂ _ → Expr Δ₃ Γ₃ ■₂} (λ _ _ → _·_)
                (H.≡-to-≅ (assoc-ren-ren T ρ* σ*)) (H.≡-to-≅ (assoc-ren-ren T₁ ρ* σ*))
                (Eassoc-ren-ren' e₁ ρ σ) (Eassoc-ren-ren' e₂ ρ σ) ⟩
      Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) e₁ · Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) e₂
    R.≅⟨ refl ⟩
      Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) (e₁ · e₂)
    R.∎
  Eassoc-ren-ren' {Δ₁} {Δ₂} {Δ₃} {_} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {`∀α l , T} (Λ l ⇒ e) ρ σ =
    R.begin
      Eren σ* σ (Eren ρ* ρ (Λ l ⇒ e))
    R.≅⟨ refl ⟩
      Λ l ⇒ Eren (Tliftᵣ σ* l) (Eliftᵣ-l σ* σ) (Eren (Tliftᵣ ρ* l) (Eliftᵣ-l ρ* ρ) e)
    R.≅⟨ H.cong₂ {B = Expr (l ∷ Δ₃) (l ◁* Γ₃)} (λ _ → Λ l ⇒_)
                 (H.≡-to-≅ (assoc-ren-ren T (Tliftᵣ ρ* _) (Tliftᵣ σ* _)))
                 (Eassoc-ren-ren' e (Eliftᵣ-l ρ* ρ) (Eliftᵣ-l σ* σ)) ⟩
      Λ l ⇒ Eren (Tliftᵣ ρ* l ∘ᵣᵣ Tliftᵣ σ* l) (Eliftᵣ-l ρ* ρ >>RR Eliftᵣ-l σ* σ) e
    R.≅⟨ H.cong₂ {B = Expr (l ∷ Δ₃) (l ◁* Γ₃)} (λ _ → Λ l ⇒_)
                 (H.≡-to-≅ (cong (λ σ → Tren σ T) (sym (ren↑-dist-∘ᵣᵣ _ ρ* σ*))))
                 (Eassoc-ren↑-ren↑-l e ρ σ) ⟩
      Λ l ⇒ Eren (Tliftᵣ (ρ* ∘ᵣᵣ σ*) l) (Eliftᵣ-l (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ)) e
    R.≅⟨ refl ⟩
      Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) (Λ l ⇒ e)
    R.∎
  Eassoc-ren-ren' {Δ₁} {Δ₂} {Δ₃} {l} {ρ*} {σ*} {Γ₁} {Γ₂} {Γ₃} {_} (_∙_ {T = T} e T′) ρ σ =
    let
      F₂ = Expr Δ₂ Γ₂ ; E₂ = sym (swap-Tren-[] ρ* T T′)                                ; sub₂ = subst F₂ E₂
      F₃ = Expr Δ₃ Γ₃ ; E₃ = sym (swap-Tren-[] (ρ* ∘ᵣᵣ σ*) T T′)                       ; sub₃ = subst F₃ E₃
      F₅ = Expr Δ₃ Γ₃ ; E₅ = sym (swap-Tren-[] σ* (Tren (Tliftᵣ ρ* _) T) (Tren ρ* T′)) ; sub₅ = subst F₅ E₅
    in
    R.begin
      Eren σ* σ (Eren ρ* ρ (e ∙ T′))
    R.≅⟨ refl ⟩
      Eren σ* σ (sub₂ (Eren ρ* ρ e ∙ Tren ρ* T′))
    R.≅⟨ H.cong₂ {B = Expr Δ₂ Γ₂} (λ _ ■ → Eren σ* σ ■) (H.≡-to-≅ (sym E₂)) (H.≡-subst-removable F₂ E₂ _) ⟩
      Eren σ* σ (Eren ρ* ρ e ∙ Tren ρ* T′)
    R.≅⟨ refl ⟩
      sub₅ (Eren σ* σ (Eren ρ* ρ e) ∙ Tren σ* (Tren ρ* T′))
    R.≅⟨ H.≡-subst-removable F₅ E₅ _ ⟩
      Eren σ* σ (Eren ρ* ρ e) ∙ Tren σ* (Tren ρ* T′)
    R.≅⟨ Hcong₃ {B = λ ■ → Expr Δ₃ Γ₃ (`∀α _ , ■)} {C = λ _ _ → Type Δ₃ _ } (λ _ ■₁ ■₂ → ■₁ ∙ ■₂)
         (H.≡-to-≅ (assoc-ren↑-ren↑ T ρ* σ*)) (Eassoc-ren-ren' e ρ σ) (H.≡-to-≅ (assoc-ren-ren T′ ρ* σ*)) ⟩
      Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) e ∙ Tren (ρ* ∘ᵣᵣ σ*) T′
    R.≅⟨ H.sym (H.≡-subst-removable F₃ E₃ _) ⟩
      sub₃ (Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) e ∙ (Tren (ρ* ∘ᵣᵣ σ*) T′))
    R.≅⟨ refl ⟩
      Eren (ρ* ∘ᵣᵣ σ*) (ρ >>RR σ) (e ∙ T′)
    R.∎ 
