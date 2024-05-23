module StratF.Misc.SubstExamples where

-- This file is only used to generate examples for the paper, and is
-- not part of the actual formalization.

-- This is only here because doing it to the real `Expr` type would
-- scramble the order of implicits, which would require a larger annoying refactoring.
module ForThePaper where
  open import StratF.TypeSubstPropertiesSem
  open import StratF.TypeSubstitution
  open import StratF.Types
  open import StratF.Expressions using (Ctx; inn; _◁_; _◁*_)
  open import Data.Nat using (ℕ; suc; zero)
  open import Level
  open import Data.List using (List; []; _∷_)

  --! TFExpr
  data Expr (Δ : LEnv) (Γ : Ctx Δ) : Type Δ l → Set where
    #_    :  (n : ℕ) → Expr Δ Γ `ℕ
    `suc  :  Expr Δ Γ `ℕ → Expr Δ Γ `ℕ
    `_    :  inn T Γ → Expr Δ Γ T
    ƛ_    :  Expr Δ (T ◁ Γ) T′ → Expr Δ Γ (T ⇒ T′)
    _·_   :  Expr Δ Γ (T ⇒ T′) → Expr Δ Γ T → Expr Δ Γ T′
    Λ_⇒_  :  ∀ (l : Level) → {T : Type (l ∷ Δ) l′} → 
             Expr (l ∷ Δ) (l ◁* Γ) T → Expr Δ Γ (`∀α l , T)
    _∙_   :  Expr Δ Γ (`∀α l , T) → (T′ : Type Δ l) → 
             Expr Δ Γ (T [ T′ ]T)

module ForTheSlides where
  open import StratF.TypeSubstPropertiesSem
  open import StratF.TypeSubstitution
  open import StratF.Types
  open import StratF.Expressions using (Ctx; inn; _◁_; _◁*_)
  open import Data.Nat using (ℕ; suc; zero)
  open import Level
  open import Data.List using (List; []; _∷_)

  --! NormalEqDef
  data _≡_ {l} {A : Set l} (x : A) : A → Set l where
     refl : x ≡ x
  
  --! OmegaEqDef
  data _≡ω_ {A : Setω} (x : A) : A → Setω where
    refl : x ≡ω x

  --! TFExprExcerpt
  data Expr (Δ : LEnv) (Γ : Ctx Δ) : Type Δ l → Set where
    `_    : inn T Γ → Expr Δ Γ T
    `suc  : Expr Δ Γ `ℕ → Expr Δ Γ `ℕ
    Λ_⇒_  : ∀ (l : Level) → {T : Type (l ∷ Δ) l′} → 
              Expr (l ∷ Δ) (l ◁* Γ) T → Expr Δ Γ (`∀α l , T)
    _∙_   : ∀ {T : Type (l ∷ Δ) l′ } → 
              Expr Δ Γ (`∀α l , T) → (T′ : Type Δ l) → Expr Δ Γ (T [ T′ ]T)
    -- ...

    #_    : (n : ℕ) → Expr Δ Γ `ℕ
    ƛ_    : Expr Δ (T ◁ Γ) T′ → Expr Δ Γ (T ⇒ T′)
    _·_   : Expr Δ Γ (T ⇒ T′) → Expr Δ Γ T → Expr Δ Γ T′

module ForTheSlides2 where
  open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong; module ≡-Reasoning)
  open ≡-Reasoning
  open import Data.List using (List; []; _∷_; [_])
  open import Data.Nat using (ℕ; suc)
  open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
  
  open import StratF.Evaluation
  open import StratF.ExprSubstitution
  open import StratF.Expressions
  open import StratF.TypeSubstProperties
  open import StratF.TypeSubstitution
  open import StratF.Types
  open import StratF.Util.Extensionality
  open import StratF.Util.PropositionalSetOmegaEquality
  open import StratF.ExprSubstitution
  
  -- small step call by value semantics
  
  --! SingleReductionExcerpt
  data _↪_ : Expr Δ Γ T → Expr Δ Γ T → Set where
    ξ-∙ : ∀ {T′ : Type Δ l′} {T : Type (l′ ∷ Δ) l} {e₁ e₂ : Expr Δ Γ (`∀α l′ , T)} →
      e₁ ↪ e₂ →
      (e₁ ∙ T′) ↪ (e₂ ∙ T′)
    β-Λ : ∀ {T : Type Δ l} {T′ : Type (l ∷ Δ) l′} {e : Expr (l ∷ Δ) (l ◁* Γ) T′} →
      ((Λ l ⇒ e) ∙ T) ↪ (e [ T ]ET)
    -- ...

    β-ƛ : 
      isValue e₂ →
      ((ƛ e₁) · e₂) ↪ (e₁ [ e₂ ]E)
    β-suc :
      `suc {Γ = Γ} (# n) ↪ (# (suc n))
    ξ-·₁ :
      e₁ ↪ e →
      (e₁ · e₂) ↪ (e · e₂)
    ξ-·₂ : 
      e₂ ↪ e → 
      isValue e₁ →
      (e₁ · e₂) ↪ (e₁ · e)
    ξ-suc :
      e₁ ↪ e →
      `suc e₁ ↪ `suc e

  infix 15 _⇓_
  --! SemanticsExcerpt
  data _⇓_ : CExpr T → CValue T → Set where
    ⇓-Λ  :  Λ l ⇒ e ⇓ (Λ l ⇒ e , V-Λ)
    ⇓-∙  :  e₁ ⇓ (Λ l ⇒ e , V-Λ) →
            (e [ T ]ET) ⇓ v →
            (e₁ ∙ T) ⇓ v
    -- ...

    ⇓-n  :  # n ⇓ (# n , V-♯)
    ⇓-s  :  e ⇓ (# n , V-♯) →
            `suc e ⇓ (# suc n , V-♯)
    ⇓-ƛ  :  ƛ e ⇓ (ƛ e , V-ƛ)
    ⇓-·  :  e₁ ⇓ (ƛ e , V-ƛ) →
            e₂ ⇓ v₂ →
            (e [ exp v₂ ]E) ⇓ v →
            (e₁ · e₂) ⇓ v


open import Relation.Binary.PropositionalEquality using (_≡_; refl; module ≡-Reasoning)
open import Data.List using (List; []; _∷_)
open import Level using (Level)

--! SubstExamples >

module Subst where

  private variable ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

  --! Def
  subst :  ∀ {A : Set ℓ} {x y : A} 
           (P : A → Set ℓ′) → x ≡ y → P x → P y
  subst P refl Px = Px  

  --! HetEqDef
  data _≅_ {A : Set ℓ₁} (x : A) : ∀ {B : Set ℓ₂} → B → Set ℓ₁ where
    refl : x ≅ x

  --! HetEqSubstRemovable
  ≡-subst-removable : ∀ {A : Set ℓ₁} (P : A → Set ℓ₂) {x y} (eq : x ≡ y) (z : P x) →
    subst P eq z ≅ z
  ≡-subst-removable P refl z = refl

  --! HetEqCongII
  cong₂ : ∀ {A : Set ℓ₁} {B : A → Set ℓ₂} {C : ∀ x → B x → Set ℓ₃} {x y u v}
          (f : (x : A) (y : B x) → C x y) → x ≅ y → u ≅ v → f x u ≅ f y v
  cong₂ f refl refl = refl

  --! HetEqConv
  ≡-to-≅ : ∀ {A : Set ℓ} {x y : A} → x ≡ y → x ≅ y
  ≡-to-≅ refl = refl

open import Relation.Binary.PropositionalEquality using (subst)
open import StratF.Types
open import StratF.TypeSubstitution hiding (_∘ₛₛ_)
open import StratF.TypeSubstProperties hiding (fusion-Tsub-Tsub; fusion-Tsub-Tsub-lift)
open import StratF.Expressions
open import StratF.ExprSubstitution hiding (Eidₛ; ESub)

module _ where
  open import Relation.Binary.PropositionalEquality using (subst; sym; trans; cong; cong₂)

  --! ESubDef
  ESub : TSub Δ₁ Δ₂ → TEnv Δ₁ → TEnv Δ₂ → Set
  ESub {Δ₁ = Δ₁} {Δ₂ = Δ₂} σ* Γ₁ Γ₂ = ∀ l (T : Type Δ₁ l) → inn T Γ₁ → Expr Δ₂ Γ₂ (Tsub σ* T)

  --! EidDef
  Eidₛ : ESub Tidₛ Γ Γ
  Eidₛ _ T x = subst (Expr _ _) (sym (TidₛT≡T T)) (` x)

  --! TCompSS
  _∘Tₛₛ_ : TSub Δ₂ Δ₃ → TSub Δ₁ Δ₂ → TSub Δ₁ Δ₃
  (σ₁ ∘Tₛₛ σ₂) _ x = Tsub σ₁ (σ₂ _ x)


  --! FusionTSubTSub
  fusion-Tsub-Tsub : ∀ (T : Type Δ₁ l) 
    (σ₁ : TSub Δ₂ Δ₃) (σ₂ : TSub Δ₁ Δ₂) →
    Tsub σ₁ (Tsub σ₂ T) ≡ Tsub (σ₁ ∘Tₛₛ σ₂) T

  fusion-Tsub-Tsub = {!!}

  private variable
    σ₁* : TSub Δ₂ Δ₃
    σ₂* : TSub Δ₁ Δ₂
    Γ₃ : TEnv Δ₃

  --! ECompSS
  _∘Eₛₛ_ :  ESub σ₁* Γ₂ Γ₃ → ESub σ₂* Γ₁ Γ₂ → 
            ESub (σ₁* ∘Tₛₛ σ₂*) Γ₁ Γ₃
  _∘Eₛₛ_ {σ₁* = σ₁*} {Γ₃ = Γ₃} {σ₂* = σ₂*} σ₁ σ₂ = λ l T x → 
    subst  (Expr _ Γ₃) (fusion-Tsub-Tsub T σ₁* σ₂*) 
           (Esub _ σ₁ (σ₂ _ _ x))

module WithPropEq where
  open import Relation.Binary.PropositionalEquality using (subst; sym; trans; cong; cong₂)
  open ≡-Reasoning

  --! DistSubst
  dist-subst :
    ∀ {ℓ ℓ' ℓ₁ ℓ₂} {A : Set ℓ} {B : Set ℓ'} {a₁ a₂ : A} (F : A → Set ℓ₁) (G : B → Set ℓ₂) →
      (a→b : A → B) (f : ∀ {a} → F a → G (a→b a)) (a₁≡a₂ : a₁ ≡ a₂) (b₁≡b₂ : a→b a₁ ≡ a→b a₂)
      (x : F a₁) →
    f {a₂} (subst F a₁≡a₂ x) ≡ subst G b₁≡b₂ (f {a₁} x)
  dist-subst _ _ _ _ refl refl _ = refl

  --! EidNeutral
  Eidₛe≡e : ∀ (e : Expr Δ Γ T) → Esub Tidₛ Eidₛ e ≡ subst (Expr Δ Γ) (sym (TidₛT≡T _)) e
  Eidₛe≡e {Δ = Δ} {Γ = Γ} (`suc e) =
    Esub Tidₛ Eidₛ (`suc e)                       ≡⟨ refl ⟩
    `suc (Esub Tidₛ Eidₛ e)                       ≡⟨ cong `suc (Eidₛe≡e e) ⟩
    `suc (subst (Expr Δ Γ) (sym (TidₛT≡T `ℕ)) e)  ≡⟨ {!!} ⟩
    subst (Expr Δ Γ) (sym (TidₛT≡T `ℕ)) (`suc e)  ∎

  Eidₛe≡e = {!!}

  --! CongTApp
  cong-∙ : ∀ {T : Type (l ∷ Δ) l′} {e₁ e₂ : Expr Δ Γ (`∀α l , T)} (e₁≡e₂ : e₁ ≡ e₂) (T₁≡T₂ : T₁ ≡ T₂) →
    let S = subst (λ T′ → Expr Δ Γ (T [ T′ ]T)) T₁≡T₂ in
    S (e₁ ∙ T₁) ≡ (e₂ ∙ T₂)
  cong-∙ refl refl = refl
  
  module _ where
    private variable
      σ₁* : TSub Δ₂ Δ₃
      σ₂* : TSub Δ₁ Δ₂
      Γ₃ : TEnv Δ₃

    --! FusionESubESub
    fusion-Esub-Esub : ∀  (e : Expr Δ₁ Γ₁ T) (σ₁ : ESub σ₁* Γ₂ Γ₃) 
                          (σ₂ : ESub σ₂* Γ₁ Γ₂) →
      let S₁ = subst (Expr Δ₃ Γ₃) (fusion-Tsub-Tsub T σ₁* σ₂*) in  
      S₁ (Esub σ₁* σ₁ (Esub σ₂* σ₂ e)) ≡ 
      Esub (σ₁* ∘Tₛₛ σ₂*) (σ₁ ∘Eₛₛ σ₂) e 

    --! FusionESubESubBody
    fusion-Esub-Esub {σ₁* = σ₁*} {Γ₂ = Γ₂} {Γ₃ = Γ₃} {σ₂* = σ₂*} (_∙_ {l = l} {T = T} e T′) σ₁ σ₂ = 
      S₁ (Esub σ₁* σ₁ (Esub σ₂* σ₂ (e ∙ T′)))                              ≡⟨ refl ⟩  -- (1)
      S₁ (Esub σ₁* σ₁ (S₂ (Esub σ₂* σ₂ e ∙ Tsub σ₂* T′)))                  ≡⟨ p₁ ⟩    -- (2)
      S₁ (S₃ (Esub σ₁* σ₁ (Esub σ₂* σ₂ e ∙ Tsub σ₂* T′)))                  ≡⟨ refl ⟩  -- (3)
      S₁ (S₃ (S₄ (Esub σ₁* σ₁ (Esub σ₂* σ₂ e) ∙ Tsub σ₁* (Tsub σ₂* T′))))  ≡⟨ p₂ ⟩    -- (4)
      S₅ (S₇ (S₈ (Esub σ₁* σ₁ (Esub σ₂* σ₂ e) ∙ Tsub σ₁* (Tsub σ₂* T′))))  ≡⟨ p₃ ⟩    -- (5)
      S₅ (S₇ (S₆ (Esub σ₁* σ₁ (Esub σ₂* σ₂ e)) ∙ Tsub σ₁* (Tsub σ₂* T′)))  ≡⟨ p₄ ⟩    -- (6)
      S₅ (Esub (σ₁* ∘Tₛₛ σ₂*) (σ₁ ∘Eₛₛ σ₂) e ∙ Tsub (σ₁* ∘Tₛₛ σ₂*) T′)     ≡⟨ refl ⟩  -- (7)
      Esub (σ₁* ∘Tₛₛ σ₂*) (σ₁ ∘Eₛₛ σ₂) (e ∙ T′)                            ∎          -- (8)
  
      where
        F₁ = Expr _ Γ₃ ; E₁ = fusion-Tsub-Tsub (T [ T′ ]T) σ₁* σ₂*                         ; S₁ = subst F₁ E₁
        F₂ = Expr _ Γ₂ ; E₂ = sym (swap-Tsub-[] σ₂* T T′)                                  ; S₂ = subst F₂ E₂
        F₃ = Expr _ Γ₃ ; E₃ = cong (Tsub σ₁*) E₂                                           ; S₃ = subst F₃ E₃
        F₄ = Expr _ Γ₃ ; E₄ = sym (swap-Tsub-[] σ₁* (Tsub (Tliftₛ σ₂* _) T) (Tsub σ₂* T′)) ; S₄ = subst F₄ E₄
        F₅ = Expr _ Γ₃ ; E₅ = sym (swap-Tsub-[] (σ₁* ∘Tₛₛ σ₂*) T T′)                       ; S₅ = subst F₅ E₅
        F₆ = Expr _ Γ₃ ; E₆ = fusion-Tsub-Tsub (`∀α _ , T) σ₁* σ₂*                         ; S₆ = subst F₆ E₆
        F₇ = λ ■ → Expr _ Γ₃ (Tsub (Tliftₛ (σ₁* ∘Tₛₛ σ₂*) l) T [ ■ ]T) ; E₇ = fusion-Tsub-Tsub T′ σ₁* σ₂* ; S₇ = subst F₇ E₇
        F₈ = Expr _ Γ₃ ; E₈ = {!!} ; S₈ = subst F₈ E₈
  
        --! FusionESubESubBodyProofA
        p₁ = cong S₁ (dist-subst F₂ F₃ (Tsub σ₁*) (Esub σ₁* σ₁) E₂ E₃ (Esub σ₂* σ₂ e ∙ Tsub σ₂* T′))
  
        --! FusionESubESubBodyProofB
        p₂ = {!!}
  
        --! FusionESubESubBodyProofC
        p₃ = {!!}
  
        --! FusionESubESubBodyProofD
        p₄ = cong S₅ (cong-∙ (fusion-Esub-Esub e σ₁ σ₂) (fusion-Tsub-Tsub T′ σ₁* σ₂*))
  
    fusion-Esub-Esub {Δ₂} {Δ₃} {Δ₁} {l} {σ₁*} {σ₂*} {Γ₁} {Γ₂} {Γ₃} {T} e σ₁ σ₂ = {!!}

module WithHetEq where

  fusion-Tsub-Tsub-lift :
    ∀ (T : Type (l ∷ Δ₁) l′) (σ₁ : TSub Δ₂ Δ₃) (σ₂ : TSub Δ₁ Δ₂) →
    Tsub (Tliftₛ σ₁ _) (Tsub (Tliftₛ σ₂ _) T) ≡ Tsub (Tliftₛ (σ₁ ∘Tₛₛ σ₂) _) T
  fusion-Tsub-Tsub-lift = {!!}

  import Relation.Binary.PropositionalEquality as ≡
  open import Relation.Binary.HeterogeneousEquality
    using (_≅_; refl; trans; sym; cong; cong₂; module ≅-Reasoning; ≡-to-≅; ≡-subst-removable)
  open ≅-Reasoning
  open import StratF.Util.HeterogeneousEqualityLemmas renaming (Hcong₃ to cong₃)

  --! FusionESubESubHet
  fusion-Esub-Esub : 
    ∀ {σ₁* : TSub Δ₂ Δ₃} {σ₂* : TSub Δ₁ Δ₂} {Γ₁ : TEnv Δ₁} {Γ₂ : TEnv Δ₂} {Γ₃ : TEnv Δ₃}
      {T : Type Δ₁ l} (e : Expr Δ₁ Γ₁ T) (σ₁ : ESub σ₁* Γ₂ Γ₃) (σ₂ : ESub σ₂* Γ₁ Γ₂) →
    Esub σ₁* σ₁ (Esub σ₂* σ₂ e) ≅ Esub (σ₁* ∘Tₛₛ σ₂*) (σ₁ ∘Eₛₛ σ₂) e
  fusion-Esub-Esub {Δ₂} {Δ₃} {Δ₁} {l} {σ₁*} {σ₂*} {Γ₁} {Γ₂} {Γ₃} {_} (_∙_ {T = T} e T′) σ₁ σ₂ = begin
    Esub σ₁* σ₁ (Esub σ₂* σ₂ (e ∙ T′))                                ≅⟨ refl ⟩  -- (1)
    Esub σ₁* σ₁ (S₂ (Esub σ₂* σ₂ e ∙ Tsub σ₂* T′))                    ≅⟨ p₁ ⟩    -- (2)
    Esub σ₁* σ₁ (Esub σ₂* σ₂ e ∙ Tsub σ₂* T′)                         ≅⟨ refl ⟩  -- (3)
    S₄ (Esub σ₁* σ₁ (Esub σ₂* σ₂ e) ∙ Tsub σ₁* (Tsub σ₂* T′))         ≅⟨ p₂ ⟩    -- (4)
    Esub σ₁* σ₁ (Esub σ₂* σ₂ e) ∙ Tsub σ₁* (Tsub σ₂* T′)              ≅⟨ p₃ ⟩    -- (5)
    Esub (σ₁* ∘Tₛₛ σ₂*) (σ₁ ∘Eₛₛ σ₂) e ∙ Tsub (σ₁* ∘Tₛₛ σ₂*) T′       ≅⟨ p₄ ⟩    -- (6)
    S₅ (Esub (σ₁* ∘Tₛₛ σ₂*) (σ₁ ∘Eₛₛ σ₂) e ∙ Tsub (σ₁* ∘Tₛₛ σ₂*) T′)  ≅⟨ refl ⟩  -- (7)
    Esub (σ₁* ∘Tₛₛ σ₂*) (σ₁ ∘Eₛₛ σ₂) (e ∙ T′)                         ∎          -- (8)

    where
      F₂ = Expr Δ₂ Γ₂ ; E₂ = ≡.sym (swap-Tsub-[] σ₂* T T′)                                  ; S₂ = subst F₂ E₂
      F₄ = Expr Δ₃ Γ₃ ; E₄ = ≡.sym (swap-Tsub-[] σ₁* (Tsub (Tliftₛ σ₂* _) T) (Tsub σ₂* T′)) ; S₄ = subst F₄ E₄
      F₅ = Expr Δ₃ Γ₃ ; E₅ = ≡.sym (swap-Tsub-[] (σ₁* ∘Tₛₛ σ₂*) T T′)                       ; S₅ = subst F₅ E₅

      --! FusionESubESubHetProofA
      p₁ = cong₂  {A = Type Δ₂ l} {B = λ T → Expr Δ₂ Γ₂ T} (λ T e → Esub σ₁* σ₁ e)
                  (sym (≡-to-≅ E₂)) (≡-subst-removable F₂ E₂ _)

      --! FusionESubESubHetProofB
      p₂ = ≡-subst-removable F₄ E₄ _        -- recall that S₄ = subst F₄ E₄
      p₄ = sym (≡-subst-removable F₅ E₅ _)  -- recall that S₅ = subst F₅ E₅

      --! FusionESubESubHetProofC
      p₃ = cong₃  {A = Type (_ ∷ Δ₃) l} {B = λ T → Expr Δ₃ Γ₃ (`∀α _ , T)} {C = λ _ _ → Type Δ₃ _ }
                  (λ _ e T′ → e ∙ T′)
                  (≡-to-≅ (fusion-Tsub-Tsub-lift T σ₁* σ₂*))
                  (fusion-Esub-Esub e σ₁ σ₂)
                  (≡-to-≅ (fusion-Tsub-Tsub T′ σ₁* σ₂*))

  fusion-Esub-Esub = {!!}

