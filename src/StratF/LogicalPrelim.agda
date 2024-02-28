module StratF.LogicalPrelim where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; [_])
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Function using (_∘_; id; case_of_; _|>_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong;
        subst-∘; subst-application; subst-application′; subst-subst-sym; subst-sym-subst; subst-subst; -- Properties
        module ≡-Reasoning)
open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open ≡-Reasoning

open import StratF.Types
open import StratF.TypeSubstitution
open import StratF.TypeSubstProperties
open import StratF.TypeSubstPropertiesSem
open import StratF.Expressions
open import StratF.ExprSubstitution
open import StratF.ExprSubstProperties
open import StratF.BigStep
open import StratF.Util.Extensionality
open import StratF.Util.PropositionalSetOmegaEquality
open import StratF.Util.SubstProperties

----------------------------------------------------------------------
--! Logical >

infixl 10 _∧_
_∧_ = _×_

-- logical relation

-- relation between a syntactic value and a semantic value
--! REL
REL : Type [] l → Set (suc l)
REL {l} T = CValue T → ⟦ T ⟧ [] → Set l 

--! RelEnv
𝓓⟦_⟧ : (Δ : LEnv) → Setω
𝓓⟦ Δ ⟧ = ∀ l → l ∈ Δ → Σ (Type [] l) REL

RelEnv = 𝓓⟦_⟧

--! substRE
π₁ : RelEnv Δ → TSub Δ []
π₁ ρ l x = proj₁ (ρ l x)

π₂ : (ρ : RelEnv Δ) → ∀ l → (x : l ∈ Δ) → REL (π₁ ρ l x)
π₂ ρ l x = proj₂ (ρ l x)

subst←RE = π₁
_₁ = π₁
_₂ = π₂

-- type renaming acting on RelEnv by composition

--! TrenAct
Tren-act : TRen Δ₁ Δ₂ → 𝓓⟦ Δ₂ ⟧ → 𝓓⟦ Δ₁ ⟧
Tren-act τ* ρ = λ l x → ρ l (τ* l x)

--! REdrop
REdrop : 𝓓⟦ l ∷ Δ ⟧ → 𝓓⟦ Δ ⟧
REdrop = Tren-act (Twkᵣ Tidᵣ)

--! REext
REext : 𝓓⟦ Δ ⟧ → (Σ (Type [] l) REL) → 𝓓⟦ l ∷ Δ ⟧
REext ρ ΣTR _ here       = ΣTR
REext ρ ΣTR _ (there x)  = ρ _ x

subst←RE-ext : ∀ (ρ : RelEnv Δ) (T : Type [] l) (R : REL T) (l′ : Level) (x : l′ ∈ (l ∷ Δ)) → subst←RE (REext ρ (T , R)) l′ x ≡ Textₛ (subst←RE ρ) T l′ x
subst←RE-ext ρ T R l here = refl
subst←RE-ext ρ T R l (there x) = refl

subst←RE-ext-ext : ∀ (ρ : RelEnv Δ) (T : Type [] l) (R : REL T) → subst←RE (REext ρ (T , R)) ≡ Textₛ (subst←RE ρ) T
subst←RE-ext-ext ρ T R = fun-ext₂ (subst←RE-ext ρ T R)

subst←RE-drop : ∀ (ρ : RelEnv (l ∷ Δ)) →
  (l′ : Level) (x : l′ ∈ Δ) → (subst←RE (REdrop ρ)) l′ x ≡ (Tdropₛ (subst←RE ρ)) l′ x
subst←RE-drop ρ l′ here = refl
subst←RE-drop ρ l′ (there x) = refl

subst←RE-drop-ext : ∀ (ρ : RelEnv (l ∷ Δ)) →
  (subst←RE (REdrop ρ)) ≡ (Tdropₛ (subst←RE ρ))
subst←RE-drop-ext ρ = fun-ext₂ (subst←RE-drop ρ)

REdrop-REext≡id : (ρ : RelEnv Δ) → (T′ : Type [] l) → (R : REL T′) → REdrop (REext ρ (T′ , R)) ≡ω ρ
REdrop-REext≡id {Δ = Δ} ρ T′ R = refl

-- holds definitionally
subst←RE-ren : ∀ (ρ : RelEnv Δ₂) (τ* : TRen Δ₁ Δ₂)
  → (l′ : Level) (x : l′ ∈ Δ₁) → subst←RE (Tren-act τ* ρ) l′ x ≡ (τ* ∘ᵣₛ subst←RE ρ) l′ x
subst←RE-ren ρ τ* l′ x = refl

--! lemmaOne
RE-ext∘lift : ∀ (ρ : 𝓓⟦ Δ ⟧) (T : Type (l ∷ Δ) l′) (T′ : Type [] l) (R : REL T′) →
  Tsub (Tliftₛ (π₁ ρ) l) T [ T′ ]T ≡ Tsub (π₁ (REext ρ (T′ , R))) T

RE-ext∘lift {l = l} ρ T T′ R =
  begin
    Tsub (Tliftₛ (subst←RE ρ) l) T [ T′ ]T
    ≡⟨ lemma2 (subst←RE ρ) T T′ ⟩
    Tsub (Textₛ (subst←RE ρ) T′) T
    ≡⟨ cong (λ G → Tsub G T) (sym (subst←RE-ext-ext ρ T′ R)) ⟩
    Tsub (subst←RE (REext ρ (T′ , R))) T
    ∎

lemma1 = RE-ext∘lift

postulate
  relenv-ext : ∀ {Δ}{f g : RelEnv Δ} → (∀ l x → f l x ≡ g l x) → f ≡ω g

Tren-act-REext-ext : (ρ : RelEnv Δ₂) (τ* : TRen Δ₁ Δ₂) (T′ : Type [] l) (R : REL T′)
  → ∀ l₂ x₂ → (REext (Tren-act τ* ρ) (T′ , R)) l₂ x₂ ≡ Tren-act (Tliftᵣ τ* l) (REext ρ (T′ , R)) l₂ x₂
Tren-act-REext-ext ρ τ* T′ R l₂ here = refl
Tren-act-REext-ext ρ τ* T′ R l₂ (there x₂) = refl

Tren-act-REext : (ρ : RelEnv Δ₂) (τ* : TRen Δ₁ Δ₂) (T′ : Type [] l) (R : REL T′)
  → (REext (Tren-act τ* ρ) (T′ , R)) ≡ω Tren-act (Tliftᵣ τ* l) (REext ρ (T′ , R))
Tren-act-REext ρ τ* T′ R = relenv-ext (Tren-act-REext-ext ρ τ* T′ R)

-- Tren-act-wk-ext : ∀ (ρ : RelEnv Δ) (T′ : Type [] l) (R : REL T′)
--   → (Tren-act (Twkᵣ Tidᵣ) (REext ρ (T′ , R))) ≡ω ρ
-- Tren-act-wk-ext ρ T′ R =
--   relenv-ext (helper ρ T′ R)
--   where
--   helper :  ∀ (ρ : RelEnv Δ) (T′ : Type [] l) (R : REL T′) l₁ (x : l₁ ∈ Δ)
--     → Tren-act (Twkᵣ Tidᵣ) (REext ρ (T′ , R)) l₁ x ≡ ρ l₁ x
--   helper ρ T′ R l₁ here = refl
--   helper ρ T′ R l₁ (there x) = refl


-- auxiliary

Gdrop-t : (σ* : TSub (l ∷ Δ) [])
  → Env (l ∷ Δ) (l ◁* Γ) (subst-to-env* σ* [])
  → Env Δ Γ (subst-to-env* (Tdropₛ σ*) [])
Gdrop-t σ* γ l T x =
  let r = γ l (Twk T) (tskip x) in
  subst id (Tren*-preserves-semantics {ρ* = Twkᵣ Tidᵣ} {subst-to-env* (Tdropₛ σ*) []} {subst-to-env* σ* []} (wkᵣ∈Ren* (subst-to-env* (Tdropₛ σ*) []) (⟦ σ* _ here ⟧ [])) T) r

Gdrop : ∀ {l}{T : Type Δ l} {Γ : Ctx Δ} {η : Env* Δ} → Env Δ (T ◁ Γ) η → Env Δ Γ η
Gdrop γ l T x = γ l T (there x)

Gdrop-extend : ∀ {l}{Δ}{Γ}{T : Type Δ l}{η : Env* Δ}
  → (γ : Env Δ Γ η)
  → (z : ⟦ T ⟧ η)
  → γ ≡ω Gdrop {T = T} (extend γ z)
Gdrop-extend {l = l} {Δ = Δ} {Γ = Γ}{T = T}{η = η} γ z = fun-extω (λ l′ → fun-ext₂ (aux l′))
  where
    aux : (l′ : Level) (T′ : Type Δ l′) (x : inn T′ Γ) → γ l′ T′ x ≡ Gdrop {T = T} (extend γ z) l′ T′ x
    aux l′ T′ here = refl
    aux l′ T′ (there x) = refl
    aux l′ .(Twk _) (tskip x) = refl

-- closing value substitution

--! CSub
CSub : TSub Δ [] → Ctx Δ → Set
CSub {Δ} σ* Γ = ∀ l (T : Type Δ l) → inn T Γ → CValue (Tsub σ* T)

--! ESSC
ς₁ : CSub σ* Γ → ESub σ* Γ ∅
ς₁ χ = λ l T x → exp (χ l T x)

ES←SC = ς₁

--! Csub
Csub : {Γ : Ctx Δ} {σ* : TSub Δ []} → CSub σ* Γ → Expr Δ Γ T → CExpr (Tsub σ* T)
Csub {σ* = σ*} χ e = Esub σ* (ES←SC χ) e

--! Cdrop
Cdrop : ∀ {l} {T : Type Δ l} → CSub σ* (T ◁ Γ) → CSub σ* Γ
Cdrop χ l T x = χ l T (there x)

--! Cextend
Cextend : ∀ {l} {T : Type Δ l} → CSub σ* Γ → CValue (Tsub σ* T) → CSub σ* (T ◁ Γ)
Cextend χ v _ _ here       = v
Cextend χ v _ _ (there x)  = χ _ _ x

Cextend-Eext : ∀ {l} {T : Type Δ l} → (χ : CSub σ* Γ) → (w : CValue (Tsub σ* T)) → 
  ES←SC (Cextend {T = T} χ w) ≡ Eextₛ _ (ES←SC χ) (exp w)
Cextend-Eext {Δ = Δ} {σ* = σ*} {Γ = Γ} {T = T} χ w =
  fun-ext (λ l → fun-ext (λ T′ → fun-ext (λ x → aux l T′ x)))
    where
      aux :  (l : Level) (T′ : Type Δ l) (x : inn T′ (T ◁ Γ)) →
        exp ((Cextend χ w) l _ x) ≡ Eextₛ σ* (ES←SC χ) (exp w) l _ x
      aux l T′ here = refl
      aux l T′ (there x) = refl

Cdrop-Cextend : ∀ {l} {σ* : TSub Δ []} {T : Type Δ l}
  → (χ : CSub σ* Γ) → (v : CValue (Tsub σ* T))
  → χ ≡ Cdrop {l = l} {T = T} (Cextend {l = l} χ v)
Cdrop-Cextend {Δ = Δ} {Γ = Γ} {l = l} {T = T} χ v =
  fun-ext λ l′ → fun-ext λ T′ → fun-ext λ x → aux l′ T′ x
  where
    aux : ∀ l′ (T′ : Type Δ l′) → (x : inn T′ Γ) → Cdrop {T = T} (Cextend χ v) l′ _ x ≡ χ l′ _ x
    aux _ _ here = refl
    aux _ _ (there x) = refl
    aux _ _ (tskip x) = refl

Cdrop-t : {Γ : Ctx Δ} → CSub σ* (l ◁* Γ) → CSub (Tdropₛ σ*) Γ
Cdrop-t {σ* = σ*} χ l T x = subst CValue (fusion-Tsub-Tren T (Twkᵣ Tidᵣ) σ*) (χ _ _ (tskip x))

--! Cextt
Cextt : ∀{l} → CSub σ* Γ → (T′ : Type [] l) → CSub (Textₛ σ* T′) (l ◁* Γ)
Cextt {σ* = σ*} χ T′ _ _ (tskip {T = T} x) = subst CValue (sym (σT≡TextₛσTwkT σ* T)) (χ _ _ x)

Cextt-Eextₛ-l : ∀{l} {T′ : Type [] l} → (χ : CSub σ* Γ)
  → ES←SC (Cextt χ T′) ≡ Eextₛ-l _ (ES←SC χ)
Cextt-Eextₛ-l {σ* = σ*}{T′ = T′} χ = fun-ext (λ l′ → fun-ext (λ T → fun-ext (λ x → aux l′ T x)))
  where
    aux : ∀ {T′} (l′ : Level) (T : Type _ l′) (x : inn T (l ◁* _))
      → ES←SC (Cextt χ T′) l′ T x ≡ Eextₛ-l σ* (ES←SC χ) l′ T x
    aux {T′ = T′} l′ .(Twk _) (tskip {T = T} x) =
      dist-subst' {F = CValue} {G = CExpr} id exp
        (sym
          (trans (fusion-Tsub-Tren T (λ z x₁ → there x₁) (Textₛ σ* T′))
           (trans (sym (fusion-Tsub-Tsub T (λ z → `_) σ*))
            (trans (cong (Tsub σ*) (TidₛT≡T T)) refl))))
        (sym
          (trans (fusion-Tsub-Tren T (λ z x₁ → there x₁) (Textₛ σ* T′))
           (trans (sym (fusion-Tsub-Tsub T (λ z → `_) σ*))
            (trans (cong (Tsub σ*) (TidₛT≡T T)) refl))))
         (χ l′ T x)

