module Logical2 where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; [_]; _++_; length; lookup; tabulate)
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

open import Ext
open import SetOmega
open import SubstProperties
open import Types
open import TypeSubstitution
open import TypeSubstProperties
open import Expressions
open import ExprSubstitution
open import ExprSubstProperties
open import BigStep

----------------------------------------------------------------------
--! Logical >

infixl 10 _∧_
_∧_ = _×_

-- logical relation

-- relation between a syntactic value and a semantic value
--! REL
REL : ∀ {l} → Type [] l → Set (suc l)
REL {l} T = Value T → ⟦ T ⟧ [] → Set l 

--! RelEnv
RelEnv : (Δ : LEnv) → Setω
RelEnv Δ = ∀ l → l ∈ Δ → Σ (Type [] l) REL

-- type renaming acting on RelEnv by composition

--! Tren-act
Tren-act : TRen Δ₁ Δ₂ → RelEnv Δ₂ → RelEnv Δ₁
Tren-act τ* ρ = λ l x → ρ l (τ* l x)

--! REdrop
REdrop : RelEnv (l ∷ Δ) → RelEnv Δ
REdrop = Tren-act (Twkᵣ Tidᵣ)

--! REext
REext : RelEnv Δ → (Σ (Type [] l) REL) → RelEnv (l ∷ Δ)
REext ρ R _ here = R
REext ρ R _ (there x) = ρ _ x

--! substRE
subst←RE : RelEnv Δ → TSub Δ []
subst←RE ρ l x = proj₁ (ρ l x)

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


lemma1 : (ρ  : RelEnv Δ) → (T  : Type (l ∷ Δ) l′) → (T′ : Type [] l) → (R  : REL T′)
  → Tsub (Tliftₛ (subst←RE ρ) l) T [ T′ ]T ≡ Tsub (subst←RE (REext ρ (T′ , R))) T
lemma1 {l = l} ρ T T′ R =
  begin
    Tsub (Tliftₛ (subst←RE ρ) l) T [ T′ ]T
    ≡⟨ lemma2 (subst←RE ρ) T T′ ⟩
    Tsub (Textₛ (subst←RE ρ) T′) T
    ≡⟨ cong (λ G → Tsub G T) (sym (subst←RE-ext-ext ρ T′ R)) ⟩
    Tsub (subst←RE (REext ρ (T′ , R))) T
    ∎

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

Gdropt : (σ* : TSub (l ∷ Δ) [])
  → Env (l ∷ Δ) (l ◁* Γ) (subst-to-env* σ* [])
  → Env Δ Γ (subst-to-env* (Tdropₛ σ*) [])
Gdropt σ* γ l T x =
  let r = γ l (Twk T) (tskip x) in
  subst id (Tren*-preserves-semantics {ρ* = Twkᵣ Tidᵣ} {subst-to-env* (Tdropₛ σ*) []} {subst-to-env* σ* []} (wkᵣ∈Ren* (subst-to-env* (Tdropₛ σ*) []) (⟦ σ* _ here ⟧ [])) T) r

ENVdrop : ∀ {l}{T : Type Δ l} → (Γ : TEnv Δ) → (η : Env* Δ) → Env Δ (T ◁ Γ) η → Env Δ Γ η
ENVdrop Γ η γ l T x = γ l T (there x)

ENVdrop-extend : ∀ {l}{Δ}{Γ}{T : Type Δ l}{η : Env* Δ}
  → (γ : Env Δ Γ η)
  → (z : ⟦ T ⟧ η)
  → γ ≡ω ENVdrop {T = T} Γ η (extend γ z)
ENVdrop-extend {l = l} {Δ = Δ} {Γ = Γ}{T = T}{η = η} γ z = fun-extω (λ l′ → fun-ext₂ (aux l′))
  where
    aux : (l′ : Level) (T′ : Type Δ l′) (x : inn T′ Γ) → γ l′ T′ x ≡ ENVdrop {T = T} Γ η (extend γ z) l′ T′ x
    aux l′ T′ here = refl
    aux l′ T′ (there x) = refl
    aux l′ .(Twk _) (tskip x) = refl

-- stratified logical relation

--! MCV
𝓥⟦_⟧ : (T : Type Δ l) → (ρ : RelEnv Δ)
  → Value (Tsub (subst←RE ρ) T) → ⟦ T ⟧ (subst-to-env* (subst←RE ρ) []) → Set l
𝓥⟦ ` α ⟧ ρ v z =
  proj₂ (ρ _ α) v (subst id (sym (subst-var-preserves α (subst←RE ρ) [])) z)
𝓥⟦ T₁ ⇒ T₂ ⟧ ρ u f =
  ∃[ e ] (exp u ≡ ƛ e) ∧
  ∀ w z → 𝓥⟦ T₁ ⟧ ρ w z → ∃[ v ] (e [ exp w ]E ⇓ v) ∧ 𝓥⟦ T₂ ⟧ ρ v (f z)
𝓥⟦ `∀α l , T ⟧ ρ u F =
  ∃[ e ] (exp u ≡ Λ l ⇒ e) ∧
  ∀ T′ R →
  ∃[ v ] (e [ T′ ]ET ⇓ v)
       ∧ let ρ′ = REext ρ (T′ , R)
         in 𝓥⟦ T ⟧ ρ′ (subst Value (lemma1 ρ T T′ R) v) (F (⟦ T′ ⟧ []))
𝓥⟦ `ℕ ⟧ ρ u z =
  ∃[ n ] (exp u ≡ (# n)) ∧ (n ≡ z)

--! MCE
𝓔⟦_⟧ : (T : Type Δ l) → (ρ : RelEnv Δ)
  → CExpr (Tsub (subst←RE ρ) T) → ⟦ T ⟧ (subst-to-env* (subst←RE ρ) []) → Set l
𝓔⟦ T ⟧ ρ e z = ∃[ v ] (e ⇓ v) ∧ 𝓥⟦ T ⟧ ρ v z

-- closing value substitution

--! CSub
CSub : TSub Δ [] → TEnv Δ → Set
CSub {Δ} σ* Γ = ∀ l (T : Type Δ l) → inn T Γ → Value (Tsub σ* T)

--! ESSC
ES←SC : {σ* : TSub Δ []} → CSub σ* Γ → ESub σ* Γ ∅
ES←SC χ = λ l T x → proj₁ (χ l T x)

--! Csub
Csub : {Γ : TEnv Δ} {σ* : TSub Δ []} → CSub σ* Γ → Expr Δ Γ T → CExpr (Tsub σ* T)
Csub {σ* = σ*} χ e = Esub σ* (ES←SC χ) e

--! Cdrop
Cdrop : ∀ {l} {T : Type Δ l} → CSub σ* (T ◁ Γ) → CSub σ* Γ
Cdrop χ l T x = χ l T (there x)

--! Cextend
Cextend : ∀ {l} {T : Type Δ l} → CSub σ* Γ → Value (Tsub σ* T) → CSub σ* (T ◁ Γ)
Cextend χ v _ _ here = v
Cextend χ v _ _ (there x) = χ _ _ x

Cextend-Eext : ∀ {l} {T : Type Δ l} → (χ : CSub σ* Γ) → (w : Value (Tsub σ* T)) → 
  ES←SC (Cextend {T = T} χ w) ≡ Eextₛ _ (ES←SC χ) (exp w)
Cextend-Eext {Δ = Δ} {σ* = σ*} {Γ = Γ} {T = T} χ w =
  fun-ext (λ l → fun-ext (λ T′ → fun-ext (λ x → aux l T′ x)))
    where
      aux :  (l : Level) (T′ : Type Δ l) (x : inn T′ (T ◁ Γ)) →
        proj₁ ((Cextend χ w) l _ x) ≡ Eextₛ σ* (ES←SC χ) (exp w) l _ x
      aux l T′ here = refl
      aux l T′ (there x) = refl

Cdrop-Cextend : ∀ {l} {σ* : TSub Δ []} {T : Type Δ l}
  → (χ : CSub σ* Γ) → (v : Value (Tsub σ* T))
  → Cdrop {l = l} {T = T} (Cextend {l = l} χ v) ≡ χ
Cdrop-Cextend {Δ = Δ} {Γ = Γ} {l = l} {T = T} χ v =
  fun-ext λ l′ → fun-ext λ T′ → fun-ext λ x → aux l′ T′ x
  where
    aux : ∀ l′ (T′ : Type Δ l′) → (x : inn T′ Γ) → Cdrop {T = T} (Cextend χ v) l′ _ x ≡ χ l′ _ x
    aux _ _ here = refl
    aux _ _ (there x) = refl
    aux _ _ (tskip x) = refl

Cdropt : {Γ : TEnv Δ} → CSub σ* (l ◁* Γ) → CSub (Tdropₛ σ*) Γ
Cdropt {σ* = σ*} χ l T x = subst Value (assoc-sub-ren T (Twkᵣ Tidᵣ) σ*) (χ _ _ (tskip x))

--! Cextt
Cextt : ∀{l} → CSub σ* Γ → (T′ : Type [] l) → CSub (Textₛ σ* T′) (l ◁* Γ)
Cextt {σ* = σ*} χ T′ _ _ (tskip {T = T} x) = subst Value (sym (σT≡TextₛσTwkT σ* T)) (χ _ _ x)

Cextt-Eextₛ-l : ∀{l} {T′ : Type [] l} → (χ : CSub σ* Γ)
  → ES←SC (Cextt χ T′) ≡ Eextₛ-l _ (ES←SC χ)
Cextt-Eextₛ-l {σ* = σ*}{T′ = T′} χ = fun-ext (λ l′ → fun-ext (λ T → fun-ext (λ x → aux l′ T x)))
  where
    aux : ∀ {T′} (l′ : Level) (T : Type _ l′) (x : inn T (l ◁* _))
      → ES←SC (Cextt χ T′) l′ T x ≡ Eextₛ-l σ* (ES←SC χ) l′ T x
    aux {T′ = T′} l′ .(Twk _) (tskip {T = T} x) =
      dist-subst' {F = (λ T₁ → Σ (Expr [] ∅ T₁) isValue)} {G = CExpr} id proj₁
        (sym
          (trans (assoc-sub-ren T (λ z x₁ → there x₁) (Textₛ σ* T′))
           (trans (sym (assoc-sub-sub T (λ z → `_) σ*))
            (trans (cong (Tsub σ*) (TidₛT≡T T)) refl))))
        (sym
          (trans (assoc-sub-ren T (λ z x₁ → there x₁) (Textₛ σ* T′))
           (trans (sym (assoc-sub-sub T (λ z → `_) σ*))
            (trans (cong (Tsub σ*) (TidₛT≡T T)) refl))))
         (χ l′ T x)


-- extended LR on environments

--! MCG
𝓖⟦_⟧ : (Γ : TEnv Δ) → (ρ : RelEnv Δ)
  → CSub (subst←RE ρ) Γ
  → let η = subst-to-env* (subst←RE ρ) [] in Env Δ Γ η → Set (levelEnv Γ)
𝓖⟦ ∅ ⟧ ρ χ γ = ⊤
𝓖⟦ T ◁ Γ ⟧ ρ χ γ = 𝓥⟦ T ⟧ ρ (χ _ _ here) (γ _ T here)
                 ∧ 𝓖⟦ Γ ⟧ ρ (Cdrop χ) (ENVdrop Γ _ γ)
𝓖⟦ l ◁* Γ ⟧ ρ χ γ = 𝓖⟦ Γ ⟧ (REdrop ρ) (Cdropt χ) (Gdropt (subst←RE ρ) γ)

----------------------------------------

-- subst-split-⇓ :
--   ∀ {Tₑ Tᵥ : Type [] l}
--   → (e : CExpr Tₑ)
--   → (v : Value Tᵥ)
--   → (Tₑ≡Tᵥ : Tₑ ≡ Tᵥ)
--   → subst CExpr Tₑ≡Tᵥ e ⇓ v
--   → e ⇓ subst Value (sym Tₑ≡Tᵥ) v
-- subst-split-⇓ e v refl x = x

--! substSplitEqEval
subst-split-eq-⇓ :
  ∀ {Tₑ Tᵥ : Type [] l}
  → (e : CExpr Tₑ)
  → (v : Value Tᵥ)
  → (Tₑ≡Tᵥ : Tₑ ≡ Tᵥ)
  → subst CExpr Tₑ≡Tᵥ e ⇓ v ≡ e ⇓ subst Value (sym Tₑ≡Tᵥ) v
subst-split-eq-⇓ e v refl = refl

-- subst-split-⇓′ :
--   ∀ {Tₑ Tᵥ : Type [] l}
--   → (e : CExpr Tₑ)
--   → (v : Value Tᵥ)
--   → (Tₑ≡Tᵥ : Tₑ ≡ Tᵥ)
--   → e ⇓ subst Value (sym Tₑ≡Tᵥ) v
--   → subst CExpr Tₑ≡Tᵥ e ⇓ v
-- subst-split-⇓′ e v refl x = x

-- subst-split-⇓₂ :
--   ∀ {T T′ : Type [] l}
--   → {e : CExpr T}
--   → {v : Value T}
--   → (T≡T′ : T ≡ T′)
--   → e ⇓ v
--   → subst CExpr T≡T′ e ⇓ subst Value T≡T′ v
-- subst-split-⇓₂ refl e⇓v = e⇓v

subst-split-eq-⇓₂ :
  ∀ {T T′ : Type [] l}
  → {e : CExpr T}
  → {v : Value T}
  → (T≡T′ : T ≡ T′)
  → e ⇓ v
  ≡ subst CExpr T≡T′ e ⇓ subst Value T≡T′ v
subst-split-eq-⇓₂ refl = refl

subst-split-[]E :
  ∀ {T₁ T₁′ : Type [] l₁} {T₂ T₂′ : Type [] l₂}
  → (e : Expr [] (T₁ ◁ ∅) T₂) (e′ : CExpr T₁′)
  → (eq₁ : T₁ ≡ T₁′) (eq₂ : T₂ ≡ T₂′)
  → subst CExpr eq₂ (e [ subst CExpr (sym eq₁) e′ ]E) ≡ (subst₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂) eq₁ eq₂ e [ e′ ]E)
subst-split-[]E e e′ refl refl = refl

subst-split-[]E′ :
  ∀ {T₁ T₁′ : Type [] l₁} {T₂ T₂′ : Type [] l₂}
  → (e : Expr [] (T₁ ◁ ∅) T₂) (e′ : CExpr T₁′)
  → (eq₁ : T₁′ ≡ T₁) (eq₂ : T₂ ≡ T₂′)
  → subst CExpr eq₂ (e [ subst CExpr eq₁ e′ ]E) ≡ (subst₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂) (sym eq₁) eq₂ e [ e′ ]E)
subst-split-[]E′ e e′ refl refl = refl

subst-split-[]E″ :
  ∀ {T₁ T₁′ : Type [] l₁} {T₂ T₂′ : Type [] l₂}
  → (e : Expr [] (T₁ ◁ ∅) T₂) (e′ : CExpr T₁)
  → (eq₁ : T₁ ≡ T₁′) (eq₂ : T₂ ≡ T₂′)
  → (subst₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂) eq₁ eq₂ e [ subst CExpr eq₁ e′ ]E)
  ≡ subst CExpr eq₂ (e [ e′ ]E) 
subst-split-[]E″ e e′ refl refl = refl

{- <-- TypeSubstProperties -}
σ[T′]≡↑τ*∘ext-ext : (ρ : RelEnv Δ₂) (τ* : TRen Δ₁ Δ₂) (T′ : Type [] l) → ∀ l′ x →  Textₛ (τ* ∘ᵣₛ subst←RE ρ) T′ l′ x ≡ (Tliftᵣ τ* l ∘ᵣₛ Textₛ (subst←RE ρ) T′) l′ x
σ[T′]≡↑τ*∘ext-ext ρ τ* T′ l′ here = refl
σ[T′]≡↑τ*∘ext-ext ρ τ* T′ l′ (there x) = refl

σ[T′]≡↑τ*∘ext : (ρ : RelEnv Δ₂) (τ* : TRen Δ₁ Δ₂) (T′ : Type [] l) →  Textₛ (τ* ∘ᵣₛ subst←RE ρ) T′ ≡ (Tliftᵣ τ* l ∘ᵣₛ Textₛ (subst←RE ρ) T′)
σ[T′]≡↑τ*∘ext ρ τ* T′ = fun-ext₂ (σ[T′]≡↑τ*∘ext-ext ρ τ* T′)
{- --> TypeSubstProperties -}

