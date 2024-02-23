module LogicalPrelim where


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
REL : Type [] l → Set (suc l)
REL {l} T = Value T → ⟦ T ⟧ [] → Set l 

--! RelEnv
RelEnv : (Δ : LEnv) → Setω
RelEnv Δ = ∀ l → l ∈ Δ → Σ (Type [] l) REL

--! substRE
π₁ : RelEnv Δ → TSub Δ []
π₁ ρ l x = proj₁ (ρ l x)

π₂ : (ρ : RelEnv Δ) → ∀ l → (x : l ∈ Δ) → REL (π₁ ρ l x)
π₂ ρ l x = proj₂ (ρ l x)

subst←RE = π₁

-- type renaming acting on RelEnv by composition

--! TrenAct
Tren-act : TRen Δ₁ Δ₂ → RelEnv Δ₂ → RelEnv Δ₁
Tren-act τ* ρ = λ l x → ρ l (τ* l x)

--! REdrop
REdrop : RelEnv (l ∷ Δ) → RelEnv Δ
REdrop = Tren-act (Twkᵣ Tidᵣ)

--! REext
REext : RelEnv Δ → (Σ (Type [] l) REL) → RelEnv (l ∷ Δ)
REext ρ ΣTR _ here = ΣTR
REext ρ ΣTR _ (there x) = ρ _ x

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
