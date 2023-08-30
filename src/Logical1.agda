{-# OPTIONS --allow-unsolved-metas #-}
module Logical1 where

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
open import SmallStep

----------------------------------------------------------------------
-- auxiliary


exprTy : {T : Type Δ l} → Expr Δ Γ T → Type Δ l
exprTy {T = T} e = T

levelTy : Type Δ l → Level
levelTy {l = l} T = l

levelEnv : TEnv Δ → Level
levelEnv ∅ = zero
levelEnv (T ◁ Γ) = levelTy T ⊔ levelEnv Γ
levelEnv (l ◁* Γ) = levelEnv Γ

levelΔ : LEnv → Level
levelΔ [] = zero
levelΔ (l ∷ Δ) = l ⊔ levelΔ Δ

----------------------------------------------------------------------

-- big step call by value semantics (analogous to Benton et al)

Value : Type [] l → Set
Value T = Expr [] ∅ T

V-ℕ :  (n : ℕ) → Value `ℕ
V-ℕ n = # n

V-ƛ : ∀ {T : Type [] l}{T′ : Type [] l′} → Expr [] (T ◁ ∅) T′ → Value (T ⇒ T′)
V-ƛ e = ƛ e

V-Λ : ∀ (l : Level) → {T : Type (l ∷ []) l′} → Expr (l ∷ []) (l ◁* ∅) T → Value (`∀α l , T)
V-Λ l e = Λ l ⇒ e

exp : Value T → Expr [] ∅ T
exp = id

-- big step semantics

variable v v₂ : Value T

infix 15 _⇓_
data _⇓_ : Expr [] ∅ T → Value T → Set where
  ⇓-n : ∀ {n} → (# n) ⇓ V-ℕ n
  ⇓-ƛ : (ƛ e) ⇓ V-ƛ e
  ⇓-· : e₁ ⇓ V-ƛ e → e₂ ⇓ v₂ → (e [ exp v₂ ]E) ⇓ v → (e₁ · e₂) ⇓ v
  ⇓-Λ : (Λ l ⇒ e) ⇓ V-Λ l e
  ⇓-∙ : e₁ ⇓ V-Λ l e → (e [ T ]ET) ⇓ v → (e₁ ∙ T) ⇓ v

-- exp-v⇓v : ∀ (v : Value T) → exp v ⇓ v
-- exp-v⇓v (.(# _) , v-n) = ⇓-n
-- exp-v⇓v (.(ƛ _) , v-ƛ) = ⇓-ƛ
-- exp-v⇓v (.(Λ _ ⇒ _) , v-Λ) = ⇓-Λ

infixl 10 _∧_
_∧_ = _×_

-- logical relation

-- relation between a syntactic value and a semantic value

REL : Type [] l → Set (suc l)
REL {l} T = Value T → ⟦ T ⟧ [] → Set l 

RelEnv : (Δ : LEnv) → Setω
RelEnv Δ = ∀ l → l ∈ Δ → Σ (Type [] l) REL

-- type renaming acting on RelEnv by composition

Tren-act : TRen Δ₁ Δ₂ → RelEnv Δ₂ → RelEnv Δ₁
Tren-act τ* ρ = λ l x → ρ l (τ* l x)

REdrop′ : RelEnv (l ∷ Δ) → RelEnv Δ
REdrop′ ρ l x = ρ l (there x)

REdrop : RelEnv (l ∷ Δ) → RelEnv Δ
REdrop = Tren-act (Twkᵣ Tidᵣ)

REdrop-≡ : ∀ ρ l x → REdrop{l = l′}{Δ = Δ} ρ l x ≡ REdrop′ ρ l x
REdrop-≡ ρ l x = refl

REext : RelEnv Δ → (Σ (Type [] l) REL) → RelEnv (l ∷ Δ)
REext ρ R _ here = R
REext ρ R _ (there x) = ρ _ x

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

-- special case of composition sub o ren

sublemma : (σ : TSub Δ []) → (Textₛ σ T) ≡ Tliftₛ σ _ ∘ₛₛ Textₛ Tidₛ T
sublemma {T = T} σ = fun-ext₂ λ where 
  _ here → refl
  _ (there x) → begin 
        σ _ x
      ≡⟨ sym (TidₛT≡T (σ _ x)) ⟩
        Tsub Tidₛ (σ _ x)
      ≡⟨ sym (assoc-sub-ren (σ _ x) (Twkᵣ Tidᵣ) (Textₛ Tidₛ T)) ⟩
        Tsub (Textₛ Tidₛ T) (Twk (σ _ x)) 
      ∎

lemma2 : (σ : TSub Δ []) → (T  : Type (l ∷ Δ) l′) → (T′ : Type [] l)
  → Tsub (Tliftₛ σ l) T [ T′ ]T ≡ Tsub (Textₛ σ T′) T
lemma2 σ T T′ = begin 
    Tsub (Textₛ Tidₛ T′) (Tsub (Tliftₛ σ _) T)
  ≡⟨ assoc-sub-sub T (Tliftₛ σ _) (Textₛ Tidₛ T′) ⟩
    Tsub (Tliftₛ σ _ ∘ₛₛ Textₛ Tidₛ T′) T
  ≡⟨ cong (λ σ → Tsub σ T) (sym (sublemma σ)) ⟩
    Tsub (Textₛ σ T′) T
  ∎
   

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

module maybe-simpler? where
        LRV′ : (T : Type Δ l) → (ρ : RelEnv Δ)
          → REL (Tsub (subst←RE ρ) T)
        LRV′ (` α) ρ v z = proj₂ (ρ _ α) v z 
        LRV′ (T₁ ⇒ T₂) ρ u f =
          ∃[ e ] (u ≡ ƛ e) ∧
          ∀ (w : Value (Tsub (subst←RE ρ) T₁)) →
          ∀ (z : ⟦ Tsub (subst←RE ρ) T₁ ⟧ []) →
          LRV′ T₁ ρ w z →
          ∃[ v ] (e [ exp w ]E ⇓ v) ∧ LRV′ T₂ ρ v (f z)
        LRV′ (`∀α l , T) ρ u F =
          ∃[ e ] (u ≡ Λ l ⇒ e) ∧
          ∀ (T′ : Type [] l) →
          ∀ (R : REL T′) →
          ∃[ v ] (e [ T′ ]ET ⇓ v) ∧ 
                 let ρ′ = REext ρ (T′ , R)
                     z′ = F (⟦ T′ ⟧ [])
                 in LRV′ T ρ′
                         (subst Value (lemma1 ρ T T′ R) v)
                         (subst id (begin
                           ⟦ Tsub (Tliftₛ (subst←RE ρ) l) T ⟧ (⟦ T′ ⟧ [] ∷ [])
                         ≡⟨ sym (Tsingle-subst-preserves [] T′ (Tsub (Tliftₛ (subst←RE ρ) l) T)) ⟩
                           ⟦ Tsub (Tliftₛ (subst←RE ρ) l) T [ T′ ]T ⟧ []
                         ≡⟨ cong (λ t → ⟦ t ⟧ []) (σ↑T[T′]≡TextₛσT′T (subst←RE ρ) T′ T) ⟩
                           ⟦ Tsub (Textₛ (subst←RE ρ) T′) T ⟧ []
                         ≡⟨ sym (cong (λ t → ⟦ Tsub t T ⟧ []) (subst←RE-ext-ext ρ T′ R) ) ⟩
                           ⟦ Tsub (subst←RE (REext ρ (T′ , R))) T ⟧ []
                         ∎) z′)
        LRV′ `ℕ ρ u z = ∃[ n ] (u ≡ (# n)) ∧ (n ≡ z)

LRV : (T : Type Δ l) → (ρ : RelEnv Δ)
  → Value (Tsub (subst←RE ρ) T) → ⟦ T ⟧ (subst-to-env* (subst←RE ρ) []) → Set l
LRV (` α) ρ v z =
  proj₂ (ρ _ α) v (subst id (sym (subst-var-preserves α (subst←RE ρ) [])) z)
LRV (T₁ ⇒ T₂) ρ u f =
  ∃[ e ] (u ≡ ƛ e) ∧
  ∀ (w : Value (Tsub (subst←RE ρ) T₁)) →
  ∀ (z : ⟦ T₁ ⟧ (subst-to-env* (subst←RE ρ) [])) →
  LRV T₁ ρ w z →
  ∃[ v ] (e [ exp w ]E ⇓ v)
       ∧ LRV T₂ ρ v (f z)
LRV (`∀α l , T) ρ u F =
  ∃[ e ] (u ≡ Λ l ⇒ e) ∧
  ∀ (T′ : Type [] l) →
  ∀ (R : REL T′) →
  ∃[ v ] (e [ T′ ]ET ⇓ v)
       ∧ let ρ′ = REext ρ (T′ , R)
         in LRV T ρ′ (subst Value (lemma1 ρ T T′ R) v) (F (⟦ T′ ⟧ []))
LRV `ℕ ρ u z =
  ∃[ n ] (u ≡ (# n)) ∧ (n ≡ z)

-- closing value substitution

CSub : TSub Δ [] → TEnv Δ → Set
CSub {Δ} σ* Γ = ESub σ* Γ ∅

ES←SC : {σ* : TSub Δ []} → CSub σ* Γ → ESub σ* Γ ∅
ES←SC = id

Csub : {Γ : TEnv Δ} {σ* : TSub Δ []} → CSub σ* Γ → Expr Δ Γ T → Expr [] ∅ (Tsub σ* T)
Csub {σ* = σ*} χ e = Esub σ* χ e

Cdrop : ∀ {l} {T : Type Δ l} → CSub σ* (T ◁ Γ) → CSub σ* Γ
Cdrop χ _ _ x = χ _ _ (there x)

Cextend : ∀ {l} {T : Type Δ l} → CSub σ* Γ → Value (Tsub σ* T) → CSub σ* (T ◁ Γ)
Cextend χ v _ _ here = v
Cextend χ v _ _ (there x) = χ _ _ x

Cextend-Eext : ∀ {l} {T : Type Δ l} → (χ : CSub σ* Γ) → (w : Value (Tsub σ* T)) → 
  Cextend {T = T} χ w ≡ Eextₛ _ χ (exp w)
Cextend-Eext {Δ = Δ} {σ* = σ*} {Γ = Γ} {T = T} χ w = fun-ext λ l → fun-ext λ T′ → fun-ext λ x → aux l T′ x
  where
    aux : (l : Level) (T′ : Type Δ l) (x : inn T′ (T ◁ Γ)) →
      (Cextend χ w) l _ x ≡ Eextₛ σ* χ (exp w) l _ x
    aux l _ here = refl
    aux l _ (there x) = refl

Cdrop-Cextend : ∀ {l} {σ* : TSub Δ []} {T : Type Δ l}
  → (χ : CSub σ* Γ) → (v : Value (Tsub σ* T))
  → Cdrop {l = l} {T = T} (Cextend {l = l} χ v) ≡ χ
Cdrop-Cextend {Δ = Δ} {Γ = Γ} {l = l} {T = T} χ v = fun-ext λ l′ → fun-ext λ T′ → fun-ext λ x → aux l′ T′ x
  where
    aux : ∀ l′ (T′ : Type Δ l′) → (x : inn T′ Γ) → Cdrop {T = T} (Cextend χ v) l′ _ x ≡ χ l′ _ x
    aux _ _ here = refl
    aux _ _ (there x) = refl
    aux _ _ (tskip x) = refl

Cdropt : {Γ : TEnv Δ} → CSub σ* (l ◁* Γ) → CSub (Tdropₛ σ*) Γ
Cdropt {σ* = σ*} χ l T x = subst Value (assoc-sub-ren T (Twkᵣ Tidᵣ) σ*) (χ _ _ (tskip x))

Cextt : ∀{l} → CSub σ* Γ → (T′ : Type [] l) → CSub (Textₛ σ* T′) (l ◁* Γ)
Cextt {σ* = σ*} χ T′ _ _ (tskip {T = T} x) = subst Value (sym (σT≡TextₛσTwkT σ* T)) (χ _ _ x)

subst-split-ƛ : 
    ∀ {t₁ t₁′ : Type [] l₁}
  → {t₂ t₂′ : Type [] l₂}
  → (eq : t₁ ⇒ t₂ ≡ t₁′ ⇒ t₂′)
  → (eq₁ : t₁ ≡ t₁′)
  → (eq₂ : t₂ ≡ t₂′)
  → (a : Expr [] (t₁ ◁ ∅) t₂)
  → subst (Expr [] ∅) eq (ƛ a) ≡ ƛ subst₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂) eq₁ eq₂ a
subst-split-ƛ refl refl refl a = refl

subst-split-Λ :
  ∀ {tᵢ tᵢ′ : Type [ l ] l₁}
  → (eqₒ : `∀α l , tᵢ ≡ `∀α l , tᵢ′)
  → (eqᵢ : tᵢ ≡ tᵢ′)
  → (a : Expr [ l ] (l ◁* ∅) tᵢ)
  → subst (Expr [] ∅) eqₒ (Λ l ⇒ a) ≡ Λ l ⇒ subst (Expr [ l ] (l ◁* ∅)) eqᵢ a
subst-split-Λ refl refl a = refl

subst-split-⇓ :
  ∀ {Tₑ Tᵥ : Type [] l}
  → (e : Value Tₑ)
  → (v : Value Tᵥ)
  → (Tₑ≡Tᵥ : Tₑ ≡ Tᵥ)
  → subst Value Tₑ≡Tᵥ e ⇓ v
  → e ⇓ subst Value (sym Tₑ≡Tᵥ) v
subst-split-⇓ e v refl x = x

Tdrop-σ≡Twk∘σ : ∀ (σ* : TSub (l ∷ Δ₁) Δ₂) → Tdropₛ σ* ≡ Twkᵣ Tidᵣ ∘ᵣₛ σ*
Tdrop-σ≡Twk∘σ σ* = fun-ext₂ (λ x y → refl)


LRVwk : ∀ {Δ}{l}{l₁}
  → (T : Type Δ l)
  → (ρ : RelEnv (l₁ ∷ Δ))
  → let σ* = subst←RE ρ
  in (v : Value (Tsub (Tdropₛ σ*) T))
  → (z : ⟦ T ⟧ (subst-to-env* (Tdropₛ σ*) []))
  → LRV T (REdrop ρ) v z
  → LRV (Twk T)
        ρ
        (subst Value (sym (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ))) v)
        (subst id (sym (Tren*-preserves-semantics {ρ* = Twkᵣ Tidᵣ} {subst-to-env* (Tdropₛ σ*) []} {subst-to-env* σ* []} (wkᵣ∈Ren* (subst-to-env* (Tdropₛ σ*) []) (⟦ σ* _ here ⟧ [])) T)) z)

LRVst : ∀ {Δ}{l}{l₁}
  → (T : Type Δ l)
  → (ρ : RelEnv (l₁ ∷ Δ))
  → let σ* = subst←RE ρ
  in (v : Value (Tsub σ* (Twk T)))
  → (z : ⟦ Twk T ⟧ (⟦ subst←RE ρ _ here ⟧ [] ∷ subst-to-env* (Tdropₛ σ*) []))
  → LRV (Twk T) ρ v z
  → LRV T (REdrop ρ)
        (subst Value (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ)) v)
        (subst id ((Tren*-preserves-semantics {ρ* = Twkᵣ Tidᵣ} {subst-to-env* (Tdropₛ σ*) []} {subst-to-env* σ* []} (wkᵣ∈Ren* (subst-to-env* (Tdropₛ σ*) []) (⟦ σ* _ here ⟧ [])) T)) z)

LRVwk (` α) ρ v z lrv-drop = lrv-drop
LRVwk (T₁ ⇒ T₂) ρ v z (e , refl , F) =
  subst₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂)
         (sym (assoc-sub-ren T₁ (Twkᵣ Tidᵣ) (subst←RE ρ)))
         (sym (assoc-sub-ren T₂ (Twkᵣ Tidᵣ) (subst←RE ρ)))
         e ,
  subst-split-ƛ (sym (assoc-sub-ren (T₁ ⇒ T₂) (Twkᵣ Tidᵣ) (subst←RE ρ))) (sym (assoc-sub-ren T₁ (Twkᵣ Tidᵣ) (subst←RE ρ))) (sym (assoc-sub-ren T₂ (Twkᵣ Tidᵣ) (subst←RE ρ))) e ,
  λ w₁ z₁ lrv-wk-t1 →
  let σ* = subst←RE ρ in
  let w₁′ = (subst Value (assoc-sub-ren T₁ (Twkᵣ Tidᵣ) (subst←RE ρ)) w₁) in
  let z₁′ = (subst id ((Tren*-preserves-semantics {ρ* = Twkᵣ Tidᵣ} {subst-to-env* (Tdropₛ σ*) []} {subst-to-env* σ* []} (wkᵣ∈Ren* (subst-to-env* (Tdropₛ σ*) []) (⟦ σ* _ here ⟧ [])) T₁)) z₁) in
  F w₁′ z₁′ (LRVst T₁ ρ w₁ z₁ lrv-wk-t1)
  |> λ where
  (v₂ , e⇓v₂ , lrv-drop-t2) →
    let lrv-wk-t2 = LRVwk T₂ ρ v₂ (z z₁′) lrv-drop-t2 in
    let e⇓v₂′ =   e⇓v₂ in 
    (subst Value (sym (assoc-sub-ren T₂ (Twkᵣ Tidᵣ) (subst←RE ρ))) v₂) ,
    subst-split-⇓ _ v₂ (assoc-sub-ren T₂ (Twkᵣ Tidᵣ) (subst←RE ρ))
      (subst (_⇓ v₂) {!!} e⇓v₂) , -- easy ;-)
    subst
      (LRV (Twk T₂) ρ (subst Value (sym (assoc-sub-ren T₂ (Twkᵣ Tidᵣ) (subst←RE ρ))) v₂))
      (begin 
        subst id
        (sym
         (Tren*-preserves-semantics
          (wkᵣ∈Ren* (subst-to-env* (Tdropₛ (subst←RE ρ)) [])
           (⟦ subst←RE ρ _ here ⟧ []))
          T₂))
        (z
         (subst id
          (Tren*-preserves-semantics
           (wkᵣ∈Ren* (subst-to-env* (Tdropₛ (subst←RE ρ)) [])
            (⟦ subst←RE ρ _ here ⟧ []))
           T₁)
          z₁))
        ≡⟨ dist-subst (λ x → z x) (Tren*-preserves-semantics
           (wkᵣ∈Ren* (subst-to-env* (Tdropₛ (subst←RE ρ)) [])
            (⟦ subst←RE ρ _ here ⟧ []))
           T₁) (sym (Tren*-preserves-semantics
           (wkᵣ∈Ren* (subst-to-env* (Tdropₛ (subst←RE ρ)) [])
            (⟦ subst←RE ρ _ here ⟧ []))
           (T₁ ⇒ T₂)))  (sym
         (Tren*-preserves-semantics
          (wkᵣ∈Ren* (subst-to-env* (Tdropₛ (subst←RE ρ)) [])
           (⟦ subst←RE ρ _ here ⟧ []))
          T₂)) z₁ 
        ⟩
          _
        ∎)
      lrv-wk-t2
LRVwk (`∀α l , T) ρ v z lrv-drop = {!!}
LRVwk `ℕ ρ v z lrv-drop = lrv-drop

LRVst = {!!}

-- extended LR on environments

LRG : (Γ : TEnv Δ) → (ρ : RelEnv Δ)
  → CSub (subst←RE ρ) Γ
  → let η = subst-to-env* (subst←RE ρ) [] in Env Δ Γ η → Set (levelEnv Γ)
LRG ∅ ρ χ γ = ⊤
LRG (T ◁ Γ) ρ χ γ = LRV T ρ (χ _ _ here) (γ _ T here) ∧  LRG Γ ρ (Cdrop χ) (ENVdrop Γ _ γ)
LRG (l ◁* Γ) ρ χ γ = LRG Γ (REdrop ρ) (Cdropt χ) (Gdropt (subst←RE ρ) γ)

-- environment lookup

LRV←LRG : (Γ : TEnv Δ) (ρ : RelEnv Δ) (χ : CSub (subst←RE ρ) Γ) (γ : Env Δ Γ (subst-to-env* (subst←RE ρ) [])) (T : Type Δ l)
  → LRG Γ ρ χ γ
  → (x : inn T Γ)
  → LRV T ρ (χ l _ x) (γ l T x)
LRV←LRG .(T ◁ _) ρ χ γ T (lrv , lrg) here = lrv
LRV←LRG (_ ◁ Γ) ρ χ γ T (lrv , lrg) (there x) = LRV←LRG _ ρ (Cdrop χ) (ENVdrop Γ _ γ) T lrg x
LRV←LRG {l = l} (l₁ ◁* Γ) ρ χ γ Tw lrg (tskip {T = T} x)
  = let σ* = subst←RE ρ in
    let χ-tskip-x = χ l (Twk T) (tskip x) in
    let χ-drop-x  = Cdropt χ l T x in
    let χ-tskip-drop-≡ : χ-tskip-x ≡ subst Value (sym (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ))) χ-drop-x
        χ-tskip-drop-≡ = sym (subst-sym-subst (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ))) in
    let γ-tskip-x = γ l (Twk T) (tskip x) in
    let γ-drop-x  = Gdropt (subst←RE ρ) γ l T x in
    let γ-tskip-drop-≡ : γ-tskip-x ≡ subst id (sym (Tren*-preserves-semantics {ρ* = Twkᵣ Tidᵣ} {subst-to-env* (Tdropₛ σ*) []} {subst-to-env* σ* []} (wkᵣ∈Ren* (subst-to-env* (Tdropₛ σ*) []) (⟦ σ* _ here ⟧ [])) T)) γ-drop-x
        γ-tskip-drop-≡ = subst-sym-subst {P = {!id!}} (Tren*-preserves-semantics {ρ* = Twkᵣ Tidᵣ}  {subst-to-env* (Tdropₛ σ*) []} {subst-to-env* σ* []} (λ q → refl) T)
    in
    let ih = LRV←LRG {l = l} Γ (REdrop ρ) (Cdropt χ) (Gdropt (subst←RE ρ) γ) T lrg x in
    let r = LRVwk T ρ χ-drop-x γ-drop-x ih
    in subst₂ (LRV (Twk T) ρ) (sym χ-tskip-drop-≡) (sym γ-tskip-drop-≡) r

Cextend-Elift : ∀ {σ* : TSub Δ []} {Γ : TEnv Δ}{l}{T : Type Δ l}{l′}{T′ : Type Δ l′}
  → (χ : CSub σ* Γ)
  → (w : Value (Tsub σ* T))
  → (e : Expr Δ (T ◁ Γ) T′)
  → Csub (Cextend χ w) e ≡ (Esub σ* (Eliftₛ σ* χ) e [ exp w ]E)
Cextend-Elift  {σ* = σ*} {Γ = Γ} {T = T} {l′ = l′} {T′ = T′} χ w e = begin
    Csub (Cextend χ w) e
  ≡⟨⟩
    Esub σ* (Cextend χ w) e
  ≡⟨ cong (λ σ → Esub σ* σ e) (Cextend-Eext χ w) ⟩
    Esub σ* (Eextₛ σ* χ (exp w)) e
  ≡⟨ Eext-Elift {σ* = σ*} χ (exp w) e ⟩
    Esub σ*
      (subst (λ τ* → ESub τ* (T ◁ Γ) ∅) (TSub-id-right σ*)
       (Eliftₛ σ* χ >>SS
        sub0 (subst (Expr [] ∅) (sym (TidₛT≡T (Tsub σ* T))) (exp w))))
      e
  ≡⟨ dist-subst' {F = (λ τ* → ESub τ* (T ◁ Γ) ∅)} {G = Expr [] ∅} 
     (λ σ → {! σ l′ ?  !}) (λ {τ*} σ → Esub τ* σ e)
     (TSub-id-right σ*) (cong (λ τ* → Tsub τ* T′) (TSub-id-right σ*))
     (Eliftₛ σ* χ >>SS
        sub0 (subst (Expr [] ∅) (sym (TidₛT≡T (Tsub σ* T))) (exp w)))
  ⟩
    subst (Expr [] ∅)
      (cong (λ τ* → Tsub τ* T′) (TSub-id-right σ*))
      (Esub (σ* ∘ₛₛ Tidₛ)
       (Eliftₛ σ* χ >>SS
        Eextₛ Tidₛ Eidₛ
        (subst (Expr [] ∅) (sym (TidₛT≡T (Tsub σ* T))) (exp w)))
       e)
  ≡⟨ subst-irrelevant (cong (λ τ* → Tsub τ* T′) (TSub-id-right σ*)) (trans (sym (assoc-sub-sub T′ σ* Tidₛ)) (TidₛT≡T (Tsub σ* T′))) _ ⟩
    subst (Expr [] ∅)
      (trans (sym (assoc-sub-sub T′ σ* Tidₛ)) (TidₛT≡T (Tsub σ* T′)))
      (Esub (σ* ∘ₛₛ Tidₛ)
       (Eliftₛ σ* χ >>SS
        Eextₛ Tidₛ Eidₛ
        (subst (Expr [] ∅) (sym (TidₛT≡T (Tsub σ* T))) (exp w)))
       e)
  ≡˘⟨ subst-subst (sym (assoc-sub-sub T′ σ* Tidₛ)) {y≡z = (TidₛT≡T (Tsub σ* T′))} ⟩
    subst (Expr [] ∅) (TidₛT≡T (Tsub σ* T′))
      (subst (Expr [] ∅) (sym (assoc-sub-sub T′ σ* Tidₛ))
       (Esub (σ* ∘ₛₛ Tidₛ)
        (Eliftₛ σ* χ >>SS
         Eextₛ Tidₛ Eidₛ
         (subst (Expr [] ∅) (sym (TidₛT≡T (Tsub σ* T))) (exp w)))
        e))
  ≡˘⟨ cong (subst (Expr _ _) (TidₛT≡T (Tsub σ* T′)))
    (subst-swap _ _ _ (Eassoc-sub-sub e (Eliftₛ σ* χ) (Eextₛ Tidₛ Eidₛ (subst (Expr _ _) (sym (TidₛT≡T (Tsub σ* T))) (exp w)))))
    ⟩
    subst (Expr _ _) (TidₛT≡T (Tsub σ* T′))
    (Esub Tidₛ (Eextₛ Tidₛ Eidₛ (subst (Expr _ _) (sym (TidₛT≡T (Tsub σ* T))) (exp w))) (Esub σ* (Eliftₛ σ* χ) e))
  ≡⟨ refl ⟩
    Esub σ* (Eliftₛ σ* χ) e [ exp w ]E
  ∎

Gdropt-ext≡id : (ρ : RelEnv Δ) (γ : Env Δ Γ (subst-to-env* (subst←RE ρ) [])) (T′ : Type [] l) (R : REL T′)
  → (Gdropt (subst←RE (REext ρ (T′ , R))) (extend-tskip γ)) ≡ω γ
Gdropt-ext≡id ρ γ T′ R =
  fun-ext-llω-ω (λ x y z → subst-subst-sym (Tren*-preserves-semantics (λ x₁ → refl) y))

Cdropt-Cextt≡id : (Γ : TEnv Δ) (ρ : RelEnv Δ) (χ : CSub (subst←RE ρ) Γ) (l : Level) (T′ : Type [] l) (R : REL T′)
  → (Cdropt (subst (λ σ → CSub σ (l ◁* Γ)) (sym (subst←RE-ext-ext ρ T′ R)) (Cextt χ T′))) ≡ χ
Cdropt-Cextt≡id Γ ρ χ l T′ R =
  let sub₁ = subst (λ σ → CSub σ (l ◁* Γ)) (sym (subst←RE-ext-ext ρ T′ R)) in
  let sub₂ = subst id refl in
  begin
    Cdropt (sub₁ (Cextt χ T′))
  ≡⟨ dist-subst' {F = (λ σ → CSub σ (l ◁* Γ))} {G = id} (λ x → CSub (Tdropₛ x) Γ) Cdropt (sym (subst←RE-ext-ext ρ T′ R)) refl (Cextt χ T′) ⟩ 
    sub₂ (Cdropt (Cextt χ T′))
  ≡⟨⟩
    Cdropt (Cextt χ T′)
  ≡⟨ (fun-ext λ x → fun-ext λ y → fun-ext λ z → (elim-subst Value
       (assoc-sub-ren y (λ z₁ x₁ → there x₁) (Textₛ (λ l₁ x₁ → proj₁ (ρ l₁ x₁)) T′))
       (sym
        (trans
         (assoc-sub-ren y (λ z₁ x₁ → there x₁)
          (Textₛ (λ l₁ x₁ → proj₁ (ρ l₁ x₁)) T′))
         (trans
          (sym (assoc-sub-sub y (λ z₁ → `_) (λ l₁ x₁ → proj₁ (ρ l₁ x₁))))
          (trans (cong (Tsub (λ l₁ x₁ → proj₁ (ρ l₁ x₁))) (TidₛT≡T y))
           refl)))) (χ x y z)))
  ⟩
    χ ∎

-- next one will become obsolete
Elift-[]≡Cextt : (Γ : TEnv Δ) (ρ : RelEnv Δ) (χ : CSub (subst←RE ρ) Γ) (l′ l : Level) (T : Type (l ∷ Δ) l′) (e : Expr (l ∷ Δ) (l ◁* Γ) T) (T′ : Type [] l) (R : REL T′)
  → let lhs = (Esub (Tliftₛ (subst←RE ρ) l) (Eliftₛ-l (subst←RE ρ) χ) e [ T′ ]ET) in
    let rhs = Csub (subst (λ σ → CSub σ (l ◁* Γ)) (sym (subst←RE-ext-ext ρ T′ R)) (Cextt χ T′)) e in
    subst (Expr [] ∅) (lemma1 ρ T T′ R) lhs ≡ rhs
Elift-[]≡Cextt Γ ρ χ l′ l T e T′ R = {!!}

{-
LRVwk-obsolete: ∀ {Δ}{l}{l₁}
  → (T : Type Δ l)
  → (Γ : TEnv Δ)
  → (ρ : RelEnv (l₁ ∷ Δ))
  → (χ : CSub (subst←RE ρ) (l₁ ◁* Γ))
  → (γ : Env (l₁ ∷ Δ) (l₁ ◁* Γ) (subst-to-env* (subst←RE ρ) []))
  → (x : inn T Γ)
  → LRV T (REdrop ρ) (Cdropt χ l _ x) (Gdropt (subst←RE ρ) γ l T x)
  → LRV (Twk T) ρ (χ l _ (tskip x)) (γ l (Twk T) (tskip x))

LRVwk-obsolete(` α) Γ ρ χ γ x lrv = lrv

LRVwk-obsolete`ℕ Γ ρ χ γ x lrv = lrv

LRVwk-obsolete(T₁ ⇒ T₂) Γ ρ χ γ x (e , cdropt-χ-x≡ƛe , F) =
  subst₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂) (dropeq{ρ = ρ} T₁) (dropeq{ρ = ρ} T₂) e ,
  (begin
    χ _ _ (tskip x)
  ≡⟨ subst-swap {F = Expr [] ∅}
       (assoc-sub-ren (T₁ ⇒ T₂) (Twkᵣ Tidᵣ) (subst←RE ρ))
       (χ _ _ (tskip x)) _ cdropt-χ-x≡ƛe
  ⟩
    subst (Expr [] ∅)
      (sym (assoc-sub-ren (T₁ ⇒ T₂) (Twkᵣ Tidᵣ) (subst←RE ρ)))
      (ƛ e)
  ≡⟨ subst-split-ƛ (sym (assoc-sub-ren (T₁ ⇒ T₂) (Twkᵣ Tidᵣ) (subst←RE ρ))) (dropeq T₁) (dropeq T₂) e ⟩
    (ƛ subst₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂) (dropeq T₁) (dropeq T₂) e)
  ∎) ,
  λ w z lrv-wk-t1 →
    let eq₁ : Tsub (subst←RE ρ) (Tren (Twkᵣ Tidᵣ) T₁) ≡ Tsub (subst←RE (REdrop ρ)) T₁
        eq₁ = begin
                Tsub (subst←RE ρ) (Tren (Twkᵣ Tidᵣ) T₁)
              ≡⟨ assoc-sub-ren T₁ (Twkᵣ Tidᵣ) (subst←RE ρ) ⟩
                Tsub (Tdropₛ (subst←RE ρ)) T₁
              ≡˘⟨ cong (λ τ* → Tsub τ* T₁) (subst←RE-drop-ext ρ) ⟩
                Tsub (subst←RE (REdrop ρ)) T₁
              ∎
    in
    let σ* = (subst←RE ρ) in
    let rr = F (subst Value eq₁ w) 
               (subst id ((Tren*-preserves-semantics {ρ* = Twkᵣ Tidᵣ} {subst-to-env* (Tdropₛ σ*) []} {subst-to-env* σ* []} (wkᵣ∈Ren* (subst-to-env* (Tdropₛ σ*) []) (⟦ σ* _ here ⟧ [])) T₁)) z)
               {! lrv-wk-t1!}
    in
    {!!}
    -- LRVwk-obsoleteT₂ Γ ρ χ γ |> λ where 
    --   r → {!!}
  where
    dropeq : ∀ {Δ}{l}{ρ : RelEnv (l₁ ∷ Δ)} → (T : Type Δ l)
      → Tsub (subst←RE (REdrop ρ)) T ≡ Tsub (subst←RE ρ) (Tren (Twkᵣ Tidᵣ) T)
    dropeq {ρ = ρ} T = trans (cong (λ τ → Tsub τ T) (subst←RE-drop-ext ρ)) (sym (assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ)))

LRVwk-obsolete(`∀α l , T) Γ ρ χ γ x (e , cdropt-χ-x≡Λe , F) =
  let eq₀ = 
        begin
          Tsub (Tliftₛ (Tdropₛ (subst←RE ρ)) l) T
        ≡⟨ cong (λ τ → Tsub (Tliftₛ τ l) T) (Tdrop-σ≡Twk∘σ (subst←RE ρ)) ⟩
         Tsub (Tliftₛ (Twkᵣ Tidᵣ ∘ᵣₛ subst←RE ρ) l) T
        ≡⟨ sym (assoc-sub↑-ren↑ T (Twkᵣ Tidᵣ) (subst←RE ρ)) ⟩
          Tsub (Tliftₛ (subst←RE ρ) l) (Tren (Tliftᵣ (Twkᵣ Tidᵣ) l) T)
        ∎
  in
  let eq₁ = 
        begin
          Tsub (Tliftₛ (subst←RE (REdrop ρ)) l) T
        ≡⟨ cong (λ τ → Tsub (Tliftₛ τ l) T) (subst←RE-drop-ext ρ) ⟩
          Tsub (Tliftₛ (Tdropₛ (subst←RE ρ)) l) T
        ≡⟨ eq₀ ⟩
          Tsub (Tliftₛ (subst←RE ρ) l) (Tren (Tliftᵣ (Twkᵣ Tidᵣ) l) T)
        ∎
  in
  subst (Expr [ l ] (l ◁* ∅)) eq₁ e ,
  (begin
    χ _ (Twk (`∀α l , T)) (tskip x)
  ≡⟨ sym (elim-subst (Expr [] ∅) (cong (`∀α l ,_) eq₀) (assoc-sub-ren (`∀α l , T) (Twkᵣ Tidᵣ) _) (χ _ _ (tskip x))) ⟩
    subst (Expr [] ∅) (cong (`∀α l ,_) eq₀) (subst Value (assoc-sub-ren (`∀α l , T) (Twkᵣ Tidᵣ) _) (χ _ _ (tskip x)))
  ≡⟨ refl ⟩
    subst (Expr [] ∅) (cong (`∀α l ,_) eq₀) (Cdropt χ _ (`∀α l , T) x)
  ≡⟨ cong (subst (Expr [] ∅) (cong (`∀α l ,_) eq₀)) cdropt-χ-x≡Λe ⟩
    subst (Expr [] ∅) (cong (`∀α l ,_) eq₀) (Λ l ⇒ e)
  ≡⟨ subst-split-Λ (cong (`∀α l ,_) eq₀) eq₁ e ⟩
    (Λ l ⇒ subst (Expr [ l ] (l ◁* ∅)) eq₁ e)
  ∎) ,
  {!!}

-}
