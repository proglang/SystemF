{-# OPTIONS --allow-unsolved-metas #-}
module Logical where

open import Level
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_; length; lookup; tabulate)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Function using (_∘_; id; case_of_; _$-; λ-)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong;
        subst-∘; subst-application; subst-application′; subst-subst-sym; -- Properties
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
Value T = Σ (Expr [] ∅ T) Val

V-ℕ :  (n : ℕ) → Value `ℕ
V-ℕ n = # n , v-n

V-ƛ : ∀ {T : Type [] l}{T′ : Type [] l′} → Expr [] (T ◁ ∅) T′ → Value (T ⇒ T′)
V-ƛ e = ƛ e , v-ƛ

V-Λ : ∀ (l : Level) → {T : Type (l ∷ []) l′} → Expr (l ∷ []) (l ◁* ∅) T → Value (`∀α l , T)
V-Λ l e = Λ l ⇒ e , v-Λ

exp : Value T → Expr [] ∅ T
exp = proj₁

-- big step semantics

variable v v₂ : Value T

infix 15 _⇓_
data _⇓_ : Expr [] ∅ T → Value T → Set where
  ⇓-n : ∀ {n} → (# n) ⇓ V-ℕ n
  ⇓-ƛ : (ƛ e) ⇓ V-ƛ e
  ⇓-· : e₁ ⇓ V-ƛ e → e₂ ⇓ v₂ → (e [ exp v₂ ]E) ⇓ v → (e₁ · e₂) ⇓ v
  ⇓-Λ : (Λ l ⇒ e) ⇓ V-Λ l e
  ⇓-∙ : e₁ ⇓ V-Λ l e → (e [ T ]ET) ⇓ v → (e₁ ∙ T) ⇓ v

exp-v⇓v : ∀ (v : Value T) → exp v ⇓ v
exp-v⇓v (.(# _) , v-n) = ⇓-n
exp-v⇓v (.(ƛ _) , v-ƛ) = ⇓-ƛ
exp-v⇓v (.(Λ _ ⇒ _) , v-Λ) = ⇓-Λ

-- adequacy

infixl 10 _∧_
_∧_ = _×_

-- logical relation

-- relation between a syntactic value and a semantic value

REL : Type [] l → Set (suc l)
REL {l} T = Value T → ⟦ T ⟧ [] → Set l 

RelEnv : (Δ : LEnv) → Setω
RelEnv Δ = ∀ l → l ∈ Δ → Σ (Type [] l) REL

REdrop : RelEnv (l ∷ Δ) → RelEnv Δ
REdrop ρ l x = ρ l (there x)

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
        LRV′ (T₁ ⇒ T₂) ρ (ƛ e , v-ƛ) f =
          ∀ (w : Value (Tsub (subst←RE ρ) T₁)) →
          ∀ (z : ⟦ Tsub (subst←RE ρ) T₁ ⟧ []) →
          LRV′ T₁ ρ w z →
          ∃[ v ] (e [ exp w ]E ⇓ v) ∧ LRV′ T₂ ρ v (f z)
        LRV′ (`∀α l , T) ρ (Λ l ⇒ e , v-Λ) F =
          ∀ (T′ : Type [] l) →
          ∀ (R : REL T′) →
          ∃[ v ] (e [ T′ ]ET ⇓ v) ∧ 
                 let ρ′ = REext ρ (T′ , R)
                 in LRV′ T ρ′ (subst Value (lemma1 ρ T T′ R) v) {!F (⟦ T′ ⟧ [])!}
        LRV′ `ℕ ρ (# n , v-n) z = n ≡ z

LRV : (T : Type Δ l) → (ρ : RelEnv Δ)
  → Value (Tsub (subst←RE ρ) T) → ⟦ T ⟧ (subst-to-env* (subst←RE ρ) []) → Set l
LRV (` α) ρ v z =
  proj₂ (ρ _ α) v (subst id (sym (subst-var-preserves α (subst←RE ρ) [])) z)
LRV (T₁ ⇒ T₂) ρ (ƛ e , v-ƛ) f =
  ∀ (w : Value (Tsub (subst←RE ρ) T₁)) →
  ∀ (z : ⟦ T₁ ⟧ (subst-to-env* (subst←RE ρ) [])) →
  LRV T₁ ρ w z →
  ∃[ v ] (e [ exp w ]E ⇓ v)
       ∧ LRV T₂ ρ v (f z)
LRV (`∀α l , T) ρ (Λ .l ⇒ e , v-Λ) F =
  ∀ (T′ : Type [] l) →
  ∀ (R : REL T′) →
  ∃[ v ] (e [ T′ ]ET ⇓ v)
       ∧ let ρ′ = REext ρ (T′ , R)
         in LRV T ρ′ (subst Value (lemma1 ρ T T′ R) v) (F (⟦ T′ ⟧ []))
LRV `ℕ ρ (# n , v-n) z =
  n ≡ z

-- closing value substitution

CSub : TSub Δ [] → TEnv Δ → Set
CSub {Δ} σ* Γ = ∀ l {T : Type Δ l} → inn T Γ → Value (Tsub σ* T)

ES←SC : {σ* : TSub Δ []} → CSub σ* Γ → ESub σ* Γ ∅
ES←SC χ = λ l x → proj₁ (χ l x)

Csub : {Γ : TEnv Δ} {σ* : TSub Δ []} → CSub σ* Γ → Expr Δ Γ T → Expr [] ∅ (Tsub σ* T)
Csub {σ* = σ*} χ e = Esub σ* (ES←SC χ) e

Cdrop : ∀ {l} {T : Type Δ l} → CSub σ* (T ◁ Γ) → CSub σ* Γ
Cdrop χ _ x = χ _ (there x)

Cextend : ∀ {l} {T : Type Δ l} → CSub σ* Γ → Value (Tsub σ* T) → CSub σ* (T ◁ Γ)
Cextend χ v _ here = v
Cextend χ v _ (there x) = χ _ x

Cextend-Eext : ∀ {l} {T : Type Δ l} → (χ : CSub σ* Γ) → (w : Value (Tsub σ* T)) → 
  ES←SC (Cextend {T = T} χ w) ≡ Eextₛ _ (ES←SC χ) (exp w)
Cextend-Eext {Δ = Δ} {σ* = σ*} {Γ = Γ} {T = T} χ w = fun-ext₂′ aux
  where
    aux : (l : Level) {T′ : Type Δ l} (x : inn T′ (T ◁ Γ)) →
      ES←SC (Cextend χ w) l x ≡ Eextₛ σ* (ES←SC χ) (exp w) l x
    aux l here = refl
    aux l (there x) = refl

Cdrop-Cextend : ∀ {l} {σ* : TSub Δ []} {T : Type Δ l}
  → (χ : CSub σ* Γ) → (v : Value (Tsub σ* T))
  → Cdrop {l = l} {T = T} (Cextend {l = l} χ v) ≡ χ
Cdrop-Cextend {Δ = Δ} {Γ = Γ} {l = l} {T = T} χ v = fun-ext₂′ aux
  where
    aux : ∀ l′ {T′ : Type Δ l′} → (x : inn T′ Γ) → Cdrop {T = T} (Cextend χ v) l′ x ≡ χ l′ x
    aux _ here = refl
    aux _ (there x) = refl
    aux _ (tskip x) = refl

Cdropt : {Γ : TEnv Δ} → CSub σ* (l ◁* Γ) → CSub (Tdropₛ σ*) Γ
Cdropt {σ* = σ*} χ l {T} x = subst (λ T → Σ (Expr [] ∅ T) Val) (assoc-sub-ren T (Twkᵣ Tidᵣ) σ*) (χ _ (tskip x))

Cextt : ∀{l} → CSub σ* Γ → (T′ : Type [] l) → CSub (Textₛ σ* T′) (l ◁* Γ)
Cextt {σ* = σ*} χ T′ _ (tskip {T = T} x) = subst (λ T → Σ (Expr [] ∅ T) Val) (sym (σT≡TextₛσTwkT σ* T)) (χ _ x)

lemma-lrv-wk1 : 
    (ρ : RelEnv (l₁ ∷ Δ))
  → (χ : CSub (subst←RE ρ) (l₁ ◁* Γ))
  → {l : Level} {T : Type Δ l}
  → (x : inn T Γ)
  → Cdropt χ l x ≡ subst (λ T → Σ (Expr [] ∅ T) Val) (assoc-sub-ren T _ (subst←RE ρ)) (χ l (tskip x))
lemma-lrv-wk1 ρ χ {l}{T} here with assoc-sub-ren T (Twkᵣ Tidᵣ) (subst←RE ρ) in eq
... | rrr = refl
lemma-lrv-wk1 ρ χ (there x) = refl
lemma-lrv-wk1 ρ χ (tskip x) = refl

lemma-lrv-wk2 :
  (ρ     : RelEnv (l ∷ Δ))
  (T₁ : Type Δ l₁) (T₂ : Type Δ l₂)
  → (e : Expr [] (Tsub (λ l₂ x₁ → proj₁ (ρ l₂ x₁)) (Tren (λ z₁ → there) T₁) ◁ ∅)
                 (Tsub (λ l₂ x₁ → proj₁ (ρ l₂ x₁)) (Tren (λ z₁ → there) T₂)))
  -- → subst (λ T → Σ (Expr [] ∅ T) Val)
  --         (assoc-sub-ren (T₁ ⇒ T₂) (Twkᵣ Tidᵣ) (subst←RE ρ))
  --         ((ƛ e) , v-ƛ)
  → let eq = cong₂ _,_ (assoc-sub-ren T₁ (Twkᵣ Tidᵣ) (subst←RE ρ)) (assoc-sub-ren T₂ (Twkᵣ Tidᵣ) (subst←RE ρ)) in
    subst (λ{ (T₁ , T₂) → Σ (Expr [] ∅ (T₁ ⇒ T₂)) Val }) eq ((ƛ e) , v-ƛ)
  ≡ ((ƛ (subst (λ{ (T₁ , T₂) → Expr [] (T₁ ◁ ∅) T₂ }) eq e)) , v-ƛ)
lemma-lrv-wk2 ρ T₁ T₂ e =
  subst-application′ (λ{ (T₁ , T₂) → Expr [] (T₁ ◁ ∅) T₂ }) (λ{ (T₁ , T₂) e → (ƛ e) , v-ƛ }) (cong₂ _,_ (assoc-sub-ren T₁ (Twkᵣ Tidᵣ) (subst←RE ρ)) (assoc-sub-ren T₂ (Twkᵣ Tidᵣ) (subst←RE ρ)))

lemma-lrv-wk3 :
  (ρ     : RelEnv (l ∷ Δ))
  (T₁ : Type Δ l₁) (T₂ : Type Δ l₂)
  → (e : Expr [] (Tsub (λ l₂ x₁ → proj₁ (ρ l₂ x₁)) (Tren (λ z₁ → there) T₁) ◁ ∅)
                 (Tsub (λ l₂ x₁ → proj₁ (ρ l₂ x₁)) (Tren (λ z₁ → there) T₂)))
  → let eq = cong₂ _,_ (assoc-sub-ren T₁ (Twkᵣ Tidᵣ) (subst←RE ρ)) (assoc-sub-ren T₂ (Twkᵣ Tidᵣ) (subst←RE ρ)) in
    subst (λ T → Σ (Expr [] ∅ T) Val)
          (assoc-sub-ren (T₁ ⇒ T₂) (Twkᵣ Tidᵣ) (subst←RE ρ))
          ((ƛ e) , v-ƛ)
  ≡ ((ƛ (subst (λ{ (T₁ , T₂) → Expr [] (T₁ ◁ ∅) T₂ }) eq e)) , v-ƛ)
lemma-lrv-wk3 {l₁ = l₁}{l₂ = l₂} ρ T₁ T₂ e =
  let eq = cong₂ _,_ (assoc-sub-ren T₁ (Twkᵣ Tidᵣ) (subst←RE ρ)) (assoc-sub-ren T₂ (Twkᵣ Tidᵣ) (subst←RE ρ)) in
  sym (dist-subst' {F = F} {G = G} h aux eq (assoc-sub-ren (T₁ ⇒ T₂) (Twkᵣ Tidᵣ) (subst←RE ρ)) e)
  where
    F : Type [] l₁ × Type [] l₂ → Set
    F (T₁ , T₂) = Expr [] (T₁ ◁ ∅) T₂
    G : Type [] (l₁ ⊔ l₂) → Set
    G T = Σ (Expr [] ∅ T) Val
    h : Type [] l₁ × Type [] l₂ → Type [] (l₁ ⊔ l₂)
    h (T₁ , T₂) = T₁ ⇒ T₂
    aux' : Type [] l₁ × Type [] l₂ → Set
    aux' (T₁ , T₂) = Expr [] (T₁ ◁ ∅) T₂ 
    aux : ∀ {a : Σ (Type [] l₁) (λ _ → Type [] l₂)} →
      F a → G (h a)
    aux {a = (T₁ , T₂)} x = (ƛ (subst aux' (cong₂ _,_ {!  !} {!   !}) e)) , v-ƛ


LRVwk : ∀ {Δ}{l}{l₁}
  → (T : Type Δ l)
  → (Γ : TEnv Δ)
  → (ρ : RelEnv (l₁ ∷ Δ))
  → (χ : CSub (subst←RE ρ) (l₁ ◁* Γ))
  → (γ : Env (l₁ ∷ Δ) (l₁ ◁* Γ) (subst-to-env* (subst←RE ρ) []))
  → (x : inn T Γ)
  → LRV T (REdrop ρ) (Cdropt χ l x) (Gdropt (subst←RE ρ) γ l T x)
  → LRV (Twk T) ρ (χ l (tskip x)) (γ l (Twk T) (tskip x))
LRVwk (` α) Γ ρ χ γ x lrv = lrv
LRVwk (T₁ ⇒ T₂) Γ ρ χ γ x lrv with χ _ (tskip x)
... | ƛ e , v-ƛ = 
  λ w z lrv-T →
    -- subst F ≡T ((ƛ e) , v-ƛ) --> (subst G ≡T (ƛ e) , v-ƛ)
    let hyp = lrv in
    ({!!} , {!!}) , {!!}
LRVwk (`∀α l , T) Γ ρ χ γ x lrv with χ _ (tskip x)
... | Λ l ⇒ e , v-Λ =
  λ T′ R → {!!}
LRVwk `ℕ Γ ρ χ γ x lrv
  with χ zero (tskip x) | γ zero `ℕ (tskip x)
... | # n , v-n | z = lrv

-- extended LR on environments

LRG : (Γ : TEnv Δ) → (ρ : RelEnv Δ)
  → CSub (subst←RE ρ) Γ
  → let η = subst-to-env* (subst←RE ρ) [] in Env Δ Γ η → Set (levelEnv Γ)
LRG ∅ ρ χ γ = ⊤
LRG (T ◁ Γ) ρ χ γ = LRV T ρ (χ _ here) (γ _ T here) ∧  LRG Γ ρ (Cdrop χ) (ENVdrop Γ _ γ)
LRG (l ◁* Γ) ρ χ γ = LRG Γ (REdrop ρ) (Cdropt χ) (Gdropt (subst←RE ρ) γ)

-- environment lookup

LRV←LRG : (Γ : TEnv Δ) (ρ : RelEnv Δ) (χ : CSub (subst←RE ρ) Γ) (γ : Env Δ Γ (subst-to-env* (subst←RE ρ) [])) (T : Type Δ l)
  → LRG Γ ρ χ γ
  → (x : inn T Γ)
  → LRV T ρ (χ l x) (γ l T x)
LRV←LRG .(T ◁ _) ρ χ γ T (lrv , lrg) here = lrv
LRV←LRG (_ ◁ Γ) ρ χ γ T (lrv , lrg) (there x) = LRV←LRG _ ρ (Cdrop χ) (ENVdrop Γ _ γ) T lrg x
LRV←LRG {l = l} (_ ◁* Γ) ρ χ γ Tw lrg (tskip {T = T} x)
  = let r = LRV←LRG {l = l} Γ (REdrop ρ) (Cdropt χ) (Gdropt (subst←RE ρ) γ) T lrg x
    in LRVwk T Γ ρ χ γ x r

Cextend-Elift : ∀ {σ* : TSub Δ []} {Γ : TEnv Δ}{l}{T : Type Δ l}{l′}{T′ : Type Δ l′}
  → (χ : CSub σ* Γ)
  → (w : Value (Tsub σ* T))
  → (e : Expr Δ (T ◁ Γ) T′)
  → Csub (Cextend χ w) e ≡ (Esub σ* (Eliftₛ σ* (ES←SC χ)) e [ exp w ]E)
Cextend-Elift {σ* = σ*} χ w e = begin
    Csub (Cextend χ w) e
  ≡⟨⟩
    Esub σ* (ES←SC (Cextend χ w)) e
  ≡⟨ cong (λ σ → Esub σ* σ e) (Cextend-Eext χ w) ⟩
    Esub σ* (Eextₛ σ* (ES←SC χ) (exp w)) e
  ≡⟨ {!   !} ⟩
    Esub σ* (Eliftₛ σ* (ES←SC χ)) e [ exp w ]E
  ∎

Gdropt-ext≡id : (ρ : RelEnv Δ) (γ : Env Δ Γ (subst-to-env* (subst←RE ρ) [])) (T′ : Type [] l) (R : REL T′)
  → (Gdropt (subst←RE (REext ρ (T′ , R))) (extend-tskip γ)) ≡ω γ
Gdropt-ext≡id ρ γ T′ R =
  fun-ext-llω-ω (λ x y z → subst-subst-sym (Tren*-preserves-semantics (λ x₁ → refl) y))
 