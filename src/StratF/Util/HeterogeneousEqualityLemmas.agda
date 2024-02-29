module StratF.Util.HeterogeneousEqualityLemmas where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)
module R = H.≅-Reasoning

-- Higher arity versions of heterogeneous cong

Hcong₃ :
  ∀ {a b c d}
    {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} {D : ∀ x → (y : B x) → C x y → Set d}
    {x y u v i j}
    (f : (x : A) (y : B x) (z : C x y) → D x y z) →
    x ≅ y →
    u ≅ v →
    i ≅ j →
    f x u i ≅ f y v j
Hcong₃ f refl refl refl = refl

Hcong₄ :
  ∀ {a b c d e}
    {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} {D : ∀ x → (y : B x) → C x y → Set d}
    {E : ∀ x → (y : B x) → (z : C x y) → D x y z → Set e}
    {x y u v i j p q}
    (f : (x : A) (y : B x) (z : C x y) (w : D x y z) → E x y z w) →
    x ≅ y →
    u ≅ v →
    i ≅ j →
    p ≅ q →
    f x u i p ≅ f y v j q
Hcong₄ f refl refl refl refl = refl

-- Functional Extensionality specialized for substitutions and renamings 

open import StratF.Util.Extensionality
open import StratF.Types
open import StratF.TypeSubstitution
open import StratF.Expressions
open import StratF.ExprSubstitution

fun-ext-h-ERen :
  ∀ {σ* σ*′ : TRen Δ₁ Δ₂} {Γ₁ : TEnv Δ₁}{Γ₂ Γ₂′ : TEnv Δ₂}
    {σ : ERen σ* Γ₁ Γ₂} {σ′ : ERen σ*′ Γ₁ Γ₂′} →
    σ* ≡ σ*′ →
    Γ₂ ≡ Γ₂′ →
    (∀ l T x → σ l T x ≅ σ′ l T x) →
    σ ≅ σ′
fun-ext-h-ERen {Δ₁} {Δ₂} {σ*} {σ*′} {Γ₁} {Γ₂} {Γ₂′} {σ} {σ′} eq-σ eq-Γ₂ f =
  fun-ext-h (λ l → dep-ext λ T → dep-ext λ x → cong₂ (λ ■₁ ■₂ → inn (Tren ■₂ T) ■₁) eq-Γ₂ eq-σ) λ l →
  fun-ext-h               (λ T → dep-ext λ x → cong₂ (λ ■₁ ■₂ → inn (Tren ■₂ T) ■₁) eq-Γ₂ eq-σ) λ T →
  fun-ext-h                             (λ x → cong₂ (λ ■₁ ■₂ → inn (Tren ■₂ T) ■₁) eq-Γ₂ eq-σ) λ x →
  f l T x

fun-ext-h-ESub :
  ∀ {σ* σ*′ : TSub Δ₁ Δ₂} {Γ₁ : TEnv Δ₁}{Γ₂ Γ₂′ : TEnv Δ₂}
    {σ : ESub σ* Γ₁ Γ₂} {σ′ : ESub σ*′ Γ₁ Γ₂′} →
    σ* ≡ σ*′ →
    Γ₂ ≡ Γ₂′ →
    (∀ l T x → σ l T x ≅ σ′ l T x) →
    σ ≅ σ′
fun-ext-h-ESub {Δ₁} {Δ₂} {σ*} {σ*′} {Γ₁} {Γ₂} {Γ₂′} {σ} {σ′} eq-σ eq-Γ₂ f =
  fun-ext-h (λ l → dep-ext λ T → dep-ext λ x → cong₂ (λ ■₁ ■₂ → Expr Δ₂ ■₁ (Tsub ■₂ T)) eq-Γ₂ eq-σ) λ l →
  fun-ext-h               (λ T → dep-ext λ x → cong₂ (λ ■₁ ■₂ → Expr Δ₂ ■₁ (Tsub ■₂ T)) eq-Γ₂ eq-σ) λ T →
  fun-ext-h                             (λ x → cong₂ (λ ■₁ ■₂ → Expr Δ₂ ■₁ (Tsub ■₂ T)) eq-Γ₂ eq-σ) λ x →
  f l T x

