-- This file contains the lemmas from SubstProperties.agda, but proven
-- with heterogeneous equality.
--
-- All proofs are without matching to show that they could also be
-- used directly at the callsite as they're just syntactic sugar.
--
-- Lemmas used involve exclusively:
-- - `H.≡-subst-removable`, `≡-subst₂-removable`;
-- - `H.cong`,  `H.cong₂`, `Hcong₃`, and `Hcong₄`;
-- - `fun-ext-h'` (a stronger form of fun-ext for heterogenous equality. Can be derived from regular `fun-ext`.

module StratF.Util.SubstPropertiesHeq where

open import Level
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open import StratF.Util.Extensionality

open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)
module R = H.≅-Reasoning
open import Function using (_$_)

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

Hcong₅ :
  ∀ {a b c d e e'}
    {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} {D : ∀ x → (y : B x) → C x y → Set d}
    {E : ∀ x → (y : B x) → (z : C x y) → D x y z → Set e}
    {F : ∀ x → (y : B x) → (z : C x y) → (w : D x y z) → E x y z w → Set e'}
    {x y u v i j p q r s}
    (f : (x : A) (y : B x) (z : C x y) (w : D x y z) (u : E x y z w) → F x y z w u) →
    x ≅ y →
    u ≅ v →
    i ≅ j →
    p ≅ q →
    r ≅ s →
    f x u i p r ≅ f y v j q s
Hcong₅ f refl refl refl refl refl = refl

≡-subst₂-removable :
  ∀ {ℓ₁} {ℓ₂} {ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂}
    (F : A → B → Set ℓ₃) {x y a b} (eq₁ : x ≡ y) (eq₂ : a ≡ b) (z : F x a) →
  subst₂ F eq₁ eq₂ z ≅ z
≡-subst₂-removable P refl refl z = refl

subst-irrelevant : 
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ : A}
    {F : A → Set ℓ₁}
    (eq eq' : a₁ ≡ a₂)
    (x : F a₁) 
  → subst F eq x ≡ subst F eq' x
subst-irrelevant {ℓ} {ℓ₁} {A} {a₁} {a₂} {F} eq eq' x =
  H.≅-to-≡ $
  R.begin
    subst F eq x
  R.≅⟨ H.≡-subst-removable F eq x ⟩
    x
  R.≅⟨ H.sym (H.≡-subst-removable F eq' x) ⟩
    subst F eq' x
  R.∎

elim-subst :
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ : A}
  → (F : A → Set ℓ₁)
  → (a₂≡a₁ : a₂ ≡ a₁)
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (x : F a₁)
  → subst F a₂≡a₁ (subst F a₁≡a₂ x) ≡ x
elim-subst {ℓ} {ℓ₁} {A} {a₁} {a₂} F a₂≡a₁ a₁≡a₂ x =
  H.≅-to-≡ $
  R.begin
    subst F a₂≡a₁ (subst F a₁≡a₂ x)
  R.≅⟨ H.≡-subst-removable F a₂≡a₁ _ ⟩
    subst F a₁≡a₂ x
  R.≅⟨ H.≡-subst-removable F a₁≡a₂ _ ⟩
    x
  R.∎

elim-subst₃ :
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ a₃ : A}
  → (F : A → Set ℓ₁)
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (a₃≡a₁ : a₃ ≡ a₁)
  → (a₂≡a₃ : a₂ ≡ a₃)
  → (x : F a₂)
  → subst F a₁≡a₂ (subst F a₃≡a₁ (subst F a₂≡a₃ x)) ≡ x
elim-subst₃ _ refl refl refl _ = refl
-- same as above

dist-subst :
  ∀ {ℓ₁ ℓ₂}
    {A A′ : Set ℓ₁} {B B′ : Set ℓ₂}
  → (f : A → B)
  → (A≡A′ : A′ ≡ A)
  → (A→B≡A′→B′ : (A → B) ≡ (A′ → B′))
  → (B≡B′ : B ≡ B′)
  → (x : A′) 
  → subst id B≡B′ (f (subst id A≡A′ x)) ≡ subst id A→B≡A′→B′ f x
dist-subst {ℓ₁} {ℓ₂} {A} {A′} {B} {B′} f A≡A′ A→B≡A′→B′ B≡B′ x =
  H.≅-to-≡ $
  R.begin
    subst id B≡B′ (f (subst id A≡A′ x))
  R.≅⟨ H.≡-subst-removable id B≡B′ _ ⟩
    f (subst id A≡A′ x)
  R.≅⟨ Hcong₄ {A = Set ℓ₁} {B = λ _ → Set ℓ₂} {C = λ A B → (A → B)} {D = λ A B _ → A} (λ _ _ ■₁ ■₂ → ■₁ ■₂)
              (H.≡-to-≅ (sym A≡A′))
              (H.≡-to-≅ B≡B′)
              (H.sym (H.≡-subst-removable id A→B≡A′→B′ f))
              (H.≡-subst-removable id A≡A′ x) ⟩
    subst id A→B≡A′→B′ f x
  R.∎

dist-subst-id : 
  ∀ {ℓ} {A B C : Set ℓ}
  → (A≡B : B ≡ A)
  → (B≡C : C ≡ B)
  → (A≡C : C ≡ A)
  → (x : C)
  → subst id A≡B (subst id B≡C x) ≡ subst id A≡C x
dist-subst-id {ℓ} {A} {B} {C} A≡B B≡C A≡C x =
  H.≅-to-≡ $
  R.begin
    subst id A≡B (subst id B≡C x)
  R.≅⟨ H.≡-subst-removable id A≡B _ ⟩
    subst id B≡C x
  R.≅⟨ H.≡-subst-removable id B≡C _ ⟩
    x
  R.≅⟨ H.sym (H.≡-subst-removable id A≡C _) ⟩
    subst id A≡C x
  R.∎

dist-subst′ :
  ∀ {ℓ₁ ℓ₂}
    {A A′ : Set ℓ₁} {B B′ : Set ℓ₂}
  → (f : A → B)
  → (A≡A′ : A ≡ A′)
  → (A→B≡A′→B′ : (A → B) ≡ (A′ → B′))
  → (B≡B′ : B ≡ B′)
  → (x : A) 
  → subst id A→B≡A′→B′ f (subst id A≡A′ x) ≡ subst id B≡B′ (f x)
dist-subst′ {ℓ₁} {ℓ₂} {A} {A′} {B} {B′} f A≡A′ A→B≡A′→B′ B≡B′ x =
  H.≅-to-≡ $
  R.begin
    subst id A→B≡A′→B′ f (subst id A≡A′ x)
  R.≅⟨ Hcong₄ {A = Set ℓ₁} {B = λ _ → Set ℓ₂}
              {C = λ ■₁ ■₂ → (■₁ → ■₂)} {D = λ ■₁ ■₂ _ → ■₁}
              (λ _ _ ■₁ ■₂ → ■₁ ■₂)
              (H.≡-to-≅ (sym A≡A′)) (H.≡-to-≅ (sym B≡B′))
              (H.≡-subst-removable id A→B≡A′→B′ _)
              (H.≡-subst-removable id A≡A′ _)
              ⟩
    f x
  R.≅⟨ H.sym (H.≡-subst-removable id B≡B′ _) ⟩
    subst id B≡B′ (f x)
  R.∎

dist-subst′′ :
  ∀ {ℓ₁ ℓ₂}
    {A : Set ℓ₁} {B B′ : A → Set ℓ₂} 
  → (a : A) 
  → (f : (a : A) → B a)
  → (A→B≡A′→B′ : ((a : A) → B a) ≡ ((a : A) → B′ a))
  → (B≡B′ : (a : A) → B a ≡ B′ a)
  → subst id (B≡B′ a) (f a) ≡ subst id A→B≡A′→B′ f a
dist-subst′′ {ℓ₁} {ℓ₂} {A} {B} {B′} a f A→B≡A′→B′ B≡B′ =
  H.≅-to-≡ $
  R.begin
    subst id (B≡B′ a) (f a)
  R.≅⟨ H.≡-subst-removable id (B≡B′ a) (f a) ⟩
    f a
  R.≅⟨ H.cong₂ {A = A → Set ℓ₂} {B = λ ■ → (a : A) → ■ a} (λ _ ■ → ■ a)
               (H.≡-to-≅ (fun-ext B≡B′))
               (H.sym (H.≡-subst-removable id A→B≡A′→B′ f)) ⟩
    subst id A→B≡A′→B′ f a
  R.∎

subst-elim′′′ :
  ∀ {ℓ}
    {A A₁ A₂ A₃ A₄ A₅ : Set ℓ} 
  → (a : A₄) 
  → (A≡A₁ : A ≡ A₁)
  → (A₂≡A : A₂ ≡ A)
  → (A₃≡A₂ : A₃ ≡ A₂)
  → (A₃≡A₄ : A₄ ≡ A₃)
  → (A≡A' : A₅ ≡ A₁)
  → (A≡A₄ : A₄ ≡ A₅)
  → subst id A≡A₁ (subst id A₂≡A (subst id A₃≡A₂ (subst id A₃≡A₄ a))) ≡ subst id A≡A' (subst id A≡A₄ a)
subst-elim′′′ _ refl refl refl refl refl refl = refl  
-- works, same as above

subst-shuffle′′′′ :
  ∀ {ℓ}
    {A₁ A₂ A₃ A₄ : Set ℓ} 
  → (a : A₃) 
  → (A≡A₁ : A₁ ≡ A₂)
  → (A≡A₂ : A₃ ≡ A₁)
  → (A≡A₃ : A₄ ≡ A₂)
  → (A≡A₄ : A₃ ≡ A₄)
  → subst id A≡A₁ (subst id A≡A₂ a) ≡ subst id A≡A₃ (subst id A≡A₄ a)
subst-shuffle′′′′ {ℓ} {A₁} {A₂} {A₃} {A₄} a A≡A₁ A≡A₂ A≡A₃ A≡A₄ =
  H.≅-to-≡ $
  R.begin
    subst id A≡A₁ (subst id A≡A₂ a)
  R.≅⟨ H.≡-subst-removable id A≡A₁ _ ⟩
    subst id A≡A₂ a
  R.≅⟨ H.≡-subst-removable id A≡A₂ _ ⟩
    a
  R.≅⟨ H.sym (H.≡-subst-removable id A≡A₄ _) ⟩
    subst id A≡A₄ a
  R.≅⟨ H.sym (H.≡-subst-removable id A≡A₃ _) ⟩
    subst id A≡A₃ (subst id A≡A₄ a)
  R.∎

dist-subst' :
  ∀ {ℓ ℓ' ℓ₁ ℓ₂} {A : Set ℓ} {B : Set ℓ'} {a₁ a₂ : A}
    {F : A → Set ℓ₁} {G : B → Set ℓ₂}
  → (a→b : A → B)
  → (f : ∀ {a} → F a → G (a→b a))
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (b₁≡b₂ : a→b a₁ ≡ a→b a₂)
  → (x : F a₁) 
  → f {a₂} (subst F a₁≡a₂ x) ≡ subst G b₁≡b₂ (f {a₁} x)
dist-subst' {ℓ} {ℓ'} {ℓ₁} {ℓ₂} {A} {B} {a₁} {a₂} {F} {G} a→b f a₁≡a₂ b₁≡b₂ x =
  H.≅-to-≡ $
  R.begin
    f (subst F a₁≡a₂ x)
  R.≅⟨ H.cong₂ {B = F} (λ _ ■ → f ■) (H.≡-to-≅ (sym a₁≡a₂)) (H.≡-subst-removable F a₁≡a₂ _) ⟩
    f x
  R.≅⟨ H.sym (H.≡-subst-removable G b₁≡b₂ _) ⟩
    subst G b₁≡b₂ (f x)
  R.∎

dist-subst′′′ :
  ∀ {ℓ₁ ℓ₂}
    {A : Set ℓ₁} {B : A → Set ℓ₂} 
  → (a : A) 
  → (a′ : A)
  → (f : (a : A) → B a)
  → (a≡a′ : a ≡ a′)
  → (Ba′≡Ba : B a′ ≡ B a)
  → f a ≡ subst id Ba′≡Ba (f a′)
dist-subst′′′ {ℓ₁} {ℓ₂} {A} {B} a a′ f a≡a′ Ba′≡Ba =
  H.≅-to-≡ $
  R.begin
    f a
  R.≅⟨ H.cong f (H.≡-to-≅ a≡a′) ⟩
    f a′
  R.≅⟨ H.sym (H.≡-subst-removable id Ba′≡Ba _) ⟩
    subst id Ba′≡Ba (f a′)
  R.∎

subst-elim′′′′ :
  ∀ {ℓ₁ ℓ₂}
    {T : Set ℓ₁} 
  → (F : T → Set ℓ₁)
  → (G : T → Set ℓ₁)
  → {t₁ t₂ : T}
  → (f : {t : T} → (F t) → (G t) → Set ℓ₂)
  → (a : F t₁)
  → (b : G t₁)
  → (t₁≡t₂ : t₁ ≡ t₂)
  → f {t₁} a b ≡ f {t₂} (subst F t₁≡t₂ a) (subst G t₁≡t₂ b)
subst-elim′′′′ {ℓ₁} {ℓ₂} {T} F G {t₁} {t₂} f a b t₁≡t₂ =
  H.≅-to-≡ $
  R.begin
    f a b
  R.≅⟨ Hcong₃ {B = λ ■₁ → F ■₁} {C = λ ■₁ _ → G ■₁} (λ _ ■₁ ■₂ → f ■₁ ■₂)
              (H.≡-to-≅ t₁≡t₂)
              (H.sym (H.≡-subst-removable F t₁≡t₂ _))
              (H.sym (H.≡-subst-removable G t₁≡t₂ _)) ⟩
    f (subst F t₁≡t₂ a) (subst G t₁≡t₂ b)
  R.∎

subst-swap′′ :
  ∀ {ℓ₁ ℓ₂}
    {T : Set ℓ₁} 
  → (F : T → Set ℓ₁)
  → (G : T → Set ℓ₁)
  → {t₁ t₂ : T}
  → (f : {t : T} → (F t) → (G t) → Set ℓ₂)
  → (a : F t₂)
  → (b : G t₁)
  → (t₁≡t₂ : t₁ ≡ t₂)
  → (t₂≡t₁ : t₂ ≡ t₁)
  → f {t₁} (subst F t₂≡t₁ a) b ≡ f {t₂} a (subst G t₁≡t₂ b)
subst-swap′′ {ℓ₁} {ℓ₂} {T} F G {t₁} {t₂} f a b t₁≡t₂ t₂≡t₁ =
  H.≅-to-≡ $
  R.begin
    f (subst F t₂≡t₁ a) b
  R.≅⟨ Hcong₃ {B = λ ■ → F ■} {C = λ ■ _ → G ■} (λ _ ■₁ ■₂ → f ■₁ ■₂)
              (H.≡-to-≅ t₁≡t₂)
              (H.≡-subst-removable F t₂≡t₁ _)
              (H.sym (H.≡-subst-removable G t₁≡t₂ _)) ⟩
    f a (subst G t₁≡t₂ b)
  R.∎

subst-cong :
  ∀ {ℓ}{ℓ₁}{ℓ₂}
    {A₁ : Set ℓ₁}
    {A₂ : Set ℓ₂}
  → (F : A₁ → Set ℓ)
  → (G : A₂ → A₁)
  → {x y : A₂}
  → (x≡y : x ≡ y)
  → (a : F (G x))
  → subst F (cong G x≡y) a ≡ subst (λ z → F (G z)) x≡y a
subst-cong {ℓ} {ℓ₁} {ℓ₂} {A₁} {A₂} F G {x} {y} x≡y a =
  H.≅-to-≡ $
  R.begin
    subst F (cong G x≡y) a
  R.≅⟨ H.≡-subst-removable F (cong G x≡y) _ ⟩
    a
  R.≅⟨ H.sym (H.≡-subst-removable (λ z → F (G z)) x≡y _) ⟩
    subst (λ z → F (G z)) x≡y a
  R.∎

subst-swap :
  ∀ {ℓ₁}{ℓ₂} {A : Set ℓ₁}
    {F : (a : A) → Set ℓ₂}
    {a₁ a₂ : A}
    (eq : a₁ ≡ a₂)
    (x : F a₁)
    (y : F a₂)
  → subst F eq x ≡ y
  → x ≡ subst F (sym eq) y
subst-swap {ℓ₁} {ℓ₂} {A} {F} {a₁} {a₂} eq x y x₁ =
  H.≅-to-≡ $
  R.begin
    x
  R.≅⟨ H.sym (H.≡-subst-removable F eq _) ⟩
    subst F eq x
  R.≅⟨ H.≡-to-≅ x₁ ⟩
    y
  R.≅⟨ H.sym (H.≡-subst-removable F (sym eq) _) ⟩
    subst F (sym eq) y
  R.∎

subst-swap′ :
  ∀ {ℓ₁}{ℓ₂} {A : Set ℓ₁}
    {F : (a : A) → Set ℓ₂}
    {a₁ a₂ : A}
    (eq : a₁ ≡ a₂)
    (x : F a₁)
    (y : F a₂)
  → subst F (sym eq) y ≡ x
  → y ≡ subst F eq x
subst-swap′ refl x y refl = refl
-- works, same as above

subst₂-swap′ :
  ∀ {ℓ₁}{ℓ₂}{ℓ₃}
    {A : Set ℓ₁}{B : Set ℓ₂}
    {F : (a : A) (b : B) → Set ℓ₃}
    {a₁ a₂ : A}
    {b₁ b₂ : B}
    (eq₁ : a₁ ≡ a₂)
    (eq₂ : b₁ ≡ b₂)
    (x : F a₁ b₁)
    (y : F a₂ b₂)
  → y ≡ subst₂ F eq₁ eq₂ x
  → subst₂ F (sym eq₁) (sym eq₂) y ≡ x
subst₂-swap′ {ℓ₁} {ℓ₂} {ℓ₃} {A} {B} {F} {a₁} {a₂} {b₁} {b₂} eq₁ eq₂ x y x₁ =
  H.≅-to-≡ $
  R.begin
    subst₂ F (sym eq₁) (sym eq₂) y
  R.≅⟨ ≡-subst₂-removable F (sym eq₁) (sym eq₂) y ⟩
    y
  R.≅⟨ H.≡-to-≅ x₁ ⟩
    subst₂ F eq₁ eq₂ x
  R.≅⟨ ≡-subst₂-removable F eq₁ eq₂ x ⟩
    x
  R.∎

subst-swap-eq :
  ∀ {ℓ₁}{ℓ₂} {A : Set ℓ₁}
    {F : (a : A) → Set ℓ₂}
    {a₁ a₂ : A}
    (eq : a₁ ≡ a₂)
    (x : F a₁)
    (y : F a₂)
  → (subst F eq x ≡ y) ≡ (x ≡ subst F (sym eq) y)
subst-swap-eq {ℓ₁} {ℓ₂} {A} {F} {a₁} {a₂} eq x y =
  H.≅-to-≡ $
  R.begin
    subst F eq x ≡ y
  R.≅⟨ Hcong₃ {A = A} {B = λ ■ → F ■} {C = λ ■ _ → F ■}
              (λ _ ■₁ ■₂ → ■₁ ≡ ■₂)
              (H.≡-to-≅ (sym eq))
              (H.≡-subst-removable F eq x)
              (H.sym (H.≡-subst-removable F (sym eq) y)) ⟩
    x ≡ subst F (sym eq) y
  R.∎

subst-swap-eq′ :
  ∀ {ℓ₁}{ℓ₂} {A : Set ℓ₁}
    {F : (a : A) → Set ℓ₂}
    {a₁ a₂ : A}
    (eq : a₂ ≡ a₁)
    (x : F a₁)
    (y : F a₂)
  → (x ≡ subst F eq y) ≡ (subst F (sym eq) x ≡ y)
subst-swap-eq′ {ℓ₁} {ℓ₂} {A} {F} {a₁} {a₂} eq x y =
  H.≅-to-≡ $
  R.begin
    x ≡ subst F eq y
  R.≅⟨ Hcong₃ {A = A} {B = λ ■ → F ■} {C = λ ■ _ → F ■}
              (λ _ ■₁ ■₂ → ■₁ ≡ ■₂)
              (H.≡-to-≅ (sym eq))
              (H.sym (H.≡-subst-removable F (sym eq) x))
              (H.≡-subst-removable F eq y) ⟩
    subst F (sym eq) x ≡ y
  R.∎

subst-id :
  ∀ {ℓ ℓ′} {A : Set ℓ′} {a : A}
  → (F : A → Set ℓ)
  → (eq : a ≡ a)
  → {x : F a}
  → subst F eq x ≡ x
subst-id {ℓ} {ℓ′} {A} {a} F eq {x} =
  H.≅-to-≡ $
  R.begin
    subst F eq x
  R.≅⟨ H.≡-subst-removable F eq x ⟩
    x
  R.∎

eta-subst : ∀ {lv lz lr}
  → {V : Set lv} {Z₁ Z₂ : Set lz} {R : Set lr}
  → (h : V → Z₁ → R)
  → (z₁≡z₂ : Z₁ ≡ Z₂)
  → subst (λ Z → V → Z → R) z₁≡z₂ h ≡ λ v → subst (λ Z → Z → R) z₁≡z₂ (h v)
eta-subst {lv} {lz} {lr} {V} {Z₁} {Z₂} {R} h z₁≡z₂ =
  H.≅-to-≡ $
  R.begin
    subst (λ Z → (V → Z → R)) z₁≡z₂ h
  R.≅⟨ H.≡-subst-removable (λ Z → (V → Z → R)) z₁≡z₂ h ⟩
    h
  R.≅⟨ refl ⟩
    (λ v → h v)
  R.≅⟨ fun-ext-h (λ _ → cong (λ ■ → ■ → R) z₁≡z₂) (λ v → H.sym (H.≡-subst-removable (λ Z → (Z → R)) z₁≡z₂ (h v))) ⟩
    (λ v → subst (λ Z → (Z → R)) z₁≡z₂ (h v))
  R.∎

fun-ext-h' :
  ∀ {a} {b} {A₁ A₂ : Set a} {B₁ : A₁ → Set b} {B₂ : A₂ → Set b}
  {f₁ : (x : A₁) → B₁ x} {f₂ : (x : A₂) → B₂ x} →
  A₁ ≡ A₂ →
  (∀ x y → x ≅ y → B₁ x ≡ B₂ y) → (∀ x y → x ≅ y → f₁ x ≅ f₂ y) → f₁ ≅ f₂
fun-ext-h' {a} {b} {A₁} {A₂} {B₁} {B₂} {f₁} {f₂} refl f g = fun-ext-h (λ x → f x x refl) (λ x → g x x refl)

app-subst : ∀ {lz lr}
  →  {Z₁ Z₂ : Set lz} {R : Set lr}
  → (h : Z₁ → R)
  → (z₁≡z₂ : Z₁ ≡ Z₂)
  → (λ z → h (subst id (sym z₁≡z₂) z)) ≡ subst (λ Z → Z → R) z₁≡z₂ h
app-subst {lz} {lr} {Z₁} {Z₂} {R} h z₁≡z₂ =
  H.≅-to-≡ $
  R.begin
    (λ z → h (subst id (sym z₁≡z₂) z))
  R.≅⟨ fun-ext-h' (sym z₁≡z₂) (λ x y x₁ → refl) (λ { x y refl → H.cong h (H.≡-subst-removable id (sym z₁≡z₂) x) }) ⟩
    (λ z → h z)
  R.≅⟨ refl ⟩
    h
  R.≅⟨ H.sym (H.≡-subst-removable (λ Z → Z → R) z₁≡z₂ h) ⟩
    subst (λ Z → Z → R) z₁≡z₂ h
  R.∎

subst₂→subst : ∀ {l a b}{A : Set a}{B : Set b}
  → {a : A}{b b′ : B}
  → (F : A → B → Set l)
  → (eq : b ≡ b′)
  → (x : F a b)
  → subst₂ F refl eq x ≡ subst (F a) eq x
subst₂→subst {l} {a} {b} {A} {B} {a₁} {b₁} {b′} F eq x =
  H.≅-to-≡ $
  R.begin
    subst₂ F refl eq x
  R.≅⟨ ≡-subst₂-removable F refl eq x ⟩
    x
  R.≅⟨ H.sym (H.≡-subst-removable (F a₁) eq x) ⟩
    subst (F a₁) eq x
  R.∎

eta-subst₂ : ∀ {lv lz lr}
  → {V₁ V₂ : Set lv} {Z₁ Z₂ : Set lz} {R : Set lr}
  → (h : V₁ → Z₁ → R)
  → (v₁≡v₂ : V₁ ≡ V₂)
  → (z₁≡z₂ : Z₁ ≡ Z₂)
  → subst₂ (λ V Z → V → Z → R) v₁≡v₂ z₁≡z₂ h ≡ λ v₂ z₂ → h (subst id (sym v₁≡v₂) v₂) (subst id (sym z₁≡z₂) z₂)
eta-subst₂ {lv} {lz} {lr} {V₁} {V₂} {Z₁} {Z₂} {R} h v₁≡v₂ z₁≡z₂ =
  H.≅-to-≡ $
  R.begin
    subst₂ (λ V Z → V → Z → R) v₁≡v₂ z₁≡z₂ h
  R.≅⟨ ≡-subst₂-removable (λ V Z → V → Z → R) v₁≡v₂ z₁≡z₂ h ⟩
    h
  R.≅⟨ fun-ext-h' v₁≡v₂ (λ _ _ _ → cong (λ ■ → ■ → R) z₁≡z₂) (λ x y x≅y →
       fun-ext-h' z₁≡z₂ (λ _ _ _ → refl) (λ x' y' x'≅y' →
       H.cong₂ h (H.trans x≅y (H.sym (H.≡-subst-removable id (sym v₁≡v₂) y)))
                 (H.trans x'≅y' (H.sym (H.≡-subst-removable id (sym z₁≡z₂) y'))))) ⟩
    (λ v₂ z₂ → h (subst id (sym v₁≡v₂) v₂) (subst id (sym z₁≡z₂) z₂))
  R.∎

subst₂-subst-subst : ∀ {lv lz lr}
  → {V : Set lv} {Z : Set lz}
  → {v₁ v₂ : V}{z₁ z₂ : Z}
  → (F : V → Z → Set lr)
  → (v₁≡v₂ : v₁ ≡ v₂)
  → (z₁≡z₂ : z₁ ≡ z₂)
  → (x : F v₁ z₁)
  → subst₂ F v₁≡v₂ z₁≡z₂ x ≡ subst (λ v → F v z₂) v₁≡v₂ (subst (F v₁) z₁≡z₂ x)
subst₂-subst-subst {lv} {lz} {lr} {V} {Z} {v₁} {v₂} {z₁} {z₂} F v₁≡v₂ z₁≡z₂ x =
  H.≅-to-≡ $
  R.begin
    subst₂ F v₁≡v₂ z₁≡z₂ x
  R.≅⟨ ≡-subst₂-removable F v₁≡v₂ z₁≡z₂ x ⟩
    x
  R.≅⟨ H.sym (H.≡-subst-removable  (F v₁) z₁≡z₂ x) ⟩
    subst (F v₁) z₁≡z₂ x
  R.≅⟨ H.sym (H.≡-subst-removable (λ v → F v z₂) v₁≡v₂ _) ⟩
    subst (λ v → F v z₂) v₁≡v₂ (subst (F v₁) z₁≡z₂ x)
  R.∎

sigma-subst : ∀ {a}{l}
  → {A A′ : Set a}
  → (f : A → Set l)
  → (A≡A′ : A ≡ A′)
  → Σ A f ≡  Σ A′ (λ a′ → f (subst id (sym A≡A′) a′))
sigma-subst {a} {l} {A} {A′} f A≡A′ =
  H.≅-to-≡ $
  R.begin
    Σ A f
  R.≅⟨ H.cong₂ {A = Set a} {B = λ ■ → (■ → Set l)} Σ
               (H.≡-to-≅ A≡A′)
               (H.sym (fun-ext-h' (sym A≡A′) (λ _ _ _ → refl)
                                  (λ { x .x refl →  H.cong f (H.≡-subst-removable id (sym A≡A′) x) }))) ⟩
    Σ A′ (λ a′ → f (subst id (sym A≡A′) a′))
  R.∎

pi-subst : ∀ {a}{l}
  → {A A′ : Set a}
  → (f : A → Set l)
  → (A′≡A : A′ ≡ A)
  → ((x : A) → f x) ≡ ((x : A′) → f (subst id A′≡A x))
pi-subst {a} {l} {A} {A′} f A′≡A =
  H.≅-to-≡ $
  R.begin
    ((x : A) → f x)
  R.≅⟨ H.cong₂ {A = Set a} {B = λ ■ → ■ → Set l} (λ ■₁ ■₂ → (x : ■₁) → ■₂ x)
               (H.≡-to-≅ (sym A′≡A))
               (fun-ext-h' (sym A′≡A) (λ _ _ _ → refl)
                           (λ { x .x refl → H.cong f (H.sym (H.≡-subst-removable id A′≡A x)) })) ⟩
    ((x : A′) → f (subst id A′≡A x))
  R.∎

subst₂-∘₁ : ∀ {a b c l}{A : Set a}{B : Set b}{C : Set c}{a₁ a₂ : A}{b₁ b₂ : B}
  → (P : C → B → Set l)
  → (f : A → C)
  → (eq₁ : a₁ ≡ a₂)
  → (eq₂ : b₁ ≡ b₂)
  → (x : P (f a₁) b₁)
  → subst₂ (P ∘ f) eq₁ eq₂ x ≡ subst₂ P (cong f eq₁) eq₂ x
subst₂-∘₁ {a} {b} {c} {l} {A} {B} {C} {a₁} {a₂} {b₁} {b₂} P f eq₁ eq₂ x =
  H.≅-to-≡ $
  R.begin
    subst₂ (P ∘ f) eq₁ eq₂ x
  R.≅⟨ ≡-subst₂-removable (P ∘ f) eq₁ eq₂ x ⟩
    x
  R.≅⟨ H.sym (≡-subst₂-removable P (cong f eq₁) eq₂ x) ⟩
    subst₂ P (cong f eq₁) eq₂ x
  R.∎

subst₂-∘ : ∀ {a b c l}{A : Set a}{B : Set b}{C : Set c}{a₁ a₂ : A}{b₁ b₂ : B}
  → (P : C → Set l)
  → (f : A → B → C)
  → (eq₁ : a₁ ≡ a₂)
  → (eq₂ : b₁ ≡ b₂)
  → (x : P (f a₁ b₁))
  → subst₂ (P ∘₂ f) eq₁ eq₂ x ≡ subst P (cong₂ f eq₁ eq₂) x
subst₂-∘ {a} {b} {c} {l} {A} {B} {C} {a₁} {a₂} {b₁} {b₂} P f eq₁ eq₂ x =
  H.≅-to-≡ $
  R.begin
    subst₂ (P ∘₂ f) eq₁ eq₂ x
  R.≅⟨ ≡-subst₂-removable (P ∘₂ f) eq₁ eq₂ x ⟩
    x
  R.≅⟨ H.sym (H.≡-subst-removable P (cong₂ f eq₁ eq₂) x) ⟩
    subst P (cong₂ f eq₁ eq₂) x
  R.∎

sym-cong₂ : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c}{a₁ a₂ : A}{b₁ b₂ : B}
  → (f : A → B → C)
  → (eq₁ : a₁ ≡ a₂)
  → (eq₂ : b₁ ≡ b₂)
  → sym (cong₂ f eq₁ eq₂) ≡ cong₂ f (sym eq₁) (sym eq₂)
sym-cong₂ f refl refl = refl

subst-cong₂ : ∀ {a b}{A₁ A₁′ : Set a}{A₂ A₂′ : Set b}
  → (eq₁ : A₁ ≡ A₁′)
  → (eq₂ : A₂ ≡ A₂′)
  → (f : A₁′ → A₂′)
  → (x : A₁)
  → subst id (sym eq₂) (f (subst id eq₁ x)) ≡ subst id (cong₂ (λ A₁ A₂ → A₁ → A₂) (sym eq₁) (sym eq₂)) f x
subst-cong₂ {a} {b} {A₁} {A₁′} {A₂} {A₂′} eq₁ eq₂ f x =
  H.≅-to-≡ $
  R.begin
    subst id (sym eq₂) (f (subst id eq₁ x))
  R.≅⟨ H.≡-subst-removable id (sym eq₂) _ ⟩
    f (subst id eq₁ x)
  R.≅⟨ Hcong₄ {A = Set a} {B = λ _ → Set b} {C = λ ■₁ ■₂ → (■₁ → ■₂)} {D = λ ■₁ ■₂ _ → ■₁} (λ _ _ ■₁ ■₂ → ■₁ ■₂)
              (H.≡-to-≅ (sym eq₁)) (H.≡-to-≅ (sym eq₂))
              (H.sym (H.≡-subst-removable id (cong₂ (λ A₃ A₄ → A₃ → A₄) (sym eq₁) (sym eq₂)) f) )
              (H.≡-subst-removable id eq₁ x) ⟩
    subst id (cong₂ (λ A₃ A₄ → A₃ → A₄) (sym eq₁) (sym eq₂)) f x
  R.∎

subst-fun : ∀ {ℓ}{ℓa ℓb ℓz}{Z : Set ℓz}{A : Z → Set ℓa}{B : Z → Set ℓb} {z₁ z₂ : Z}
  → (z₁≡z₂ : z₁ ≡ z₂)
  → (f : A z₁ → B z₁ → Set ℓ)
  → subst (λ (z : Z) → A z → B z → Set ℓ) z₁≡z₂ f ≡ λ a b → f (subst A (sym z₁≡z₂) a) (subst B (sym z₁≡z₂) b)
subst-fun {ℓ} {ℓa} {ℓb} {ℓz} {Z} {A} {B} {z₁} {z₂} z₁≡z₂ f =
  H.≅-to-≡ $
  R.begin
    subst (λ z → (A z → B z → Set ℓ)) z₁≡z₂ f
  R.≅⟨ H.≡-subst-removable (λ z → (A z → B z → Set ℓ)) z₁≡z₂ f ⟩
    f
  R.≅⟨ fun-ext-h' (cong A z₁≡z₂) (λ _ _ _ → cong (λ z → B z → Set ℓ) z₁≡z₂) (λ x y x≅y →
       fun-ext-h' (cong B z₁≡z₂) (λ _ _ _ → refl) λ x' y' x'≅y' →
       H.cong₂ f (H.trans x≅y (H.sym (H.≡-subst-removable A (sym z₁≡z₂) y)))
                 (H.trans x'≅y' (H.sym (H.≡-subst-removable B (sym z₁≡z₂) y')))) ⟩
    (λ a b → f (subst A (sym z₁≡z₂) a) (subst B (sym z₁≡z₂) b))
  R.∎

subst-fun-special : ∀
    {ℓa} {A : Set ℓa}
    {ℓr} {R₁ R₂ : A → Set ℓr}
  → (R₁≡R₂ : R₁ ≡ R₂)
  → (eq1 : ((a : A) → R₁ a) ≡ ((a : A) → R₂ a))
  → (f : (a : A) → R₁ a)
  → (x : A)
  → subst id eq1 f x ≡ subst id (cong (λ r → r x) R₁≡R₂) (f x)
subst-fun-special {ℓa} {A} {ℓr} {R₁} {R₂} R₁≡R₂ eq1 f x =
  H.≅-to-≡ $
  R.begin
    subst id eq1 f x
  R.≅⟨ H.cong₂ {A = A → Set ℓr} {B = λ ■ → (a : A) → ■ a} (λ _ ■ → ■ x)
               (H.≡-to-≅ (fun-ext (λ x → cong (λ ■ → ■ x) (sym R₁≡R₂))))
               (H.≡-subst-removable id eq1 f) ⟩
    f x
  R.≅⟨ H.sym (H.≡-subst-removable id (cong (λ r → r x) R₁≡R₂) (f x)) ⟩
    subst id (cong (λ r → r x) R₁≡R₂) (f x)
  R.∎

subst-const : ∀ {a b}{A : Set a}{B : Set b}{x y : A}
  → (x≡y : x ≡ y)
  → {z : B}
  → subst (λ (z : A) → B) x≡y z ≡ z
subst-const {a} {b} {A} {B} {x} {y} x≡y {z} =
  H.≅-to-≡ $
  R.begin
    subst (λ z₁ → B) x≡y z
  R.≅⟨ H.≡-subst-removable (λ z₁ → B) x≡y z ⟩
    z
  R.∎

sym-sym : ∀ {a}{A : Set a}{x₁ x₂ : A}
  → (eq : x₁ ≡ x₂)
  → sym (sym eq) ≡ eq
sym-sym refl = refl

-- Lemmas from Logical.agda ---------------------------------------------------

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

open import StratF.Util.PropositionalSetOmegaEquality
open import StratF.Types
open import StratF.TypeSubstitution
open import StratF.TypeSubstProperties
open import StratF.Expressions
open import StratF.ExprSubstitution
open import StratF.ExprSubstProperties hiding (module R)
open import StratF.BigStep
open import StratF.Logical hiding (
  subst-split-eq-⇓; subst-split-eq-⇓₂; subst-split-[]E;
  subst-split-[]E′; subst-split-[]E″
  )

subst-split-eq-⇓ :
  ∀ {Tₑ Tᵥ : Type [] l}
  → (e : CExpr Tₑ)
  → (v : Value Tᵥ)
  → (Tₑ≡Tᵥ : Tₑ ≡ Tᵥ)
  → subst CExpr Tₑ≡Tᵥ e ⇓ v ≡ e ⇓ subst Value (sym Tₑ≡Tᵥ) v
subst-split-eq-⇓ {l} {Tₑ} {Tᵥ} e v Tₑ≡Tᵥ =
  H.≅-to-≡ $
  R.begin
    subst CExpr Tₑ≡Tᵥ e ⇓ v
  R.≅⟨ Hcong₃ {A = Type [] l} {B = λ ■ → CExpr ■} {C = λ ■ _ → Value ■} (λ _ ■₁ ■₂ → ■₁ ⇓ ■₂)
              (H.≡-to-≅ (sym Tₑ≡Tᵥ))
              (H.≡-subst-removable CExpr Tₑ≡Tᵥ e)
              (H.sym (H.≡-subst-removable Value (sym Tₑ≡Tᵥ) v)) ⟩
    e ⇓ subst Value (sym Tₑ≡Tᵥ) v
  R.∎

subst-split-eq-⇓₂ :
  ∀ {T T′ : Type [] l}
  → {e : CExpr T}
  → {v : Value T}
  → (T≡T′ : T ≡ T′)
  → e ⇓ v
  ≡ subst CExpr T≡T′ e ⇓ subst Value T≡T′ v
subst-split-eq-⇓₂ {l} {T} {T′} {e} {v} T≡T′ =
  H.≅-to-≡ $
  R.begin
    e ⇓ v
  R.≅⟨ Hcong₃ {A = Type [] l} {B = λ ■ → CExpr ■} {C = λ ■ _ → Value ■} (λ _ ■₁ ■₂ → ■₁ ⇓ ■₂)
              (H.≡-to-≅ T≡T′)
              (H.sym (H.≡-subst-removable CExpr T≡T′ e))
              (H.sym (H.≡-subst-removable Value T≡T′ v)) ⟩
    subst CExpr T≡T′ e ⇓ subst Value T≡T′ v
  R.∎

subst-split-[]E :
  ∀ {T₁ T₁′ : Type [] l₁} {T₂ T₂′ : Type [] l₂}
  → (e : Expr [] (T₁ ◁ ∅) T₂) (e′ : CExpr T₁′)
  → (eq₁ : T₁ ≡ T₁′) (eq₂ : T₂ ≡ T₂′)
  → subst CExpr eq₂ (e [ subst CExpr (sym eq₁) e′ ]E) ≡ (subst₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂) eq₁ eq₂ e [ e′ ]E)
subst-split-[]E {l₁} {l₂} {T₁} {T₁′} {T₂} {T₂′} e e′ eq₁ eq₂ =
  H.≅-to-≡ $
  R.begin
    subst CExpr eq₂ (e [ subst CExpr (sym eq₁) e′ ]E)
  R.≅⟨ H.≡-subst-removable CExpr eq₂ _ ⟩
    e [ subst CExpr (sym eq₁) e′ ]E
  R.≅⟨ Hcong₄ {A = Type [] l₁} {B = λ _ → Type [] l₂}
              {C = λ ■₁ ■₂ → Expr [] (■₁ ◁ ∅) ■₂ } {D = λ ■₁ ■₂ _ → CExpr ■₁}
              (λ _ _ ■₁ ■₂ → ■₁ [ ■₂ ]E)
              (H.≡-to-≅ eq₁) (H.≡-to-≅ eq₂)
              (H.sym (≡-subst₂-removable (λ T₃ → Expr [] (T₃ ◁ ∅)) eq₁ eq₂ e))
              (H.≡-subst-removable CExpr (sym eq₁) e′) ⟩
    (subst₂ (λ T₃ → Expr [] (T₃ ◁ ∅)) eq₁ eq₂ e) [ e′ ]E
  R.∎

subst-split-[]E′ :
  ∀ {T₁ T₁′ : Type [] l₁} {T₂ T₂′ : Type [] l₂}
  → (e : Expr [] (T₁ ◁ ∅) T₂) (e′ : CExpr T₁′)
  → (eq₁ : T₁′ ≡ T₁) (eq₂ : T₂ ≡ T₂′)
  → subst CExpr eq₂ (e [ subst CExpr eq₁ e′ ]E) ≡ (subst₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂) (sym eq₁) eq₂ e [ e′ ]E)
subst-split-[]E′ {l₁} {l₂} {T₁} {T₁′} {T₂} {T₂′} e e′ eq₁ eq₂ =
  H.≅-to-≡ $
  R.begin
    subst CExpr eq₂ (e [ subst CExpr eq₁ e′ ]E)
  R.≅⟨ H.≡-subst-removable CExpr eq₂ _ ⟩
    e [ subst CExpr eq₁ e′ ]E
  R.≅⟨ Hcong₄ {A = Type [] l₁} {B = λ _ → Type [] l₂}
              {C = λ ■₁ ■₂ → Expr [] (■₁ ◁ ∅) ■₂} {D = λ ■₁ ■₂ _ → CExpr ■₁}
              (λ _ _ ■₁ ■₂ → ■₁ [ ■₂ ]E)
              (H.≡-to-≅ (sym eq₁)) (H.≡-to-≅ eq₂)
              (H.sym (≡-subst₂-removable (λ T₃ → Expr [] (T₃ ◁ ∅)) (sym eq₁) eq₂ e))
              (H.≡-subst-removable CExpr eq₁ e′ ) ⟩
    subst₂ (λ T₃ → Expr [] (T₃ ◁ ∅)) (sym eq₁) eq₂ e [ e′ ]E
  R.∎

subst-split-[]E″ :
  ∀ {T₁ T₁′ : Type [] l₁} {T₂ T₂′ : Type [] l₂}
  → (e : Expr [] (T₁ ◁ ∅) T₂) (e′ : CExpr T₁)
  → (eq₁ : T₁ ≡ T₁′) (eq₂ : T₂ ≡ T₂′)
  → (subst₂ (λ T₁ T₂ → Expr [] (T₁ ◁ ∅) T₂) eq₁ eq₂ e [ subst CExpr eq₁ e′ ]E)
  ≡ subst CExpr eq₂ (e [ e′ ]E) 
subst-split-[]E″ {l₁} {l₂} {T₁} {T₁′} {T₂} {T₂′} e e′ eq₁ eq₂ =
  H.≅-to-≡ $
  R.begin
    (subst₂ (λ T₃ → Expr [] (T₃ ◁ ∅)) eq₁ eq₂ e [ subst CExpr eq₁ e′ ]E)
  R.≅⟨ Hcong₄ {A = Type [] l₁} {B = λ _ → Type [] l₂}
              {C = λ ■₁ ■₂ → Expr [] (■₁ ◁ ∅) ■₂} {D = λ ■₁ ■₂ _ → CExpr ■₁}
              (λ _ _ ■₁ ■₂ → ■₁ [ ■₂ ]E)
              (H.≡-to-≅ (sym eq₁)) (H.≡-to-≅ (sym eq₂))
              (≡-subst₂-removable (λ T₃ → Expr [] (T₃ ◁ ∅)) eq₁ eq₂ e)
              (H.≡-subst-removable CExpr eq₁ e′) ⟩
    e [ e′ ]E
  R.≅⟨ H.sym (H.≡-subst-removable CExpr eq₂ _) ⟩
    subst CExpr eq₂ (e [ e′ ]E)
  R.∎
