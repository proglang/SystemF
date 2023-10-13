open import Level
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open import Ext

module SubstProperties where

subst-irrelevant : 
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ : A}
    {F : A → Set ℓ₁}
    (eq eq' : a₁ ≡ a₂)
    (x : F a₁) 
  → subst F eq x ≡ subst F eq' x
subst-irrelevant refl refl x = refl

elim-subst :
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ : A}
  → (F : A → Set ℓ₁)
  → (a₂≡a₁ : a₂ ≡ a₁)
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (x : F a₁)
  → subst F a₂≡a₁ (subst F a₁≡a₂ x) ≡ x
elim-subst _ refl refl _ = refl

elim-subst₃ :
  ∀ {ℓ ℓ₁} {A : Set ℓ} {a₁ a₂ a₃ : A}
  → (F : A → Set ℓ₁)
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (a₃≡a₁ : a₃ ≡ a₁)
  → (a₂≡a₃ : a₂ ≡ a₃)
  → (x : F a₂)
  → subst F a₁≡a₂ (subst F a₃≡a₁ (subst F a₂≡a₃ x)) ≡ x
elim-subst₃ _ refl refl refl _ = refl

dist-subst :
  ∀ {ℓ₁ ℓ₂}
    {A A′ : Set ℓ₁} {B B′ : Set ℓ₂}
  → (f : A → B)
  → (A≡A′ : A′ ≡ A)
  → (A→B≡A′→B′ : (A → B) ≡ (A′ → B′))
  → (B≡B′ : B ≡ B′)
  → (x : A′) 
  → subst id B≡B′ (f (subst id A≡A′ x)) ≡ subst id A→B≡A′→B′ f x
dist-subst _ refl refl refl _ = refl

dist-subst-id : 
  ∀ {ℓ} {A B C : Set ℓ}
  → (A≡B : B ≡ A)
  → (B≡C : C ≡ B)
  → (A≡C : C ≡ A)
  → (x : C)
  → subst id A≡B (subst id B≡C x) ≡ subst id A≡C x
dist-subst-id refl refl refl x = refl

dist-subst′ :
  ∀ {ℓ₁ ℓ₂}
    {A A′ : Set ℓ₁} {B B′ : Set ℓ₂}
  → (f : A → B)
  → (A≡A′ : A ≡ A′)
  → (A→B≡A′→B′ : (A → B) ≡ (A′ → B′))
  → (B≡B′ : B ≡ B′)
  → (x : A) 
  → subst id A→B≡A′→B′ f (subst id A≡A′ x) ≡ subst id B≡B′ (f x)
dist-subst′ _ refl refl refl _ = refl

dist-subst′′ :
  ∀ {ℓ₁ ℓ₂}
    {A : Set ℓ₁} {B B′ : A → Set ℓ₂} 
  → (a : A) 
  → (f : (a : A) → B a)
  → (A→B≡A′→B′ : ((a : A) → B a) ≡ ((a : A) → B′ a))
  → (B≡B′ : (a : A) → B a ≡ B′ a)
  → subst id (B≡B′ a) (f a) ≡ subst id A→B≡A′→B′ f a
dist-subst′′ a _ A→B≡A′→B′ B≡B′ with fun-ext B≡B′ | B≡B′ a
dist-subst′′ _ _ refl B≡B′ | refl | refl = refl 

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

subst-shuffle′′′′ :
  ∀ {ℓ}
    {A₁ A₂ A₃ A₄ : Set ℓ} 
  → (a : A₃) 
  → (A≡A₁ : A₁ ≡ A₂)
  → (A≡A₂ : A₃ ≡ A₁)
  → (A≡A₃ : A₄ ≡ A₂)
  → (A≡A₄ : A₃ ≡ A₄)
  → subst id A≡A₁ (subst id A≡A₂ a) ≡ subst id A≡A₃ (subst id A≡A₄ a)
subst-shuffle′′′′ _ refl refl refl refl = refl


dist-subst' :
  ∀ {ℓ ℓ' ℓ₁ ℓ₂} {A : Set ℓ} {B : Set ℓ'} {a₁ a₂ : A}
    {F : A → Set ℓ₁} {G : B → Set ℓ₂}
  → (a→b : A → B)
  → (f : ∀ {a} → F a → G (a→b a))
  → (a₁≡a₂ : a₁ ≡ a₂)
  → (b₁≡b₂ : a→b a₁ ≡ a→b a₂)
  → (x : F a₁) 
  → f {a₂} (subst F a₁≡a₂ x) ≡ subst G b₁≡b₂ (f {a₁} x)
dist-subst' _ _ refl refl _ = refl

dist-subst′′′ :
  ∀ {ℓ₁ ℓ₂}
    {A : Set ℓ₁} {B : A → Set ℓ₂} 
  → (a : A) 
  → (a′ : A)
  → (f : (a : A) → B a)
  → (a≡a′ : a ≡ a′)
  → (Ba′≡Ba : B a′ ≡ B a)
  → f a ≡ subst id Ba′≡Ba (f a′)
dist-subst′′′ _ _ _ refl refl = refl

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
subst-elim′′′′ _ _ _ _ _ refl = refl

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
subst-swap′′ _ _ _ _ _ refl refl = refl

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
subst-cong F G refl a = refl

subst-swap :
  ∀ {ℓ₁}{ℓ₂} {A : Set ℓ₁}
    {F : (a : A) → Set ℓ₂}
    {a₁ a₂ : A}
    (eq : a₁ ≡ a₂)
    (x : F a₁)
    (y : F a₂)
  → subst F eq x ≡ y
  → x ≡ subst F (sym eq) y
subst-swap refl x y refl = refl

subst-id :
  ∀ {ℓ ℓ′} {A : Set ℓ′} {a : A}
  → (F : A → Set ℓ)
  → (eq : a ≡ a)
  → {x : F a}
  → subst F eq x ≡ x
subst-id F refl = refl

eta-subst : ∀ {lv lz lr}
  → {V : Set lv} {Z₁ Z₂ : Set lz} {R : Set lr}
  → (h : V → Z₁ → R)
  → (z₁≡z₂ : Z₁ ≡ Z₂)
  → subst (λ Z → V → Z → R) z₁≡z₂ h ≡ λ v → subst (λ Z → Z → R) z₁≡z₂ (h v)
eta-subst h refl = refl

app-subst : ∀ {lz lr}
  →  {Z₁ Z₂ : Set lz} {R : Set lr}
  → (h : Z₁ → R)
  → (z₁≡z₂ : Z₁ ≡ Z₂)
  → (λ z → h (subst id (sym z₁≡z₂) z)) ≡ subst (λ Z → Z → R) z₁≡z₂ h
app-subst h refl = refl


subst₂→subst : ∀ {l a b}{A : Set a}{B : Set b}
  → {a : A}{b b′ : B}
  → (F : A → B → Set l)
  → (eq : b ≡ b′)
  → (x : F a b)
  → subst₂ F refl eq x ≡ subst (F a) eq x
subst₂→subst F refl x = refl

