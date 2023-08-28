module SetOmega where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)


-- equality for Setω

data _≡ω_ {A : Setω} (x : A) : A → Setω where
  refl : x ≡ω x

congωl : ∀ {b} {A : Setω} {B : Set b} (f : A → B) {x y : A} → x ≡ω y → f x ≡ f y
congωl f refl = refl

conglω : ∀ {a} {A : Set a} {B : Setω} (f : A → B) {x y : A} → x ≡ y → f x ≡ω f y
conglω f refl = refl

congωω : ∀ {A : Setω} {B : Setω} (f : A → B) {x y : A} → x ≡ω y → f x ≡ω f y
congωω f refl = refl

-- conglωω : ∀ {a} {A : Set a} {B : Setω} {C : Setω} (f : A → B → C) {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≡ x₂ → y₁ ≡ω y₂ → f x₁ y₁ ≡ω f x₂ y₂
-- conglωω f refl refl = refl

transω : ∀ {A : Setω} {x y z : A} → x ≡ω y → y ≡ω z → x ≡ω z
transω refl refl = refl

symω : ∀ {A : Setω} {x y : A} → x ≡ω y → y ≡ω x
symω refl = refl

substω : ∀ {b}{A : Setω} → (F : (x : A) → Set b) →
  ∀ {x y : A} → x ≡ω y → F x → F y
substω f refl x = x

substlω : ∀ {a b}{A : Set a}{B : Setω} → (F : (x : A) → B → Set b) →
  ∀ {x₁ y₁ : A} {x₂ y₂ : B} → x₁ ≡ y₁ → x₂ ≡ω y₂ → F x₁ x₂ → F y₁ y₂
substlω F refl refl x = x

substωl : ∀ {a}{A : Set a} → (F : (x : A) → Setω) →
  ∀ {x y : A} → x ≡ y → F x → F y
substωl f refl x = x

substωω : ∀ {A : Setω} → (F : (x : A) → Setω) →
  ∀ {x y : A} → x ≡ω y → F x → F y
substωω f refl x = x

substωlω-l : ∀ {b d}{A : Setω}{B : A → Set b}{C : A → Setω}(F : (a : A) → B a → C a → Set d)
  → {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} {c₁ : C a₁} {c₂ : C a₂}
  → (a₁≡a₂ : a₁ ≡ω a₂) → b₁ ≡ substω B (symω a₁≡a₂) b₂ → c₁ ≡ω substωω C (symω a₁≡a₂) c₂ →  F a₁ b₁ c₁ → F a₂ b₂ c₂
substωlω-l F refl refl refl x = x

substlωl-l : ∀ {a c d}{A : Set a}{B : A → Setω}{C : A → Set c}(F : (a : A) → B a → C a → Set d)
  → {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} {c₁ : C a₁} {c₂ : C a₂}
  → (a₁≡a₂ : a₁ ≡ a₂) → b₁ ≡ω substωl B (sym a₁≡a₂) b₂ → c₁ ≡ subst C (sym a₁≡a₂) c₂ →  F a₁ b₁ c₁ → F a₂ b₂ c₂
substlωl-l F refl refl refl x = x

