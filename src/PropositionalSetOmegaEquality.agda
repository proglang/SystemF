module PropositionalSetOmegaEquality where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)


-- equality for Setω

data _≡ω_ {A : Setω} (x : A) : A → Setω where
  refl : x ≡ω x

congωl : ∀ {b} {A : Setω} {B : Set b} (f : A → B) {x y : A} → x ≡ω y → f x ≡ f y
congωl f refl = refl

congωωl : ∀ {b} {A : Setω} {B : Setω} {C : Set b} (f : A → B → C) {x y : A} {x′ y′ : B} → x ≡ω y → x′ ≡ω y′ → f x x′ ≡ f y y′
congωωl f refl refl = refl

conglω : ∀ {a} {A : Set a} {B : Setω} (f : A → B) {x y : A} → x ≡ y → f x ≡ω f y
conglω f refl = refl

congωω : ∀ {A : Setω} {B : Setω} (f : A → B) {x y : A} → x ≡ω y → f x ≡ω f y
congωω f refl = refl

conglωω : ∀ {a} {A : Set a} {B : Setω} {C : Setω} (f : A → B → C) {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≡ x₂ → y₁ ≡ω y₂ → f x₁ y₁ ≡ω f x₂ y₂
conglωω f refl refl = refl

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


dep-substωl : ∀ {a b}{A : Setω}{B : A → Set a} → (F : (x : A) → B x → Set b) →
  ∀ {x₁ y₁ : A} {x₂ : B x₁} {y₂ : B y₁} → (x₁≡y₁ : x₁ ≡ω y₁) → substω B x₁≡y₁ x₂ ≡ y₂ → F x₁ x₂ → F y₁ y₂
dep-substωl F refl refl a = a

dep-substωll : ∀ {a b c}{A : Setω}{B : A → Set a}{C : A → Set c} → (F : (x : A) → B x → C x → Set b) →
  ∀ {x₁ y₁ : A} {x₂ : B x₁} {y₂ : B y₁} {x₃ : C x₁} {y₃ : C y₁} → (x₁≡y₁ : x₁ ≡ω y₁) → substω B x₁≡y₁ x₂ ≡ y₂ → substω C x₁≡y₁ x₃ ≡ y₃ → F x₁ x₂ x₃ → F y₁ y₂ y₃
dep-substωll F refl refl refl a = a


substω-∘ :
  ∀ {b c} {A : Setω} {B : Set b}
    {a b : A}
  → (F : B → Set c)
  → (G : A → B)
  → {x : F (G a)}
  → (eq : a ≡ω b)
  → substω (λ z → F (G z)) eq x ≡ subst F (congωl G eq) x
substω-∘ G F refl = refl

{- definitional -}
substω-id :
  ∀ {ℓ} {A : Setω} {a : A}
  → (F : A → Set ℓ)
  → (eq : a ≡ω a)
  → {x : F a}
  → substω F eq x ≡ x
substω-id F refl = refl

substω-elim :
  ∀ {ℓ} {A : Setω} {a b : A}
  → (F : A → Set ℓ)
  → (eq₁ eq₂ : a ≡ω b)
  → {x : F a}
  → substω F eq₁ x ≡ substω F eq₂ x
substω-elim F refl refl = refl

dcongωl : ∀ {b} {A : Setω} {B : A → Set b}
  → (f : (a : A) → B a)
  → {x y : A}
  → (x≡ωy : x ≡ω y)
  → f x ≡ substω B (symω x≡ωy) (f y)
dcongωl f refl = refl

dcongωlll : ∀ {b}{c}{d} {A : Setω} {B : A → Set b}{C : A → Set c}{D : Set d}
  → (f : (a : A) → B a → C a → D)
  → {a₁ a₂ : A}
  → {b₁ : B a₁}{b₂ : B a₂}
  → {c₁ : C a₁}{c₂ : C a₂}
  → (a₁≡ωa₂ : a₁ ≡ω a₂)
  → (b₁≡b₂ : b₁ ≡ substω B (symω a₁≡ωa₂) b₂)
  → (c₁≡c₂ : c₁ ≡ substω C (symω a₁≡ωa₂) c₂)
  → f a₁ b₁ c₁ ≡ f a₂ b₂ c₂
dcongωlll f refl refl refl = refl

substω-congω : ∀ {ℓ}{ℓ₁}
    {A₁ : Set ℓ₁}
    {A₂ : Setω}
  → (F : A₁ → Set ℓ)
  → (G : A₂ → A₁)
  → {x y : A₂}
  → (x≡y : x ≡ω y)
  → (a : F (G x))
  → substω (λ z → F (G z)) x≡y a ≡ subst F (congωl G x≡y) a
substω-congω F G refl a = refl
