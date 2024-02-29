-- This file contains definitions and lemmas for heterogeneous equality on Setω.

-- The definitions and proofs are identical to those for regular
-- heterogeneous equality from the standard library, except that they
-- talk about `Setω` types instead of `Set ℓ` types.

module StratF.Util.HeterogeneousSetOmegaEquality where

open import Level 
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.HeterogeneousEquality using (_≅_)

open import StratF.Util.PropositionalSetOmegaEquality using (_≡ω_; substω; substωω)

REL : Setω → Setω → Setω₁
REL A B = A → B → Setω

_⇒_ : ∀ {A B : Setω} → REL A B → REL A B → Setω
P ⇒ Q = ∀ {x y} → P x y → Q x y
  
infix 4 _≅ω_

data _≅ω_ {A : Setω} (x : A) : {B : Setω} → B → Setω where
     refl : x ≅ω x
 
≅ω-to-≡ω : ∀ {A : Setω} {x y : A} → x ≅ω y → x ≡ω y
≅ω-to-≡ω refl = _≡ω_.refl 

≡ω-to-≅ω : ∀ {A : Setω} {x y : A} → x ≡ω y → x ≅ω y
≡ω-to-≅ω _≡ω_.refl = refl

reflexive : ∀{A : Setω} → _⇒_ {A = A} _≡ω_ (λ x y → x ≅ω y)
reflexive _≡ω_.refl = refl

sym : ∀ {A : Setω} {B : Setω} {x : A} {y : B} → x ≅ω y → y ≅ω x
sym refl = refl

trans : ∀ {A : Setω} {B : Setω} {C : Setω} {x : A} {y : B} {z : C} → x ≅ω y → y ≅ω z → x ≅ω z
trans refl eq = eq

≡ω-substωω-removable : ∀ {A : Setω} (P : A → Setω) {x y} (eq : x ≡ω y) (z : P x) →
                   substωω P eq z ≅ω z
≡ω-substωω-removable P _≡ω_.refl z = refl

≡ω-substω-removable : ∀ {l} {A : Setω} (P : A → Set l) {x y} (eq : x ≡ω y) (z : P x) →
                   substω P eq z ≅ z
≡ω-substω-removable P _≡ω_.refl z = _≅_.refl

cong : ∀ {A : Setω} {B : A → Setω} {x y}
       (f : (x : A) → B x) → x ≅ω y → f x ≅ω f y
cong f refl = refl

cong-ωl : ∀ {l} {A : Setω} {B : A → Set l} {x y}
       (f : (x : A) → B x) → x ≅ω y → f x ≅ f y
cong-ωl f refl = _≅_.refl


cong₂ : ∀ {A : Setω} {B : A → Setω} {C : ∀ x → B x → Setω} {x y u v}
        (f : (x : A) (y : B x) → C x y) → x ≅ω y → u ≅ω v → f x u ≅ω f y v
cong₂ f refl refl = refl

cong₂-ωωl : ∀ {l} {A : Setω} {B : A → Setω} {C : ∀ x → B x → Set l} {x y u v}
      (f : (x : A) (y : B x) → C x y) → x ≅ω y → u ≅ω v → f x u ≅ f y v
cong₂-ωωl f refl refl = _≅_.refl

cong₂-ωll : ∀ {l l'} {A : Setω} {B : A → Set l'} {C : ∀ x → B x → Set l} {x y u v}
      (f : (x : A) (y : B x) → C x y) → x ≅ω y → u ≅ v → f x u ≅ f y v
cong₂-ωll f refl _≅_.refl = _≅_.refl

cong₃-ωll :
  ∀ {b c d}
    {A : Setω} {B : A → Set b} {C : ∀ x → B x → Set c} {D : ∀ x → (y : B x) → C x y → Set d}
    {x y u v i j}
    (f : (x : A) (y : B x) (z : C x y) → D x y z) →
    x ≅ω y →
    u ≅ v →
    i ≅ j →
    f x u i ≅ f y v j
cong₃-ωll  f refl _≅_.refl _≅_.refl = _≅_.refl

cong₄-ωlll :
  ∀ {b c d e}
    {A : Setω} {B : A → Set b} {C : ∀ x → B x → Set c} {D : ∀ x → (y : B x) → C x y → Set d}
    {E : ∀ x → (y : B x) → (z : C x y) → D x y z → Set e}
    {x y u v i j p q}
    (f : (x : A) (y : B x) (z : C x y) (w : D x y z) → E x y z w) →
    x ≅ω y →
    u ≅ v →
    i ≅ j →
    p ≅ q →
    f x u i p ≅ f y v j q
cong₄-ωlll f refl  _≅_.refl  _≅_.refl  _≅_.refl =  _≅_.refl


cong-app₄ : ∀ {b c d e} 
        {A : Setω} {B : A → Set b} {C : ∀ x → B x → Set c} 
        {D : ∀ x → (y : B x) → C x y → Set d} {E : ∀ x → (y : B x) → (z : C x y) → D x y z → Set e}
        {f g : (x : A) (y : B x) (z : C x y) (w : D x y z) → E x y z w} →
        f ≅ω g → (x : A) (y : B x) (z : C x y) (w : D x y z) → f x ≅ g x
cong-app₄ refl x y z w = _≅_.refl

module ≅ω-Reasoning where
  infix  1 begin_
  infixr 2 _≅ω⟨⟩_ step-≅ω
  infix  3 _∎

  begin_ : ∀ {A : Setω} {B : Setω} {x : A} {y : B}
    → x ≅ω y
      -----
    → x ≅ω y
  begin x≅ωy  =  x≅ωy

  _≅ω⟨⟩_ : ∀ {A : Setω} {B : Setω} (x : A) {y : B}
    → x ≅ω y
      -----
    → x ≅ω y
  x ≅ω⟨⟩ x≅ωy  =  x≅ωy

  step-≅ω : ∀ {A : Setω} {B : Setω} {C : Setω} (x : A) {y : B} {z : C} → y ≅ω z → x ≅ω y → x ≅ω z
  step-≅ω x y≅ωz x≅ωy  =  trans x≅ωy y≅ωz

  syntax step-≅ω x y≅ωz x≅ωy  =  x ≅ω⟨  x≅ωy ⟩ y≅ωz

  _∎ : ∀ {A : Setω} (x : A)
      -----
    → x ≅ω x
  x ∎  =  refl
    
