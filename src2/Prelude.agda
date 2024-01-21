module Prelude where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.List using (List; []; _∷_)

postulate
  fun-ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

infix 4 _∋_
data _∋_ {ℓ} {A : Set ℓ} : List A → A → Set ℓ where
  zero : ∀ {xs x} → (x ∷ xs) ∋ x
  suc  : ∀ {xs x y} → xs ∋ x → (y ∷ xs) ∋ x