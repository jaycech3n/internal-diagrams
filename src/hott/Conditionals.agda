{-# OPTIONS --without-K --rewriting #-}

module hott.Conditionals where

open import hott.Base public

-- Semicolon in next two definitions is `\;0`
case : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
       → A ⊔ B → (A → C) → (B → C) → C
case a⊔b f g = ⊔-rec f g a⊔b

if : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → Dec A → (A → B) → (¬ A → B) → B
if = case

case_then_else = case
if_then_else = if
