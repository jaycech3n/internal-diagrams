{-# OPTIONS --without-K --rewriting #-}

module hott.Conditionals where

open import hott.Base public

case : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
       → A ⊔ B → (A → C) → (B → C) → C
case a⊔b f g = ⊔-rec f g a⊔b

depcase : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} (C : A ⊔ B → Type ℓ₃)
          → (a+b : A ⊔ B)
          → ((a : A) → C (inl a)) → ((b : B) → C (inr b))
          → C a+b
depcase C a+b f g = ⊔-elim {C = C} f g a+b

if : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → Dec A → (A → B) → (¬ A → B) → B
if = case

case_then_else = case
if_then_else = if
