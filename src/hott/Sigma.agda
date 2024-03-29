{-# OPTIONS --without-K --rewriting #-}

module hott.Sigma where

open import hott.Base public

Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ[ x ﹕ A ] B -- use \:9

last-two : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
  → A × B × C → B × C
last-two (_ , b , c) = b , c

-- A bit of an ad-hoc place for this for now
¬uncurry : ∀ {ℓ₁ ℓ₂ ℓ₃}
  → {A : Type ℓ₁} {B : A → Type ℓ₂} {C : (a : A) → B a → Type ℓ₃}
  → ¬ ((a : A) (b : B a) → C a b)
  → ¬ ((p : Σ A B) → C (fst p) (snd p))
¬uncurry ¬f g = ¬f $ curry g

private
  module triples {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : A → Type ℓ₂} {C : {a : A} (b : B a) → Type ℓ₃}
    where

    2nd : (u : Σ[ a ﹕ A ] Σ[ b ﹕ B a ] C b) → B (fst u)
    2nd = fst ∘ snd

    3rd : (u : Σ[ a ﹕ A ] Σ[ b ﹕ B a ] C b) → C (2nd u)
    3rd = snd ∘ snd

    first-two : Σ[ a ﹕ A ] Σ[ b ﹕ B a ] C b → Σ[ a ﹕ A ] B a
    first-two (a , b , _) = a , b

  module equivalences {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} (e : A ≃ B) where
    fwd-transp-Σ-dom : {C : B → Type ℓ₃} → Σ B C → Σ A (C ∘ –> e)
    fwd-transp-Σ-dom {C} (b , c) = <– e b , transp C (! (<–-inv-r e b)) c

    bwd-transp-Σ-dom : {C : A → Type ℓ₃} → Σ A C → Σ B (C ∘ <– e)
    bwd-transp-Σ-dom {C} (a , c)= –> e a , transp C (! (<–-inv-l e a)) c

open triples public
open equivalences public
