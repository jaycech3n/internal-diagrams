{-# OPTIONS --without-K --rewriting #-}

module hott.WeaklyConstant where

open import hott.Base public
open import hott.NType public
open import hott.Sigma
open import hott.Unit

-- Weakly constant functions; see
-- "Notions of Anonymous Existence in Martin-Löf Type Theory".
wconst : ∀ {ℓ ℓ'} → {A : Type ℓ} {B : Type ℓ'} → (A → B) → Type _
wconst {A = A} f = (x y : A) → f x == f y

module _ {ℓ} {A : Type ℓ} where
  wconst-id-is-prop-aux : wconst (idf A) → is-prop (wconst (idf A))
  wconst-id-is-prop-aux w = Π-level2 $ prop-paths-prop ⦃ h ⦄
    where
    h : is-prop A
    h = all-paths-is-prop w

  wconst-id-is-prop : is-prop (wconst (idf A))
  wconst-id-is-prop = inhab-to-prop-is-prop wconst-id-is-prop-aux

  id-wconst-equiv-is-prop : wconst (idf A) ≃ is-prop A
  id-wconst-equiv-is-prop = all-paths-is-prop , is-eq _ g f-g g-f
    where
    g = λ p → prop-has-all-paths ⦃ p ⦄
    f-g = λ _ → prop-has-all-paths _ _
    g-f = λ _ → prop-path wconst-id-is-prop _ _

  wconst-into-prop-is-prop :
    ∀ {ℓ'} {B : Type ℓ'} (f : A → B) → is-prop B → is-prop (wconst f)
  wconst-into-prop-is-prop f h =
    Π-level2 (λ a a' → prop-paths-prop ⦃ h ⦄ (f a) (f a'))

-- We say that a type A is "contracted by f", aka "is f-contracted",
-- if A is pointed, and there is a type B such that f : A → B is a
-- weakly constant function.
is-contracted-by : ∀ {ℓ ℓ'} {B : Type ℓ'} (A : Type ℓ) → (A → B) → Type (ℓ ∪ ℓ')
is-contracted-by {B = B} A f = Σ[ a ﹕ A ] wconst f

infix 999 is-contracted-by-syntax
is-contracted-by-syntax = is-contracted-by
syntax is-contracted-by-syntax A f = is- f -contracted A

module _ {ℓ} (A : Type ℓ) where
  is-id-contracted-equiv-is-contr :
    is-(idf A)-contracted A ≃ is-contr A
  is-id-contracted-equiv-is-contr = f , is-eq _ g f-g g-f
    where
    f : is-(idf A)-contracted A → is-contr A
    f (a , w) = has-level-in (a , w a)

    g : is-contr A → is-(idf A)-contracted A
    g (has-level-in (a , w)) = a , λ x y → ! (w x) ∙ w y

    f-g = λ _ → prop-path is-contr-is-prop _ _

    g-f = λ _ → pair= idp (prop-path wconst-id-is-prop _ _)

  is-trivially-contracted-equiv-inhab :
    is-(!⊤)-contracted A ≃ A
  is-trivially-contracted-equiv-inhab = fst , is-eq _ g f-g g-f
    where
    g = λ a → a , λ _ _ → idp
    f-g = λ _ → idp
    g-f = λ _ →
      pair= idp (prop-path (wconst-into-prop-is-prop !⊤ Unit-level) _ _)
