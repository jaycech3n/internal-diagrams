{-# OPTIONS --without-K --rewriting #-}

module hott.Paths where

open import hott.Base public

private
  variable {ℓ ℓ₁ ℓ₂ ℓ₃} : ULevel

transp! : {A : Type ℓ₁} (B : A → Type ℓ₂)
  {x y : A} (p : x == y) → B y → B x
transp! B p = transp B (! p)

transp-∘ : {A : Type ℓ₁} {B : Type ℓ₂}
  (P : B → Type ℓ₃) (f : A → B)
  {x y : A} (p : x == y)
  → transp (P ∘ f) p == transp P (ap f p)
transp-∘ P f idp = idp

-- Ad hoc lemmas used in various places
<!∙>∙!∙ : {A : Type ℓ} {x y z : A} (p : y == x) (q : y == z)
          → (! p ∙ q) ∙ ! q ∙ p == idp
<!∙>∙!∙ idp idp = idp

from-over-lr : {A : Type ℓ₁} (B : A → Type ℓ₂)
  → {x y z w : A} {u : B x} {v : B w}
  → (p : x == y) (q : y == z) (r : z == w)
  → u == v [ B ↓ p ∙ q ∙ r ]
  → transp B p u == transp! B r v [ B ↓ q ]
from-over-lr B idp idp idp p = p

ap-const :
  {A : Type ℓ₁} {B : Type ℓ₂} {b : B} {x y : A} (p : x == y)
  → ap (λ _ → b) p == idp
ap-const idp = idp
