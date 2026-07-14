{-# OPTIONS --without-K --rewriting #-}

{- Some tests: What exactly computes?
   This is a pure experimentation module that can be removed sooner or later.
 -}

module reedy.ComputationTests where

open import reedy.SimpleSemicategories
open import reedy.SemiSimplex
open import reedy.Cosieves Δop
open Cosieves-StrictlyOriented Δop-strictly-oriented
open SimpleSemicategory Δop

private
  dec-to-bool : ∀ {ℓ} {A : Type ℓ} → Dec A → Bool
  dec-to-bool (inl _) = true
  dec-to-bool (inr _) = false

-- The edge {0,1} of [2], i.e. a morphism 2 → 1 of Δ₊ᵒᵖ.
e01 : hom 2 1
e01 =
  ltS ,
  ( (λ { (O , _) → 0 , ltSR (ltSR ltS) ; (1+ _ , _) → 1 , ltSR ltS })
  , (λ { (O , _) (O , _) v → ⊥-rec (¬<-self v)
       ; (O , _) (1+ _ , _) _ → ltS
       ; (1+ _ , _) (O , _) v → ⊥-rec (≮O _ v)
       ; (1+ _ , u) (1+ _ , w) v →
           ⊥-rec (≮O _ (<-≤-< (<-cancel-S v) (<S-≤ (<-cancel-S w)))) }) )

_ : hom-size 2 0 == 3
_ = idp

_ : hom-size 2 1 == 3
_ = idp

_ : hom-size 3 1 == 6
_ = idp

private
  u0 : 0 < hom-size 2 0
  u0 = ltSR (ltSR ltS)
  u1 : 1 < hom-size 2 0
  u1 = ltSR ltS
  u2 : 2 < hom-size 2 0
  u2 = ltS

_ : idx (#[ 0 ] 2 0 u0) == 0
_ = idp

_ : dec-to-bool (e01 ∣? #[ 0 ] 2 0 u0) == true
_ = idp

_ : dec-to-bool (e01 ∣? #[ 1 ] 2 0 u1) == true
_ = idp

_ : dec-to-bool (e01 ∣? #[ 2 ] 2 0 u2) == false
_ = idp

private
  s1 : shape 2 0 1
  s1 = inr (ltSR ltS)
  s2 : shape 2 0 2
  s2 = inr ltS
  s3 : shape 2 0 3
  s3 = inl idp

_ : count-factors 2 0 0 (O≤ _) e01 == 0
_ = idp

_ : count-factors 2 0 1 s1 e01 == 1
_ = idp

_ : count-factors 2 0 2 s2 e01 == 2
_ = idp

_ : count-factors 2 0 3 s3 e01 == 2
_ = idp

-- `count-factors-full i h s f : count-factors i h (hom-size i h) s f
--                               == hom-size j h` is now a path between two
-- numerals that are definitionally equal (both 2, above). But the *path* is a
-- long =⟨_⟩ chain, not idp, so it does not reduce.
