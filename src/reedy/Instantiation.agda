{-# OPTIONS --without-K --rewriting #-}

{- Instantiating the diagram construction:

* the cwf is the Syntax (in the sense of Altenkirch-Kaposi);
* the index category is Δ₊op.

This is the motivating example of the whole development: In an internal
set-levelcwf (here: the initial such internal cwf), we can construct
semisimplicial types. -}

module reedy.Instantiation where

open import reedy.SimpleSemicategories
open import reedy.SemiSimplex
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe
open import cwfs.Syntax

open CwFStructure synCwF
open PiStructure synPi
open UniverseStructure synU
open import cwfs.Telescopes synCwF
open Πₜₑₗ synPi
open TelIndexedTypes synU

import reedy.Diagrams as Diagrams

-- The diagram construction at Δ₊ᵒᵖ, with coefficients in the syntax.
module Δ-syntax-diagrams =
  Diagrams Δop Δop-strictly-oriented
    synCwF synPi synU synSet

-- The truncated semisimplicial types, as contexts of the syntax.
𝕊𝕊𝕋 : ℕ → ConS
𝕊𝕊𝕋 = Δ-syntax-diagrams.𝔻

-- Check with C-c C-n to what the below normalise.
x0 : ConS
x0 =  𝕊𝕊𝕋 0

x1 : ConS
x1 =  𝕊𝕊𝕋 1

x2 : ConS
x2 =  𝕊𝕊𝕋 2

x3 : ConS
x3 =  𝕊𝕊𝕋 3

x4 : ConS
x4 =  𝕊𝕊𝕋 4


{- If we normalise the above expressions with C-c C-n, the first two become the
   "obviously correct thing". Afterwards, it becomes long and difficult to read.
   For example, x4 normalises to the monster term below.
   Is there a good argument why we're really producing semisimplicial types?
   One Agda-internal way to do it would be to interpret this in some 2LTT, and
   show that they really become equivalent to the expected Reedy fibrant
   diagrams. But this seems difficult, maybe even unfeasible.
   We could also try some meta-theoretic argument instead.

x4 normalises to:

◇S ▹S US ▹S
cwfs.Telescopes.Πₜₑₗ.Πₜₑₗ synCwF synPi
(Diagrams.Mᵒ Δop
 (λ f {z} g h u →
    coe
    (ap
     (_<
      fst
      (LocallyFiniteSemicategoryStructure.idx' Δ-locfinstr
       (<-trans (h .fst) (f .fst) ,
        (λ x → f .snd .fst (h .snd .fst x)) ,
        (λ s t u₁ →
           f .snd .snd (h .snd .fst s) (h .snd .fst t)
           (h .snd .snd s t u₁)))))
     (!
      (LocallyFiniteSemicategoryStructure.idx'-def Δ-locfinstr
       (<-trans (g .fst) (f .fst) ,
        (λ x → f .snd .fst (g .snd .fst x)) ,
        (λ s t u₁ →
           f .snd .snd (g .snd .fst s) (g .snd .fst t)
           (g .snd .snd s t u₁))))))
    (coe
     (ap
      (_<_
       (fst
        (fst (snd (ΔHom-equiv-aux z₁ z (z <? z₁)))
         (<-trans (g .fst) (f .fst) ,
          (λ x → f .snd .fst (g .snd .fst x)) ,
          (λ s t u₁ →
             f .snd .snd (g .snd .fst s) (g .snd .fst t)
             (g .snd .snd s t u₁))))))
      (!
       (LocallyFiniteSemicategoryStructure.idx'-def Δ-locfinstr
        (<-trans (h .fst) (f .fst) ,
         (λ x → f .snd .fst (h .snd .fst x)) ,
         (λ s t u₁ →
            f .snd .snd (h .snd .fst s) (h .snd .fst t)
            (h .snd .snd s t u₁))))))
     ((Δ-oriented-core f g h | z <? z₁ | z <? z₁)
      (coe
       (ap (_<_ (fst (fst (snd (ΔHom-equiv-aux z₁ z (z <? z₁))) g)))
        (LocallyFiniteSemicategoryStructure.idx'-def Δ-locfinstr h))
       (coe
        (ap
         (_< fst (LocallyFiniteSemicategoryStructure.idx' Δ-locfinstr h))
         (LocallyFiniteSemicategoryStructure.idx'-def Δ-locfinstr g))
        u)))))
 synCwF synPi synU synSet 1 0
 (LocallyFiniteSemicategoryStructure.hom-size Δ-locfinstr 1 0)
 (inl idp))
US
▹S
cwfs.Telescopes.Πₜₑₗ.Πₜₑₗ synCwF synPi
(Diagrams.Mᵒ Δop
 (λ f {z} g h u →
    coe
    (ap
     (_<
      fst
      (LocallyFiniteSemicategoryStructure.idx' Δ-locfinstr
       (<-trans (h .fst) (f .fst) ,
        (λ x → f .snd .fst (h .snd .fst x)) ,
        (λ s t u₁ →
           f .snd .snd (h .snd .fst s) (h .snd .fst t)
           (h .snd .snd s t u₁)))))
     (!
      (LocallyFiniteSemicategoryStructure.idx'-def Δ-locfinstr
       (<-trans (g .fst) (f .fst) ,
        (λ x → f .snd .fst (g .snd .fst x)) ,
        (λ s t u₁ →
           f .snd .snd (g .snd .fst s) (g .snd .fst t)
           (g .snd .snd s t u₁))))))
    (coe
     (ap
      (_<_
       (fst
        (fst (snd (ΔHom-equiv-aux z₁ z (z <? z₁)))
         (<-trans (g .fst) (f .fst) ,
          (λ x → f .snd .fst (g .snd .fst x)) ,
          (λ s t u₁ →
             f .snd .snd (g .snd .fst s) (g .snd .fst t)
             (g .snd .snd s t u₁))))))
      (!
       (LocallyFiniteSemicategoryStructure.idx'-def Δ-locfinstr
        (<-trans (h .fst) (f .fst) ,
         (λ x → f .snd .fst (h .snd .fst x)) ,
         (λ s t u₁ →
            f .snd .snd (h .snd .fst s) (h .snd .fst t)
            (h .snd .snd s t u₁))))))
     ((Δ-oriented-core f g h | z <? z₁ | z <? z₁)
      (coe
       (ap (_<_ (fst (fst (snd (ΔHom-equiv-aux z₁ z (z <? z₁))) g)))
        (LocallyFiniteSemicategoryStructure.idx'-def Δ-locfinstr h))
       (coe
        (ap
         (_< fst (LocallyFiniteSemicategoryStructure.idx' Δ-locfinstr h))
         (LocallyFiniteSemicategoryStructure.idx'-def Δ-locfinstr g))
        u)))))
 synCwF synPi synU synSet 2 1
 (LocallyFiniteSemicategoryStructure.hom-size Δ-locfinstr 2 1)
 (inl idp))
US
▹S
cwfs.Telescopes.Πₜₑₗ.Πₜₑₗ synCwF synPi
(Diagrams.Mᵒ Δop
 (λ f {z} g h u →
    coe
    (ap
     (_<
      fst
      (LocallyFiniteSemicategoryStructure.idx' Δ-locfinstr
       (<-trans (h .fst) (f .fst) ,
        (λ x → f .snd .fst (h .snd .fst x)) ,
        (λ s t u₁ →
           f .snd .snd (h .snd .fst s) (h .snd .fst t)
           (h .snd .snd s t u₁)))))
     (!
      (LocallyFiniteSemicategoryStructure.idx'-def Δ-locfinstr
       (<-trans (g .fst) (f .fst) ,
        (λ x → f .snd .fst (g .snd .fst x)) ,
        (λ s t u₁ →
           f .snd .snd (g .snd .fst s) (g .snd .fst t)
           (g .snd .snd s t u₁))))))
    (coe
     (ap
      (_<_
       (fst
        (fst (snd (ΔHom-equiv-aux z₁ z (z <? z₁)))
         (<-trans (g .fst) (f .fst) ,
          (λ x → f .snd .fst (g .snd .fst x)) ,
          (λ s t u₁ →
             f .snd .snd (g .snd .fst s) (g .snd .fst t)
             (g .snd .snd s t u₁))))))
      (!
       (LocallyFiniteSemicategoryStructure.idx'-def Δ-locfinstr
        (<-trans (h .fst) (f .fst) ,
         (λ x → f .snd .fst (h .snd .fst x)) ,
         (λ s t u₁ →
            f .snd .snd (h .snd .fst s) (h .snd .fst t)
            (h .snd .snd s t u₁))))))
     ((Δ-oriented-core f g h | z <? z₁ | z <? z₁)
      (coe
       (ap (_<_ (fst (fst (snd (ΔHom-equiv-aux z₁ z (z <? z₁))) g)))
        (LocallyFiniteSemicategoryStructure.idx'-def Δ-locfinstr h))
       (coe
        (ap
         (_< fst (LocallyFiniteSemicategoryStructure.idx' Δ-locfinstr h))
         (LocallyFiniteSemicategoryStructure.idx'-def Δ-locfinstr g))
        u)))))
 synCwF synPi synU synSet 3 2
 (LocallyFiniteSemicategoryStructure.hom-size Δ-locfinstr 3 2)
 (inl idp))
US

There are some experiments with the strictified syntax (which uses rewrites).
However, there is a better way:
-}

{-
The "honest" way to demonstrate that the construction does what it
claims to do, at least for low numbers. This does not rely on SyntaxStrict
or rewrite rules. It just shows that the expression that the construction
produces are *propositionally* equal to what one would expect.
-}



open Δ-syntax-diagrams.Convenience using (𝔸 ; A ; Mᵒᵗᵒᵗ)

-- equality of Π-types

Π= : ∀ {Γ} {X X' : TyS Γ} (p : X == X')
     {B : TyS (Γ ▹S X)} {B' : TyS (Γ ▹S X')}
   → B == B' [ (λ Z → TyS (Γ ▹S Z)) ↓ p ]
   → ΠS X B == ΠS X' B'
Π= idp idp = idp

-- Û is the variable A₀ of the context (◇S ▹S US)
Û : TmS {◇S ▹S US} US
Û = coeᵀᵐ U[] (υ U)

-- A 0 is *definitionally* generic[ • ]type
A0= : A 0 == ElS Û
A0= = generic[•]type=

-- hand-written contexts that we would expect:

expected-x0 : ConS
expected-x0 = ◇S

expected-x1 : ConS
expected-x1 = ◇S ▹S US

-- in nice form, we expect 𝕊𝕊𝕋 2 = (A₀ : U, A₁ : El A₀ → El A₀ → U)

expected-x2 : ConS
expected-x2 = ◇S ▹S US ▹S ΠS (ElS Û) (ΠS (ElS Û [ pS (ElS Û) ]TS) US)


-- the three instances above *are* correct:

x0-correct : 𝕊𝕊𝕋 0 == expected-x0
x0-correct = idp

x1-correct : 𝕊𝕊𝕋 1 == expected-x1
x1-correct = idp

-- 𝕊𝕊𝕋 2 is not judgmentally correct, it needs a proof.

𝔸1-shape : 𝔸 1 == ΠS (A 0 [ id ]) (ΠS (A 0 [ id ◦ π (A 0 [ id ]) ]) US)
𝔸1-shape = idp

private
  -- the first slot: A 0 [ id ] == El Û
  q₀ : A 0 [ id ] == ElS Û
  q₀ = [id] ∙ A0=

  -- the rest of the telescope, as a function of the first slot, so that we can
  -- transport it along q₀.
  G : (Z : TyS (◇S ▹S US)) → TyS (◇S ▹S US ▹S Z)
  G Z = ΠS (A 0 [ id ◦ π Z ]) US

  -- G at the right-hand endpoint is what we want, up to idl and A0=.
  r : G (ElS Û) == ΠS (ElS Û [ pS (ElS Û) ]TS) US
  r = ap (λ W → ΠS W US)
         (ap (A 0 [_]) (idl (π (ElS Û))) ∙ ap (_[ π (ElS Û) ]) A0=)

𝔸1-nf : 𝔸 1 == ΠS (ElS Û) (ΠS (ElS Û [ pS (ElS Û) ]TS) US)
𝔸1-nf = Π= q₀ (apd G q₀ ▹ r)

x2-correct : 𝕊𝕊𝕋 2 == expected-x2
x2-correct = ap (◇S ▹S US ▹S_) 𝔸1-nf

-- Moral of the story: The strictification doesn't actually buy us very much
-- (one level more definitional, but we also don't get 𝕊𝕊𝕋 3.)
