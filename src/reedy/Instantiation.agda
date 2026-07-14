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
open import cwfs.Syntax

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

-}
