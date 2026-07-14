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

{- If we normalise the above expressions with C-c C-n, the first two become the
   "obviously correct thing". Afterwards, it becomes long and difficult to read.
   Is there a good argument why we're really producing semisimplicial types?
   One Agda-internal way to do it would be to interpret this in some 2LTT, and
   show that they really become equivalent to the expected Reedy fibrant diagrams.
   But this seems difficult, maybe even unfeasible.
   We could also try some meta-theoretic argument instead.
-}
