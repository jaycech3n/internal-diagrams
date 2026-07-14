{-# OPTIONS --without-K --rewriting #-}

{- This is a version of Instantiation.agda where, instead of Syntax.agda, we
   instantiate at StrictSyntax.agda.
   The point is that this allows Agda to compute a little bit more. This check
   should be read as a demonstration, not an actual proof about the syntax.
   
   Each `idp` says: the context the construction produces is *definitionally*
   the hand-written context. This works until n ≤ 2.

   The reason why it doesn't compute for n = 3 is that reedy.Diagrams transports
   along the propositional ℕ-equality `count-factors-full` in the clause

     M⃗ᵗᵒᵖ i (1+ h) O s f = wkn-sub ... (idd (M= ... cf-full) ◦ˢᵘᵇ M⃗ ...) ...

   To make y3 compute, we would need reedy.Diagrams to compute on that path.
   Maybe this could work by routing M= through a decidable-equality normaliser,
   or something like that, but then we would have the same problem at the next
   stage.
-}

module reedy.InstantiationStrict where

open import reedy.SimpleSemicategories
open import reedy.SemiSimplex
open import cwfs.CwFs
open import cwfs.SyntaxStrict

import reedy.Diagrams as Diagrams

module Δ-strict-diagrams =
  Diagrams Δop Δop-strictly-oriented
    synxCwF synxPi synxU synxSet

𝕊𝕊𝕋ˣ : ℕ → ConX
𝕊𝕊𝕋ˣ = Δ-strict-diagrams.𝔻

-- Here's what the construction produces:

y0 : ConX
y0 = 𝕊𝕊𝕋ˣ 0

y1 : ConX
y1 = 𝕊𝕊𝕋ˣ 1

y2 : ConX
y2 = 𝕊𝕊𝕋ˣ 2

y3 : ConX
y3 = 𝕊𝕊𝕋ˣ 3

y4 : ConX
y4 = 𝕊𝕊𝕋ˣ 4

-- Here's the hand-written semisimplicial contexts:

expected0 : ConX
expected0 = ◇X

expected1 : ConX
expected1 = ◇X ▹X UX

-- A₀: the universe variable of (◇ ▹ U), decoded by El.
A₀ : TyX (◇X ▹X UX)
A₀ = ElX (qX UX)

-- 𝔸1 = A₀ → A₀ → U, the second argument's type being A₀ weakened past the
-- first argument.
𝔸1 : TyX (◇X ▹X UX)
𝔸1 = ΠX A₀ (ΠX (ElX (qX UX [ pX A₀ ]tX)) UX)

expected2 : ConX
expected2 = ◇X ▹X UX ▹X 𝔸1

-- The constructed terms are judgmentall the hand-written ones:

--   𝕊𝕊𝕋 0 = ()
y0-nf : y0 == expected0
y0-nf = idp

--   𝕊𝕊𝕋 1 = (A₀ : U)
y1-nf : y1 == expected1
y1-nf = idp

--   𝕊𝕊𝕋 2 = (A₀ : U, A₁ : A₀ → A₀ → U)
y2-nf : y2 == expected2
y2-nf = idp
