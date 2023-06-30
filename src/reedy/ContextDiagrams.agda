{-# OPTIONS --without-K --rewriting --termination-depth=4 #-}

open import reedy.IndexSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.ContextDiagrams {ℓₘᴵ ℓₒ ℓₘ}
  (I : SuitableSemicategory ℓₘᴵ)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open SuitableSemicategory I
open import reedy.LinearSieves I

open CwFStructure cwfstr renaming (_◦_ to _◦ˢᵘᵇ_)
open PiStructure pistr
open UniverseStructure univstr
open import cwfs.Telescopes cwfstr
open Πₜₑₗ pistr

SCT : ℕ → Con
𝔸 : (n : ℕ) → Ty (SCT n)
M : (i h t : ℕ) → shape i h t → Tel (SCT (1+ h))

M[1+_] : ∀ n → Tel (SCT(1+ n))
M[1+ n ] = M (1+ n) n (hom-size (1+ n) n) (full-shape-1+ n)

SCT O = ◆
SCT (1+ n) = SCT n ∷ 𝔸 n

𝔸 O = U
𝔸 (1+ n) = Πₜₑₗ M[1+ n ] U

A : (n : ℕ) → Tm[ SCT (1+ n) ] (𝔸 n ʷ)
A n = var (SCT (1+ n))

M i O (1+ t) sh =
  let M-prev = M i O t (shapeₜ↓ sh) -- (1)
  in M-prev ‣ wkn el (A O ᵁ) byₜₑₗ M-prev

M i (1+ h) (1+ t) sh = M-prev ‣ el substituted-filler
  where
  M-prev = M i (1+ h) t (shapeₜ↓ sh)

  M[1+h]ʷ : Tel (SCT (2+ h))
  M[1+h]ʷ = M[1+ h ] [ π (𝔸 (1+ h)) ]ₜₑₗ

  -- Bureaucratic conversion
  p : 𝔸 (1+ h) ʷ == Πₜₑₗ M[1+h]ʷ U
  p = Πₜₑₗ-[]-comm M[1+ h ] U (π (𝔸 (1+ h))) ∙ ap (Πₜₑₗ M[1+h]ʷ) U[]

  generic-filler : Tm[ SCT (2+ h) ++ₜₑₗ M[1+h]ʷ ] U
  generic-filler = appₜₑₗ M[1+h]ʷ (coeᵀᵐ p (A (1+ h)))

  substituted-filler : Tm[ SCT (2+ h) ++ₜₑₗ M-prev ] U
  substituted-filler = generic-filler [ {!!} ]ₜ ᵁ

M i (1+ h) O sh = (M i h (hom-size i h) (shapeₕ↓ sh)) [ π _ ]ₜₑₗ
M i O O sh = •

{- Comments

(1) Putting the definition of M' in a where block causes termination errors?...
-}
