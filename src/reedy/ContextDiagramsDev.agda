{-# OPTIONS --without-K --rewriting --termination-depth=4 #-}

open import reedy.IndexSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.ContextDiagramsDev {ℓₘᴵ ℓₒ ℓₘ}
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

open import reedy.ShapedTelescopes I cwfstr
open Πₛₜₑₗ pistr

SCT : ℕ → Con
𝔸 : (n : ℕ) → Ty (SCT n)
M : (i h t : ℕ) (sh : shape i h t) → Tel (SCT (1+ h)) [ i , h , t ] sh

SCT O = ◆
SCT (1+ n) = SCT n ∷ 𝔸 n

SCT-∷ : ∀ n → Σ[ X ː Ty (SCT n) ] SCT n ∷ X == SCT (1+ n)
SCT-∷ n = 𝔸 n , idp

M[1+_] : ∀ n → Tel (SCT(1+ n)) [ 1+ n , n , hom-size (1+ n) n ] full-shape[1+ n ]
M[1+ n ] = M (1+ n) n (hom-size (1+ n) n) full-shape[1+ n ]

𝔸 O = U
𝔸 (1+ n) = Πₛₜₑₗ M[1+ n ] U

A : (n : ℕ) → Tm[ SCT (1+ n) ] (𝔸 n ʷ)
A n = var (SCT (1+ n))

M i O (1+ t) sh =
  let M-prev = M i O t (shapeₜ↓ sh) -- (1)
  in M-prev ‣ wkn el (A O ᵁ) byₛₜₑₗ M-prev

M i (1+ h) (1+ t) sh = M-prev ‣ el substituted-filler
  where
  M-prev = M i (1+ h) t (shapeₜ↓ sh)

  M[1+h]ʷ : Tel (SCT (2+ h)) [ 1+ h , 1+ h , O ] (top-shape (1+ h))
  M[1+h]ʷ = M[1+ h ] ↑ₛₜₑₗ 𝔸 (1+ h)

  -- Bureaucratic conversion
  p : 𝔸 (1+ h) ʷ == Πₛₜₑₗ M[1+h]ʷ U
  p = Πₛₜₑₗ-[]-comm M[1+ h ] U (π (𝔸 (1+ h))) ∙ ap (Πₛₜₑₗ M[1+h]ʷ) U[]

  generic-filler : Tm[ SCT (2+ h) ++ₛₜₑₗ M[1+h]ʷ ] U
  generic-filler = appₛₜₑₗ M[1+h]ʷ (coeᵀᵐ p (A (1+ h)))

  substituted-filler : Tm[ SCT (2+ h) ++ₛₜₑₗ M-prev ] U
  substituted-filler = generic-filler [ {!!} ]ₜ ᵁ

M i (1+ h) O sh = M i h (hom-size i h) (shapeₕ↓ sh) ↑ₛₜₑₗ 𝔸 (1+ h)
M i O O sh = •

{- Comments

(1) Putting the definition of M' in a where block causes termination errors?...
-}
