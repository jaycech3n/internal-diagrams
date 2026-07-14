{-# OPTIONS --without-K --rewriting #-}

module reedy.SimpleSemicategories where

open import categories.Semicategories public
open import categories.Inverse public
open import categories.LocallyFinite public

record SimpleSemicategory ℓₘ : Type (lsuc ℓₘ) where
  field
    wildsemicatstr : WildSemicategoryStructure lzero ℓₘ ℕ
    inversestr : InverseWildSemicategoryStructure (idf ℕ) wildsemicatstr
    locfinstr : LocallyFiniteSemicategoryStructure wildsemicatstr

  open WildSemicategoryStructure wildsemicatstr public
  open InverseWildSemicategoryStructure inversestr public
  open LocallyFiniteSemicategoryStructure locfinstr public

  private
    module definitions where
      is-monotone-precomp : ∀ {i j} (f : hom i j) → Type ℓₘ
      is-monotone-precomp {j = j} f =
        ∀ {k} (g h : hom j k)
        → g ≺ h
        → g ◦ f ≺ h ◦ f

  open definitions public

  private
    module lemmas where
      ¬divides-same-target :
        ∀ i j t (u : t < hom-size i j) (f : hom i j)
        → ¬ (f ∣ #[ t ] i j u)
      ¬divides-same-target i j t u f (g , _) = endo-hom-empty g

      ¬O<hom-size-O : ∀ i t → ¬ (t < hom-size 0 i)
      ¬O<hom-size-O i t u = ≮O i $ hom-inverse 0 i (#[ t ] 0 i u)

  open lemmas public

is-strictly-oriented : ∀ {ℓₘ} → SimpleSemicategory ℓₘ → Type ℓₘ
is-strictly-oriented C = ∀ {m n} (f : hom m n) → is-monotone-precomp f
  where open SimpleSemicategory C

module SimpleSemicategories-IsStrictlyOriented {ℓₘ}
  (C : SimpleSemicategory ℓₘ)
  (strictly-oriented : is-strictly-oriented C)
  where
  open SimpleSemicategory C

  abstract
    hom-is-epi : ∀ {l m n} (f : hom l m) (g h : hom m n)
      → g ◦ f == h ◦ f
      → g == h
    hom-is-epi f g h p = ⊔-rec
      (idf _)
      (λ{ (inl u) → ⊥-rec $
            ¬≺-self _ (transp (_≺ h ◦ f) p (strictly-oriented f g h u))
        ; (inr u) → ⊥-rec $
            ¬≺-self _ (transp (h ◦ f ≺_) p (strictly-oriented f h g u)) })
      $ ≺-trichotomy g h

    ≺-cancel-r : ∀ {l m n} (f : hom l m) (g h : hom m n)
      → g ◦ f ≺ h ◦ f
      → g ≺ h
    ≺-cancel-r f g h u with ≺-trichotomy g h
    ... | inl idp = ⊥-rec (¬≺-self _ u)
    ... | inr (inl v) = v
    ... | inr (inr v) = ⊥-rec $ ¬≺-self _ $ <-trans (strictly-oriented f h g v) u

    ≼-cancel-r : ∀ {l m n} (f : hom l m) (g h : hom m n)
      → g ◦ f ≼ h ◦ f
      → g ≼ h
    ≼-cancel-r f g h (inl p) = =-≼ (hom-is-epi _ _ _ (idx=-hom= p))
    ≼-cancel-r f g h (inr u) = inr (≺-cancel-r _ _ _ u)

  -- In a strictly oriented semicategory, divisibility is a proposition:
  -- the factor is unique because every morphism is an epimorphism, and
  -- hom-sets are sets.
  ∣-is-prop :
    ∀ {i j h} (f : hom i j) (m : hom i h)
    → is-prop (f ∣ m)
  ∣-is-prop f m = all-paths-is-prop
    λ{ (g , p) (g' , p') →
       pair= (hom-is-epi f g g' (p ∙ ! p'))
             (prop-has-all-paths-↓ ⦃ has-level-apply hom-is-set _ _ ⦄) }

  idx-◦-O :
    ∀ {l m n} (f : hom l m) (g : hom m n)
    → idx (g ◦ f) == O
    → idx g == O
  idx-◦-O {l} {m} {n} f g p = ¬O<-=O _ bot
    where module _ (c : O < idx g) where
    u = hom[ _ , _ ]-inhab g
    [O] = #[ O ] m n u

    w : g ◦ f ≼ [O] ◦ f
    w = (O≤ _) ◂$ transp! (_≤ idx ([O] ◦ f)) p

    q : idx g == O
    q = ≤O-=O (≼-cancel-r _ _ _ w ◂$ transp (idx g ≤_) (idx-hom# _))

    bot : ⊥
    bot = ¬<-self (c ◂$ transp (O <_) q)
