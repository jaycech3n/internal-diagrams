Well founded order on shapes
============================

\begin{code}

{-# OPTIONS --without-K --rewriting #-}

open import reedy.SimpleSemicategories

module reedy.ShapeOrder {ℓₘ} (I : SimpleSemicategory ℓₘ) where

open import hott.Induction
open import reedy.CosieveShapes I

open SimpleSemicategory I

\end{code}

Lexicographic order on shapes.

\begin{code}

data _>ₛ_ (sh : Shape) : Shape → Type₀ where
  on-𝑖 : ∀ {sh'} → 𝑖 sh > 𝑖 sh' → sh >ₛ sh'
  on-ℎ : ∀ {h' t' s'} → ℎ sh > h' → sh >ₛ shape (𝑖 sh) h' t' s'
  on-𝑡 : ∀ {t' s'} → 𝑡 sh > t' → sh >ₛ shape (𝑖 sh) (ℎ sh) t' s'

_<ₛ_ : Shape → Shape → Type₀
sh <ₛ sh' = sh' >ₛ sh

<ₛ-trans : ∀ {sh sh' sh''} → sh <ₛ sh' → sh' <ₛ sh'' → sh <ₛ sh''
<ₛ-trans (on-𝑖 u) (on-𝑖 v) = on-𝑖 (<-trans u v)
<ₛ-trans (on-𝑖 u) (on-ℎ _) = on-𝑖 u
<ₛ-trans (on-𝑖 u) (on-𝑡 _) = on-𝑖 u
<ₛ-trans (on-ℎ _) (on-𝑖 v) = on-𝑖 v
<ₛ-trans (on-ℎ u) (on-ℎ v) = on-ℎ (<-trans u v)
<ₛ-trans (on-ℎ u) (on-𝑡 _) = on-ℎ u
<ₛ-trans (on-𝑡 _) (on-𝑖 v) = on-𝑖 v
<ₛ-trans (on-𝑡 _) (on-ℎ v) = on-ℎ v
<ₛ-trans (on-𝑡 u) (on-𝑡 v) = on-𝑡 (<-trans u v)

_≤ₛ_ : Shape → Shape → Type₀
sh ≤ₛ sh' = (sh == sh') ⊔ (sh <ₛ sh')

≤ₛ-trans : ∀ {sh sh' sh''} → sh ≤ₛ sh' → sh' ≤ₛ sh'' → sh ≤ₛ sh''
≤ₛ-trans (inl idp) v = v
≤ₛ-trans (inr u) (inl idp) = inr u
≤ₛ-trans (inr u) (inr v) = inr (<ₛ-trans u v)

𝑖-≤ₛ-monotone : ∀ {sh sh'} → sh ≤ₛ sh' → 𝑖 sh ≤ 𝑖 sh'
𝑖-≤ₛ-monotone (inl idp) = lteE
𝑖-≤ₛ-monotone (inr (on-𝑖 w)) = inr w
𝑖-≤ₛ-monotone (inr (on-ℎ _)) = lteE
𝑖-≤ₛ-monotone (inr (on-𝑡 _)) = lteE

\end{code}

Accessibilty predicate and induction.

\begin{code}

<ₛ-Acc = Acc Shape _<ₛ_

<ₛ-Accc : ∀ i h t s → Type₀
<ₛ-Accc i h t s = <ₛ-Acc (shape i h t s)

<ₛ-is-wf-aux : ∀ i h t s → <ₛ-Acc (shape i h t s)
<ₛ-is-wf-aux i h t s = acc _ (aux i h t s)
  where
  -- By case distinction on the proof of <ₛ
  aux : ∀ i h t s → ∀ sh' → sh' <ₛ shape i h t s → Acc Shape _<ₛ_ sh'
  aux .(1+ i') h t s (shape i' h' t' s') (on-𝑖 ltS) = <ₛ-is-wf-aux i' h' t' s'
  aux (1+ i) h t s sh' (on-𝑖 (ltSR w)) = aux i O O (O≤ _) sh' (on-𝑖 w)
  aux i h t s (shape .i h' t' s') (on-ℎ ltS) = <ₛ-is-wf-aux i h' t' s'
  aux i (1+ h) t s sh' (on-ℎ (ltSR w)) = aux i h O (O≤ _) sh' (on-ℎ w)
  aux i h .(1+ _) s (shape i h t' s') (on-𝑡 ltS) = <ₛ-is-wf-aux i h t' s'
  aux i h (1+ t) s sh' (on-𝑡 (ltSR w)) = aux i h t (prev-is-shape s) sh' (on-𝑡 w)

<ₛ-is-wf : ∀ {sh} → <ₛ-Acc sh
<ₛ-is-wf {shape i h t s} = <ₛ-is-wf-aux i h t s

open WellFoundedInduction Shape _<ₛ_ (λ sh → <ₛ-is-wf {sh})
  renaming (wf-ind to shape-ind)
  public

\end{code}
