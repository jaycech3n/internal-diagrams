{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

open import reedy.SimpleSemicategories

module reedy.Cosieves {ℓₘ} (I : SimpleSemicategory ℓₘ) where

open SimpleSemicategory I


{- Shapes of linear cosieves -}

shape : ℕ → ℕ → ℕ → Type₀
shape i h t = t ≤ hom-size i h

prev-shape : ∀ {i h t} → shape i h (1+ t) → shape i h t
prev-shape = S≤-≤

full-shape : ∀ i h → shape i h (hom-size i h)
full-shape i h = lteE

total-shape-1+ : ∀ i → shape (1+ i) i (hom-size (1+ i) i)
total-shape-1+ i = full-shape (1+ i) i

<-shape : ∀ {i h t} → t < hom-size i h → shape i h t
<-shape = inr

Shape = Σ[ i ﹕ ℕ ] Σ[ h ﹕ ℕ ] Σ[ t ﹕ ℕ ] shape i h t

𝑖 : Shape → ℕ
𝑖 = fst

ℎ : Shape → ℕ
ℎ = fst ∘ snd

𝑡 : Shape → ℕ
𝑡 = 2nd ∘ snd

is-shape : ((i , h , t , _) : Shape) → shape i h t
is-shape = 3rd ∘ snd


{- Shape equality -}

shape-is-prop : ∀ {i h t} → is-prop (shape i h t)
shape-is-prop = ≤-is-prop

shape-path : ∀ {i h t} (s s' : shape i h t) → s == s'
shape-path = prop-has-all-paths


{- Counting factors -}

count-factors :
  ∀ i h t {j} → shape i h t → hom i j → ℕ
count-factors[_,_,1+_] :
  ∀ i h t (u : t < hom-size i h) {j} (f : hom i j)
  → Dec (f ∣ (#[ t ] i h u))
  → ℕ

count-factors i h O s f = O
count-factors i h (1+ t) s f =
  count-factors[ i , h ,1+ t ] u f (f ∣? #[ t ] i h u)
  where u = S≤-< s

count-factors[ i , h ,1+ t ] u f (inr no) =
  count-factors i h t (<-shape u) f
count-factors[ i , h ,1+ t ] u f (inl yes) =
  1+ (count-factors i h t (<-shape u) f)

-- Lemma 6.22 (paper version as of 16.01.24)
count-factors-top-level :
  ∀ i h t (s : shape i h t) (f : hom i h)
  → count-factors i h t s f == O
count-factors-top-level i h O s f = idp
count-factors-top-level i h (1+ t) s f with f ∣? #[ t ] i h (S≤-< s)
... | inl (g , _) = ⊥-rec (endo-hom-empty g)
... | inr no = count-factors-top-level i h t (prev-shape s) f

-- Intermediate results for Lemma 6.23
module count-factors-properties (i h j : ℕ) (f : hom i j) where
  module 6∙24 where

  module 6∙25 where
    -- Proof here differs from the paper
    count-factors-all-O-hom-size-O :
      (∀ t s → count-factors i h t s f == O) → hom-size j h == O
    count-factors-all-O-hom-size-O P = {!!}
{-
-- Lemma 6.10 (12.10.23)
-- The proof here differs from the paper.
module count-factors-properties (i h j : ℕ) (f : hom i j) where
  count-factors-all-O-hom-size-O :
    (∀ t s → count-factors i h t s f == O) → hom-size j h == O
  count-factors-all-O-hom-size-O P =
    ¬O<-=O (hom-size j h) (λ O<homjh →
      O<¬=O (c {O<homjh}) (transp! (O <_) (p) (O<S _)) (P (1+ t₀) w))
    where module _ {u : O < hom-size j h} where
      [0] = #[ O ] j h u
      idx₀ = idx-of ([0] ◦ f)
      t₀ = fst idx₀
      v = snd idx₀
      w = <-S≤ v
      c = count-factors i h (1+ t₀) w f

      f∣?[t₀] : f ∣ #[ t₀ ] i h v
      f∣?[t₀] rewrite hom#-idx ([0] ◦ f) = [0] , idp

      p : c == 1+ _
      p = {!count-factors-rec i h t₀ f (<-S≤ v) f∣?[t₀]!}

  hom-size-O-no-divisible :
    hom-size j h == O → ∀ t u → ¬ (f ∣ #[ t ] i h u)
  hom-size-O-no-divisible p t u (g , q) =
    ≮O _ $ transp (O <_) p $ hom[ j , h ]-inhab g

  no-divisible-count-factors-all-O :
    (∀ t u → ¬ (f ∣ #[ t ] i h u)) → ∀ t s → count-factors i h t s f == O
  no-divisible-count-factors-all-O P O s = idp
  no-divisible-count-factors-all-O P (1+ t) s with f ∣? #[ t ] i h (S≤-< s)
  ... | inl yes = ⊥-rec $ P _ _ yes
  ... | inr no = {!no-divisible-count-factors-all-O P t (S≤-≤ s)!}

  no-divisible-hom-size-O :
    (∀ t u → ¬ (f ∣ #[ t ] i h u)) → hom-size j h == O
  no-divisible-hom-size-O =
    count-factors-all-O-hom-size-O ∘ no-divisible-count-factors-all-O

  -- Lots of annoying finagling to the right form in this... could probably do
  -- all this more concisely. Maybe by formulating using ℕ instead of Fin (see
  -- e.g.  Martín's TypeTopology).
  hom-size>O-exists-divisible :
    O < hom-size j h
    → Σ (Fin (hom-size i h)) λ (t , u) → f ∣ #[ t ] i h u
  hom-size>O-exists-divisible O<hom =
    ¬∀Fin¬ _ _ (λ (t , u) → f ∣? #[ t ] i h u) $
      ¬uncurry $ contra $ ≠-inv $ <-to-≠ O<hom
    where
    contra : hom-size j h ≠ O → ¬ (∀ t u → ¬ (f ∣ #[ t ] i h u))
    contra = contrapos no-divisible-hom-size-O
-}

module Cosieves-IsStrictlyOriented
  (I-strictly-oriented : is-strictly-oriented I)
  where
  open SimpleSemicategories-IsStrictlyOriented I I-strictly-oriented

  {-
  module _ {i j h : ℕ} {size-cond : 0 < hom-size j h} (f : hom i j) where
    0<homih : 0 < hom-size i h
    0<homih = hom[ i , h ]-inhab $ #[ 0 ] j h size-cond ◦ f

    divby : (t : ℕ) → t < hom-size i h → hom j h
    divby O u = if f ∣? #[ 0 ] i h u
      then fst
      else λ _ → #[ 0 ] j h size-cond
    divby (1+ t) u = if f ∣? #[ 1+ t ] i h u
      then fst
      else λ _ → divby t (S<-< u)

    abstract
      divby= : ∀ {t u g} → g ◦ f == #[ t ] i h u → divby t u == g
      divby= {O} {u} {g} w with f ∣? #[ 0 ] i h u
      ... | inl (g' , p) = hom-is-epi _ _ _ (p ∙ ! w)
      ... | inr no = ⊥-rec $ no (g , w)
      divby= {1+ t} {u} {g} w with f ∣? #[ 1+ t ] i h u
      ... | inl (g' , p) = hom-is-epi _ _ _ (p ∙ ! w)
      ... | inr no = ⊥-rec $ no (g , w)

      divby-◦ : ∀ t u → f ∣ #[ t ] i h u → divby t u ◦ f == #[ t ] i h u
      divby-◦ t u (g , p) rewrite divby= p = p

    -- Lemma 6.11 (12.10.23)
    divby-lub : (t : ℕ) (u : t < hom-size i h ) (g : hom j h)
      → g ◦ f ≼ #[ t ] i h u
      → g ≼ divby t u
    divby-lub O u g w = =-≼ (! $ divby= (≼[O] _ _ w))
    divby-lub (1+ t) u g w with f ∣? #[ 1+ t ] i h u
    ... | inl (g' , p) = ≼-cancel-r _ _ _ (transp (_ ≼_) (! p) w)
    ... | inr no with w
    ...          | inl p = ⊥-rec $ no (g , hom= p)
    ...          | inr u = divby-lub t _ _ (≺S-≼ _ _ u)

    -- Lemma 6.12 (12.10.23), and extras
    module smallest-divisible
      (t₀ : ℕ)
      (u : t₀ < hom-size i h)
      (divisible : f ∣ #[ t₀ ] i h u)
      (smallest : (t : ℕ) (v : t < hom-size i h)
                  → f ∣ #[ t ] i h v
                  → t₀ ≤ t)
      where
      smallest-divisible-divby : {v : O < hom-size j h}
        → divby t₀ u == #[ O ] j h v
      smallest-divisible-divby {v} = ≼[O] v _ lem'
        where
        p : (divby t₀ u) ◦ f == #[ t₀ ] i h u
        p = divby-◦ t₀ u divisible

        [0] = #[ 0 ] j h v
        [0]◦f = [0] ◦ f
        i₀ = to-ℕ $ idx-of [0]◦f
        w = snd $ idx-of [0]◦f

        f∣[i₀] : f ∣ #[ i₀ ] i h w
        f∣[i₀] = [0] , ! (hom#-idx [0]◦f)

        q : #[ t₀ ] i h u ≼ [0]◦f
        q = idx≤-≼ _ _ $
          transp (_≤ i₀) (! $ ap to-ℕ (idx-hom# (t₀ , u))) $
          smallest i₀ w f∣[i₀]

        lem : (divby t₀ u) ◦ f ≼ [0]◦f
        lem rewrite p = q

        lem' : divby t₀ u ≼ [0]
        lem' = ≼-cancel-r _ _ _ lem

      divby-◦-ub : (t : ℕ) (v : t < hom-size i h)
        → t₀ ≤ t → divby t v ◦ f ≼ #[ t ] i h v
      divby-◦-ub t v =
        Fin[ hom-size i h ]-ind-from (t₀ , u)
          (λ (t , v) → divby t v ◦ f ≼ #[ t ] i h v)
          (=-≼ (divby-◦ t₀ u divisible))
          ind-case
          (t , v)
        where
        ind-case :
          (t : ℕ)
          (v : 1+ t < hom-size i h)
          (w : (t₀ , u) ≤-Fin (t , S<-< v))
          (ih : (divby t (S<-< v) ◦ f) ≼ #[ t ] i h (S<-< v))
          → divby (1+ t) v ◦ f ≼ #[ 1+ t ] i h v
        ind-case t v w ih with f ∣? #[ 1+ t ] i h v
        ... | inl (_ , p) = =-≼ p
        ... | inr no = inr (≼-≺-≺ ih (#[ t ]≺S (S<-< v) v))

      <-smallest-divisible-divby :
        ∀ t v → (t , v) <-Fin (t₀ , u) → divby t v == #[ O ] j h size-cond
      <-smallest-divisible-divby O v w with f ∣? #[ 0 ] i h v
      ... | inl yes = ⊥-rec $ ¬≤> (t₀ , u) (O , v) (smallest _ _ yes) w
      ... | inr no = idp
      <-smallest-divisible-divby (1+ t) v w with f ∣? #[ 1+ t ] i h v
      ... | inl yes = ⊥-rec $ ¬≤> (t₀ , u) (1+ t , v) (smallest _ _ yes) w
      ... | inr no = <-smallest-divisible-divby t (S<-< v) (S<-< w)

    -- Lemma 6.13 (16.10.23)
    divby-monotone : ∀ t t' u u' → t < t' → divby t u ≼ divby t' u'
    divby-monotone t .(1+ t) u u' ltS =
      case (Fin-trichotomy' t₀ (t , u)) case-t₀≤t case-t<t₀
      where
      open count-factors-properties i h j f

      smallest-divisible =
        let div = hom-size>O-exists-divisible size-cond
        in Fin-smallest-witness (λ (t , u) → f ∣? #[ t ] i h u) (fst div) (snd div)

      t₀ = fst smallest-divisible
      Pt₀ = 2nd smallest-divisible
      t₀-smallest = 3rd smallest-divisible

      open smallest-divisible (fst t₀) (snd t₀) Pt₀ (curry t₀-smallest)

      case-t₀≤t : t₀ ≤-Fin (t , u) → divby t u ≼ divby (1+ t) u'
      case-t₀≤t v = divby-lub (1+ t) u' _ lem
        where lem = ≼-≺-≼ (divby-◦-ub t u v) (#[ t ]≺S u u')

      case-t<t₀ : (t , u) <-Fin t₀ → divby t u ≼ divby (1+ t) u'
      case-t<t₀ v rewrite <-smallest-divisible-divby t u v = [O]-min size-cond _

    divby-monotone t (1+ t') u u' (ltSR v) =
      ≼-trans
        (divby-monotone t t' u (S<-< u') v)
        (divby-monotone t' (1+ t') (S<-< u') u' ltS)

  count-factors[_,_,1+_]-shape :
    ∀ i h t u {j} (f : hom i j)
    → (d : Dec (f ∣ #[ t ] i h u))
    → count-factors[ i , h ,1+ t ] u f d ≤ hom-size j h
  count-factors[ i , h ,1+ O ]-shape u f (inl yes) = {!!}
  count-factors[ i , h ,1+ 1+ t ]-shape u f (inl yes) = {!!}
  count-factors[ i , h ,1+ O ]-shape u f (inr no) = O≤ _
  count-factors[ i , h ,1+ 1+ t ]-shape u f (inr no) =
    count-factors[ i , h ,1+ t ]-shape v f (f ∣? #[ t ] i h v)
    where v = S<-< u -- S≤-< (inr u)
  -}

  module Lemma-6∙34-alt where -- paper version 17.10.24
    record Shape-helper (i h t : ℕ) ⦃ s : shape i h t ⦄ : Type₀  where
      constructor _,_
      field
        dt : ℕ
        eq : dt == hom-size i h − t

    count-factors-shape :
      ∀ i h t s {j} (f : hom i j)
      → count-factors i h t s f ≤ hom-size j h
    count-factors-shape[_,_,1+_] :
      ∀ i h t u {j} (f : hom i j) d
      → count-factors[ i , h ,1+ t ] u f d ≤ hom-size j h

    count-factors-shape i h O s f = O≤ _
    count-factors-shape i h (1+ t) s f =
      count-factors-shape[ i , h ,1+ t ] u f (f ∣? #[ t ] i h u)
      where u = S≤-< s

    count-factors-shape[ i , h ,1+ t ] u f (inl yes) = {!!}
    count-factors-shape[ i , h ,1+ t ] u f (inr no) =
      count-factors-shape i h t (<-shape u) f

  module Lemma-6∙34 where -- paper version 17.10.24
    count-factors-shape :
      ∀ i h t s {j} (f : hom i j)
      → count-factors i h t s f ≤ hom-size j h
    count-factors-shape[_,_,1+_] :
      ∀ i h t u {j} (f : hom i j) d
      → count-factors[ i , h ,1+ t ] u f d ≤ hom-size j h

    count-factors-shape i h O s f = O≤ _
    count-factors-shape i h (1+ t) s f =
      count-factors-shape[ i , h ,1+ t ] u f (f ∣? #[ t ] i h u)
      where u = S≤-< s

    count-factors-shape[ i , h ,1+ t ] u f (inl yes) = {!!}
    count-factors-shape[ i , h ,1+ t ] u f (inr no) =
      count-factors-shape i h t (<-shape u) f

  open Lemma-6∙34 public

  module Lemma-6∙23 where -- version 17.10.24
    count-factors-full :
      ∀ i h s {j} (f : hom i j)
      → count-factors i h (hom-size i h) s f == hom-size j h
    count-factors-full = {!!}

  open Lemma-6∙23 public

  -- Need this too; prove it on paper:
  count-factors-comp :
    ∀ i h t s {j} (f : hom i j) {k} (g : hom j k)
    → ∀ {s'}
    → count-factors i h t s (g ◦ f)
      == count-factors j h (count-factors i h t s f) s' g
  count-factors-comp i h O s f g = idp
  count-factors-comp i h (1+ t) s f g = {!!}
