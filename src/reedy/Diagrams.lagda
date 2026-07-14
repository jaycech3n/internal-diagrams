A HoTT construction of Reedy fibrant diagrams
in contexts of a set-level category with families
=============================================

For a strictly oriented simple semicategory I (e.g. the opposite of the
semisimplex category Δ₊) and a set-level cwf C with Π-types and a universe,
we construct the context that corresponds to I-indexed Reedy fibrant diagrams.
The motivation example is the construction of semisimplicial types, internally.

The important assumption is that our cwf is set-level; we wouldn't expect this
to work for wild cwfs. (If it worked, it would provide a solution to the problem
of constructing semisimplicial types.)
In our experience, termination is tricky, but the current development passes the
termination checker. To do this, the termination-depth is set to 99.
(TODO: this surely can be improved!)

\begin{code}

{-# OPTIONS --without-K --rewriting --termination-depth=99 #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe
open import cwfs.SetLevel

module reedy.Diagrams {ℓₘᴵ ℓₒ ℓₘ}
  (I : SimpleSemicategory ℓₘᴵ)
  (I-strictly-oriented : is-strictly-oriented I)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  (setlvlstr : SetLevelStructure cwfstr)
  where

open SimpleSemicategory I
open SimpleSemicategories-IsStrictlyOriented I I-strictly-oriented
open import reedy.Cosieves I
open Cosieves-StrictlyOriented I-strictly-oriented

open CwFStructure cwfstr renaming (_◦_ to _◦ˢᵘᵇ_ ; ass to assˢᵘᵇ)
open SetLevelStructure setlvlstr
open PiStructure pistr
open UniverseStructure univstr
open import cwfs.Telescopes cwfstr
open Πₜₑₗ pistr
open TelIndexedTypes univstr
open TelescopeWeakening setlvlstr

\end{code}


Preliminaries, Overview, and Declarations
-----------------------------------------

The construction is a large mutually inductive definition with a large number of
components. The first two core ones are 𝔻 and Mᵒ:

• The context ( 𝔻 i ≡ A₀ : 𝔸₀, A₁ : 𝔸₁, ..., A(i - 1) : 𝔸(i - 1) ) consists of
  the "diagram fillers" up to level i, where 𝔸 k are the types of the fillers.

• Mᵒ (i, h, t) s : Tel 𝔻(h + 1) is the partial matching object of the diagram as
  a telescope.

\begin{code}

𝔻 : ℕ → Con
Mᵒ : (i h t : ℕ) → shape i h t → Tel (𝔻 (1+ h))

\end{code}

For readability, we immediately define a host of frequently used abbreviations.

\begin{code}

module Convenience where

  M : (i h t : ℕ) → shape i h t → Con
  M i h t s = close (Mᵒ i h t s)

  Mᵒᵗᵒᵗ : (i : ℕ) → Tel (𝔻 i)
  Mᵒᵗᵒᵗ O = •
  Mᵒᵗᵒᵗ (1+ i) = Mᵒ (1+ i) i (hom-size (1+ i) i) (total-shape-1+ i)

  Mᵒᶠᵘˡˡ : (i h : ℕ) → Tel (𝔻 (1+ h))
  Mᵒᶠᵘˡˡ i h = Mᵒ i h full shp
    where
    full = hom-size i h
    shp = full-shape i h

  𝔸 : (i : ℕ) → Ty (𝔻 i)
  𝔸 i = Πₜₑₗ (Mᵒᵗᵒᵗ i) U

  A : (i : ℕ) → Ty (𝔻 i ∷ 𝔸 i ++ₜₑₗ Mᵒᵗᵒᵗ i [ π (𝔸 i) ]ₜₑₗ)
  A i = generic[ Mᵒᵗᵒᵗ i ]type

  M=shape : ∀ {i h t} s s' → M i h t s == M i h t s'
  M=shape {i} {h} {t} s s' = ap (M i h t) (shape-path s s')

  M= : ∀ i h {t} s {t'} s' → t == t' → M i h t s == M i h t' s'
  M= i h {t} s {.t} s' idp = M=shape s s'

  M=-idp : ∀ {i h t s} → M= i h {t} s s idp == idp
  M=-idp {i} {h} {t} {s} =
    ap (ap (M i h t)) (prop-path shape-id-is-prop (shape-path s s) idp)

  M=-∙ :
    ∀ i h {t} s {t'} s' {t''} s''
    → (p : t == t') (q : t' == t'')
    → M= i h s s' p ∙ M= i h s' s'' q == M= i h s s'' (p ∙ q)
  M=-∙ i h s s' s'' idp idp =
    ! (ap-∙ _ (shape-path s s') (shape-path s' s''))
    ∙ ap (ap _) (prop-path shape-id-is-prop _ _)

open Convenience

\end{code}

Then we can write down the definition of 𝔻:

\begin{code}

𝔻 O = ◆
𝔻 (1+ i) = 𝔻 i ∷ 𝔸 i

\end{code}

Note that we have not yet given the definition of Mᵒ. This definition uses the
functoriality of the partial matching object functor, which is given by the
additional components M⃗ (for the action on morphisms) and M⃗◦ (for functoriality
of M⃗).

\begin{code}

M⃗ :
  ∀ i h t s {j} (f : hom i j)
  → let cf = count-factors i h t s f in
    (cfs : shape j h cf)
  → Sub (M i h t s) (M j h cf cfs)

M⃗◦ :
  ∀ i h t s {j} (f : hom i j) {k} (g : hom j k)
  → let cf = count-factors i h t s f in
    (cfs : shape j h cf)
  → let cg      = count-factors j h cf cfs g
        c[gf]   = count-factors i h t s (g ◦ f)
        c[g][f] = count-factors j h cf cfs g
    in
    (cgs : shape k h cg)
    (cgfs : shape k h c[gf])
    (p : c[gf] == c[g][f])
  → M⃗ j h cf cfs g cgs ◦ˢᵘᵇ M⃗ i h t s f cfs
    ==
    idd (M= k h cgfs cgs p) ◦ˢᵘᵇ M⃗ i h t s (g ◦ f) cgfs

\end{code}

Our construction does not satisfy some desired equalities definitionally, so we
need to transport along certain propositional equalities.

One of these is the following equality Mᵗᵒᵗ=. Morally this is just reflexivity,
but for computational reasons it needs to be defined mutually with the other
diagram components.

\begin{code}

Mᵗᵒᵗ= : ∀ i → M i i O (O≤ _) == close (Mᵒᵗᵒᵗ i [ π (𝔸 i) ]ₜₑₗ)

\end{code}

We also define, for better abstraction, abbreviations M-improper= and M⃗ᵗᵒᵖ.
We request that they satisfy a certain composition rule.

\begin{code}

M-improper= :
  ∀ i h t (s : shape i h t) (f : hom i h)
    (cfs : shape h h (count-factors i h t s f))
  → M h h (count-factors i h t s f) cfs == close (Mᵒᵗᵒᵗ h [ π (𝔸 h) ]ₜₑₗ)
M-improper= i h t s f cfs =
  M= h h cfs (O≤ _) (count-factors-top-level i h t s f) ∙ Mᵗᵒᵗ= h

M⃗ᵗᵒᵖ :
  ∀ i h t (s : shape i h t) (f : hom i h)
  → Sub (M i h t s) (close (Mᵒᵗᵒᵗ h [ π (𝔸 h) ]ₜₑₗ))

M⃗ᵗᵒᵖ= :
  ∀ i h t (s : shape i h t) (f : hom i h)
    (cfs : shape h h (count-factors i h t s f))
  → M⃗ᵗᵒᵖ i h t s f == idd (M-improper= i h t s f cfs) ◦ˢᵘᵇ M⃗ i h t s f cfs

M⃗[_,_][_] :
  ∀ i h t (s : shape i h t) (u : t < hom-size i h)
  → Sub (M i h t s) (close (Mᵒᵗᵒᵗ h [ π (𝔸 h) ]ₜₑₗ))
M⃗[ i , h ][ t ] s u = M⃗ᵗᵒᵖ i h t s (#[ t ] i h u)

-- important new compatibility component: the boundary projections M⃗ᵗᵒᵖ form a
-- cone which is preserved by the matching object substitutions M⃗.
-- It is proved by its own induction.

needᵍ :
  ∀ i h t (s : shape i h t) {j} (f : hom i j)
    (cfs : shape j h (count-factors i h t s f)) (g : hom j h)
  → M⃗ᵗᵒᵖ j h (count-factors i h t s f) cfs g ◦ˢᵘᵇ M⃗ i h t s f cfs
    == M⃗ᵗᵒᵖ i h t s (g ◦ f)

need :
  ∀ i h t (s : shape i h t) (u : t < hom-size i h)
  → ∀ {j} (f : hom i j)
  → let cf = count-factors i h t s f in
    (yes : f ∣ #[ t ] i h u)
    (cfs : shape j h cf)
    (cfu : cf < hom-size j h)
  → M⃗ᵗᵒᵖ j h cf cfs (#[ cf ] j h cfu) ◦ˢᵘᵇ M⃗ i h t s f cfs
    == M⃗[ i , h ][ t ] s u

need i h t s u {j} f yes cfs cfu =
  needᵍ i h t s f cfs (#[ cf ] j h cfu)
  ∙ ap (M⃗ᵗᵒᵖ i h t s) w
  where
  cf = count-factors i h t s f

  w : #[ cf ] j h cfu ◦ f == #[ t ] i h u
  w = ap (_◦ f) (! (divisible-factor-count-factors i h t u f (fst yes) (snd yes)))
      ∙ snd yes

\end{code}


Partial matching objects: Mᵒ (object part)
------------------------------------------

Now we define the partial matching object functor.

The object part of the functor is Mᵒ.

\begin{code}

Mᵒ i h (1+ t) s = Mᵒ i h t prev ‣ A h [ M⃗[ i , h ][ t ] prev u ]
  where
  prev = prev-shape s
  u = <-from-shape s
Mᵒ i (1+ h) O s = Mᵒᶠᵘˡˡ i h [ π (𝔸 (1+ h)) ]ₜₑₗ
Mᵒ i O O s = •

\end{code}

With the definition of Mᵒ in place we can now prove Mᵗᵒᵗ= by induction on i.

\begin{code}

Mᵗᵒᵗ= O = idp
Mᵗᵒᵗ= (1+ _) = idp

-- This works too, of course.
-- Mᵗᵒᵗ= =
--   ℕ-ind
--     (λ i → M i i O (O≤ $ hom-size i i) == close (Mᵒᵗᵒᵗ i [ π (𝔸 i) ]ₜₑₗ))
--     idp
--     (λ _ _ → idp)

\end{code}

Clauses of the boundary projection M⃗ᵗᵒᵖ for f : hom i h into height level.

\begin{code}

comm :
  ∀ i j h t t' s s' (f : hom i j)
  → let cf = count-factors i h t s f in
    (p : cf == t') {cfs : shape j h cf}
  → πₜₑₗ (Mᵒ j h t' s') ◦ˢᵘᵇ idd (M= j h _ _ p) ◦ˢᵘᵇ M⃗ i h t s f cfs
    == πₜₑₗ (Mᵒ i h t s)

M⃗ᵗᵒᵖ i h (1+ t) s f =
  M⃗ᵗᵒᵖ i h t prev f ◦ˢᵘᵇ π (A h [ M⃗[ i , h ][ t ] prev u ])
  where
  prev = prev-shape s
  u = <-from-shape s

M⃗ᵗᵒᵖ i (1+ h) O s f =
  wkn-sub (Mᵒᶠᵘˡˡ i h) (Mᵒᶠᵘˡˡ (1+ h) h)
    (idd (M= (1+ h) h shf (full-shape (1+ h) h) cf-full)
      ◦ˢᵘᵇ M⃗ i h fullᵢ shpᵢ f shf)
    (comm i (1+ h) h fullᵢ (hom-size (1+ h) h) shpᵢ (full-shape (1+ h) h)
      f cf-full {shf})
    (𝔸 (1+ h))
  where
  fullᵢ = hom-size i h
  shpᵢ = full-shape i h
  shf = count-factors-shape i h fullᵢ shpᵢ f
  cf-full = count-factors-full i h shpᵢ f

M⃗ᵗᵒᵖ i O O s f = id

\end{code}

Several auxiliary lemmas.
Composition with the coercion arrows idd (M= ...) commutes with the
projections π, the generic types Aₑ, the variables υ, and the matching object
substitutions M⃗.
\begin{code}

-- The type of the "topmost" cell of the matching context M i h (1+ m) ŝ:
-- this matching context is, definitionally, an extension
--   M k h (1+ m) ŝ ≡ M k h m (prev-shape ŝ) ∷ Aₑ k h m ŝ.
Aₑ : ∀ k h m (ŝ : shape k h (1+ m)) → Ty (M k h m (prev-shape ŝ))
Aₑ k h m ŝ = A h [ M⃗[ k , h ][ m ] (prev-shape ŝ) (<-from-shape ŝ) ]

π-M=-comm :
  ∀ k h m₁ m₂ (e : m₁ == m₂)
    (ŝ₁ : shape k h (1+ m₁)) (ŝ₂ : shape k h (1+ m₂))
  → π (Aₑ k h m₂ ŝ₂) ◦ˢᵘᵇ idd (M= k h ŝ₁ ŝ₂ (ap 1+ e))
    == idd (M= k h (prev-shape ŝ₁) (prev-shape ŝ₂) e) ◦ˢᵘᵇ π (Aₑ k h m₁ ŝ₁)
π-M=-comm k h m .m idp ŝ₁ ŝ₂ =
  transp!
    (λ ŝ → π (Aₑ k h m ŝ₂) ◦ˢᵘᵇ idd (M= k h ŝ ŝ₂ idp)
         == idd (M= k h (prev-shape ŝ) (prev-shape ŝ₂) idp) ◦ˢᵘᵇ π (Aₑ k h m ŝ))
    (shape-path ŝ₁ ŝ₂)
    ( ap (λ w → π (Aₑ k h m ŝ₂) ◦ˢᵘᵇ idd w) M=-idp
      ∙ idr _
      ∙ ! (idl _)
      ∙ ! (ap (λ w → idd w ◦ˢᵘᵇ π (Aₑ k h m ŝ₂)) M=-idp) )

Aₑ-M= :
  ∀ k h m₁ m₂ (e : m₁ == m₂)
    (ŝ₁ : shape k h (1+ m₁)) (ŝ₂ : shape k h (1+ m₂))
  → Aₑ k h m₂ ŝ₂ [ idd (M= k h (prev-shape ŝ₁) (prev-shape ŝ₂) e) ]
    == Aₑ k h m₁ ŝ₁
Aₑ-M= k h m .m idp ŝ₁ ŝ₂ =
  transp!
    (λ ŝ → Aₑ k h m ŝ₂ [ idd (M= k h (prev-shape ŝ) (prev-shape ŝ₂) idp) ]
         == Aₑ k h m ŝ)
    (shape-path ŝ₁ ŝ₂)
    (ap (λ w → Aₑ k h m ŝ₂ [ idd w ]) M=-idp ∙ [id])

υ-M= :
  ∀ k h m₁ m₂ (e : m₁ == m₂)
    (ŝ₁ : shape k h (1+ m₁)) (ŝ₂ : shape k h (1+ m₂))
    (P : Aₑ k h m₁ ŝ₁ [ π (Aₑ k h m₁ ŝ₁) ]
         == Aₑ k h m₂ ŝ₂ [ π (Aₑ k h m₂ ŝ₂) ] [ idd (M= k h ŝ₁ ŝ₂ (ap 1+ e)) ])
  → coeᵀᵐ P (υ (Aₑ k h m₁ ŝ₁))
    == υ (Aₑ k h m₂ ŝ₂) [ idd (M= k h ŝ₁ ŝ₂ (ap 1+ e)) ]ₜ
υ-M= k h m .m idp ŝ₁ ŝ₂ P =
  transp!
    (λ{ (ŝ , Pₓ) → coeᵀᵐ Pₓ (υ (Aₑ k h m ŝ))
                   == υ (Aₑ k h m ŝ₂) [ idd (M= k h ŝ ŝ₂ idp) ]ₜ })
    (prop-path Σ-inst (ŝ₁ , P) (ŝ₂ , P₀))
    dgl
  where
  P₀ : Aₑ k h m ŝ₂ [ π (Aₑ k h m ŝ₂) ]
       == Aₑ k h m ŝ₂ [ π (Aₑ k h m ŝ₂) ] [ idd (M= k h ŝ₂ ŝ₂ idp) ]
  P₀ = ! ( ap (λ w → Aₑ k h m ŝ₂ [ π (Aₑ k h m ŝ₂) ] [ idd w ])
              (M=-idp {k} {h} {1+ m} {ŝ₂})
         ∙ [id] )

  Σ-inst : is-prop
    (Σ (shape k h (1+ m)) λ ŝ →
        Aₑ k h m ŝ [ π (Aₑ k h m ŝ) ]
        == Aₑ k h m ŝ₂ [ π (Aₑ k h m ŝ₂) ] [ idd (M= k h ŝ ŝ₂ idp) ])
  Σ-inst = Σ-level shape-is-prop (λ ŝ → has-level-apply Ty-is-set _ _)

  dgl : coeᵀᵐ P₀ (υ (Aₑ k h m ŝ₂))
        == υ (Aₑ k h m ŝ₂) [ idd (M= k h ŝ₂ ŝ₂ idp) ]ₜ
  dgl = from-over-set {p = P₀} (!ᵈ α)
    where
    α : υ (Aₑ k h m ŝ₂) [ idd (M= k h ŝ₂ ŝ₂ idp) ]ₜ == υ (Aₑ k h m ŝ₂)
        over⟨ ap (λ w → Aₑ k h m ŝ₂ [ π (Aₑ k h m ŝ₂) ] [ idd w ])
                 (M=-idp {k} {h} {1+ m} {ŝ₂})
              ∙ [id] ⟩
    α = ↓-ap-in Tm (λ w → Aₑ k h m ŝ₂ [ π (Aₑ k h m ŝ₂) ] [ idd w ])
          (apd (λ w → υ (Aₑ k h m ŝ₂) [ idd w ]ₜ) (M=-idp {k} {h} {1+ m} {ŝ₂}))
        ∙ᵈ [id]ₜ

M⃗-M=-comm :
  ∀ i h t₁ t₂ (e : t₁ == t₂) (s₁ : shape i h t₁) (s₂ : shape i h t₂)
    {j} (g : hom i j)
    (cgs₂ : shape j h (count-factors i h t₂ s₂ g))
    (cgs₁ : shape j h (count-factors i h t₁ s₁ g))
    (ce : count-factors i h t₁ s₁ g == count-factors i h t₂ s₂ g)
  → M⃗ i h t₂ s₂ g cgs₂ ◦ˢᵘᵇ idd (M= i h s₁ s₂ e)
    == idd (M= j h cgs₁ cgs₂ ce) ◦ˢᵘᵇ M⃗ i h t₁ s₁ g cgs₁
M⃗-M=-comm i h t .t idp s₁ s₂ {j} g cgs₂ cgs₁ ce =
  transp!
    (λ{ (ŝ , cgsₓ , ceₓ) →
        M⃗ i h t s₂ g cgs₂ ◦ˢᵘᵇ idd (M= i h ŝ s₂ idp)
        == idd (M= j h cgsₓ cgs₂ ceₓ) ◦ˢᵘᵇ M⃗ i h t ŝ g cgsₓ })
    (prop-path Σ-inst (s₁ , cgs₁ , ce) (s₂ , cgs₂ , idp))
    dgl
  where
  Σ-inst : is-prop
    (Σ (shape i h t) λ ŝ →
      Σ (shape j h (count-factors i h t ŝ g)) λ _ →
        count-factors i h t ŝ g == count-factors i h t s₂ g)
  Σ-inst =
    Σ-level shape-is-prop
      (λ ŝ → Σ-level shape-is-prop (λ _ → ℕ-id-is-prop))

  dgl : M⃗ i h t s₂ g cgs₂ ◦ˢᵘᵇ idd (M= i h s₂ s₂ idp)
        == idd (M= j h cgs₂ cgs₂ idp) ◦ˢᵘᵇ M⃗ i h t s₂ g cgs₂
  dgl = ap (λ w → M⃗ i h t s₂ g cgs₂ ◦ˢᵘᵇ idd w) M=-idp
         ∙ idr _
         ∙ ! (idl _)
         ∙ ! (ap (λ w → idd w ◦ˢᵘᵇ M⃗ i h t s₂ g cgs₂) M=-idp)

\end{code}



Partial matching objects: M⃗ (morphism part)
--------------------------------------------

Now, the action M⃗ of the partial matching object on morphisms f.

We need the following commutation lemma in its definition.


The recursive definition of M⃗ in the (i, h, t+1) case requires its type to
compute to the appropriate value depending on whether or not f divides [t]ⁱₕ. To
actually allow this computation to occur, the type needs to expose an argument
of type (Dec (f ∣ #[ t ] i h u)).

\begin{code}

M⃗[_,_,1+_]-deptype :
  ∀ i h t (s : shape i h (1+ t)) {j} (f : hom i j)
  → (d : Dec (f ∣ #[ t ] i h (<-from-shape s)))
  → {cfs : shape j h (count-factors-aux i h t (<-from-shape s) f d)}
  → Type _
M⃗[ i , h ,1+ t ]-deptype s {j} f d {cfs} =
  Sub (M i h (1+ t) s)
      (M j h (count-factors-aux i h t (<-from-shape s) f d) cfs)

\end{code}

We also expose the discriminant in an auxiliary implementation of M⃗ (i, h, t+1);
this will be needed when defining M⃗◦.

\begin{code}

M⃗[_,_,1+_] :
  ∀ i h t s {j} (f : hom i j)
  → let u = <-from-shape s in
    (d : Dec (f ∣ #[ t ] i h u))
  → (cfs : shape j h (count-factors-aux i h t u f d))
  → M⃗[ i , h ,1+ t ]-deptype s f d {cfs}

M⃗[ i , h ,1+ t ] s {j} f d@(inl yes) cfs =
  M⃗ i h t prev f prev-cfs ◦ˢᵘᵇ π (A h [ _ ]) ,, (υ _ ◂$ coeᵀᵐ q)
  where
  prev = prev-shape s
  u = <-from-shape s
  cf = count-factors i h t prev f
  prev-cfs = prev-shape cfs
  cfu = <-from-shape cfs
  [cf] = #[ cf ] j h cfu

  p : M⃗[ j , h ][ cf ] prev-cfs cfu ◦ˢᵘᵇ M⃗ i h t prev f prev-cfs
      == M⃗[ i , h ][ t ] prev u
  p = need i h t prev u f yes prev-cfs cfu

  q : A h [ M⃗[ i , h ][ t ] prev u ] [ π _ ] ==
      A h [ M⃗[ j , h ][ cf ] prev-cfs cfu ] [ M⃗ i h t prev f _ ◦ˢᵘᵇ π _ ]
  q = ap (_[ π _ ]) ([= ! p ] ∙ [◦]) ∙ ! [◦]

M⃗[ i , h ,1+ t ] s f (inr no) _ = M⃗ i h t prev f _ ◦ˢᵘᵇ π (A h [ _ ])
  where prev = prev-shape s

\end{code}

Now we can wrap the above up into a definition of M⃗. We also define the
(i, h+1, 0) and (i, 0, 0) cases.

\begin{code}

M⃗ i h (1+ t) s f _ = M⃗[ i , h ,1+ t ] s f (f ∣? #[ t ] i h u) _
  where u = <-from-shape s

M⃗ i (1+ h) O s {j} f _ =
  wkn-sub (Mᵒᶠᵘˡˡ i h) (Mᵒᶠᵘˡˡ j h)
    (idd eq ◦ˢᵘᵇ M⃗ i h fullᵢ shpᵢ f _)
    (comm i j h fullᵢ fullⱼ shpᵢ shpⱼ f cf-fullⱼ)
    (𝔸 (1+ h))
  where
  fullᵢ = hom-size i h
  shpᵢ = full-shape i h

  cf = count-factors i h fullᵢ shpᵢ f
  sh = count-factors-shape i h fullᵢ shpᵢ f

  fullⱼ = hom-size j h
  shpⱼ = full-shape j h

  cf-fullⱼ = count-factors-full i h shpᵢ f

  eq : M j h cf sh == M j h fullⱼ shpⱼ
  eq = M= j h _ _ cf-fullⱼ

M⃗ i O O s f _ = id

\end{code}

Proof of the "new" (compared to the attempts from some years ago) condition
needᵍ. This is similar to the clauses of M⃗ᵗᵒᵖ and M⃗.

\begin{code}

needᵍ i h (1+ t) s {j} f cfs g =
  decase (discrim i h t (<-from-shape s) f) cfs
  where
  prev = prev-shape s
  u = <-from-shape s

  decase :
    (d : Dec (f ∣ #[ t ] i h u))
    (cfsₓ : shape j h (count-factors-aux i h t u f d))
    → M⃗ᵗᵒᵖ j h (count-factors-aux i h t u f d) cfsₓ g
        ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f d cfsₓ
      == M⃗ᵗᵒᵖ i h (1+ t) s (g ◦ f)
  decase (inl yes) cfsₓ =
    assˢᵘᵇ
    ∙ ap (M⃗ᵗᵒᵖ j h _ (prev-shape cfsₓ) g ◦ˢᵘᵇ_) βπ
    ∙ ! assˢᵘᵇ
    ∙ ap (_◦ˢᵘᵇ π (A h [ M⃗[ i , h ][ t ] prev u ]))
         (needᵍ i h t prev f (prev-shape cfsₓ) g)
  decase (inr no) cfsₓ =
    ! assˢᵘᵇ
    ∙ ap (_◦ˢᵘᵇ π (A h [ M⃗[ i , h ][ t ] prev u ]))
         (needᵍ i h t prev f cfsₓ g)

needᵍ i (1+ h) O s {j} f cfs g =
  wkn-sub-unique Θₖ X (Wg ◦ˢᵘᵇ Wf) Wgf cond1 cond2
  where
  X = 𝔸 (1+ h)
  Θᵢ = Mᵒᶠᵘˡˡ i h
  Θⱼ = Mᵒᶠᵘˡˡ j h
  Θₖ = Mᵒᶠᵘˡˡ (1+ h) h

  fullᵢ = hom-size i h
  shpᵢ = full-shape i h
  fullⱼ = hom-size j h
  shpⱼ = full-shape j h
  fullₖ = hom-size (1+ h) h
  shpₖ = full-shape (1+ h) h

  cf' = count-factors i h fullᵢ shpᵢ f
  shf = count-factors-shape i h fullᵢ shpᵢ f
  cf-fullⱼ = count-factors-full i h shpᵢ f
  σf = idd (M= j h shf shpⱼ cf-fullⱼ) ◦ˢᵘᵇ M⃗ i h fullᵢ shpᵢ f shf
  pf = comm i j h fullᵢ fullⱼ shpᵢ shpⱼ f cf-fullⱼ {shf}

  cg' = count-factors j h fullⱼ shpⱼ g
  shg = count-factors-shape j h fullⱼ shpⱼ g
  cg-fullₖ = count-factors-full j h shpⱼ g
  σg = idd (M= (1+ h) h shg shpₖ cg-fullₖ) ◦ˢᵘᵇ M⃗ j h fullⱼ shpⱼ g shg
  pg = comm j (1+ h) h fullⱼ fullₖ shpⱼ shpₖ g cg-fullₖ {shg}

  cgf' = count-factors i h fullᵢ shpᵢ (g ◦ f)
  shgf = count-factors-shape i h fullᵢ shpᵢ (g ◦ f)
  cgf-fullₖ = count-factors-full i h shpᵢ (g ◦ f)
  σgf = idd (M= (1+ h) h shgf shpₖ cgf-fullₖ) ◦ˢᵘᵇ M⃗ i h fullᵢ shpᵢ (g ◦ f) shgf
  pgf = comm i (1+ h) h fullᵢ fullₖ shpᵢ shpₖ (g ◦ f) cgf-fullₖ {shgf}

  Wf = wkn-sub Θᵢ Θⱼ σf pf X
  Wg = wkn-sub Θⱼ Θₖ σg pg X
  Wgf = wkn-sub Θᵢ Θₖ σgf pgf X

  cgs× = count-factors-shape j h cf' shf g
  ce× : count-factors j h cf' shf g == cg'
  ce× = count-factors= j h g cf' fullⱼ cf-fullⱼ
  p× : cgf' == count-factors j h cf' shf g
  p× = count-factors-comp i h fullᵢ shpᵢ f g shf

  F : σg ◦ˢᵘᵇ σf == σgf
  F =
    assˢᵘᵇ
    ∙ ap (idd (M= (1+ h) h shg shpₖ cg-fullₖ) ◦ˢᵘᵇ_) (! assˢᵘᵇ)
    ∙ ap (λ w → idd (M= (1+ h) h shg shpₖ cg-fullₖ)
                ◦ˢᵘᵇ (w ◦ˢᵘᵇ M⃗ i h fullᵢ shpᵢ f shf))
         (M⃗-M=-comm j h cf' fullⱼ cf-fullⱼ shf shpⱼ g shg cgs× ce×)
    ∙ ap (idd (M= (1+ h) h shg shpₖ cg-fullₖ) ◦ˢᵘᵇ_) assˢᵘᵇ
    ∙ ap (λ w → idd (M= (1+ h) h shg shpₖ cg-fullₖ)
                ◦ˢᵘᵇ (idd (M= (1+ h) h cgs× shg ce×) ◦ˢᵘᵇ w))
         (M⃗◦ i h fullᵢ shpᵢ f g shf cgs× shgf p×)
    ∙ ! assˢᵘᵇ
    ∙ ap (_◦ˢᵘᵇ (idd (M= (1+ h) h shgf cgs× p×)
                 ◦ˢᵘᵇ M⃗ i h fullᵢ shpᵢ (g ◦ f) shgf))
         ( idd-◦ (M= (1+ h) h cgs× shg ce×) (M= (1+ h) h shg shpₖ cg-fullₖ)
         ∙ ap idd (M=-∙ (1+ h) h cgs× shg shpₖ ce× cg-fullₖ) )
    ∙ ! assˢᵘᵇ
    ∙ ap (_◦ˢᵘᵇ M⃗ i h fullᵢ shpᵢ (g ◦ f) shgf)
         ( idd-◦ (M= (1+ h) h shgf cgs× p×)
                 (M= (1+ h) h cgs× shpₖ (ce× ∙ cg-fullₖ))
         ∙ ap idd
             ( M=-∙ (1+ h) h shgf cgs× shpₖ p× (ce× ∙ cg-fullₖ)
             ∙ ap (M= (1+ h) h shgf shpₖ)
                  (prop-path ℕ-id-is-prop (p× ∙ ce× ∙ cg-fullₖ) cgf-fullₖ) ) )

  cond1 : (π X ++ₛ Θₖ) ◦ˢᵘᵇ (Wg ◦ˢᵘᵇ Wf) == (π X ++ₛ Θₖ) ◦ˢᵘᵇ Wgf
  cond1 =
    ! assˢᵘᵇ
    ∙ ap (_◦ˢᵘᵇ Wf) (wkn-sub-comm Θⱼ Θₖ σg pg X)
    ∙ assˢᵘᵇ
    ∙ ap (σg ◦ˢᵘᵇ_) (wkn-sub-comm Θᵢ Θⱼ σf pf X)
    ∙ ! assˢᵘᵇ
    ∙ ap (_◦ˢᵘᵇ (π X ++ₛ Θᵢ)) F
    ∙ ! (wkn-sub-comm Θᵢ Θₖ σgf pgf X)

  cond2 : πₜₑₗ (wkₜₑₗ Θₖ) ◦ˢᵘᵇ (Wg ◦ˢᵘᵇ Wf) == πₜₑₗ (wkₜₑₗ Θₖ) ◦ˢᵘᵇ Wgf
  cond2 =
    ! assˢᵘᵇ
    ∙ ap (_◦ˢᵘᵇ Wf) (wkn-sub-π Θⱼ Θₖ σg pg X)
    ∙ wkn-sub-π Θᵢ Θⱼ σf pf X
    ∙ ! (wkn-sub-π Θᵢ Θₖ σgf pgf X)

needᵍ i O O s {j} f cfs g = idl id

\end{code}

Can this go here?

\begin{code}

idd◦M⃗=' :
  ∀ i h t s {j} (f : hom i j)
  → let cf = count-factors i h t s f in
    (s₀ s₁ : shape j h cf)
  → (p q : cf == cf)
  → idd (M= j h s₀ s₁ p) ◦ˢᵘᵇ M⃗ i h t s f s₀ ==
    idd (M= j h s₁ s₁ q) ◦ˢᵘᵇ M⃗ i h t s f s₁
idd◦M⃗=' i h t s {j} f s₀ s₁ p q =
  ap (λ (sₓ , e) → idd (M= j h sₓ s₁ e) ◦ˢᵘᵇ M⃗ i h t s f sₓ)
     (pair×=
       (prop-path shape-is-prop s₀ s₁)
       (prop-path has-level-apply-instance p q))

-- The special case of comm where the coercion arrow is trivial.
comm-unidd :
  ∀ i j h t s (f : hom i j) s''
  → πₜₑₗ (Mᵒ j h (count-factors i h t s f) s'') ◦ˢᵘᵇ M⃗ i h t s f s''
    == πₜₑₗ (Mᵒ i h t s)
comm-unidd i j h t s f s'' =
  ! (ap (πₜₑₗ (Mᵒ j h (count-factors i h t s f) s'') ◦ˢᵘᵇ_)
        (ap (λ w → idd w ◦ˢᵘᵇ M⃗ i h t s f s'') M=-idp ∙ idl _))
  ∙ comm i j h t _ s s'' f idp {s''}

comm i j h (1+ t) _ s s' f idp {cfs} =
  ap (πₜₑₗ (Mᵒ j h (count-factors i h (1+ t) s f) s') ◦ˢᵘᵇ_)
     ( idd◦M⃗=' i h (1+ t) s f cfs s' idp idp
     ∙ ap (λ w → idd w ◦ˢᵘᵇ M⃗ i h (1+ t) s f s') M=-idp
     ∙ idl _ )
  ∙ core (discrim i h t (<-from-shape s) f) s'
  where
  core :
    (d : Dec (f ∣ #[ t ] i h (<-from-shape s)))
    (s'' : shape j h (count-factors-aux i h t (<-from-shape s) f d))
    → πₜₑₗ (Mᵒ j h (count-factors-aux i h t (<-from-shape s) f d) s'')
        ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f d s''
      == πₜₑₗ (Mᵒ i h (1+ t) s)
  core (inl yes) s'' =
    assˢᵘᵇ
    ∙ ap (πₜₑₗ (Mᵒ j h _ (prev-shape s'')) ◦ˢᵘᵇ_) βπ
    ∙ ! assˢᵘᵇ
    ∙ ap (_◦ˢᵘᵇ π (A h [ M⃗[ i , h ][ t ] (prev-shape s) (<-from-shape s) ]))
         (comm-unidd i j h t (prev-shape s) f (prev-shape s''))
  core (inr no) s'' =
    ! assˢᵘᵇ
    ∙ ap (_◦ˢᵘᵇ π (A h [ M⃗[ i , h ][ t ] (prev-shape s) (<-from-shape s) ]))
         (comm-unidd i j h t (prev-shape s) f s'')

comm i j (1+ h) O _ s s' f idp {cfs} =
  ap (πₜₑₗ (Mᵒ j (1+ h) (count-factors i (1+ h) O s f) s') ◦ˢᵘᵇ_)
     ( idd◦M⃗=' i (1+ h) O s f cfs s' idp idp
     ∙ ap (λ w → idd w ◦ˢᵘᵇ M⃗ i (1+ h) O s f s') M=-idp
     ∙ idl _ )
  ∙ wkn-sub-π (Mᵒᶠᵘˡˡ i h) (Mᵒᶠᵘˡˡ j h)
      (idd (M= j h (count-factors-shape i h (hom-size i h) (full-shape i h) f)
                   (full-shape j h)
                   (count-factors-full i h (full-shape i h) f))
        ◦ˢᵘᵇ M⃗ i h (hom-size i h) (full-shape i h) f
             (count-factors-shape i h (hom-size i h) (full-shape i h) f))
      (comm i j h (hom-size i h) (hom-size j h) (full-shape i h)
        (full-shape j h) f (count-factors-full i h (full-shape i h) f))
      (𝔸 (1+ h))
comm i j O O cf s s' f idp {cfs} =
  πₜₑₗ • ◦ˢᵘᵇ idd (M= j O cfs s' idp) ◦ˢᵘᵇ id
  =⟨ (idd◦M⃗=' i O O s f cfs s' idp idp) |in-ctx (πₜₑₗ • ◦ˢᵘᵇ_) ⟩
  πₜₑₗ • ◦ˢᵘᵇ idd (M= j O s' s' idp) ◦ˢᵘᵇ id
  =⟨ M=-idp |in-ctx (λ ◻ → πₜₑₗ • ◦ˢᵘᵇ idd ◻ ◦ˢᵘᵇ id) ⟩
  πₜₑₗ • ◦ˢᵘᵇ idd idp ◦ˢᵘᵇ id
  =⟨ idl (id ◦ˢᵘᵇ id) ∙ idl id ⟩
  πₜₑₗ •
  =∎

\end{code}

We also need to transport along equalities giving the values of
  M⃗ (j, h, count-factors (i, h, t) f) g
in each of the cases where g divides, or does not divide, [count-factors...]ʲₕ.

\begin{code}

idd◦M⃗= :
  ∀ i h t (s : shape i h (1+ t))
  → ∀ {j} (f : hom i j)
  → (d : Dec (f ∣ #[ t ] i h (<-from-shape s)))
  → let c = count-factors-aux i h t (<-from-shape s) f d in
    (s₀ s₁ : shape j h c)
  → (p q : c == c)
  → idd (M= j h s₀ s₁ p) ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f d s₀ ==
    idd (M= j h s₁ s₁ q) ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f d s₁
idd◦M⃗= i h t s {j} f d s₀ s₁ p q =
  ap (λ (sₓ , e) → idd (M= j h sₓ s₁ e) ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f d sₓ)
     (pair×=
       (prop-path shape-is-prop s₀ s₁)
       (prop-path has-level-apply-instance p q))

M⃗rec=-yes :
  ∀ i h t (s : shape i h (1+ t)) {j} (f : hom i j)
  → let prev = prev-shape s
        cf = count-factors i h (1+ t) s f
        cfp = count-factors i h t prev f
    in
    (yes : f ∣ #[ t ] i h (<-from-shape s))
    (cfs : shape j h cf)
    (cfs' : shape j h (1+ cfp))
  → let r = count-factors-divisible i h t s f yes
    in
    M⃗ i h (1+ t) s f cfs
    ==
    idd (M= j h cfs' cfs (! r)) ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f (inl yes) cfs'
M⃗rec=-yes i h t s {j} f yes cfs cfs' =
  transp F (prop-path Dec-∣-is-prop (inl yes) (discrim i h t (<-from-shape s) f))
    base cfs
  where
  u : t < hom-size i h
  u = <-from-shape s

  prev : shape i h t
  prev = prev-shape s

  cfp : ℕ
  cfp = count-factors i h t prev f

  Dec-∣-is-prop : is-prop (Dec (f ∣ #[ t ] i h (<-from-shape s)))
  Dec-∣-is-prop = {! certainly true!}

  F : Dec (f ∣ #[ t ] i h (<-from-shape s)) → Type ℓₘ
  F d =
    (cfsₓ : shape j h (count-factors-aux i h t u f d))
    → M⃗[ i , h ,1+ t ] s f d cfsₓ
      == idd (M= j h cfs' cfsₓ
                (! (count-factors-divisible-aux i h t u f d yes {prev})))
         ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f (inl yes) cfs'

  base : F (inl yes)
  base cfsₓ =
    ! (ap (λ w → idd w ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f (inl yes) cfsₓ)
          (M=-idp {j} {h} {1+ cfp} {cfsₓ})
       ∙ idl _)
    ∙ ! (idd◦M⃗= i h t s f (inl yes) cfs' cfsₓ (! r₁) idp)
    where
    r₁ : count-factors-aux i h t u f (inl yes)
         == 1+ (count-factors i h t prev f)
    r₁ = count-factors-divisible-aux i h t u f (inl yes) yes {prev}

abstract
  M⃗rec=-no :
    ∀ i h t (s : shape i h (1+ t)) {j} (f : hom i j)
    → (no : ¬ (f ∣ #[ t ] i h (<-from-shape s)))
    → let prev = prev-shape s
          cf = count-factors i h (1+ t) s f
          cfp = count-factors i h t prev f
          p = count-factors-not-divisible i h t s f no
      in
      (cfs : shape j h cf) (cfps : shape j h cfp)
    → M⃗ i h (1+ t) s f cfs ==
      idd (M= j h cfps cfs (! p)) ◦ˢᵘᵇ M⃗ i h t prev f cfps ◦ˢᵘᵇ π (A h [ _ ])
  M⃗rec=-no i h t s {j} f no cfs cfps with discrim i h t (<-from-shape s) f
  ... | inl yes = ⊥-rec $ no yes
  ... | inr no' =
        ! $
        idd (M= j h cfps cfs p)
          ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f (inr no') cfps
        =⟨ idd◦M⃗= i h t s f (inr no') cfps cfs p idp ⟩
        idd (M= j h cfs cfs idp) ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f (inr no') cfs
        =⟨ ap
            (λ ◻ →
              idd (ap (M j h _) ◻) ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f (inr no') cfs)
              (prop-path shape-id-is-prop (shape-path cfs cfs) idp)
        ⟩
        id ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f (inr no') cfs
        =⟨ idl _ ⟩
        M⃗[ i , h ,1+ t ] s f (inr no') cfs
        =∎
        where
        p : count-factors-aux i h t (<-from-shape s) f (inr no') ==
            count-factors-aux i h t (<-from-shape s) f (inr no')
        p = ! $ count-factors-not-divisible-aux i h t (<-from-shape s)
                  f (inr no') no

\end{code}

The bridge between the boundary projection M⃗ᵗᵒᵖ and the generic matching
object substitution M⃗: composing the latter with the coercion arrow
idd (M-improper= ...) gives the former.  The proof is by the same case
analysis as the definition of M⃗ᵗᵒᵖ; the tip case uses the computation rule
M⃗rec=-no, since no morphism of hom i h divides another one.

\begin{code}

M⃗ᵗᵒᵖ= i h (1+ t) s f cfs =
  transp G (prop-path Dec-∣-is-prop (inr no) (discrim i h t u f)) base cfs
  where
  prev = prev-shape s
  u = <-from-shape s

  no : ¬ (f ∣ #[ t ] i h u)
  no = ¬divides-same-target i h t u f

  Dec-∣-is-prop : is-prop (Dec (f ∣ #[ t ] i h u))
  Dec-∣-is-prop = {! certainly true !}

  G : Dec (f ∣ #[ t ] i h u) → Type ℓₘ
  G d =
    (cfsₓ : shape h h (count-factors-aux i h t u f d))
    → M⃗ᵗᵒᵖ i h (1+ t) s f
      == idd (M= h h cfsₓ (O≤ _) (count-factors-top-level-aux i h t u f d)
              ∙ Mᵗᵒᵗ= h)
         ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f d cfsₓ

  base : G (inr no)
  base cfsₓ =
    ap (_◦ˢᵘᵇ π (A h [ M⃗[ i , h ][ t ] prev u ])) (M⃗ᵗᵒᵖ= i h t prev f cfsₓ)
    ∙ assˢᵘᵇ

M⃗ᵗᵒᵖ= i (1+ h) O s f cfs =
  transp!
    (λ sₓ → M⃗ᵗᵒᵖ i (1+ h) O s f
          == idd (M-improper= i (1+ h) O s f sₓ) ◦ˢᵘᵇ M⃗ i (1+ h) O s f sₓ)
    (shape-path cfs (O≤ _))
    (! ( ap (λ w → idd (w ∙ Mᵗᵒᵗ= (1+ h)) ◦ˢᵘᵇ M⃗ i (1+ h) O s f (O≤ _))
            (M=-idp {1+ h} {1+ h} {O} {O≤ _})
       ∙ idl _ ))

M⃗ᵗᵒᵖ= i O O s f cfs =
  transp!
    (λ sₓ → M⃗ᵗᵒᵖ i O O s f
          == idd (M-improper= i O O s f sₓ) ◦ˢᵘᵇ M⃗ i O O s f sₓ)
    (shape-path cfs (O≤ _))
    (! ( ap (λ w → idd (w ∙ Mᵗᵒᵗ= O) ◦ˢᵘᵇ M⃗ i O O s f (O≤ _))
            (M=-idp {O} {O} {O} {O≤ _})
       ∙ idl _ ))

\end{code}


Partial matching objects: M⃗◦ (functoriality)
---------------------------------------------

Again, in the (i, h, t+1) case we need the type of M⃗◦ to compute on whether or
not certain morphisms divide [t]ⁱₕ.

\begin{code}

M⃗◦[_,_,1+_]-deptype :
  ∀ i h t (s : shape i h (1+ t))
    {j} (f : hom i j) {k} (g : hom j k)
  → let u = <-from-shape s in
    Dec (g ◦ f ∣ #[ t ] i h u)
  → Dec (f ∣ #[ t ] i h u)
  → Type _
M⃗◦[ i , h ,1+ t ]-deptype s {j} f {k} g dgf df =
  let u = <-from-shape s
      cf = count-factors-aux i h t u f df
  in
    (cfs : shape j h cf)
  → let cg = count-factors j h cf cfs g
        c[gf] = count-factors-aux i h t u (g ◦ f) dgf
        c[g][f] = count-factors j h cf cfs g
    in
    (cgs : shape k h cg)
    (cgfs : shape k h c[gf])
    (p : c[gf] == c[g][f])
  → M⃗ j h cf cfs g cgs ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f df cfs
    ==
    idd (M= k h cgfs cgs p) ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s (g ◦ f) dgf cgfs

M⃗◦[_,_,1+_] :
  ∀ i h t (s : shape i h (1+ t))
    {j} (f : hom i j) {k} (g : hom j k)
  → let u = <-from-shape s in
    (dgf : Dec (g ◦ f ∣ #[ t ] i h u))
  → (df : Dec (f ∣ #[ t ] i h u))
  → M⃗◦[ i , h ,1+ t ]-deptype s f g dgf df

M⃗◦[ i , h ,1+ t ] s {j} f {k} g (inl yes[gf]) (inl yes[f]) cfs cgs cgfs p =
  idd-cancel-l Ẽ _ _ main
  where
  prev = prev-shape s
  prev-cfs = prev-shape cfs
  prev-cgfs = prev-shape cgfs

  u = <-from-shape s
  cfp = count-factors i h t prev f
  cgfp = count-factors i h t prev (g ◦ f)

  yes[g] = comp-divides-second-divides i h t u f g yes[gf]

  cfpu = <-from-shape cfs

  cgp = count-factors j h cfp prev-cfs g

  r : count-factors j h (1+ cfp) cfs g == 1+ cgp
  r = count-factors-divisible j h cfp cfs g yes[g] {prev-cfs}

  cgs' : shape k h (1+ cgp)
  cgs' = transp (shape k h) r cgs

  prev-cgs' = prev-shape cgs'

  p' : cgfp == cgp
  p' = count-factors-comp i h t prev f g prev-cfs

  Ẽ = M= k h cgs cgs' r

  cgfpu = <-from-shape cgfs

  Bᵢ = A h [ M⃗[ i , h ][ t ] prev u ]
  Bⱼ = A h [ M⃗[ j , h ][ cfp ] prev-cfs cfpu ]

  P_f = M⃗[ i , h ,1+ t ] s f (inl yes[f]) cfs
  P_gf = M⃗[ i , h ,1+ t ] s (g ◦ f) (inl yes[gf]) cgfs
  P_g = M⃗[ j , h ,1+ cfp ] cfs g (inl yes[g]) cgs'

  -- Explicit reconstructions of the coercion paths appearing inside the
  -- bodies of P_f, P_g and P_gf (needed to guide elaboration below).
  p_fⁱ : M⃗[ j , h ][ cfp ] prev-cfs cfpu ◦ˢᵘᵇ M⃗ i h t prev f prev-cfs
         == M⃗[ i , h ][ t ] prev u
  p_fⁱ = need i h t prev u f yes[f] prev-cfs cfpu

  q_fⁱ : Bᵢ [ π Bᵢ ] == Bⱼ [ M⃗ i h t prev f prev-cfs ◦ˢᵘᵇ π Bᵢ ]
  q_fⁱ = ap (_[ π Bᵢ ]) ([= ! p_fⁱ ] ∙ [◦]) ∙ ! [◦]

  p_gⁱ : M⃗[ k , h ][ cgp ] prev-cgs' (<-from-shape cgs')
           ◦ˢᵘᵇ M⃗ j h cfp prev-cfs g prev-cgs'
         == M⃗[ j , h ][ cfp ] prev-cfs cfpu
  p_gⁱ = need j h cfp prev-cfs cfpu g yes[g] prev-cgs' (<-from-shape cgs')

  q_gⁱ : Bⱼ [ π Bⱼ ]
         == A h [ M⃗[ k , h ][ cgp ] prev-cgs' (<-from-shape cgs') ]
            [ M⃗ j h cfp prev-cfs g prev-cgs' ◦ˢᵘᵇ π Bⱼ ]
  q_gⁱ = ap (_[ π Bⱼ ]) ([= ! p_gⁱ ] ∙ [◦]) ∙ ! [◦]

  p_gfⁱ : M⃗[ k , h ][ cgfp ] prev-cgfs cgfpu
            ◦ˢᵘᵇ M⃗ i h t prev (g ◦ f) prev-cgfs
          == M⃗[ i , h ][ t ] prev u
  p_gfⁱ = need i h t prev u (g ◦ f) yes[gf] prev-cgfs cgfpu

  q_gfⁱ : Bᵢ [ π Bᵢ ]
          == A h [ M⃗[ k , h ][ cgfp ] prev-cgfs cgfpu ]
             [ M⃗ i h t prev (g ◦ f) prev-cgfs ◦ˢᵘᵇ π Bᵢ ]
  q_gfⁱ = ap (_[ π Bᵢ ]) ([= ! p_gfⁱ ] ∙ [◦]) ∙ ! [◦]

  lemA : idd Ẽ ◦ˢᵘᵇ M⃗ j h (1+ cfp) cfs g cgs == P_g
  lemA =
    ap (idd Ẽ ◦ˢᵘᵇ_) (M⃗rec=-yes j h cfp cfs g yes[g] cgs cgs')
    ∙ ! assˢᵘᵇ
    ∙ ap (_◦ˢᵘᵇ P_g)
        ( idd-◦ (M= k h cgs' cgs (! r)) Ẽ
        ∙ ap idd ( M=-∙ k h cgs' cgs cgs' (! r) r
                 ∙ ap (M= k h cgs' cgs') (!-inv-l r)
                 ∙ M=-idp ) )
    ∙ idl P_g

  first : π (Aₑ k h cgp cgs') ◦ˢᵘᵇ (P_g ◦ˢᵘᵇ P_f)
          == π (Aₑ k h cgp cgs')
             ◦ˢᵘᵇ (idd (M= k h cgfs cgs' (ap 1+ p')) ◦ˢᵘᵇ P_gf)
  first =
    ! assˢᵘᵇ
    ∙ ap (_◦ˢᵘᵇ P_f) βπ
    ∙ assˢᵘᵇ
    ∙ ap (M⃗ j h cfp prev-cfs g prev-cgs' ◦ˢᵘᵇ_) βπ
    ∙ ! assˢᵘᵇ
    ∙ ap (_◦ˢᵘᵇ π (A h [ M⃗[ i , h ][ t ] prev u ]))
         (M⃗◦ i h t prev f g prev-cfs prev-cgs' prev-cgfs p')
    ∙ assˢᵘᵇ
    ∙ ! ( ! assˢᵘᵇ
        ∙ ap (_◦ˢᵘᵇ P_gf) (π-M=-comm k h cgfp cgp p' cgfs cgs')
        ∙ assˢᵘᵇ
        ∙ ap (idd (M= k h prev-cgfs prev-cgs' p') ◦ˢᵘᵇ_) βπ )

  P̂ : Aₑ k h cgfp cgfs [ π (Aₑ k h cgfp cgfs) ]
      == Aₑ k h cgp cgs' [ π (Aₑ k h cgp cgs') ]
         [ idd (M= k h cgfs cgs' (ap 1+ p')) ]
  P̂ = ! ( ![◦]
        ∙ [= π-M=-comm k h cgfp cgp p' cgfs cgs' ]
        ∙ [◦]
        ∙ ap (_[ π (Aₑ k h cgfp cgfs) ]) (Aₑ-M= k h cgfp cgp p' cgfs cgs') )

  second : coe!ᵀᵐ [◦] (υ (Aₑ k h cgp cgs') [ P_g ◦ˢᵘᵇ P_f ]ₜ)
           == coe!ᵀᵐ [◦]
                (υ (Aₑ k h cgp cgs')
                  [ idd (M= k h cgfs cgs' (ap 1+ p')) ◦ˢᵘᵇ P_gf ]ₜ)
           over⟨ [= first ] ⟩
  second = over-irr (chainL ∙ᵈ !ᵈ chainR)
    where
    chainL =
      coeᵀᵐ-out ![◦] (υ (Aₑ k h cgp cgs') [ P_g ◦ˢᵘᵇ P_f ]ₜ)
      ∙ᵈ [◦]ₜ
      ∙ᵈ (βυ |in-ctx↓ᵀᵐ _[ P_f ]ₜ)
      ∙ᵈ !ᵈ (coeᵀᵐ-[]ₜ-stable q_gⁱ (υ Bⱼ) P_f)
      ∙ᵈ βυ
      ∙ᵈ coeᵀᵐ-out q_fⁱ (υ Bᵢ)

    chainR =
      coeᵀᵐ-out ![◦]
        (υ (Aₑ k h cgp cgs')
          [ idd (M= k h cgfs cgs' (ap 1+ p')) ◦ˢᵘᵇ P_gf ]ₜ)
      ∙ᵈ [◦]ₜ
      ∙ᵈ ap (_[ P_gf ]ₜ) (! (υ-M= k h cgfp cgp p' cgfs cgs' P̂))
      ∙ᵈ !ᵈ (coeᵀᵐ-[]ₜ-stable P̂ (υ (Aₑ k h cgfp cgfs)) P_gf)
      ∙ᵈ βυ
      ∙ᵈ coeᵀᵐ-out q_gfⁱ (υ Bᵢ)

  KEY : P_g ◦ˢᵘᵇ P_f == idd (M= k h cgfs cgs' (ap 1+ p')) ◦ˢᵘᵇ P_gf
  KEY = sub= _ _ first second

  main : idd Ẽ ◦ˢᵘᵇ (M⃗ j h (1+ cfp) cfs g cgs ◦ˢᵘᵇ P_f)
         == idd Ẽ ◦ˢᵘᵇ (idd (M= k h cgfs cgs p) ◦ˢᵘᵇ P_gf)
  main =
    ! assˢᵘᵇ
    ∙ ap (_◦ˢᵘᵇ P_f) lemA
    ∙ KEY
    ∙ ! ( ! assˢᵘᵇ
        ∙ ap (_◦ˢᵘᵇ P_gf)
             ( idd-◦ (M= k h cgfs cgs p) Ẽ
             ∙ ap idd (M=-∙ k h cgfs cgs cgs' p r) )
        ∙ ap (λ w → idd (M= k h cgfs cgs' w) ◦ˢᵘᵇ P_gf)
             (prop-path ℕ-id-is-prop (p ∙ r) (ap 1+ p')) )

M⃗◦[ i , h ,1+ t ] s f g (inl yes[gf]) (inr no[f]) =
  ⊥-rec $ no[f] $ comp-divides-first-divides i h t _ f g yes[gf]

M⃗◦[ i , h ,1+ t ] s {j} f {k} g (inr no[gf]) (inl yes[f]) cfs cgs cgfs p =

  M⃗ j h (1+ cfp) cfs g cgs ◦ˢᵘᵇ (M⃗ i h t prev f prev-cfs ◦ˢᵘᵇ π (A h [ _ ]) ,, _)

  =⟨ ap (_◦ˢᵘᵇ (M⃗ i h t prev f prev-cfs ◦ˢᵘᵇ π (A h [ _ ]) ,, _))
        (M⃗rec=-no j h cfp cfs g no[g] cgs cgs') ⟩

  (idd (M= k h cgs' cgs (! q)) ◦ˢᵘᵇ M⃗ j h cfp prev-cfs g cgs'
    ◦ˢᵘᵇ π (A h [ _ ]))
  ◦ˢᵘᵇ (M⃗ i h t prev f prev-cfs ◦ˢᵘᵇ π (A h [ _ ]) ,, _)

  =⟨ assˢᵘᵇ ∙ ap (idd (M= k h cgs' cgs (! q)) ◦ˢᵘᵇ_) assˢᵘᵇ ⟩

  idd (M= k h cgs' cgs (! q)) ◦ˢᵘᵇ M⃗ j h cfp prev-cfs g cgs'
  ◦ˢᵘᵇ π (A h [ _ ]) ◦ˢᵘᵇ (M⃗ i h t prev f prev-cfs ◦ˢᵘᵇ π (A h [ _ ]) ,, _)

  =⟨ βπ
   |in-ctx (λ ◻ →
     idd (M= k h cgs' cgs (! q))
     ◦ˢᵘᵇ M⃗ j h cfp prev-cfs g cgs'
     ◦ˢᵘᵇ ◻) ⟩

  idd (M= k h cgs' cgs (! q)) ◦ˢᵘᵇ M⃗ j h cfp prev-cfs g cgs'
  ◦ˢᵘᵇ M⃗ i h t prev f prev-cfs ◦ˢᵘᵇ π (A h [ _ ])

  =⟨ ap (idd (M= k h cgs' cgs (! q)) ◦ˢᵘᵇ_) (! assˢᵘᵇ) ∙ ! assˢᵘᵇ ⟩

  (idd (M= k h cgs' cgs (! q))
    ◦ˢᵘᵇ M⃗ j h cfp prev-cfs g cgs' ◦ˢᵘᵇ M⃗ i h t prev f prev-cfs)
  ◦ˢᵘᵇ π (A h [ _ ])

  =⟨ M⃗◦ i h t prev f g prev-cfs cgs' cgfs (r ∙ e)
   |in-ctx (λ ◻ →
     (idd (M= k h cgs' cgs (! q))
       ◦ˢᵘᵇ ◻)
     ◦ˢᵘᵇ π (A h [ _ ])) ⟩

  (idd (M= k h cgs' cgs (! q))
    ◦ˢᵘᵇ idd (M= k h cgfs cgs' (r ∙ e)) ◦ˢᵘᵇ M⃗ i h t prev (g ◦ f) cgfs)
  ◦ˢᵘᵇ π (A h [ _ ])

  =⟨ ap (_◦ˢᵘᵇ π (A h [ _ ])) (! assˢᵘᵇ) ⟩

  ((idd (M= k h cgs' cgs (! q)) ◦ˢᵘᵇ idd (M= k h cgfs cgs' (r ∙ e)))
    ◦ˢᵘᵇ M⃗ i h t prev (g ◦ f) cgfs)
  ◦ˢᵘᵇ π (A h [ _ ])

  =⟨ idd-◦ (M= k h cgfs cgs' (r ∙ e)) (M= k h cgs' cgs (! q))
   ∙ ap idd
       ( M=-∙ k h cgfs cgs' cgs (r ∙ e) (! q)
       ∙ ap (M= k h cgfs cgs) (prop-path ℕ-id-is-prop ((r ∙ e) ∙ ! q) p) )
   |in-ctx (λ ◻ →
     (◻
       ◦ˢᵘᵇ M⃗ i h t prev (g ◦ f) cgfs)
     ◦ˢᵘᵇ π (A h [ _ ])) ⟩

  (idd (M= k h cgfs cgs p) ◦ˢᵘᵇ M⃗ i h t prev (g ◦ f) cgfs) ◦ˢᵘᵇ π (A h [ _ ])

  =⟨ assˢᵘᵇ ⟩

  idd (M= k h cgfs cgs p) ◦ˢᵘᵇ M⃗ i h t prev (g ◦ f) cgfs ◦ˢᵘᵇ π (A h [ _ ]) =∎

  where
  prev = prev-shape s
  prev-cfs = prev-shape cfs
  cfp = count-factors i h t prev f

  u = <-from-shape s
  no[g] = comp-divides-contra i h t u f g yes[f] no[gf]
  dg = inr no[g]

  cgs' = count-factors-shape-aux j h cfp (<-from-shape cfs) g dg

  q = count-factors-not-divisible j h cfp cfs g no[g]
  r = count-factors-comp i h t prev f g prev-cfs
  e = ap (λ ◻ → count-factors j h cfp ◻ g) (shape-path prev-cfs prev-cfs)

M⃗◦[ i , h ,1+ t ] s f g (inr no[gf]) (inr no[f]) cfs cgs cgfs p =
  ! assˢᵘᵇ
  ∙ ap (_◦ˢᵘᵇ π (A h [ _ ])) (M⃗◦ i h t (prev-shape s) f g cfs cgs cgfs p)
  ∙ assˢᵘᵇ

M⃗◦ i h (1+ t) s {j} f {k} g =
  M⃗◦[ i , h ,1+ t ] s f g
    (discrim i h t _ (g ◦ f))
    (discrim i h t _ f)

\end{code}

\begin{code}

M⃗◦ i (1+ h) O s {j} f {k} g cfs cgs cgfs p =
  CORE ∙ ! collapse
  where
  X = 𝔸 (1+ h)
  Θᵢ = Mᵒᶠᵘˡˡ i h
  Θⱼ = Mᵒᶠᵘˡˡ j h
  Θₖ = Mᵒᶠᵘˡˡ k h

  fullᵢ = hom-size i h
  shpᵢ = full-shape i h
  fullⱼ = hom-size j h
  shpⱼ = full-shape j h
  fullₖ = hom-size k h
  shpₖ = full-shape k h

  -- Data of the weakening substitution for f
  cf' = count-factors i h fullᵢ shpᵢ f
  shf = count-factors-shape i h fullᵢ shpᵢ f
  cf-fullⱼ = count-factors-full i h shpᵢ f
  σf = idd (M= j h shf shpⱼ cf-fullⱼ) ◦ˢᵘᵇ M⃗ i h fullᵢ shpᵢ f shf
  pf = comm i j h fullᵢ fullⱼ shpᵢ shpⱼ f cf-fullⱼ {shf}

  -- ... for g
  cg' = count-factors j h fullⱼ shpⱼ g
  shg = count-factors-shape j h fullⱼ shpⱼ g
  cg-fullₖ = count-factors-full j h shpⱼ g
  σg = idd (M= k h shg shpₖ cg-fullₖ) ◦ˢᵘᵇ M⃗ j h fullⱼ shpⱼ g shg
  pg = comm j k h fullⱼ fullₖ shpⱼ shpₖ g cg-fullₖ {shg}

  -- ... and for g ◦ f
  cgf' = count-factors i h fullᵢ shpᵢ (g ◦ f)
  shgf = count-factors-shape i h fullᵢ shpᵢ (g ◦ f)
  cgf-fullₖ = count-factors-full i h shpᵢ (g ◦ f)
  σgf = idd (M= k h shgf shpₖ cgf-fullₖ) ◦ˢᵘᵇ M⃗ i h fullᵢ shpᵢ (g ◦ f) shgf
  pgf = comm i k h fullᵢ fullₖ shpᵢ shpₖ (g ◦ f) cgf-fullₖ {shgf}

  Wf = wkn-sub Θᵢ Θⱼ σf pf X
  Wg = wkn-sub Θⱼ Θₖ σg pg X
  Wgf = wkn-sub Θᵢ Θₖ σgf pgf X

  -- Functoriality one level down, on the σ's:
  cgs× = count-factors-shape j h cf' shf g
  ce× : count-factors j h cf' shf g == cg'
  ce× = count-factors= j h g cf' fullⱼ cf-fullⱼ
  p× : cgf' == count-factors j h cf' shf g
  p× = count-factors-comp i h fullᵢ shpᵢ f g shf

  F : σg ◦ˢᵘᵇ σf == σgf
  F =
    assˢᵘᵇ
    ∙ ap (idd (M= k h shg shpₖ cg-fullₖ) ◦ˢᵘᵇ_) (! assˢᵘᵇ)
    ∙ ap (λ w → idd (M= k h shg shpₖ cg-fullₖ)
                ◦ˢᵘᵇ (w ◦ˢᵘᵇ M⃗ i h fullᵢ shpᵢ f shf))
         (M⃗-M=-comm j h cf' fullⱼ cf-fullⱼ shf shpⱼ g shg cgs× ce×)
    ∙ ap (idd (M= k h shg shpₖ cg-fullₖ) ◦ˢᵘᵇ_) assˢᵘᵇ
    ∙ ap (λ w → idd (M= k h shg shpₖ cg-fullₖ)
                ◦ˢᵘᵇ (idd (M= k h cgs× shg ce×) ◦ˢᵘᵇ w))
         (M⃗◦ i h fullᵢ shpᵢ f g shf cgs× shgf p×)
    ∙ ! assˢᵘᵇ
    ∙ ap (_◦ˢᵘᵇ (idd (M= k h shgf cgs× p×) ◦ˢᵘᵇ M⃗ i h fullᵢ shpᵢ (g ◦ f) shgf))
         ( idd-◦ (M= k h cgs× shg ce×) (M= k h shg shpₖ cg-fullₖ)
         ∙ ap idd (M=-∙ k h cgs× shg shpₖ ce× cg-fullₖ) )
    ∙ ! assˢᵘᵇ
    ∙ ap (_◦ˢᵘᵇ M⃗ i h fullᵢ shpᵢ (g ◦ f) shgf)
         ( idd-◦ (M= k h shgf cgs× p×) (M= k h cgs× shpₖ (ce× ∙ cg-fullₖ))
         ∙ ap idd
             ( M=-∙ k h shgf cgs× shpₖ p× (ce× ∙ cg-fullₖ)
             ∙ ap (M= k h shgf shpₖ)
                  (prop-path ℕ-id-is-prop (p× ∙ ce× ∙ cg-fullₖ) cgf-fullₖ) ) )

  cond1 : (π X ++ₛ Θₖ) ◦ˢᵘᵇ (Wg ◦ˢᵘᵇ Wf) == (π X ++ₛ Θₖ) ◦ˢᵘᵇ Wgf
  cond1 =
    ! assˢᵘᵇ
    ∙ ap (_◦ˢᵘᵇ Wf) (wkn-sub-comm Θⱼ Θₖ σg pg X)
    ∙ assˢᵘᵇ
    ∙ ap (σg ◦ˢᵘᵇ_) (wkn-sub-comm Θᵢ Θⱼ σf pf X)
    ∙ ! assˢᵘᵇ
    ∙ ap (_◦ˢᵘᵇ (π X ++ₛ Θᵢ)) F
    ∙ ! (wkn-sub-comm Θᵢ Θₖ σgf pgf X)

  cond2 : πₜₑₗ (wkₜₑₗ Θₖ) ◦ˢᵘᵇ (Wg ◦ˢᵘᵇ Wf) == πₜₑₗ (wkₜₑₗ Θₖ) ◦ˢᵘᵇ Wgf
  cond2 =
    ! assˢᵘᵇ
    ∙ ap (_◦ˢᵘᵇ Wf) (wkn-sub-π Θⱼ Θₖ σg pg X)
    ∙ wkn-sub-π Θᵢ Θⱼ σf pf X
    ∙ ! (wkn-sub-π Θᵢ Θₖ σgf pgf X)

  CORE : Wg ◦ˢᵘᵇ Wf == Wgf
  CORE = wkn-sub-unique Θₖ X (Wg ◦ˢᵘᵇ Wf) Wgf cond1 cond2

  collapse : idd (M= k (1+ h) cgfs cgs p) ◦ˢᵘᵇ Wgf == Wgf
  collapse =
    ap (λ{ (sₓ , eₓ) → idd (M= k (1+ h) sₓ cgs eₓ) ◦ˢᵘᵇ Wgf })
       (pair×= (shape-path cgfs cgs) (prop-path ℕ-id-is-prop p idp))
    ∙ ap (λ w → idd w ◦ˢᵘᵇ Wgf) M=-idp
    ∙ idl Wgf

M⃗◦ i O O s f {k} g cfs cgs cgfs idp =
  ap (λ ◻ → idd ◻ ◦ˢᵘᵇ id) (! $ ap-const $ prop-has-all-paths cgfs cgs)

\end{code}
