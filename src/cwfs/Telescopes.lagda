Telescopes in wild cwf's
========================

\begin{code}

{-# OPTIONS --without-K --rewriting #-}

open import cwfs.CwFs

module cwfs.Telescopes {ℓₒ ℓₘ} {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C) where

open CwFStructure cwfstr

\end{code}


Telescopes
----------

Small inductive-recursive definition of
• telescopes Θ in internal contexts Γ, and
• context extension by telescopes.

\begin{code}

data Tel (Γ : Con) : Type ℓₒ
_++ₜₑₗ_ : (Γ : Con) → Tel Γ → Con

infixl 30 _++ₜₑₗ_
infixl 35 _‣_

data Tel Γ where
  • : Tel Γ
  _‣_ : (Θ : Tel Γ) → Ty (Γ ++ₜₑₗ Θ) → Tel Γ

Γ ++ₜₑₗ • = Γ
Γ ++ₜₑₗ (Θ ‣ A) = (Γ ++ₜₑₗ Θ) ∷ A

\end{code}

We "close" a telescope Θ by appending it to its context Γ.

\begin{code}

close : {Γ : Con} → Tel Γ → Con
close {Γ} Θ = Γ ++ₜₑₗ Θ

\end{code}


Substitution in telescopes
--------------------------

Consider a telescope Θ = (Δ ⊢ A₁, A₂, ..., Aₙ) in context Δ. For any
substitution f : Sub Γ Δ we get the telescope Θ[f]ₜₑₗ given by the left hand
column of the diagram

                 ⋮                            ⋮
                 ↡                             ↡
      Γ ∷ A₁[f] ∷ A₂[f ∷ₛ A₁] ------------> Δ ∷ A₁ ∷ A₂
                 |         f ∷ₛ A₁ ∷ₛ A₂         |
                 ↡                             ↡
           Γ ∷ A₁[f] ----------------------> Δ ∷ A₁
                 |           f ∷ₛ A₁            |
                 ↡                             ↡
                 Γ --------------------------> Δ
                               f

(see cwfs.CwFs for the definition of _∷ₛ_).

\begin{code}

infixl 40 _[_]ₜₑₗ _++ₛ_

_[_]ₜₑₗ : ∀ {Γ Δ} → Tel Δ → Sub Γ Δ → Tel Γ
_++ₛ_ : ∀ {Γ Δ} (f : Sub Γ Δ) (Θ : Tel Δ) → Sub (Γ ++ₜₑₗ Θ [ f ]ₜₑₗ) (Δ ++ₜₑₗ Θ)

• [ f ]ₜₑₗ = •
(Θ ‣ A) [ f ]ₜₑₗ = Θ [ f ]ₜₑₗ ‣ A [ f ++ₛ Θ ]

f ++ₛ • = f
f ++ₛ (Θ ‣ A) = f ++ₛ Θ ∷ₛ A

private
  module sanity-check
    (Γ Δ : Con) (f : Sub Γ Δ)
    (A₁ : Ty Δ) (A₂ : Ty (Δ ∷ A₁)) (A₃ : Ty (Δ ∷ A₁ ∷ A₂))
    where
    Θ = • ‣ A₁ ‣ A₂ ‣ A₃

    _ : Θ [ f ]ₜₑₗ == • ‣ A₁ [ f ] ‣ A₂ [ f ∷ₛ A₁ ] ‣ A₃ [ f ∷ₛ A₁ ∷ₛ A₂ ]
    _ = idp

\end{code}

Projection, forgetting a telescope.

\begin{code}

πₜₑₗ : ∀ {Γ} (Θ : Tel Γ) → Sub (Γ ++ₜₑₗ Θ) Γ
πₜₑₗ • = id
πₜₑₗ (Θ ‣ A) = πₜₑₗ Θ ◦ π A

\end{code}

The following diagram commutes:

                   σ ++ₛ Θ
         Γ ++ Θ[σ] ------> Δ ++ Θ
    π (Θ[σ]) |                | π Θ
             ↓                ↓
             Γ -------------> Δ
                     σ

\begin{code}

++ₛ-comm : ∀ {Γ Δ} (σ : Sub Γ Δ) (Θ : Tel Δ)
  → πₜₑₗ Θ ◦ (σ ++ₛ Θ) == σ ◦ πₜₑₗ (Θ [ σ ]ₜₑₗ)
++ₛ-comm σ • = idl _ ∙ ! (idr _)
++ₛ-comm σ (Θ ‣ A) =
  (πₜₑₗ Θ ◦ π A) ◦ (σ ++ₛ Θ ∷ₛ A)
    =⟨ ass ⟩
  πₜₑₗ Θ ◦ (π A ◦ (σ ++ₛ Θ ∷ₛ A))
    =⟨ ap (πₜₑₗ Θ ◦_) βπ ⟩
  πₜₑₗ Θ ◦ (σ ++ₛ Θ) ◦ π (A [ σ ++ₛ Θ ])
    =⟨ ! ass ∙ (ap (_◦ π _) $ ++ₛ-comm σ Θ) ∙ ass ⟩
  σ ◦ πₜₑₗ (Θ [ σ ]ₜₑₗ) ◦ π (A [ σ ++ₛ Θ ])
    =∎

\end{code}

Weakening a telescope by a type.

\begin{code}

infix 32 wknₜₑₗ_by

wknₜₑₗ_by : ∀ {Γ} → Tel Γ → (X : Ty Γ) → Tel (Γ ∷ X)
wknₜₑₗ Θ by X = Θ [ π X ]ₜₑₗ

wkₜₑₗ : ∀ {Γ} {X : Ty Γ} → Tel Γ → Tel (Γ ∷ X)
wkₜₑₗ {X = X} Θ = wknₜₑₗ Θ by X

\end{code}

Weakening a type by a telescope (i.e. repeated weakening).

\begin{code}

infix 37 wkn_byₜₑₗ

wkn_byₜₑₗ : ∀ {Γ} → Ty Γ → (Θ : Tel Γ) → Ty (Γ ++ₜₑₗ Θ)
wkn X byₜₑₗ Θ = X [ πₜₑₗ Θ ]

wknₜ_byₜₑₗ : ∀ {Γ} {X : Ty Γ} (x : Tm X) (Θ : Tel Γ) → Tm (wkn X byₜₑₗ Θ)
wknₜ x byₜₑₗ Θ = x [ πₜₑₗ Θ ]ₜ

\end{code}

TODO: clean up the following.

\begin{code}

-- A particular version of a weakened variable υ that we need.
υ⁺ : ∀ {Γ} (Θ : Tel Γ) (X : Ty Γ) → Tm (X [ πₜₑₗ Θ ◦ (π X ++ₛ Θ) ])
υ⁺ Θ X = coeᵀᵐ p (υ X [ πₜₑₗ (Θ [ π X ]ₜₑₗ) ]ₜ)
  where
  p : X [ π X ] [ πₜₑₗ (wknₜₑₗ Θ by X) ] == X [ πₜₑₗ Θ ◦ (π X ++ₛ Θ) ]
  p = ![◦] ∙ [= ! (++ₛ-comm (π X) Θ)]

\end{code}

NEW: Telescope weakening.

Given telescopes Θ, Θ' over Γ and a substitution σ : Sub (Γ ++ Θ) (Γ ++ Θ')
over Γ (i.e. commuting with the projections to Γ), we construct its weakening
by a type X : Ty Γ,

                      σ↑X
    Γ ∷ X ++ Θ[π X] -------> Γ ∷ X ++ Θ'[π X]
         |                        |
         | π X ++ₛ Θ              | π X ++ₛ Θ'
         ↓                        ↓
       Γ ++ Θ ------------------> Γ ++ Θ'
                       σ

such that the square commutes and σ↑X again lies over Γ ∷ X.  We also prove
that σ↑X is the unique substitution with these two properties.

** THIS IS WHERE SET-LEVEL COMES IN. **
In a general wild cwf this construction requires an infinite tower of
coherence data (the first layer of which is the pentagon coherence for
substitution in types). We work in a *set-level* cwf, where
all such coherences are automatic. This is the only place where the
set-level assumptions enter the diagram construction.

\begin{code}

open import cwfs.SetLevel

module TelescopeWeakening (setlvlstr : SetLevelStructure cwfstr) where
  open SetLevelStructure setlvlstr

  wkn-sub-lemma :
    ∀ {Γ} (Θ Θ' : Tel Γ) (X : Ty Γ)
    → (σ : Sub (Γ ++ₜₑₗ Θ) (Γ ++ₜₑₗ Θ'))
    → πₜₑₗ Θ' ◦ σ == πₜₑₗ Θ
    → Σ (Sub (Γ ∷ X ++ₜₑₗ wkₜₑₗ Θ) (Γ ∷ X ++ₜₑₗ wkₜₑₗ Θ'))
      λ σ↑X → ((π X ++ₛ Θ') ◦ σ↑X == σ ◦ (π X ++ₛ Θ))
            × (πₜₑₗ (wkₜₑₗ Θ') ◦ σ↑X == πₜₑₗ (wkₜₑₗ Θ))

  wkn-sub-lemma {Γ} Θ • X σ p =
    πₜₑₗ (wkₜₑₗ Θ) ,
    ! (++ₛ-comm (π X) Θ) ∙ ap (_◦ (π X ++ₛ Θ)) (! p ∙ idl σ) ,
    idl _

  wkn-sub-lemma {Γ} Θ (Θ' ‣ A) X σ p = σ↑ , sq , sl
    where
    Ā = A [ π X ++ₛ Θ' ]

    σ' : Sub (Γ ++ₜₑₗ Θ) (Γ ++ₜₑₗ Θ')
    σ' = π A ◦ σ

    p' : πₜₑₗ Θ' ◦ σ' == πₜₑₗ Θ
    p' = ! ass ∙ p

    rec = wkn-sub-lemma Θ Θ' X σ' p'
    τ = fst rec
    sq' = fst (snd rec)   -- (π X ++ₛ Θ') ◦ τ == σ' ◦ (π X ++ₛ Θ)
    sl' = snd (snd rec)   -- πₜₑₗ (wkₜₑₗ Θ') ◦ τ == πₜₑₗ (wkₜₑₗ Θ)

    c₀ : Tm (A [ π A ] [ σ ] [ π X ++ₛ Θ ])
    c₀ = υ A [ σ ]ₜ [ π X ++ₛ Θ ]ₜ

    e : A [ π A ] [ σ ] [ π X ++ₛ Θ ] == Ā [ τ ]
    e = ap (_[ π X ++ₛ Θ ]) ![◦] ∙ ![◦] ∙ [= ! sq' ] ∙ [◦]

    a : Tm (Ā [ τ ])
    a = coeᵀᵐ e c₀

    σ↑ : Sub (Γ ∷ X ++ₜₑₗ wkₜₑₗ Θ) (Γ ∷ X ++ₜₑₗ wkₜₑₗ (Θ' ‣ A))
    σ↑ = τ ,, a

    P : ((π X ++ₛ Θ') ◦ π Ā) ◦ σ↑ == π A ◦ (σ ◦ (π X ++ₛ Θ))
    P = ass ∙ ap ((π X ++ₛ Θ') ◦_) βπ ∙ sq' ∙ ass

    Q : coe!ᵀᵐ [◦] ((coe!ᵀᵐ [◦] (υ Ā)) [ σ↑ ]ₜ)
        == coe!ᵀᵐ [◦] (υ A [ σ ◦ (π X ++ₛ Θ) ]ₜ)
        over⟨ [= P ] ⟩
    Q = over-irr $
      coeᵀᵐ-out ![◦] _
      ∙ᵈ !ᵈ (coeᵀᵐ-[]ₜ-stable ![◦] (υ Ā) σ↑)
      ∙ᵈ βυ
      ∙ᵈ coeᵀᵐ-out e c₀
      ∙ᵈ !ᵈ [◦]ₜ
      ∙ᵈ coeᵀᵐ-in ![◦] _

    sq : (π X ++ₛ (Θ' ‣ A)) ◦ σ↑ == σ ◦ (π X ++ₛ Θ)
    sq = ,,-◦ ∙ ⟨= P ,, Q =⟩ ∙ ! (η-sub (σ ◦ (π X ++ₛ Θ)))

    sl : πₜₑₗ (wkₜₑₗ (Θ' ‣ A)) ◦ σ↑ == πₜₑₗ (wkₜₑₗ Θ)
    sl = ass ∙ ap (πₜₑₗ (wkₜₑₗ Θ') ◦_) βπ ∙ sl'

  wkn-sub :
    ∀ {Γ} (Θ Θ' : Tel Γ) (σ : Sub (Γ ++ₜₑₗ Θ) (Γ ++ₜₑₗ Θ'))
    → πₜₑₗ Θ' ◦ σ == πₜₑₗ Θ
    → (X : Ty Γ)
    → Sub (Γ ∷ X ++ₜₑₗ wkₜₑₗ Θ) (Γ ∷ X ++ₜₑₗ wkₜₑₗ Θ')
  wkn-sub Θ Θ' σ p X = fst (wkn-sub-lemma Θ Θ' X σ p)

  wkn-sub-comm :
    ∀ {Γ} (Θ Θ' : Tel Γ) (σ : Sub (Γ ++ₜₑₗ Θ) (Γ ++ₜₑₗ Θ'))
    → (p : πₜₑₗ Θ' ◦ σ == πₜₑₗ Θ)
    → (X : Ty Γ)
    → (π X ++ₛ Θ') ◦ wkn-sub Θ Θ' σ p X == σ ◦ (π X ++ₛ Θ)
  wkn-sub-comm Θ Θ' σ p X = fst (snd (wkn-sub-lemma Θ Θ' X σ p))

  wkn-sub-π :
    ∀ {Γ} (Θ Θ' : Tel Γ) (σ : Sub (Γ ++ₜₑₗ Θ) (Γ ++ₜₑₗ Θ'))
    → (p : πₜₑₗ Θ' ◦ σ == πₜₑₗ Θ)
    → (X : Ty Γ)
    → πₜₑₗ (wkₜₑₗ Θ') ◦ wkn-sub Θ Θ' σ p X == πₜₑₗ (wkₜₑₗ Θ)
  wkn-sub-π Θ Θ' σ p X = snd (snd (wkn-sub-lemma Θ Θ' X σ p))

\end{code}

The two projections out of a weakened telescope context are jointly monic.
As a consequence, wkn-sub σ is the *unique* substitution fitting into the
commuting square above and lying over Γ ∷ X; this gives functoriality of
weakening, which is needed for the functor laws of the matching object
functor in the diagram construction.

\begin{code}

  wkn-sub-unique :
    ∀ {Γ} (Θ' : Tel Γ) (X : Ty Γ) {Ξ : Con}
    → (W W' : Sub Ξ (Γ ∷ X ++ₜₑₗ wkₜₑₗ Θ'))
    → (π X ++ₛ Θ') ◦ W == (π X ++ₛ Θ') ◦ W'
    → πₜₑₗ (wkₜₑₗ Θ') ◦ W == πₜₑₗ (wkₜₑₗ Θ') ◦ W'
    → W == W'
  wkn-sub-unique • X W W' _ r = ! (idl W) ∙ r ∙ idl W'
  wkn-sub-unique {Γ} (Θ' ‣ A) X {Ξ} W W' q r =
    sub= W W' first second
    where
    Ā = A [ π X ++ₛ Θ' ]

    -- Rearrange π A ◦ ((π X ++ₛ Θ' ∷ₛ A) ◦ V) for V : Sub Ξ (Γ ∷ X ++ₜₑₗ wkₜₑₗ (Θ' ‣ A))
    rearr : (V : Sub Ξ (Γ ∷ X ++ₜₑₗ wkₜₑₗ (Θ' ‣ A)))
      → π A ◦ ((π X ++ₛ (Θ' ‣ A)) ◦ V) == (π X ++ₛ Θ') ◦ (π Ā ◦ V)
    rearr V = ! ass ∙ ap (_◦ V) ∷ₛ-comm ∙ ass

    q₁ : (π X ++ₛ Θ') ◦ (π Ā ◦ W) == (π X ++ₛ Θ') ◦ (π Ā ◦ W')
    q₁ = ! (rearr W) ∙ ap (π A ◦_) q ∙ rearr W'

    r₁ : πₜₑₗ (wkₜₑₗ Θ') ◦ (π Ā ◦ W) == πₜₑₗ (wkₜₑₗ Θ') ◦ (π Ā ◦ W')
    r₁ = ! ass ∙ r ∙ ass

    first : π Ā ◦ W == π Ā ◦ W'
    first = wkn-sub-unique Θ' X (π Ā ◦ W) (π Ā ◦ W') q₁ r₁

    -- Relate the last component of V to the last component of the composite
    -- (π X ++ₛ (Θ' ‣ A)) ◦ V, as a dependent path.
    module _ (V : Sub Ξ (Γ ∷ X ++ₜₑₗ wkₜₑₗ (Θ' ‣ A))) where
      second-aux =
        coeᵀᵐ-out ![◦] (υ Ā [ V ]ₜ)
        ∙ᵈ coeᵀᵐ-[]ₜ-stable ![◦] (υ Ā) V
        ∙ᵈ !ᵈ (βυ |in-ctx↓ᵀᵐ _[ V ]ₜ)
        ∙ᵈ !ᵈ ([◦]ₜ {f = V} {g = π X ++ₛ (Θ' ‣ A)} {t = υ A})

    second : coe!ᵀᵐ [◦] (υ Ā [ W ]ₜ) == coe!ᵀᵐ [◦] (υ Ā [ W' ]ₜ)
             over⟨ [= first ] ⟩
    second = over-irr $
      second-aux W
      ∙ᵈ ↓-ap-in Tm ((A [ π A ]) [_]) (apd (υ A [_]ₜ) q)
      ∙ᵈ !ᵈ (second-aux W')

\end{code}

\begin{code}

{- Previous version of wkn-sub-lemma had commuting squares instead of triangles,
   which was unnecessary.

-- Weaken a *substitution* between telescopes by a type
wkn-sub-lemma : ∀ {Γ Δ} (Θ : Tel Γ) (X : Ty Δ) (σ₀ : Sub Γ Δ)
  (Θ' : Tel Δ)
  (σ : Sub (Γ ++ₜₑₗ Θ) (Δ ++ₜₑₗ Θ'))
  → πₜₑₗ Θ' ◦ σ == σ₀ ◦ πₜₑₗ Θ
  → Σ (Sub (Γ ∷ X [ σ₀ ] ++ₜₑₗ wkₜₑₗ Θ) (Δ ∷ X ++ₜₑₗ wkₜₑₗ Θ'))
    λ σ↑X → (π X ++ₛ Θ') ◦ σ↑X == σ ◦ (π (X [ σ₀ ]) ++ₛ Θ)

wkn-sub-lemma Θ X σ₀ • σ p =
  (σ ◦ (π (X [ σ₀ ]) ++ₛ Θ) ,, coeᵀᵐ q (υ⁺ Θ (X [ σ₀ ])))
  , βπ
  where
  σ-σ₀ : σ == σ₀ ◦ πₜₑₗ Θ
  σ-σ₀ = ! idl ∙ p

  q : X [ σ₀ ] [ πₜₑₗ Θ ◦ (π (X [ σ₀ ]) ++ₛ Θ) ]
      == X [ σ ◦ (π (X [ σ₀ ]) ++ₛ Θ) ]
  q = ![◦] ∙ [= ! ass ∙ ap (_◦ (π (X [ σ₀ ]) ++ₛ Θ)) (! σ-σ₀) ]

wkn-sub-lemma {Γ} {Δ} Θ X σ₀ (Θ' ‣ A) σ p =
  σ↑X , comm
  where
  -- Notation
  π++Θ = π (X [ σ₀ ]) ++ₛ Θ
  π++Θ' = π X ++ₛ Θ'
  π++Θ'‣A = π X ++ₛ (Θ' ‣ A)

  πσ-σ₀ : πₜₑₗ Θ' ◦ π A ◦ σ == σ₀ ◦ πₜₑₗ Θ
  πσ-σ₀ = ! ass ∙ p

  rec = wkn-sub-lemma Θ X σ₀ Θ' (π A ◦ σ) πσ-σ₀
  πσ↑X = fst rec

  πσ↑X-comm : π++Θ' ◦ πσ↑X == (π A ◦ σ) ◦ π++Θ
  πσ↑X-comm = snd rec

  botleft = σ ◦ π++Θ

  q : A ʷ [ botleft ] == A [ π++Θ' ] [ πσ↑X ]
  q = ![◦] ∙ ! [= ass ] ∙ ! [= πσ↑X-comm ] ∙ [◦]

  σ↑X = (πσ↑X ,, coeᵀᵐ q (υ A [ botleft ]ₜ))

  topright = π++Θ'‣A ◦ σ↑X

  comm : topright == botleft
  comm =
    topright

      =⟨ idp ⟩

    ( π++Θ' ◦ π _ ,, coeᵀᵐ ![◦] (υ _) ) ◦ σ↑X

      =⟨ ,,-◦ ⟩

    ( (π++Θ' ◦ π _) ◦ σ↑X ,,
      coeᵀᵐ ![◦] (coeᵀᵐ ![◦] (υ _) [ σ↑X ]ₜ) )

      =⟨ ⟨=,, coeᵀᵐ[]ₜ ![◦] (υ _) σ↑X |in-ctx (coeᵀᵐ ![◦]) =⟩ ⟩

    ( (π++Θ' ◦ π _) ◦ σ↑X ,,
      coeᵀᵐ ![◦] (coeᵀᵐ (ap (_[ σ↑X ]) ![◦]) (υ _ [ σ↑X ]ₜ)) )

      =⟨ ⟨=,, {!!} =⟩ ⟩

    ( (π++Θ' ◦ π _) ◦ σ↑X ,,
      coeᵀᵐ ![◦] (coeᵀᵐ (ap (_[ σ↑X ]) ![◦]) (coeᵀᵐ ([= ! βπ ] ∙ [◦]) (coeᵀᵐ q
        (υ _ [ botleft ]ₜ)))) )

      =⟨ ⟨= ass ,,=⟩ ⟩
    ( π++Θ' ◦ π _ ◦ σ↑X ,, _ )
      =⟨ ⟨= βπ |in-ctx (π++Θ' ◦_) ,,=⟩ ⟩
    ( π++Θ' ◦ πσ↑X ,, _ )
      =⟨ ⟨= πσ↑X-comm ,,=⟩ ⟩
    ( (π A ◦ σ) ◦ π++Θ ,, _ )
      =⟨ ⟨= ass ,,=⟩ ⟩
    ( π A ◦ botleft ,, _ )
      =⟨ ⟨=,, {!!} =⟩ ⟩
    ( π A ◦ botleft ,, coe!ᵀᵐ [◦] (υ A [ botleft ]ₜ) )
      =⟨ ! (η-sub botleft) ⟩
    botleft
      =∎

wkn-sub : ∀ {Γ Δ} (Θ : Tel Γ) (X : Ty Δ) (σ₀ : Sub Γ Δ)
  (Θ' : Tel Δ)
  (σ : Sub (Γ ++ₜₑₗ Θ) (Δ ++ₜₑₗ Θ'))
  → πₜₑₗ Θ' ◦ σ == σ₀ ◦ πₜₑₗ Θ
  → Sub (Γ ∷ X [ σ₀ ] ++ₜₑₗ wkₜₑₗ Θ) (Δ ∷ X ++ₜₑₗ wkₜₑₗ Θ')
wkn-sub {Γ} {Δ} Θ X σ₀ Θ' σ p = fst (wkn-sub-lemma {Γ} {Δ} Θ X σ₀ Θ' σ p)
-}


-- Internal Π types from telescopes
open import cwfs.Pi
module Πₜₑₗ (pistr : PiStructure cwfstr) where
  open PiStructure pistr

  Πₜₑₗ : ∀ {Γ} (Θ : Tel Γ) → Ty (Γ ++ₜₑₗ Θ) → Ty Γ
  Πₜₑₗ • B = B
  Πₜₑₗ (Θ ‣ A) B = Πₜₑₗ Θ (Π′ A B)

  Πₜₑₗ[] :
    ∀ {Γ Δ} (Θ : Tel Δ) (B : Ty (Δ ++ₜₑₗ Θ)) (f : Sub Γ Δ)
    → (Πₜₑₗ Θ B) [ f ] == Πₜₑₗ (Θ [ f ]ₜₑₗ) (B [ f ++ₛ Θ ])
  Πₜₑₗ[] • B f = idp
  Πₜₑₗ[] (Θ ‣ A) B f = Πₜₑₗ[] Θ (Π′ A B) f ∙ ap (Πₜₑₗ (Θ [ f ]ₜₑₗ)) Π′[]

  appₜₑₗ : ∀ {Γ} (Θ : Tel Γ) {B : Ty (Γ ++ₜₑₗ Θ)} → Tm (Πₜₑₗ Θ B) → Tm B
  appₜₑₗ • f = f
  appₜₑₗ (Θ ‣ A) f = app (appₜₑₗ Θ f)

  λₜₑₗ : ∀ {Γ} (Θ : Tel Γ) {B : Ty (Γ ++ₜₑₗ Θ)} → Tm B → Tm (Πₜₑₗ Θ B)
  λₜₑₗ • b = b
  λₜₑₗ (Θ ‣ A) b = λₜₑₗ Θ (λ′ b)

  λₜₑₗappₜₑₗ : ∀ {Γ} Θ {B : Ty (Γ ++ₜₑₗ Θ)} f → λₜₑₗ Θ {B} (appₜₑₗ Θ {B} f) == f
  λₜₑₗappₜₑₗ • f = idp
  λₜₑₗappₜₑₗ (Θ ‣ A) f = ap (λₜₑₗ Θ) (ηΠ′ _) ∙ λₜₑₗappₜₑₗ Θ f

  appₜₑₗλₜₑₗ : ∀ {Γ} Θ {B : Ty (Γ ++ₜₑₗ Θ)} b → appₜₑₗ Θ {B} (λₜₑₗ Θ b) == b
  appₜₑₗλₜₑₗ • b = idp
  appₜₑₗλₜₑₗ (Θ ‣ A) b = ap app (appₜₑₗλₜₑₗ Θ _) ∙ βΠ′ b

  Tm-Πₜₑₗ-equiv : ∀ {Γ} (Θ : Tel Γ) (B : Ty (Γ ++ₜₑₗ Θ)) → Tm (Πₜₑₗ Θ B) ≃ Tm B
  Tm-Πₜₑₗ-equiv Θ B = equiv (appₜₑₗ Θ) (λₜₑₗ Θ) (appₜₑₗλₜₑₗ Θ) (λₜₑₗappₜₑₗ Θ)

  open import cwfs.Universe
  module TelIndexedTypes (univstr : UniverseStructure cwfstr) where
    open UniverseStructure univstr

    generic[_]type :
      ∀ {Γ} (Θ : Tel Γ)
      → let X = Πₜₑₗ Θ U in
        Ty (Γ ∷ X ++ₜₑₗ Θ [ π X ]ₜₑₗ)
    generic[ Θ ]type = el $ appₜₑₗ (Θ [ π X ]ₜₑₗ) $ transp Tm p (υ X)
      where
      X = Πₜₑₗ Θ U

      p : X [ π X ] == Πₜₑₗ (Θ [ π X ]ₜₑₗ) U
      p = Πₜₑₗ[] Θ U (π X) ∙ ap (Πₜₑₗ (Θ [ π X ]ₜₑₗ)) U[]

    generic[•]type= :
      ∀ {Γ} → generic[ • :> Tel Γ ]type == el (transp Tm U[] (υ U))
    generic[•]type= {Γ} = ap-idf U[] |in-ctx (λ p → el (transp Tm p (υ U)))

\end{code}
