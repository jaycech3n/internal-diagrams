{-# OPTIONS --without-K --rewriting #-}

{- The syntax as canonical example cwf. This is taken from:

  Thorsten Altenkirch and Ambrus Kaposi,
  "Type Theory in Type Theory using Quotient Inductive Types", POPL 2016,

Everything here is just postulated. If we switched to cubical, we could
make the whole thing into a proper definition.

We made some adaptions so that the Altenkirch-Kaposi work fits into our
framework. The main change is that we use --without-K, and we "made up"
for this by requesting that the syntax is a set, with the conditions
  `SubS-is-set`
  `TyS-is-set`
  `TmS-is-set`
below. (But note that we should be able to get away without the first
and the third.)

This set-level cwf is the motivating example for the question whether
we can construct Reedy fibrant diagrams in an internal cwf.
-}

module cwfs.Syntax where

open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe
open import cwfs.SetLevel

--------------------------------------------------------------------------------
-- 1.  Sorts and operations (postulated constructors of the QIIT)

infixr 40 _∘S_
infixl 40 _[_]TS _[_]tS
infixl 35 _▹S_
infixl 35 _,S_

postulate
  -- the four sorts
  ConS : Type lzero
  SubS : ConS → ConS → Type lzero
  TyS  : ConS → Type lzero
  TmS  : {Γ : ConS} → TyS Γ → Type lzero

  -- category structure on contexts and substitutions
  _∘S_ : ∀ {Γ Δ Θ} → SubS Δ Θ → SubS Γ Δ → SubS Γ Θ
  idS  : ∀ {Γ} → SubS Γ Γ
  assS : ∀ {Γ Δ Θ Ξ} {f : SubS Θ Ξ} {g : SubS Δ Θ} {h : SubS Γ Δ}
       → (f ∘S g) ∘S h == f ∘S (g ∘S h)
  idlS : ∀ {Γ Δ} (f : SubS Γ Δ) → idS ∘S f == f
  idrS : ∀ {Γ Δ} (f : SubS Γ Δ) → f ∘S idS == f

  -- terminal (empty) context
  ◇S  : ConS
  εS  : ∀ {Γ} → SubS Γ ◇S
  ◇ηS : ∀ {Γ} (σ : SubS Γ ◇S) → σ == εS

  -- types and their substitution
  _[_]TS : ∀ {Γ Δ} → TyS Δ → SubS Γ Δ → TyS Γ
  [id]TS : ∀ {Γ} {A : TyS Γ} → A [ idS ]TS == A
  [∘]TS  : ∀ {Γ Δ Θ} {f : SubS Γ Δ} {g : SubS Δ Θ} {A : TyS Θ}
         → A [ g ∘S f ]TS == A [ g ]TS [ f ]TS

  -- terms and their substitution
  _[_]tS : ∀ {Γ Δ} {A : TyS Δ} → TmS A → (f : SubS Γ Δ) → TmS (A [ f ]TS)
  [id]tS : ∀ {Γ} {A : TyS Γ} {t : TmS A}
         → PathOver TmS [id]TS (t [ idS ]tS) t
  [∘]tS  : ∀ {Γ Δ Θ} {f : SubS Γ Δ} {g : SubS Δ Θ} {A : TyS Θ} {t : TmS A}
         → PathOver TmS [∘]TS (t [ g ∘S f ]tS) (t [ g ]tS [ f ]tS)

  -- comprehension:  context extension, weakening, variable, substitution pairing
  _▹S_ : (Γ : ConS) → TyS Γ → ConS
  pS   : ∀ {Γ} (A : TyS Γ) → SubS (Γ ▹S A) Γ
  qS   : ∀ {Γ} (A : TyS Γ) → TmS (A [ pS A ]TS)
  _,S_ : ∀ {Γ Δ} {A : TyS Δ} (f : SubS Γ Δ) → TmS (A [ f ]TS) → SubS Γ (Δ ▹S A)

  -- Π-types
  ΠS   : ∀ {Γ} (A : TyS Γ) → TyS (Γ ▹S A) → TyS Γ
  lamS : ∀ {Γ} {A : TyS Γ} {B : TyS (Γ ▹S A)} → TmS B → TmS (ΠS A B)
  appS : ∀ {Γ} {A : TyS Γ} {B : TyS (Γ ▹S A)} → TmS (ΠS A B) → TmS B

  -- a universe (El-only, à la Coquand / Altenkirch-Kaposi)
  US  : ∀ {Γ} → TyS Γ
  ElS : ∀ {Γ} → TmS {Γ} US → TyS Γ

  -- set-truncation: the no-UIP adaptation (see header)
  SubS-is-set : ∀ {Γ Δ} → is-set (SubS Γ Δ)
  TyS-is-set  : ∀ {Γ}   → is-set (TyS Γ)
  TmS-is-set  : ∀ {Γ} {A : TyS Γ} → is-set (TmS A)

--------------------------------------------------------------------------------
-- 2.  The underlying wild category, context and type/term structure

synWildCat : WildCategory lzero lzero
synWildCat = record
  { Ob = ConS
  ; wildcatstr = record
      { wildsemicatstr = record { hom = SubS ; _◦_ = _∘S_ ; ass = assS }
      ; id = idS ; idl = idlS ; idr = idrS } }

synCtx : ContextStructure synWildCat
synCtx = record
  { ◆ = ◇S
  ; ◆-terminal = λ Γ → has-level-in (εS , λ σ → ! (◇ηS σ)) }

synTyTm : TyTmStructure synWildCat
synTyTm = record
  { ctxstr = synCtx
  ; Ty = TyS ; _[_] = _[_]TS ; [id] = [id]TS ; [◦] = [∘]TS
  ; Tm = TmS ; _[_]ₜ = _[_]tS ; [id]ₜ = [id]tS ; [◦]ₜ = [∘]tS }

-- Opening exposes the record notation ([◦], over⟨_⟩, coeᵀᵐ, coe!ᵀᵐ, [=_], …),
-- so the equation postulates below are stated in *exactly* the field forms of
-- ComprehensionStructure, guaranteeing a definitional match.
open TyTmStructure synTyTm

--------------------------------------------------------------------------------
-- 3.  Comprehension equations (β/η for context extension)

postulate
  βπS : ∀ {Γ Δ} {f : SubS Γ Δ} {A : TyS Δ} {t : TmS (A [ f ])}
      → pS A ◦ (f ,S t) == f
  βυS : ∀ {Γ Δ} {f : SubS Γ Δ} {A : TyS Δ} {t : TmS (A [ f ])}
      → qS A [ f ,S t ]ₜ == t over⟨ ! [◦] ∙ [= βπS ] ⟩
  ηS,, : ∀ {Γ} {A : TyS Γ} → (pS A ,S qS A) == id
  ,∘S  : ∀ {Γ Δ Θ} {f : SubS Γ Δ} {g : SubS Δ Θ} {A : TyS Θ} {t : TmS (A [ g ])}
       → (g ,S t) ◦ f == (g ◦ f ,S coe!ᵀᵐ [◦] (t [ f ]ₜ))

synCompr : ComprehensionStructure synWildCat
synCompr = record
  { tytmstr = synTyTm
  ; _∷_ = _▹S_ ; π = pS ; υ = qS ; _,,_ = _,S_
  ; βπ = βπS ; βυ = βυS ; η,, = ηS,, ; ,,-◦ = ,∘S }

synCwF : CwFStructure synWildCat
synCwF = record { compstr = synCompr }

-- the derived weakening substitution f ∷ₛ A, needed to state Π[]/lam[]
open CwFStructure synCwF using (_∷ₛ_)

--------------------------------------------------------------------------------
-- 4.  Π and universe equations

postulate
  βΠS : ∀ {Γ} {A : TyS Γ} {B : TyS (Γ ▹S A)} (b : TmS B)
      → appS (lamS b) == b
  ηΠS : ∀ {Γ} {A : TyS Γ} {B : TyS (Γ ▹S A)} (f : TmS (ΠS A B))
      → lamS (appS f) == f
  Π[]S : ∀ {Γ Δ} {A : TyS Δ} {B : TyS (Δ ▹S A)} {f : SubS Γ Δ}
       → (ΠS A B) [ f ] == ΠS (A [ f ]) (B [ f ∷ₛ A ])
  lam[]S : ∀ {Γ Δ} {A : TyS Δ} {B : TyS (Δ ▹S A)} {f : SubS Γ Δ} {b : TmS B}
         → PathOver TmS Π[]S ((lamS b) [ f ]ₜ) (lamS (b [ f ∷ₛ A ]ₜ))

  U[]S  : ∀ {Γ Δ} {f : SubS Γ Δ} → US [ f ] == US
  El[]S : ∀ {Γ Δ} {f : SubS Γ Δ} {T : TmS {Δ} US}
        → (ElS T) [ f ] == ElS (coeᵀᵐ U[]S (T [ f ]ₜ))

synPi : PiStructure synCwF
synPi = record
  { Π′ = ΠS ; λ′ = lamS ; app = appS
  ; βΠ′ = βΠS ; ηΠ′ = ηΠS ; Π′[] = Π[]S ; λ′[]ₜ = lam[]S }

synU : UniverseStructure synCwF
synU = record { U = US ; el = ElS ; U[] = U[]S ; el[] = El[]S }

synSet : SetLevelStructure synCwF
synSet = record
  { Sub-is-set = SubS-is-set ; Ty-is-set = TyS-is-set ; Tm-is-set = TmS-is-set }
