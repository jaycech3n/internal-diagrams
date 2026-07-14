{-# OPTIONS --without-K --rewriting #-}

{- This is a STRICT version of Syntax.agda. More precisely, it is a copy of
   Syntax.agda with rewrite pragmas to get some strictness.

   We keep this separate from Syntax.agda because rewrite pragmas are
   potentially dangerous. Every rule below is an oriented instance of one of
   the postulated equations of Syntax.agda. The system is most likely not
   confluent, but good enough for testing.
-}

module cwfs.SyntaxStrict where

open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe
open import cwfs.SetLevel

infixr 40 _∘X_
infixl 40 _[_]TX _[_]tX
infixl 35 _▹X_
infixl 35 _,X_

postulate
  ConX : Type lzero
  SubX : ConX → ConX → Type lzero
  TyX  : ConX → Type lzero
  TmX  : {Γ : ConX} → TyX Γ → Type lzero

  _∘X_ : ∀ {Γ Δ Θ} → SubX Δ Θ → SubX Γ Δ → SubX Γ Θ
  idX  : ∀ {Γ} → SubX Γ Γ

postulate
  assX : ∀ {Γ Δ Θ Ξ} {f : SubX Θ Ξ} {g : SubX Δ Θ} {h : SubX Γ Δ}
       → ((f ∘X g) ∘X h) ↦ (f ∘X (g ∘X h))
{-# REWRITE assX #-}

postulate
  idlX : ∀ {Γ Δ} {f : SubX Γ Δ} → (idX ∘X f) ↦ f
{-# REWRITE idlX #-}

postulate
  idrX : ∀ {Γ Δ} {f : SubX Γ Δ} → (f ∘X idX) ↦ f
{-# REWRITE idrX #-}

postulate
  ◇X  : ConX
  εX  : ∀ {Γ} → SubX Γ ◇X
  -- Not a rewrite rule: the left-hand side would be a bare variable.
  ◇ηX : ∀ {Γ} (σ : SubX Γ ◇X) → σ == εX

postulate
  _[_]TX : ∀ {Γ Δ} → TyX Δ → SubX Γ Δ → TyX Γ

postulate
  [id]TX : ∀ {Γ} {A : TyX Γ} → (A [ idX ]TX) ↦ A
{-# REWRITE [id]TX #-}

postulate
  [∘]TX : ∀ {Γ Δ Θ} {f : SubX Γ Δ} {g : SubX Δ Θ} {A : TyX Θ}
        → (A [ g ]TX [ f ]TX) ↦ (A [ g ∘X f ]TX)
{-# REWRITE [∘]TX #-}

postulate
  _[_]tX : ∀ {Γ Δ} {A : TyX Δ} → TmX A → (f : SubX Γ Δ) → TmX (A [ f ]TX)

postulate
  [id]tX : ∀ {Γ} {A : TyX Γ} {t : TmX A} → (t [ idX ]tX) ↦ t
{-# REWRITE [id]tX #-}

postulate
  [∘]tX : ∀ {Γ Δ Θ} {f : SubX Γ Δ} {g : SubX Δ Θ} {A : TyX Θ} {t : TmX A}
        → (t [ g ∘X f ]tX) ↦ (t [ g ]tX [ f ]tX)
{-# REWRITE [∘]tX #-}

postulate
  _▹X_ : (Γ : ConX) → TyX Γ → ConX
  pX   : ∀ {Γ} (A : TyX Γ) → SubX (Γ ▹X A) Γ
  qX   : ∀ {Γ} (A : TyX Γ) → TmX (A [ pX A ]TX)
  _,X_ : ∀ {Γ Δ} {A : TyX Δ} (f : SubX Γ Δ) → TmX (A [ f ]TX) → SubX Γ (Δ ▹X A)

postulate
  βπX : ∀ {Γ Δ} {f : SubX Γ Δ} {A : TyX Δ} {t : TmX (A [ f ]TX)}
      → (pX A ∘X (f ,X t)) ↦ f
{-# REWRITE βπX #-}

-- Type-correct only because βπX is already active.
postulate
  βυX : ∀ {Γ Δ} {f : SubX Γ Δ} {A : TyX Δ} {t : TmX (A [ f ]TX)}
      → (qX A [ f ,X t ]tX) ↦ t
{-# REWRITE βυX #-}

postulate
  ηX : ∀ {Γ} {A : TyX Γ} → (pX A ,X qX A) ↦ (idX {Γ ▹X A})
{-# REWRITE ηX #-}

postulate
  ,∘X : ∀ {Γ Δ Θ} {f : SubX Γ Δ} {g : SubX Δ Θ} {A : TyX Θ} {t : TmX (A [ g ]TX)}
      → ((g ,X t) ∘X f)
        ↦ (_,X_ {A = A} (g ∘X f) (_[_]tX {A = A [ g ]TX} t f))
{-# REWRITE ,∘X #-}

wkX : ∀ {Γ Δ} (f : SubX Γ Δ) (A : TyX Δ) → SubX (Γ ▹X A [ f ]TX) (Δ ▹X A)
wkX f A = (f ∘X pX (A [ f ]TX)) ,X qX (A [ f ]TX)

postulate
  ΠX   : ∀ {Γ} (A : TyX Γ) → TyX (Γ ▹X A) → TyX Γ
  lamX : ∀ {Γ} {A : TyX Γ} {B : TyX (Γ ▹X A)} → TmX B → TmX (ΠX A B)
  appX : ∀ {Γ} {A : TyX Γ} {B : TyX (Γ ▹X A)} → TmX (ΠX A B) → TmX B

postulate
  βΠX : ∀ {Γ} {A : TyX Γ} {B : TyX (Γ ▹X A)} {b : TmX B} → appX (lamX b) ↦ b
{-# REWRITE βΠX #-}

postulate
  Π[]X : ∀ {Γ Δ} {A : TyX Δ} {B : TyX (Δ ▹X A)} {f : SubX Γ Δ}
       → (ΠX A B [ f ]TX) ↦ ΠX (A [ f ]TX) (B [ wkX f A ]TX)
{-# REWRITE Π[]X #-}

postulate
  ηΠX : ∀ {Γ} {A : TyX Γ} {B : TyX (Γ ▹X A)} (f : TmX (ΠX A B))
      → lamX (appX f) == f
  lam[]X : ∀ {Γ Δ} {A : TyX Δ} {B : TyX (Δ ▹X A)} {f : SubX Γ Δ} {b : TmX B}
         → (lamX b [ f ]tX) == lamX (b [ wkX f A ]tX)

postulate
  UX  : ∀ {Γ} → TyX Γ
  ElX : ∀ {Γ} → TmX {Γ} UX → TyX Γ

postulate
  U[]X : ∀ {Γ Δ} {f : SubX Γ Δ} → (UX {Δ} [ f ]TX) ↦ UX {Γ}
{-# REWRITE U[]X #-}

postulate
  El[]X : ∀ {Γ Δ} {f : SubX Γ Δ} {T : TmX {Δ} UX}
        → (ElX T [ f ]TX) ↦ ElX (T [ f ]tX)
{-# REWRITE El[]X #-}

postulate
  SubX-is-set : ∀ {Γ Δ} → is-set (SubX Γ Δ)
  TyX-is-set  : ∀ {Γ}   → is-set (TyX Γ)
  TmX-is-set  : ∀ {Γ} {A : TyX Γ} → is-set (TmX A)


-- Structures

synxWildCat : WildCategory lzero lzero
synxWildCat = record
  { Ob = ConX
  ; wildcatstr = record
      { wildsemicatstr = record { hom = SubX ; _◦_ = _∘X_ ; ass = idp }
      ; id = idX ; idl = λ f → idp ; idr = λ f → idp } }

synxCtx : ContextStructure synxWildCat
synxCtx = record
  { ◆ = ◇X
  ; ◆-terminal = λ Γ → has-level-in (εX , λ σ → ! (◇ηX σ)) }

synxTyTm : TyTmStructure synxWildCat
synxTyTm = record
  { ctxstr = synxCtx
  ; Ty = TyX ; _[_] = _[_]TX ; [id] = idp ; [◦] = idp
  ; Tm = TmX ; _[_]ₜ = _[_]tX ; [id]ₜ = idp
  ; [◦]ₜ = λ {Γ} {Δ} {Ε} {f} {g} {A} {t} → idp }

synxCompr : ComprehensionStructure synxWildCat
synxCompr = record
  { tytmstr = synxTyTm
  ; _∷_ = _▹X_ ; π = pX ; υ = qX ; _,,_ = _,X_
  ; βπ = idp ; βυ = idp ; η,, = idp ; ,,-◦ = idp }

synxCwF : CwFStructure synxWildCat
synxCwF = record { compstr = synxCompr }

synxPi : PiStructure synxCwF
synxPi = record
  { Π′ = ΠX ; λ′ = lamX ; app = appX
  ; βΠ′ = λ b → idp ; ηΠ′ = ηΠX ; Π′[] = idp
  ; λ′[]ₜ = λ {Γ} {Δ} {A} {B} {f} {b} → lam[]X {Γ} {Δ} {A} {B} {f} {b} }

synxU : UniverseStructure synxCwF
synxU = record { U = UX ; el = ElX ; U[] = idp ; el[] = idp }

synxSet : SetLevelStructure synxCwF
synxSet = record
  { Sub-is-set = SubX-is-set ; Ty-is-set = TyX-is-set ; Tm-is-set = TmX-is-set }

