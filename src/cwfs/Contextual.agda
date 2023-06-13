{-# OPTIONS --without-K --rewriting #-}

module cwfs.Contextual where

open import cwfs.CwFs

record LenStructure {ℓₒ ℓₘ} {C : WildCategory ℓₒ ℓₘ} (cwfstr : CwFStructure C)
  : Type (lsuc (ℓₒ l⊔ ℓₘ)) where

  open CwFStructure cwfstr

  field
    len : Con → ℕ
    len-∷ : (Γ : Con) (A : Ty Γ) → len (Γ ∷ A) == 1+ (len Γ)

  ∷-len : ∀ n → Σ[ Γ ː Con ] Ty Γ × (len Γ == n) → Σ[ Γ ː Con ] len Γ == 1+ n
  ∷-len _ (Γ , A , idp) = (Γ ∷ A) , len-∷ Γ A

record ContextualStructure {ℓₒ ℓₘ} {C : WildCategory ℓₒ ℓₘ} (cwfstr : CwFStructure C)
  : Type (lsuc (ℓₒ l⊔ ℓₘ)) where

  field lenstr : LenStructure cwfstr
  open LenStructure lenstr
  open CwFStructure cwfstr

  field
    len-◆-equiv : ∀ {Γ} → (Γ == ◆) ≃ (len Γ == O)
      -- Do we actually need it to be this strong?
      -- What about just (len ◆ == O) × (len Γ == O → Γ == ◆)?
      -- A : You do need this; see Con-codes in cwfs.contextual.CwFs
    len-∷-equiv : ∀ {n} → is-equiv (∷-len n)

  len-◆ : len ◆ == O
  len-◆ = –> len-◆-equiv idp

  private
    module context-operations where
      dest-context :
        ∀ {n} (Γ : Con) → len Γ == 1+ n → Σ[ Δ ː Con ] Ty Δ × (len Δ == n)
      dest-context = curry (inv-equiv len-∷-equiv)

      split-context :
        ∀ {n} (Γ : Con) → len Γ == 1+ n → Σ[ Δ ː Con ] Ty Δ
      split-context Γ p = first-two (dest-context Γ p)

  open context-operations

  {-
  conᶜ-of : ∀ {n} → (Γ : Con) → ⦃ len Γ == n ⦄ → Conᶜ n
  con-conᶜ : ∀ {n} → (Γ : Con) → ⦃ p : len Γ == n ⦄ → Γ == con-of (conᶜ-of Γ)

  conᶜ-of {O} Γ = lift tt
  conᶜ-of {1+ n} Γ ⦃ p ⦄ = conᶜ-of Δ , transp Ty (con-conᶜ Δ) A
    where
    ΔAq = dest-context Γ p
    Δ = fst ΔAq
    A = 2nd ΔAq
    instance q = 3rd ΔAq

  con-conᶜ {O} Γ ⦃ p ⦄ = <– len-◆-equiv p
  con-conᶜ {1+ n} Γ ⦃ p ⦄ = {!-- switching to another formulation for now,
    but should figure out whether this is actually provable!}
  -}

module Contextual-contextual-core {ℓₒ ℓₘ} {C : WildCategory ℓₒ ℓₘ} (cwf : CwFStructure C)
  where

  -- Given a CwF 𝒞, the sub-CwF on the contexts generated by ◆ and
  -- ∷ is a contextual CwF. We call this the *contextual core* of 𝒞.

  open CwFStructure cwf

  -- (Isomorphic to the) Subcategory of C inductively generated by ◆ and ∷
  Cᶜ : WildCategory ℓₒ ℓₘ
  WildCategory.Ob Cᶜ = Σ[ n ː ℕ ] Conᶜ n
  WildCategory.wildcatstr Cᶜ = record
    { wildsemicatstr = record
        { hom = λ{ (_ , γ) (_ , δ) → Sub (con-of γ) (con-of δ) }
        ; _◦_ = _◦_
        ; ass = ass }
    ; id = id
    ; idl = idl
    ; idr = idr }

  ctxstrᶜ : ContextStructure Cᶜ
  ctxstrᶜ = record
    { ◆ = O , lift unit
    ; ◆-terminal = λ{ (_ , γ) → ◆-terminal (con-of γ) } }

  open ContextStructure ctxstrᶜ

  tytmstrᶜ : TyTmStructure Cᶜ
  tytmstrᶜ = record
    { ctxstr = ctxstrᶜ
    ; Ty = λ{ (_ , γ) → Ty (con-of γ) }
    ; _[_] = _[_]
    ; [id] = [id]
    ; [◦] = [◦]
    ; Tm = Tm
    ; _[_]ₜ = _[_]ₜ
    ; [id]ₜ = [id]ₜ
    ; [◦]ₜ = [◦]ₜ }

  coeᵀᵐᶜ= :
    {Γ @ (n , γ) : ContextStructure.Con ctxstrᶜ}
    {A A' : Ty (con-of γ)}
    (p : A == A') (t : Tm A)
    → TyTmStructure.coeᵀᵐ tytmstrᶜ {Γ} p t == coeᵀᵐ p t
  coeᵀᵐᶜ= idp t = idp

  cwfstrᶜ : CwFStructure Cᶜ
  CwFStructure.compstr cwfstrᶜ = record
    { tytmstr = tytmstrᶜ
    ; _∷_ = λ (n , γ) A → 1+ n , γ , A
    ; π = π
    ; υ = υ
    ; _,,_ = _,,_
    ; βπ = βπ
    ; βυ = βυ
    ; η,, = η,,
    ; ,,-◦ = ,,-◦ ∙ ⟨=,, ! (coeᵀᵐᶜ= (! [◦]) _) =⟩ }

  lenstrᶜ : LenStructure cwfstrᶜ
  LenStructure.len lenstrᶜ = fst
  LenStructure.len-∷ lenstrᶜ Γ A = idp

  ContextualCoreStructure : ContextualStructure cwfstrᶜ
  ContextualStructure.lenstr ContextualCoreStructure = lenstrᶜ
  ContextualStructure.len-◆-equiv ContextualCoreStructure =
    equiv (λ{ idp → idp }) (λ{ idp → idp }) (λ{ idp → idp }) (λ{ idp → idp })
  ContextualStructure.len-∷-equiv ContextualCoreStructure {n} =
    is-eq (∷-len n)
      (λ{ ((_ , γ , A) , idp) → (n , γ) , A , idp })
      (λ{ ((_ , γ) , idp) → idp })
      (λ{ ((_ , γ) , A , idp) → idp })
    where open LenStructure lenstrᶜ using (∷-len)
