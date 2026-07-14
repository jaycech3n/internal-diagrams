{-# OPTIONS --without-K --rewriting #-}

{- Conditions on a wild cwf that make it set-level
   (and thus remove wildness).

NOTE. Of the three fields below, the diagram construction (reedy.Diagrams
and the TelescopeWeakening module of cwfs.Telescopes) only ever uses
Ty-is-set. This means that the construction in fact goes through for any
wild cwf whose *types* form sets, with no assumption on substitutions,
terms, or contexts. That was pretty much expected, of course. We still
list the other components for now. -}

module cwfs.SetLevel where

open import cwfs.CwFs

record SetLevelStructure {ℓₒ ℓₘ} {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C) : Type (lsuc (ℓₒ ∪ ℓₘ)) where

  open CwFStructure cwfstr

  field
    Sub-is-set : ∀ {Γ Δ} → is-set (Sub Γ Δ)
    Ty-is-set  : ∀ {Γ} → is-set (Ty Γ)
    Tm-is-set  : ∀ {Γ} {A : Ty Γ} → is-set (Tm A)

  private
    module helpers where
      -- Two generic transport lemmas for terms (these do not use the
      -- set-level assumptions; they are included here for convenience).
      coeᵀᵐ-in : ∀ {Γ} {A B : Ty Γ} (p : A == B) (t : Tm A)
        → t == coeᵀᵐ p t over⟨ p ⟩
      coeᵀᵐ-in idp t = idp

      coeᵀᵐ-out : ∀ {Γ} {A B : Ty Γ} (p : A == B) (t : Tm A)
        → coeᵀᵐ p t == t over⟨ ! p ⟩
      coeᵀᵐ-out idp t = idp

      {- Proof irrelevance for parallel equalities of types, substitutions and
      terms.  These are the workhorses: they are what "set-level" buys us. -}

      Ty=-irr : ∀ {Γ} {A B : Ty Γ} (p q : A == B) → p == q
      Ty=-irr {Γ} {A} {B} = prop-path (has-level-apply Ty-is-set A B)

      Sub=-irr : ∀ {Γ Δ} {f g : Sub Γ Δ} (p q : f == g) → p == q
      Sub=-irr {f = f} {g} = prop-path (has-level-apply Sub-is-set f g)

      Tm=-irr : ∀ {Γ} {A : Ty Γ} {a b : Tm A} (p q : a == b) → p == q
      Tm=-irr {a = a} {b} = prop-path (has-level-apply Tm-is-set a b)

      -- Coercions along parallel type equalities agree.
      coeᵀᵐ-irr : ∀ {Γ} {A B : Ty Γ} (p q : A == B) (t : Tm A)
        → coeᵀᵐ p t == coeᵀᵐ q t
      coeᵀᵐ-irr p q t = ap (λ e → coeᵀᵐ e t) (Ty=-irr p q)

      -- Change the base path of a dependent path between terms.
      over-irr : ∀ {Γ} {A B : Ty Γ} {p q : A == B} {a : Tm A} {b : Tm B}
        → a == b over⟨ p ⟩ → a == b over⟨ q ⟩
      over-irr {p = p} {q} = ↓-equal-paths (Ty=-irr p q)

      {- In a set-level cwf a dependent path between terms is the same as an
      equation between coercions, along *any* choice of base path. -}

      from-over-set : ∀ {Γ} {A B : Ty Γ} {p e : A == B} {a : Tm A} {b : Tm B}
        → a == b over⟨ e ⟩ → coeᵀᵐ p a == b
      from-over-set {p = p} α = to-coeᵀᵐˡ (over-irr {q = p} α)

      to-over-set : ∀ {Γ} {A B : Ty Γ} {p e : A == B} {a : Tm A} {b : Tm B}
        → coeᵀᵐ p a == b → a == b over⟨ e ⟩
      to-over-set {p = p} {e} α = over-irr {p = p} {e} (from-coeᵀᵐˡ α)

      -- Two coercions of the same term are equal over any path between the
      -- target types.
      coeᵀᵐ-over : ∀ {Γ} {A B B' : Ty Γ} (p : A == B) (q : A == B')
        (e : B == B') (t : Tm A)
        → coeᵀᵐ p t == coeᵀᵐ q t over⟨ e ⟩
      coeᵀᵐ-over p q idp t = coeᵀᵐ-irr p q t

      -- A term equals any coercion of itself, over any base path.
      coeᵀᵐ-over-r : ∀ {Γ} {A B : Ty Γ} (q e : A == B) (t : Tm A)
        → t == coeᵀᵐ q t over⟨ e ⟩
      coeᵀᵐ-over-r q e t = to-over-set {p = q} {e} idp

  open helpers public
