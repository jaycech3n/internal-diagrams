{-# OPTIONS --without-K --rewriting #-}

module cwfs.Sigma where

open import cwfs.CwFs

record SigmaStructure {ℓₒ ℓₘ} {C : WildCategory ℓₒ ℓₘ} (cwfstr : CwFStructure C)
  : Type (lsuc (ℓₒ ∪ ℓₘ)) where

  open CwFStructure cwfstr

  field
    Σ′   : ∀ {Γ} (A : Ty Γ) (B : Ty (Γ ∷ A)) → Ty Γ
    _﹐_ : ∀ {Γ} {A} {B : Ty (Γ ∷ A)} (a : Tm A) (b : Tm (B ⟦ a ⟧)) → Tm (Σ′ A B)
    fst′ : ∀ {Γ} {A} {B : Ty (Γ ∷ A)} → Tm (Σ′ A B) → Tm A
    snd′ : ∀ {Γ} {A} {B : Ty (Γ ∷ A)} (ab : Tm (Σ′ A B)) → Tm (B ⟦ fst′ ab ⟧)

    ﹐-fst′ : ∀ {Γ} {A} {B : Ty (Γ ∷ A)} {a : Tm A} {b : Tm (B ⟦ a ⟧)}
              → fst′ (a ﹐ b) == a

    ﹐-snd′ : ∀ {Γ} {A} {B : Ty (Γ ∷ A)} {a : Tm A} {b : Tm (B ⟦ a ⟧)}
              → snd′ (a ﹐ b) == b over⟨ ﹐-fst′ |in-ctx (B ⟦_⟧) ⟩

    ηΣ′ : ∀ {Γ} {A} {B : Ty (Γ ∷ A)} {ab : Tm (Σ′ A B)} → (fst′ ab ﹐ snd′ ab) == ab

    Σ′[] : ∀ {Γ Δ} {A B} {f : Sub Γ Δ} → (Σ′ A B) [ f ] == Σ′ (A [ f ]) (B [ f ∷ₛ A ])

    ﹐[]ₜ : ∀ {Γ Δ} {A B} {f : Sub Γ Δ} {a : Tm A} {b : Tm (B ⟦ a ⟧)}
            → (a ﹐ b) [ f ]ₜ == (a [ f ]ₜ ﹐ coe!ᵀᵐ ([]-⟦⟧ B f a) (b [ f ]ₜ)) over⟨ Σ′[] ⟩

  private
    module notation where
      infixl 35 _×′_
      _×′_ : ∀ {Γ} (A B : Ty Γ) → Ty Γ
      A ×′ B = Σ′ A (B [ π A ])

  open notation public
