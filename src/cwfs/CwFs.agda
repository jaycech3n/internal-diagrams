{-# OPTIONS --without-K --rewriting #-}

module cwfs.CwFs where

open import cwfs.Core public

-- Precoherent CwFs
record CwFStructure {ℓₒ ℓₘ} (C : WildCategory ℓₒ ℓₘ) : Type (lsuc (ℓₒ l⊔ ℓₘ)) where

  field compstr : ComprehensionStructure C
  open ComprehensionStructure compstr hiding (tytmstr) public

  private
    module notation where
      infixl 40 ap↓-Tm

      ap↓-Tm : {Γ Δ : Con} {f : Ty Γ → Ty Δ}
          (g : {A : Ty Γ} → Tm A → (Tm ∘ f) A)
          {A A' : Ty Γ} {p : A == A'}
          {a : Tm A} {a' : Tm A'}
        → a == a' [ Tm ↓ p ]
        → g a == g a' [ Tm ↓ ap f p ]
      ap↓-Tm g q = ap↓2 {A = Con} {B = Ty} {C = Tm} g q

      syntax ap↓-Tm g q = q |in-ctx↓ᵀᵐ g

      Tm[_] : ∀ Γ → Ty Γ → Type ℓₘ
      Tm[ Γ ] A = Tm A

      _ʷ : {Γ : Con} {A : Ty Γ} → Ty Γ → Ty (Γ ∷ A)
      _ʷ {A = A} B = B [ π A ]

      _ʷₜ : {Γ : Con} {A B : Ty Γ} → Tm B → Tm (B [ π A ])
      _ʷₜ {A = A} b = b [ π A ]ₜ

      instance
        witness-∷ : {Γ : Con} {A : Ty Γ} → Γ ∷ A == Γ ∷ A
        witness-∷ = idp

      var : {Γ : Con} {A : Ty Γ} (Δ : Con) → ⦃ Δ == Γ ∷ A ⦄ → Tm[ Γ ∷ A ] (A ʷ)
      var {Γ} {A} .(Γ ∷ A) ⦃ idp ⦄ = υ A

    module extension where
      _,,₊_ : ∀ Γ {A : Ty Γ} → Tm A → Sub Γ (Γ ∷ A)
      Γ ,,₊ a = id ,, a [ id ]ₜ

    module term-coercions {Γ : Con} where
      coeᵀᵐ-∙ : {A B C : Ty Γ} {t : Tm A} (p : A == B) (q : B == C)
               → coeᵀᵐ (p ∙ q) t == coeᵀᵐ q (coeᵀᵐ p t)
      coeᵀᵐ-∙ idp q = idp

      coeᵀᵐ-∙! : {A B C : Ty Γ} {t : Tm A} (p : A == B) (q : B == C)
                → coeᵀᵐ q (coeᵀᵐ p t) == coeᵀᵐ (p ∙ q) t
      coeᵀᵐ-∙! p q = ! (coeᵀᵐ-∙ p q)

      coe!ᵀᵐ-∙ : {A B C : Ty Γ} {t : Tm C} (p : A == B) (q : B == C)
                → coe!ᵀᵐ (p ∙ q) t == coe!ᵀᵐ p (coe!ᵀᵐ q t)
      coe!ᵀᵐ-∙ idp q = idp

      coe!ᵀᵐ-∙! : {A B C : Ty Γ} {t : Tm C} (p : A == B) (q : B == C)
                 → coe!ᵀᵐ p (coe!ᵀᵐ q t) == coe!ᵀᵐ (p ∙ q) t
      coe!ᵀᵐ-∙! p q = ! (coe!ᵀᵐ-∙ p q)

      -- Mediating between dependent paths and coercions
      to-coeᵀᵐˡ : {A A' : Ty Γ} {t : Tm A} {t' : Tm A'} {p : A == A'}
                 → t == t' over-Tm⟨ p ⟩
                 → coeᵀᵐ p t == t'
      to-coeᵀᵐˡ {t = t} {t'} {idp} = idf (t == t')

      to-coeᵀᵐʳ : {A A' : Ty Γ} {t : Tm A} {t' : Tm A'} {p : A == A'}
                 → t == t' over-Tm⟨ p ⟩
                 → t == coe!ᵀᵐ p t'
      to-coeᵀᵐʳ {t = t} {t'} {idp} = idf (t == t')

      from-coeᵀᵐˡ : {A A' : Ty Γ} {t : Tm A} {t' : Tm A'} {p : A == A'}
                  → coeᵀᵐ p t == t'
                  → t == t' over-Tm⟨ p ⟩
      from-coeᵀᵐˡ {t = t} {t'} {idp} = idf (t == t')

      from-over-∙ :
        {A B C : Ty Γ} {p : A == B} {q : B == C}
        {a : Tm A} {c : Tm C}
        → a == c over-Tm⟨ p ∙ q ⟩ → coeᵀᵐ p a == c over-Tm⟨ q ⟩
      from-over-∙ {p = idp} = idf _

    -- Codes for listlike contexts; see cwfs.Contextual.agda for more
    module listlike-contexts where
      Conᶜ : ℕ → Type ℓₒ
      con-of : {n : ℕ} → Conᶜ n → Con

      Conᶜ O = Lift ⊤
      Conᶜ (1+ n) = Σ[ γ ː Conᶜ n ] Ty (con-of γ)

      con-of {O} _ = ◆
      con-of {1+ n} (γ , A) = con-of γ ∷ A

  open notation public
  open extension public
  open term-coercions public
  open listlike-contexts public

  private
    module equalities where
      -- An equality of extended substitutions is a pair consisting of an equality
      -- between the first substitutions and a dependent path between the extending
      -- elements.
      ⟨=_,,_=⟩ : ∀ {Γ Δ} {A : Ty Δ} {f f' : Sub Γ Δ} {t : Tm (A [ f ])} {t' : Tm (A [ f' ])}
                → (p : f == f')
                → t == t' over-Tm⟨ [= p ] ⟩
                → (f ,, t ) == (f' ,, t')
      ⟨= idp ,, idp =⟩ = idp

      ⟨=,,_=⟩ : ∀ {Γ Δ} {A : Ty Δ} {f : Sub Γ Δ} {t t' : Tm (A [ f ])}
                → t == t'
                → (f ,, t ) == (f ,, t')
      ⟨=,, idp =⟩ = idp

      ⟨=_,,=⟩ : ∀ {Γ Δ} {A : Ty Δ} {f f' : Sub Γ Δ} {t : Tm (A [ f ])}
                → (p : f == f')
                → (f ,, t ) == (f' ,, coeᵀᵐ [= p ] t)
      ⟨= idp ,,=⟩ = idp

      υ-,, : ∀ {Γ} (A : Ty Γ) (a : Tm A)
             → υ A [ Γ ,,₊ a ]ₜ == a [ π A ]ₜ [ Γ ,,₊ a ]ₜ
      υ-,, {Γ} A a =
        υ A [ Γ ,,₊ a ]ₜ
          =⟨ βυ ⟫ᵈ
        a [ id ]ₜ
          =⟨ !ᵈ [= βπ ]ₜ ∙ᵈ [◦]ₜ ⟩ᵈ
        a [ π A ]ₜ [ Γ ,,₊ a ]ₜ
          =∎↓⟨ <!∙>∙!∙ [◦] [= βπ ] ⟩

      -- Important lemma: coercions along equalities of hypothetical/weakened elements
      -- are stable under substitution by _,,_.
      coeᵀᵐ-,,-stable :
        ∀ {Γ Δ} {A : Ty Δ} {A' : Ty (Δ ∷ A)}
          (p : A [ π A ] == A') (x : Tm (A [ π A ])) (f : Sub Γ Δ) (t : Tm (A [ f ]))
        → x [ f ,, t ]ₜ == (coeᵀᵐ p x) [ f ,, t ]ₜ over-Tm⟨ p |in-ctx (_[ f ,, t ]) ⟩
      coeᵀᵐ-,,-stable idp x f t = idp

  open equalities public

  private
    module universal-properties where

      ,,-uniq : ∀ {Γ Δ} {f : Sub Γ Δ} {A : Ty Δ} {t : Tm (A [ f ])}
                  (ϕ : Sub Γ (Δ ∷ A))
                  (πϕ : π A ◦ ϕ == f)
                  (υϕ : υ A [ ϕ ]ₜ == t over-Tm⟨ (! [◦] ∙ [= πϕ ]) ⟩)
                → ϕ == (f ,, t)
      ,,-uniq {f = f} {A} {t} ϕ πϕ υϕ =
        ϕ
          =⟨ ! idl ⟩
        id ◦ ϕ
          =⟨ ! η,, |in-ctx (_◦ ϕ) ⟩
        (π A ,, υ A) ◦ ϕ
          =⟨ ,,-◦ ⟩
        (π A ◦ ϕ ,, coe!ᵀᵐ [◦] (υ A [ ϕ ]ₜ) )
          =⟨ ⟨= πϕ ,, from-over-∙ υϕ =⟩ ⟩
        (f ,, t)
          =∎

  open universal-properties public

  private
    module weakening {Γ Δ : Con} where

      {- Given f : Sub Δ Γ and A : Ty Γ, we get the weakening (f ↑ A) of f by A that,
      intuitively, acts as f does, and leaves the "free variable x : A" alone. This
      diagram commutes:

                            f ↑ A
                   Γ ∷ A[f] -----> Δ ∷ A
            π (A[f]) |               | π A    (*)
                     ↓               ↓
                     Γ ------------> Δ
                             f
      -}

      _↑_ : (f : Sub Γ Δ) (A : Ty Δ) → Sub (Γ ∷ A [ f ]) (Δ ∷ A)
      f ↑ A = f ◦ π (A [ f ]) ,, coe!ᵀᵐ [◦] (υ (A [ f ]))

      ↑-comm : {A : Ty Δ} {f : Sub Γ Δ} → π A ◦ (f ↑ A) == f ◦ π (A [ f ])
      ↑-comm = βπ

      {- Given f and A as in (*) above and a : Tm A, we have (Γ ,,₊ a) := (id ,, a[id]ₜ)
      and the two compositions forming the boundary of the square below:

                            f ↑ A
                   Γ ∷ A[f] -----> Δ ∷ A
          Γ ,,₊ a[f] ↑               ↑ Δ ,,₊ a    (**)
                     |               |
                     Γ ------------> Δ
                             f

      There is also a direct substitution on the diagonal, which is (f ,, a[f]ₜ).
      We show that the two compositions are each equal to the diagonal, which implies
      that the compositions are equal.

      The first is easy: -}

      ,,₊-◦ : {A : Ty Δ} (f : Sub Γ Δ) (a : Tm A)
              → (Δ ,,₊ a) ◦ f == (f ,, a [ f ]ₜ)
      ,,₊-◦ f a =
        (Δ ,,₊ a) ◦ f
          =⟨ ,,-◦ ⟩
        (id ◦ f ,, coe!ᵀᵐ [◦] (a [ id ]ₜ [ f ]ₜ))
          =⟨ ⟨= idl ,, from-over-∙ (!ᵈ [◦]ₜ ∙ᵈ [= idl ]ₜ) =⟩ ⟩
        (f ,, a [ f ]ₜ)
          =∎

      {- The second is a bit more work. We use the universal property ,,-uniq and
      prove a series of somewhat lengthy reductions. -}

      -- In (**), going up, left and then down (by π) is the same as f.
      ⊓-lemma : {A : Ty Δ} (f : Sub Γ Δ) (a : Tm A)
                → π A ◦ (f ↑ A) ◦ (Γ ,,₊ a [ f ]ₜ) == f
      ⊓-lemma f a = ! ass
                    ∙ (↑-comm |in-ctx (_◦ (Γ ,,₊ a [ f ]ₜ)))
                    ∙ ass
                    ∙ (βπ |in-ctx (f ◦_))
                    ∙ idr

      ↑-,,₊ : {A : Ty Δ} (f : Sub Γ Δ) (a : Tm A)
              → (f ↑ A) ◦ (Γ ,,₊ a [ f ]ₜ) == (f ,, a [ f ]ₜ)
      ↑-,,₊ {A} f a = ,,-uniq ((f ↑ A) ◦ (Γ ,,₊ a [ f ]ₜ)) (⊓-lemma f a) (red1 ∙ᵈ red2)
        where
        calc : υ A [ f ↑ A ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
              == a [ π A ]ₜ [ f ↑ A ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
        calc =
          υ A [ f ↑ A ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ βυ |in-ctx↓ᵀᵐ _[ Γ ,,₊ a [ f ]ₜ ]ₜ ⟫ᵈ
          coe!ᵀᵐ [◦] (υ (A [ f ])) [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ !ᵈ (coeᵀᵐ-,,-stable (! [◦]) (υ (A [ f ])) id (a [ f ]ₜ [ id ]ₜ)) ⟫ᵈ
          υ (A [ f ]) [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ υ-,, (A [ f ]) (a [ f ]ₜ) ⟫ᵈ
          a [ f ]ₜ [ π (A [ f ]) ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ !ᵈ [◦]ₜ |in-ctx↓ᵀᵐ _[ Γ ,,₊ a [ f ]ₜ ]ₜ ⟫ᵈ
          a [ f ◦ π (A [ f ]) ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ !ᵈ [= ↑-comm ]ₜ ∙ᵈ [◦]ₜ |in-ctx↓ᵀᵐ _[ Γ ,,₊ a [ f ]ₜ ]ₜ ⟩ᵈ
          a [ π A ]ₜ [ f ↑ A ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =∎↓⟨ =ₛ-out base-paths-equal ⟩
          where
            base-paths-equal :
              (! [◦] ∙ [= βπ ] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ]) ◃∙
              ! (! [◦] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ]) ◃∙
              (! [◦] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ]) ◃∙
              (! [= βπ ] ∙ [◦] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ]) ◃∎
              =ₛ idp ◃∎
            base-paths-equal =
              (! [◦] ∙ [= βπ ] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ])
              ◃∙ ! (! [◦] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ])
              ◃∙ (! [◦] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ])
              ◃∙ (! [= βπ ] ∙ [◦] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ])
              ◃∎
                =ₛ₁⟨ 1 & 2 & !-inv-l (! [◦] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ]) ⟩

              (! [◦] ∙ [= βπ ] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ])
              ◃∙ idp
              ◃∙ (! [= βπ ] ∙ [◦] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ])
              ◃∎
                =ₛ₁⟨ ! (ap-∙ _[ Γ ,,₊ (a [ f ]ₜ) ] (! [◦] ∙ [= βπ ]) (! [= βπ ] ∙ [◦]))
                   ∙ (<!∙>∙!∙ [◦] [= βπ ] |in-ctx (ap _[ Γ ,,₊ a [ f ]ₜ ])) ⟩

              idp ◃∎ ∎ₛ

        red1 : υ A [ (f ↑ A) ◦ (Γ ,,₊ a [ f ]ₜ) ]ₜ
               == a [ π A ]ₜ [ (f ↑ A) ◦ (Γ ,,₊ a [ f ]ₜ) ]ₜ
        red1 =
          υ A [ (f ↑ A) ◦ (Γ ,,₊ a [ f ]ₜ) ]ₜ
            =⟨ [◦]ₜ ↓ [◦] ⟫ᵈ
          υ A [ f ↑ A ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ calc ⟫ᵈ
          a [ π A ]ₜ [ f ↑ A ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ !ᵈ [◦]ₜ ↓ ! [◦] ⟩ᵈ
          a [ π A ]ₜ [ (f ↑ A) ◦ (Γ ,,₊ a [ f ]ₜ) ]ₜ
            =∎↓⟨ !-inv-r [◦] ⟩

        red2 : a [ π A ]ₜ [ (f ↑ A) ◦ (Γ ,,₊ a [ f ]ₜ) ]ₜ == a [ f ]ₜ
                 over-Tm⟨ ! [◦] ∙ [= ⊓-lemma f a ] ⟩
        red2 = !ᵈ [◦]ₜ ∙ᵈ [= ⊓-lemma f a ]ₜ

        {- Failed attempt; just some random path in the total space may not lie over
        the path we want in the base:

        wrong-red : υ A [ (f ↑ A) ◦ (Γ ,,₊ a [ f ]ₜ) ]ₜ == a [ f ]ₜ
                       over-Tm⟨ ! [◦] ∙ [= ⊓-lemma f a ] ⟩
        wrong-red =
          υ A [ (f ↑ A) ◦ (Γ ,,₊ a [ f ]ₜ) ]ₜ
            =⟨ [◦]ₜ ↓ [◦] ⟫ᵈ
          υ A [ f ◦ π (A [ f ]) ,, coe!ᵀᵐ [◦] (υ (A [ f ])) ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ βυ |in-ctx↓ᵀᵐ (_[ Γ ,,₊ a [ f ]ₜ ]ₜ) ⟫ᵈ
          coe!ᵀᵐ [◦] (υ (A [ f ])) [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ !ᵈ (coeᵀᵐ-,,-stable (! [◦]) (υ (A [ f ])) id (a [ f ]ₜ [ id ]ₜ)) ⟫ᵈ
          υ (A [ f ]) [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ βυ ⟫ᵈ
          a [ f ]ₜ [ id ]ₜ
            =⟨ !ᵈ [◦]ₜ ∙ᵈ [= idr ]ₜ ⟩ᵈ
          a [ f ]ₜ
            =∎↓⟨ {!!} ⟩ -}

      ,,₊-comm : {A : Ty Δ} (f : Sub Γ Δ) (a : Tm A)
                 → (Δ ,,₊ a) ◦ f == (f ↑ A) ◦ (Γ ,,₊ a [ f ]ₜ)
      ,,₊-comm f a = ,,₊-◦ f a ∙ ! (↑-,,₊ f a)

  open weakening public

  private
    module substitutions where
      infix 40 _⟦_⟧ _⟦_⟧ₜ

      _⟦_⟧ : ∀ {Γ} {A : Ty Γ} (B : Ty (Γ ∷ A)) (a : Tm A) → Ty Γ
      _⟦_⟧ {Γ} B a = B [ Γ ,,₊ a ]

      _⟦_⟧ₜ : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} (b : Tm B) (a : Tm A) → Tm (B ⟦ a ⟧)
      _⟦_⟧ₜ {Γ} b a = b [ Γ ,,₊ a ]ₜ

      -- Commutation law
      []-⟦⟧ : ∀ {Γ Δ} {A : Ty Δ} (B : Ty (Δ ∷ A)) (f : Sub Γ Δ) (a : Tm A)
              → B [ f ↑ A ] ⟦ a [ f ]ₜ ⟧ == B ⟦ a ⟧ [ f ]
      []-⟦⟧ B f a = ! [◦] ∙ ! [= ,,₊-comm f a ] ∙ [◦]

      -- Coercing to equal substitutions
      coe-cod : ∀ {Γ Δ Δ'} → Δ == Δ' → Sub Γ Δ → Sub Γ Δ'
      coe-cod idp = idf _

  open substitutions public
