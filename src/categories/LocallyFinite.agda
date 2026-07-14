{-# OPTIONS --without-K --rewriting #-}

module categories.LocallyFinite where

open import categories.Semicategories public

-- Untruncatedly finite hom sets
record LocallyFiniteSemicategoryStructure {ℓₒ ℓₘ} {Ob : Type ℓₒ}
  (C : WildSemicategoryStructure ℓₒ ℓₘ Ob)
  : Type (lsuc (ℓₒ ∪ ℓₘ)) where
  open WildSemicategoryStructure C

  field
    hom-finite : ∀ x y → Σ[ n ﹕ ℕ ] (hom x y ≃ Fin n)

  private
    module basic-definitions where
      -- NOTE: this block used to be `abstract`. This is now changed
      -- so that hom-size, idx' etc. reduce on concrete numerals, which
      -- lets Agda evaluate the diagram construction if the cwf is
      -- sufficiently strict.
      module _ where
        hom-size : (x y : Ob) → ℕ
        hom-size x y = fst (hom-finite x y)

        hom-equiv : (x y : Ob) → hom x y ≃ Fin (hom-size x y)
        hom-equiv x y = snd (hom-finite x y)

        idx' : ∀ {x y} → hom x y → Fin (hom-size x y)
        idx' {x} {y} f = –> (hom-equiv x y) f

        hom[_,_]#' : ∀ x y → Fin (hom-size x y) → hom x y
        hom[ x , y ]#' = <– (hom-equiv x y)

        hom#'-idx' : ∀ {x y} (f : hom x y)
                     → hom[ x , y ]#' (idx' f) == f
        hom#'-idx' {x} {y} f = <–-inv-l (hom-equiv x y) f

        idx'-hom#' : ∀ {x y} (i : Fin (hom-size x y))
                     → idx' (hom[ x , y ]#' i) == i
        idx'-hom#' {x} {y} i = <–-inv-r (hom-equiv x y) i

        -- The defining equation of idx', exported explicitly.
        idx'-def : ∀ {x y} (f : hom x y)
                   → to-ℕ (idx' f) == to-ℕ (–> (snd (hom-finite x y)) f)
        idx'-def f = idp

  open basic-definitions public

  private
    module indices where
      idx : ∀ {x y} → hom x y → ℕ
      idx = to-ℕ ∘ idx'

      idx<hom-size : ∀ {x y} (f : hom x y) → idx f < hom-size x y
      idx<hom-size f = snd (idx' f)

      #[_] : (i : ℕ) (x y : Ob) → i < hom-size x y → hom x y
      #[ i ] x y u = hom[ x , y ]#' (i , u)

      #[]= : ∀ {i} {x y} {u u'} → #[ i ] x y u == #[ i ] x y u'
      #[]= {i} {x} {y} = ap (#[ i ] x y) (<-has-all-paths _ _)

      module _ {x y : Ob} where
        hom#-idx :
          (f : hom x y)
          → {u : idx f < hom-size x y}
          → #[ idx f ] x y u == f
        hom#-idx f = #[]= ∙ hom#'-idx' f

        idx-hom# :
          (i : ℕ) {u : i < hom-size x y}
          → idx (#[ i ] x y u) == i
        idx-hom# i {u} = ap to-ℕ (idx'-hom#' (i , u))

        hom=-idx= :
          {f g : hom x y}
          → f == g
          → idx f == idx g
        hom=-idx= idp = idp

        idx=-hom= :
          {f g : hom x y}
          → idx f == idx g
          → f == g
        idx=-hom= {f} {g} p =
          ! (hom#'-idx' f) ∙
          ap hom[ x , y ]#' (Fin= p) ∙
          hom#'-idx' g

  open indices public

  private
    module hom-order {x y : Ob} where
      _≺_ : (f g : hom x y) → Type₀
      f ≺ g = idx f < idx g

      _≼_ : (f g : hom x y) → Type₀
      f ≼ g = idx f ≤ idx g

      ≺-trans : {f g h : hom x y} → f ≺ g → g ≺ h → f ≺ h
      ≺-trans = <-trans

      ≼-trans : {f g h : hom x y} → f ≼ g → g ≼ h → f ≼ h
      ≼-trans {f} {g} {h} u v =
        ≤-trans {idx f} {idx g} {idx h} u v

      ≼-≺-≺ : {f g h : hom x y} → f ≼ g → g ≺ h → f ≺ h
      ≼-≺-≺ = ≤-<-<

      ≼-≺-≼ : {f g h : hom x y} → f ≼ g → g ≺ h → f ≼ h
      ≼-≺-≼ u v = inr (≼-≺-≺ u v)

      =-≼ : {f g : hom x y} → f == g → f ≼ g
      =-≼ p = inl (ap idx p)

      ≺-≼ : {f g : hom x y} → f ≺ g → f ≼ g
      ≺-≼ w = inr w

      ¬≺-self : (f : hom x y) → ¬ (f ≺ f)
      ¬≺-self f = ¬<-self

      abstract
        ≺-trichotomy : (f g : hom x y) → (f == g) ⊔ (f ≺ g) ⊔ (g ≺ f)
        ≺-trichotomy f g = ⊔-rec
          (inl ∘ idx=-hom=)
          (λ{ (inl u) → inr $ inl u
            ; (inr u) → inr $ inr u })
          $ ℕ-trichotomy (idx f) (idx g)

      ≺-dichot : (f g : hom x y) → (f ≺ g) ⊔ (g ≼ f)
      ≺-dichot f g = ⊔-rec
        (λ{ idp → inr (=-≼ idp) })
        (λ{ (inl u) → inl u ; (inr u) → inr (inr u) })
        $ ≺-trichotomy f g

      ≺-contrapos : (f' g' f g : hom x y) → (g ≼ f → g' ≼ f') → f' ≺ g' → f ≺ g
      ≺-contrapos f' g' f g w f'≺g' = ⊔-rec
        (idf _)
        (λ g≼f → ⊥-rec $ ¬≺-self _ $ ≼-≺-≺ (w g≼f) f'≺g')
        $ ≺-dichot f g

      module _ (u : O < hom-size x y) where
        [O]-min : (f : hom x y) → #[ O ] x y u ≼ f
        [O]-min f = transp (_≤ (idx f)) (! $ idx-hom# _) (O≤ _)

        ≼[O]-=[O] : (f : hom x y) → f ≼ #[ O ] x y u → f == #[ O ] x y u
        ≼[O]-=[O] f (inl p) = idx=-hom= p
        ≼[O]-=[O] f (inr v) = ⊥-rec $ ≮O _
          (transp (idx f <_) (idx-hom# _) v)

      #[_]≺S :
        (t : ℕ) (u : t < hom-size x y) (v : 1+ t < hom-size x y)
        → #[ t ] x y u ≺ #[ 1+ t ] x y v
      #[ t ]≺S u v rewrite idx-hom# t {u} | idx-hom# (1+ t) {v} = ltS

      ≺#S-≼# :
        (f : hom x y) (i : ℕ)
        {u : i < hom-size x y} {v : 1+ i < hom-size x y}
        → f ≺ #[ 1+ i ] x y v → f ≼ #[ i ] x y u
      ≺#S-≼# f i {u} {v} w = transp! (idx f ≤_) (idx-hom# _) w'
        where
        w' : idx f ≤ i
        w' = <S-≤ $ transp (idx f <_) (idx-hom# _) w

      #≼#-idx≤ : ∀ {t t'} {u u'} → #[ t ] x y u ≼ #[ t' ] x y u' → t ≤ t'
      #≼#-idx≤ w = w ◂$ transp (_≤ _) (idx-hom# _) ◂$ transp (_ ≤_) (idx-hom# _)

  open hom-order public

  private
    module decidability where
      -- _≟Fin_, not the library's abstract _≟-Fin_: see hott.Fin.
      _≟-hom_ : ∀ {x y} → has-dec-eq (hom x y)
      f ≟-hom g = if (idx' f ≟Fin idx' g)
                    (λ  p → inl (idx=-hom= (ap to-ℕ p)))
                    (λ ¬p → inr (¬p ∘ ap idx'))

      Σ-hom? : ∀ {ℓ} {x y} (P : hom x y → Type ℓ)
               → ((f : hom x y) → Dec (P f))
               → Dec (Σ[ f ﹕ hom x y ] (P f))
      Σ-hom? {ℓ} {x} {y} P u =
        if dec-Fin
          (λ  w → inl (<– e (fst w) , snd w))
          (λ ¬w → inr (λ{ (f , p) → ¬w (–> e f , transp P (! (<–-inv-l e f)) p) }))
          where
          n = hom-size x y
          e = hom-equiv x y

          u' : (i : Fin n) → Dec (P (<– e i))
          u' = bwd-transp-Π-dom e u

          dec-Fin : Dec (Σ[ i ﹕ Fin n ] P (<– e i))
          dec-Fin = Σ-Fin? (P ∘ (<– e)) u'

      _≺?_ : ∀ {x y} → Decidable $ _≺_ {x} {y}
      f ≺? g = (idx f) <? (idx g)

      _≼?_ : ∀ {x y} → Decidable $ _≼_ {x} {y}
      f ≼? g = (idx f) ≤? (idx g)

  open decidability

  private
    module division where
      module _ {x y z} (f : hom x y) where
        _∣_ : hom x z → Type ℓₘ
        _∣_ h = Σ[ g ﹕ hom y z ] g ◦ f == h

        _∣?_ : (h : hom x z) → Dec (_∣_ h)
        _∣?_ h = Σ-hom? (λ g → g ◦ f == h) (λ g → g ◦ f ≟-hom h)

        ∣-of-equals : (h h' : hom x z) → h == h' → _∣_ h → _∣_ h'
        ∣-of-equals h h' idp w = w

        ∣◦ : (g : hom y z) → _∣_ (g ◦ f)
        ∣◦ g = g , idp

      ∣#[]= :
        ∀ {x y z} {f : hom x y} {t} {u u'}
        → f ∣ #[ t ] x z u
        → f ∣ #[ t ] x z u'
      ∣#[]= = ∣-of-equals _ _ _ #[]=

      ∣◦hom#-idx :
        ∀ {x y z} (f : hom x y) (g : hom y z)
        → {u : idx (g ◦ f) < hom-size x z}
        → f ∣ #[ idx (g ◦ f) ] x z u
      ∣◦hom#-idx f g = ∣◦ f g ◂$ transp (f ∣_) (! (hom#-idx _))

  open division public

  private
    module hom-lemmas where
      hom[_,_]-inhab : ∀ x y → hom x y → O < hom-size x y
      hom[ x , y ]-inhab f = ≤-<-< (O≤ _) (idx<hom-size f)

      hom-is-set : ∀ {x y} → is-set (hom x y)
      hom-is-set {x} {y} = equiv-preserves-level e' ⦃ Lift-level Fin-is-set ⦄
                             where
                             n = hom-size x y
                             e = hom-equiv x y
                             e' : Lift {j = ℓₘ} (Fin n) ≃ hom x y
                             e' = (lift-equiv ∘e e)⁻¹

  open hom-lemmas public

  {- Unused for now; was meant to be a more "semantic" way of implementing
  -- cosieve restriction for the internal inverse diagram construction.
  private
    module counting where
      -- The number of (g : hom x y) satisfying f ≼ g and (P g)
      #-hom[_,_]-from_st :
        ∀ {ℓ} x y
        → (f : hom x y)
        → (P : hom x y → Type ℓ)
        → ((f : hom x y) → Dec (P f))
        → ℕ
      #-hom[ x , y ]-from f st P P? =
        #-Fin n from (idx-of f) to n , lteE and idx<hom-size f
          st (P ∘ hom[ x , y ]#) (P? ∘ hom[ x , y ]#)
        where n = hom-size x y

      #-hom-ub :
        ∀ {ℓ} x y (f : hom x y)
          (P : hom x y → Type ℓ) (P? : (f : hom x y) → Dec (P f))
        → #-hom[ x , y ]-from f st P P? ≤ hom-size x y
      #-hom-ub x y f P P? =
        #-Fin-coarse-ub n (idx-of f) n lteE (idx<hom-size f) _ _
        where n = hom-size x y

      -- Counting factors
      #-factors :
        ∀ {i h m} (t : Fin (hom-size i h)) (f : hom i m)
        → O < hom-size m h
        → Σ[ n ﹕ ℕ ] n ≤ hom-size m h
      #-factors{i} {h} {m} t f u =
        #-hom[ m , h ]-from [O] st (λ α → α ◦ f ≼ [t]) (λ α → α ◦ f ≼? [t]) ,
        #-hom-ub m h [O] (λ α → α ◦ f ≼ [t]) (λ α → α ◦ f ≼? [t])
        where
          [O] = hom[ m , h ]# (O , u)
          [t] = hom[ i , h ]# t

      #-factors-of-hom[_,_]≤[_]-through :
        ∀ i h {m} (t : Fin (hom-size i h)) (f : hom i m)
        → O < hom-size m h
        → ℕ
      #-factors-of-hom[_,_]≤[_]-through i h {m} t f u =
        fst (#-factors {i} {h} {m} t f u)

      #-factors-ub :
        ∀ {i h m} t (f : hom i m) (u : O < hom-size m h)
        → #-factors-of-hom[ i , h ]≤[ t ]-through f u ≤ hom-size m h
      #-factors-ub t f u = snd (#-factors t f u)
  -}
