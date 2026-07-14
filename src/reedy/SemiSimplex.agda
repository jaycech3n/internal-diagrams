{-# OPTIONS --without-K --rewriting #-}

{- The opposite semisimplex category Δ₊ᵒᵖ as a SimpleSemicategory.

One definition of Δ₊ was suggested in the PhD thesis of Nicolai Kraus, cf
  https://nicolaikraus.github.io/docs/thesisagda_nicolai/Deltaplus.html
This file follows that suggestion. In fact, the definition of Δ₊ is quite
short; most of this file is about putting it into the correct framework.
-}

module reedy.SemiSimplex where

open import reedy.SimpleSemicategories

-- Strictly increasing maps between standard finite sets

is-increasing : {m n : ℕ} → (Fin m → Fin n) → Type₀
is-increasing {m} f = (s t : Fin m) → to-ℕ s < to-ℕ t → to-ℕ (f s) < to-ℕ (f t)

is-increasing-is-prop :
  {m n : ℕ} {f : Fin m → Fin n} → is-prop (is-increasing f)
is-increasing-is-prop =
  Π-level (λ s → Π-level (λ t → Π-level (λ u → <-is-prop)))

SIncMap : ℕ → ℕ → Type₀
SIncMap m n = Σ (Fin m → Fin n) is-increasing

-- Equality of increasing maps is equality of the underlying functions.
SIncMap= :
  {m n : ℕ} {F G : SIncMap m n}
  → ((i : Fin m) → fst F i == fst G i)
  → F == G
SIncMap= {m} {n} {F} {G} h =
  pair= (λ= h) (prop-has-all-paths-↓ ⦃ is-increasing-is-prop {m} {n} {fst G} ⦄)

-- The category Δ₊ᵒᵖ: hom-sets, composition, associativity

ΔHom : ℕ → ℕ → Type₀
ΔHom i j = (j < i) × SIncMap (1+ j) (1+ i)

Δ∘ : {x y z : ℕ} → ΔHom y z → ΔHom x y → ΔHom x z
Δ∘ (w , (G , incG)) (v , (F , incF)) =
  <-trans w v , ((F ∘ G) , (λ s t u → incF _ _ (incG s t u)))

-- Associativity is judgmental on the function part; the only work is the
-- proof-irrelevant `j < i` and increasing-witness components.
Δ∘-ass : {x y z w : ℕ} (f : ΔHom z w) (g : ΔHom y z) (h : ΔHom x y)
  → Δ∘ (Δ∘ f g) h == Δ∘ f (Δ∘ g h)
Δ∘-ass {x} {y} {z} {w} (a , (F , iF)) (b , (G , iG)) (c , (H , iH)) =
  pair×= (<= _ _)
    (pair= idp (prop-path (is-increasing-is-prop {1+ w} {1+ x} {H ∘ G ∘ F}) _ _))

Δ-wildsemicatstr : WildSemicategoryStructure lzero lzero ℕ
Δ-wildsemicatstr = record
  { hom = ΔHom
  ; _◦_ = Δ∘
  ; ass = λ {x} {y} {z} {w} {f} {g} {h} → Δ∘-ass f g h }

-- deg = idf ℕ; the bundled proof j < i is exactly the inverse-category datum.
Δ-inversestr : InverseWildSemicategoryStructure (idf ℕ) Δ-wildsemicatstr
Δ-inversestr = record { hom-inverse = λ x y → fst }

-- Binomial coefficients and coproducts of finite sets

binom : ℕ → ℕ → ℕ
binom n O = 1
binom O (1+ m) = O
binom (1+ n) (1+ m) = binom n (1+ m) + binom n m

⊔-emap : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄}
  → A ≃ C → B ≃ D → (A ⊔ B) ≃ (C ⊔ D)
⊔-emap u v = equiv (⊔-fmap (–> u) (–> v)) (⊔-fmap (<– u) (<– v)) to-from from-to
  where
  to-from : ∀ x → ⊔-fmap (–> u) (–> v) (⊔-fmap (<– u) (<– v) x) == x
  to-from (inl c) = ap inl (<–-inv-r u c)
  to-from (inr d) = ap inr (<–-inv-r v d)
  from-to : ∀ x → ⊔-fmap (<– u) (<– v) (⊔-fmap (–> u) (–> v) x) == x
  from-to (inl a) = ap inl (<–-inv-l u a)
  from-to (inr b) = ap inr (<–-inv-l v b)

≤-+-add-r : (a b : ℕ) → a ≤ a + b
≤-+-add-r O b = O≤ b
≤-+-add-r (1+ a) b = ≤-ap-S (≤-+-add-r a b)

-- Fin a ⊔ Fin b ≃ Fin (a + b), with the left summand at the LOWER indices:
-- index of (inl k) is k, index of (inr k) is a + k.
finsum-to : {a b : ℕ} → Fin a ⊔ Fin b → Fin (a + b)
finsum-to {a} {b} (inl (k , u)) = k , <-≤-< u (≤-+-add-r a b)
finsum-to {a} {b} (inr (k , u)) = a + k , <-+-l a u

finsum-shift : {a b : ℕ} → Fin a ⊔ Fin b → Fin (1+ a) ⊔ Fin b
finsum-shift (inl (k , v)) = inl (1+ k , <-ap-S v)
finsum-shift (inr x) = inr x

finsum-from : (a : ℕ) {b : ℕ} → Fin (a + b) → Fin a ⊔ Fin b
finsum-from O c = inr c
finsum-from (1+ a) (O , u) = inl (O , O<S a)
finsum-from (1+ a) (1+ c , u) = finsum-shift (finsum-from a (c , <-cancel-S u))

finsum-to-from : (a : ℕ) {b : ℕ} (c : Fin (a + b))
  → finsum-to (finsum-from a c) == c
finsum-to-from O c = Fin= idp
finsum-to-from (1+ a) (O , u) = Fin= idp
finsum-to-from (1+ a) {b} (1+ c , u)
  with finsum-from a {b} (c , <-cancel-S u) | finsum-to-from a {b} (c , <-cancel-S u)
... | inl (k , v) | ih = Fin= (ap S (Fin=-elim ih))
... | inr (k , v) | ih = Fin= (ap S (Fin=-elim ih))

finsum-from-to : (a : ℕ) {b : ℕ} (x : Fin a ⊔ Fin b)
  → finsum-from a (finsum-to x) == x
finsum-from-to O (inl (k , u)) = ⊥-rec (≮O _ u)
finsum-from-to O (inr (k , u)) = ap inr (Fin= idp)
finsum-from-to (1+ a) (inl (O , u)) = ap inl (Fin= idp)
finsum-from-to (1+ a) {b} (inl (1+ k , u)) =
  ap (λ z → finsum-shift (finsum-from a {b} z)) (Fin= idp)
  ∙ ap finsum-shift (finsum-from-to a (inl (k , <-cancel-S u)))
  ∙ ap inl (Fin= idp)
finsum-from-to (1+ a) {b} (inr (k , u)) =
  ap (λ z → finsum-shift (finsum-from a {b} z)) (Fin= idp)
  ∙ ap finsum-shift (finsum-from-to a (inr (k , u)))

Fin-⊔ : {a b : ℕ} → (Fin a ⊔ Fin b) ≃ Fin (a + b)
Fin-⊔ {a} {b} = equiv finsum-to (finsum-from a) (finsum-to-from a) (finsum-from-to a)

-- Splitting SIncMap (1+ m) (1+ n) by "does it hit the top value n?"

module _ {m n : ℕ} where

  -- Values of an increasing map are bounded by the value at the top argument.
  val-≤-top : (F : SIncMap (1+ m) (1+ n)) (i : Fin (1+ m))
    → to-ℕ (fst F i) ≤ to-ℕ (fst F (m , ltS))
  val-≤-top (f , inc) i = ⊔-rec
    (λ p → inl (ap (to-ℕ ∘ f) (Fin= p)))
    (λ v → inr (inc i (m , ltS) v))
    (<S-≤ (snd i))

  -- Case A: top value below n; all values fit into Fin n.
  restr-all : (F : SIncMap (1+ m) (1+ n))
    → to-ℕ (fst F (m , ltS)) < n
    → SIncMap (1+ m) n
  restr-all F@(f , inc) u =
    (λ i → to-ℕ (f i) , ≤-<-< (val-≤-top F i) u) , (λ s t w → inc s t w)

  -- Case B: top value exactly n; restrict to the first m arguments.
  restr-init : (F : SIncMap (1+ m) (1+ n))
    → to-ℕ (fst F (m , ltS)) == n
    → SIncMap m n
  restr-init (f , inc) p =
    (λ i → to-ℕ (f (Fin-S i)) ,
           transp (to-ℕ (f (Fin-S i)) <_) p (inc (Fin-S i) (m , ltS) (snd i))) ,
    (λ s t w → inc (Fin-S s) (Fin-S t) w)

  -- Extension of g : Fin m → Fin n to Fin (1+ m) → Fin (1+ n) sending the top
  -- argument to the top value n and keeping the other values.
  ext-fun : (g : Fin m → Fin n) (i : ℕ) → Dec (i < m) → Fin (1+ n)
  ext-fun g i (inl v) = Fin-S (g (i , v))
  ext-fun g i (inr _) = n , ltS

  ext : (g : Fin m → Fin n) → Fin (1+ m) → Fin (1+ n)
  ext g (i , u) = ext-fun g i (i <? m)

  ext-β< : (g : Fin m → Fin n) (i : ℕ) (u : i < 1+ m) (v : i < m)
    → ext g (i , u) == Fin-S (g (i , v))
  ext-β< g i u v with i <? m
  ... | inl v' = ap (λ w → Fin-S (g (i , w))) (<= v' v)
  ... | inr ¬v = ⊥-rec (¬v v)

  ext-βtop : (g : Fin m → Fin n) (i : ℕ) (u : i < 1+ m) (¬v : ¬ (i < m))
    → ext g (i , u) == (n , ltS)
  ext-βtop g i u ¬v with i <? m
  ... | inl v = ⊥-rec (¬v v)
  ... | inr _ = idp

  ext-inc : (g : Fin m → Fin n) → is-increasing g → is-increasing (ext g)
  ext-inc g inc (i , u) (j , w) i<j =
    transp (_< to-ℕ (ext g (j , w))) (! p) lem
    where
    v : i < m
    v = <-≤-< i<j (<S-≤ w)

    p : to-ℕ (ext g (i , u)) == to-ℕ (g (i , v))
    p = ap to-ℕ (ext-β< g i u v)

    lem : to-ℕ (g (i , v)) < to-ℕ (ext g (j , w))
    lem with j <? m
    ... | inl v' = inc (i , v) (j , v') i<j
    ... | inr _ = snd (g (i , v))

  split-to-aux : (F : SIncMap (1+ m) (1+ n)) → Dec (to-ℕ (fst F (m , ltS)) < n)
    → SIncMap (1+ m) n ⊔ SIncMap m n
  split-to-aux F (inl u) = inl (restr-all F u)
  split-to-aux F (inr ¬u) =
    inr (restr-init F (≤-between-= (<S-≤ (snd (fst F (m , ltS)))) (≮-to-≥ ¬u)))

  split-to : SIncMap (1+ m) (1+ n) → SIncMap (1+ m) n ⊔ SIncMap m n
  split-to F = split-to-aux F (to-ℕ (fst F (m , ltS)) <? n)

  split-from : SIncMap (1+ m) n ⊔ SIncMap m n → SIncMap (1+ m) (1+ n)
  split-from (inl (g , inc)) = (Fin-S ∘ g) , (λ s t w → inc s t w)
  split-from (inr (g , inc)) = ext g , ext-inc g inc

  split-to-from : (x : SIncMap (1+ m) n ⊔ SIncMap m n)
    → split-to (split-from x) == x
  split-to-from (inl (g , inc)) with to-ℕ (g (m , ltS)) <? n
  ... | inl u = ap inl (SIncMap= (λ i → Fin= idp))
  ... | inr ¬u = ⊥-rec (¬u (snd (g (m , ltS))))
  split-to-from (inr (g , inc)) with to-ℕ (ext g (m , ltS)) <? n
  ... | inl u =
    ⊥-rec (¬<-self (transp (_< n) (ap to-ℕ (ext-βtop g m ltS ¬<-self)) u))
  ... | inr ¬u =
    ap inr (SIncMap=
      (λ i → Fin= (ap to-ℕ (ext-β< g (to-ℕ i) (ltSR (snd i)) (snd i)))))

  split-from-to : (F : SIncMap (1+ m) (1+ n)) → split-from (split-to F) == F
  split-from-to F@(f , inc) with to-ℕ (f (m , ltS)) <? n
  ... | inl u = SIncMap= (λ i → Fin= idp)
  ... | inr ¬u = SIncMap= exteq
    where
    p : to-ℕ (f (m , ltS)) == n
    p = ≤-between-= (<S-≤ (snd (f (m , ltS)))) (≮-to-≥ ¬u)

    g' : Fin m → Fin n
    g' = fst (restr-init F p)

    exteq : (iw : Fin (1+ m)) → ext g' iw == f iw
    exteq (i , w) = ⊔-rec case= case< (<S-≤ w)
      where
      case= : i == m → ext g' (i , w) == f (i , w)
      case= q = ext-βtop g' i w (λ v → ¬<-self (transp (_< m) q v))
                ∙ Fin= (! (ap (to-ℕ ∘ f) (Fin= q) ∙ p))
      case< : i < m → ext g' (i , w) == f (i , w)
      case< v = ext-β< g' i w v ∙ Fin= (ap (to-ℕ ∘ f) (Fin= idp))

  split-≃ : SIncMap (1+ m) (1+ n) ≃ (SIncMap (1+ m) n ⊔ SIncMap m n)
  split-≃ = equiv split-to split-from split-to-from split-from-to

-- SIncMap m n ≃ Fin (binom n m)

-- The empty increasing map.
sinc-O : (n : ℕ) → SIncMap O n
sinc-O n = (λ i → ⊥-rec (≮O _ (snd i))) , (λ s t _ → ⊥-rec (≮O _ (snd s)))

SIncMap-equiv : (m n : ℕ) → SIncMap m n ≃ Fin (binom n m)
SIncMap-equiv O n = equiv (λ _ → O , ltS) (λ _ → sinc-O n)
  (λ i → Fin1-has-all-paths _ i)
  (λ F → SIncMap= (λ i → ⊥-rec (≮O _ (snd i))))
SIncMap-equiv (1+ m) O = equiv
  (λ F → ⊥-rec (≮O _ (snd (fst F (O , O<S m)))))
  (λ i → ⊥-rec (≮O _ (snd i)))
  (λ i → ⊥-rec (≮O _ (snd i)))
  (λ F → ⊥-rec (≮O _ (snd (fst F (O , O<S m)))))
SIncMap-equiv (1+ m) (1+ n) =
  Fin-⊔ ∘e ⊔-emap (SIncMap-equiv (1+ m) n) (SIncMap-equiv m n) ∘e split-≃

-- hom-finite and the SimpleSemicategory instance Δop

ΔHom-equiv-aux : (i j : ℕ) → Dec (j < i) → Σ ℕ (λ s → ΔHom i j ≃ Fin s)
ΔHom-equiv-aux i j (inl u) =
  binom (1+ i) (1+ j) ,
  SIncMap-equiv (1+ j) (1+ i) ∘e
    equiv snd (λ F → u , F) (λ F → idp) (λ { (v , F) → pair×= (<= u v) idp })
ΔHom-equiv-aux i j (inr ¬u) =
  O , equiv (λ h → ⊥-rec (¬u (fst h))) (λ i' → ⊥-rec (≮O _ (snd i')))
        (λ i' → ⊥-rec (≮O _ (snd i'))) (λ h → ⊥-rec (¬u (fst h)))

ΔHom-finite : (i j : ℕ) → Σ ℕ (λ s → ΔHom i j ≃ Fin s)
ΔHom-finite i j = ΔHom-equiv-aux i j (j <? i)

Δ-locfinstr : LocallyFiniteSemicategoryStructure Δ-wildsemicatstr
Δ-locfinstr = record { hom-finite = ΔHom-finite }

Δop : SimpleSemicategory lzero
Δop = record
  { wildsemicatstr = Δ-wildsemicatstr
  ; inversestr = Δ-inversestr
  ; locfinstr = Δ-locfinstr }

{- Colexicographic order and monotonicity of the enumeration

   The interface defines g ≺ h on a hom-set as idx g < idx h, where idx is the
   position under ΔHom-finite. For Δop that enumeration is colexicographic, so
   we relate ≺ to the colex order and show precomposition preserves the latter. -}

-- f <colex g iff f and g agree above some index i where f i < g i.
_<colex_ : {m n : ℕ} (f g : Fin m → Fin n) → Type₀
_<colex_ {m} f g =
  Σ (Fin m) (λ i →
    (to-ℕ (f i) < to-ℕ (g i)) × ((j : Fin m) → to-ℕ i < to-ℕ j → f j == g j))

-- Postcomposition with an increasing map strictly preserves colex.
postcomp-colex : {n l : ℕ} (φ : Fin n → Fin l) → is-increasing φ
  → {m : ℕ} {f g : Fin m → Fin n}
  → f <colex g → (φ ∘ f) <colex (φ ∘ g)
postcomp-colex φ incφ {f = f} {g} (i , u , eqs) =
  i , incφ (f i) (g i) u , (λ j w → ap φ (eqs j w))

-- Colex trichotomy for arbitrary functions Fin m → Fin n.
colex-tri : {m n : ℕ} (f g : Fin m → Fin n)
  → ((i : Fin m) → f i == g i) ⊔ ((f <colex g) ⊔ (g <colex f))
colex-tri {O} f g = inl (λ i → ⊥-rec (≮O _ (snd i)))
colex-tri {1+ m} {n} f g =
  ⊔-rec case=
    (⊔-rec (λ u → inr (inl (top-wit f g u))) (λ u → inr (inr (top-wit g f u))))
    (ℕ-trichotomy (to-ℕ (f top)) (to-ℕ (g top)))
  where
  top : Fin (1+ m)
  top = m , ltS

  -- If the top values are strictly comparable, the top is a colex witness.
  top-wit : (f' g' : Fin (1+ m) → Fin n)
    → to-ℕ (f' top) < to-ℕ (g' top) → f' <colex g'
  top-wit f' g' u = top , u , (λ j w → ⊥-rec (no-between w (snd j)))

  -- If the top values agree, a colex witness for the restrictions lifts.
  lift-wit : (f' g' : Fin (1+ m) → Fin n)
    → to-ℕ (f' top) == to-ℕ (g' top)
    → (f' ∘ Fin-S) <colex (g' ∘ Fin-S)
    → f' <colex g'
  lift-wit f' g' p' (i , u , eqs) = Fin-S i , u , eqs'
    where
    eqs' : (j : Fin (1+ m)) → to-ℕ (Fin-S i) < to-ℕ j → f' j == g' j
    eqs' (j₀ , w) v = ⊔-rec
      (λ q → ap f' (Fin= {i = j₀ , w} {j = top} q)
             ∙ Fin= {i = f' top} {j = g' top} p'
             ∙ ! (ap g' (Fin= {i = j₀ , w} {j = top} q)))
      (λ v' → ap f' (Fin= {i = j₀ , w} {j = Fin-S (j₀ , v')} idp)
              ∙ eqs (j₀ , v') v
              ∙ ! (ap g' (Fin= {i = j₀ , w} {j = Fin-S (j₀ , v')} idp)))
      (<S-≤ w)

  case= : to-ℕ (f top) == to-ℕ (g top)
    → ((i : Fin (1+ m)) → f i == g i) ⊔ ((f <colex g) ⊔ (g <colex f))
  case= p = ⊔-rec
    (λ h → inl (glue h))
    (⊔-rec (λ c → inr (inl (lift-wit f g p c)))
           (λ c → inr (inr (lift-wit g f (! p) c))))
    (colex-tri (f ∘ Fin-S) (g ∘ Fin-S))
    where
    glue : ((j : Fin m) → f (Fin-S j) == g (Fin-S j))
      → (j : Fin (1+ m)) → f j == g j
    glue h (j₀ , w) = ⊔-rec
      (λ q → ap f (Fin= {i = j₀ , w} {j = top} q)
             ∙ Fin= {i = f top} {j = g top} p
             ∙ ! (ap g (Fin= {i = j₀ , w} {j = top} q)))
      (λ v → ap f (Fin= {i = j₀ , w} {j = Fin-S (j₀ , v)} idp)
             ∙ h (j₀ , v)
             ∙ ! (ap g (Fin= {i = j₀ , w} {j = Fin-S (j₀ , v)} idp)))
      (<S-≤ w)

-- The enumeration SIncMap-equiv is strictly monotone from colex to <.
idx-mono : (m n : ℕ) (F G : SIncMap m n)
  → fst F <colex fst G
  → to-ℕ (–> (SIncMap-equiv m n) F) < to-ℕ (–> (SIncMap-equiv m n) G)
idx-mono O n F G (i , _) = ⊥-rec (≮O _ (snd i))
idx-mono (1+ m) O F G _ = ⊥-rec (≮O _ (snd (fst F (O , O<S m))))
idx-mono (1+ m) (1+ n) F@(f , incf) G@(g , incg) (i , u , eqs)
  with to-ℕ (f (m , ltS)) <? n | to-ℕ (g (m , ltS)) <? n
... | inl uF | inl uG =
  idx-mono (1+ m) n (restr-all F uF) (restr-all G uG)
    (i , u , (λ j w → Fin= (ap to-ℕ (eqs j w))))
... | inl uF | inr ¬uG =
  <-≤-< (snd x) (≤-+-add-r (binom n (1+ m)) (to-ℕ y))
  where
  x = –> (SIncMap-equiv (1+ m) n) (restr-all (f , incf) uF)
  y = –> (SIncMap-equiv m n)
        (restr-init (g , incg)
          (≤-between-= (<S-≤ (snd (g (m , ltS)))) (≮-to-≥ ¬uG)))
... | inr ¬uF | inl uG = ⊥-rec (⊔-rec case-top case-below (<S-≤ (snd i)))
  where
  -- f hits the top value n but g does not: colex f g is contradictory.
  case-top : to-ℕ i == m → ⊥
  case-top q = ¬uF (<-trans u'' uG)
    where
    u' : to-ℕ (f (m , ltS)) < to-ℕ (g i)
    u' = transp (_< to-ℕ (g i)) (ap (to-ℕ ∘ f) (Fin= {i = i} {j = m , ltS} q)) u
    u'' : to-ℕ (f (m , ltS)) < to-ℕ (g (m , ltS))
    u'' = transp (to-ℕ (f (m , ltS)) <_)
                 (ap (to-ℕ ∘ g) (Fin= {i = i} {j = m , ltS} q)) u'
  case-below : to-ℕ i < m → ⊥
  case-below v = ¬uF (transp (_< n) (! (ap to-ℕ e)) uG)
    where
    e : f (m , ltS) == g (m , ltS)
    e = eqs (m , ltS) v
... | inr ¬uF | inr ¬uG =
  <-+-l (binom n (1+ m))
    (idx-mono m n (restr-init (f , incf) pF) (restr-init (g , incg) pG) c')
  where
  pF : to-ℕ (f (m , ltS)) == n
  pF = ≤-between-= (<S-≤ (snd (f (m , ltS)))) (≮-to-≥ ¬uF)
  pG : to-ℕ (g (m , ltS)) == n
  pG = ≤-between-= (<S-≤ (snd (g (m , ltS)))) (≮-to-≥ ¬uG)

  -- The colex witness cannot be the top argument, since f and g both take
  -- the value n there.
  wit-below : to-ℕ i < m
  wit-below = ⊔-rec
    (λ q → ⊥-rec (¬<-self (nn q)))
    (idf _)
    (<S-≤ (snd i))
    where
    module _ (q : to-ℕ i == m) where
      u' : to-ℕ (f (m , ltS)) < to-ℕ (g i)
      u' = transp (_< to-ℕ (g i)) (ap (to-ℕ ∘ f) (Fin= {i = i} {j = m , ltS} q)) u
      u'' : to-ℕ (f (m , ltS)) < to-ℕ (g (m , ltS))
      u'' = transp (to-ℕ (f (m , ltS)) <_)
                   (ap (to-ℕ ∘ g) (Fin= {i = i} {j = m , ltS} q)) u'
      nn : n < n
      nn = transp (n <_) pG (transp (_< to-ℕ (g (m , ltS))) pF u'')

  c' : fst (restr-init (f , incf) pF) <colex fst (restr-init (g , incg) pG)
  c' = (to-ℕ i , wit-below) ,
       transp (λ z → to-ℕ (f z) < to-ℕ (g z))
              (Fin= {i = i} {j = Fin-S (to-ℕ i , wit-below)} idp) u ,
       (λ j wj → Fin= (ap to-ℕ (eqs (Fin-S j) wj)))

-- Converse of idx-mono, via colex trichotomy.
colex-of-idx< : (m n : ℕ) (F G : SIncMap m n)
  → to-ℕ (–> (SIncMap-equiv m n) F) < to-ℕ (–> (SIncMap-equiv m n) G)
  → fst F <colex fst G
colex-of-idx< m n F G u = ⊔-rec
  (λ h → ⊥-rec (¬<-self
    (transp (λ z → to-ℕ (–> (SIncMap-equiv m n) z)
                   < to-ℕ (–> (SIncMap-equiv m n) G))
            (SIncMap= {m} {n} {F} {G} h) u)))
  (⊔-rec (idf _)
         (λ c → ⊥-rec (¬<-self (<-trans u (idx-mono m n G F c)))))
  (colex-tri (fst F) (fst G))

-- Strict orientation

-- The transparent index of a morphism under ΔHom-finite.
Δidx : {x y : ℕ} → ΔHom x y → ℕ
Δidx {x} {y} f = to-ℕ (–> (snd (ΔHom-finite x y)) f)

-- Precomposition is strictly monotone for the colex-induced order: idx< is
-- pulled back to colex, transported along f, and pushed forward to idx<.
Δ-oriented-core : {x y z : ℕ} (f : ΔHom x y) (g h : ΔHom y z)
  → Δidx g < Δidx h → Δidx (Δ∘ g f) < Δidx (Δ∘ h f)
Δ-oriented-core {x} {y} {z} f g h with z <? y | z <? x
... | inl uy | inl ux = λ u →
  idx-mono (1+ z) (1+ x) (snd (Δ∘ g f)) (snd (Δ∘ h f))
    (postcomp-colex (fst (snd f)) (snd (snd f))
      (colex-of-idx< (1+ z) (1+ y) (snd g) (snd h) u))
... | inl uy | inr ¬ux = λ _ → ⊥-rec (¬ux (<-trans (fst g) (fst f)))
... | inr ¬uy | _ = λ _ → ⊥-rec (¬uy (fst g))

module StrictOrientation
  (idx-def : (x y : ℕ) (f : SimpleSemicategory.hom Δop x y)
    → SimpleSemicategory.idx Δop f == Δidx f)
  where

  private module C = SimpleSemicategory Δop

  Δop-is-strictly-oriented : is-strictly-oriented Δop
  Δop-is-strictly-oriented {x} {y} f {z} g h u =
    transp! (_< C.idx (h C.◦ f)) (idx-def x z (Δ∘ g f))
      (transp! (Δidx (Δ∘ g f) <_) (idx-def x z (Δ∘ h f))
        (Δ-oriented-core f g h
          (transp (Δidx g <_) (idx-def y z h)
            (transp (_< C.idx h) (idx-def y z g) u))))

Δop-strictly-oriented : is-strictly-oriented Δop
Δop-strictly-oriented =
  StrictOrientation.Δop-is-strictly-oriented
    (λ x y f → SimpleSemicategory.idx'-def Δop f)
