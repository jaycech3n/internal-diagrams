{-# OPTIONS --without-K --rewriting #-}

module hott.Fin where

open import hott.Base public
open import hott.Conditionals public
open import hott.Decidable public
open import hott.Nat public
open import hott.Sigma public

to-ℕ : ∀ {n} → Fin n → ℕ
to-ℕ = fst

1+Fin : ∀ {n} ((m , _) : Fin n) → 1+ m < n → Fin n
1+Fin (m , _) h = 1+ m , h

module Fin-equality where
  Fin= : ∀ {n} {i j : Fin n} → to-ℕ i == to-ℕ j → i == j
  Fin= {_} {.(fst j) , fstj<n} {j} idp = pair= idp (prop-path <-is-prop _ _)

  Fin=-is-prop : ∀ {n} {i j : Fin n} → is-prop (i == j)
  Fin=-is-prop {_} {i} {j} = has-level-apply Fin-is-set i j

  Fin1-is-prop : is-prop (Fin 1)
  has-level-apply Fin1-is-prop (i , i<1) (j , j<1) =
    has-level-in (Fin= (<1-=O i<1 ∙ ! (<1-=O j<1)) , λ p → prop-path Fin=-is-prop _ _)

  Fin1-has-all-paths : has-all-paths (Fin 1)
  Fin1-has-all-paths i j = prop-path Fin1-is-prop _ _

  Fin=-elim : ∀ {n} {i j : Fin n} → i == j → fst i == fst j
  Fin=-elim {n} {_ , _} {.(_ , _)} idp = idp

open Fin-equality public

{- Transparent decidable equality for ℕ and Fin.

The library's ℕ-has-dec-eq and Fin-has-dec-eq (hence the _≟-ℕ_ / _≟-Fin_ of
hott.Base) sit inside `abstract` blocks, so they never reduce.
Here, we want something that computes: _∣?_ (divisibility of morphisms) is
built from Fin-equality, so with the library versions `count-factors i h t s f`
never reduces to a numeral, and the whole diagram construction is stuck at
height ≥ 1 no matter how strict the ambient cwf is.

These copies are definitionally the same functions of the library functions,
just not abstract.  Only the `inl`/`inr` head matters for reduction; the ≠-proofs
in the negative branches may stay opaque, which is harmless. -}
module Fin-dec-eq-transparent where
  infix 40 _≟ℕ_ _≟Fin_

  _≟ℕ_ : has-dec-eq ℕ
  O ≟ℕ O = inl idp
  O ≟ℕ (1+ n) = inr (ℕ-O≠S n)
  (1+ n) ≟ℕ O = inr (ℕ-S≠O n)
  (1+ n) ≟ℕ (1+ m) =
    if (n ≟ℕ m) (λ p → inl (ap 1+ p)) (λ ¬p → inr (¬p ∘ ℕ-S-is-inj n m))

  _≟Fin_ : ∀ {n} → has-dec-eq (Fin n)
  i ≟Fin j =
    if (to-ℕ i ≟ℕ to-ℕ j) (λ p → inl (Fin= p)) (λ ¬p → inr (¬p ∘ Fin=-elim))

open Fin-dec-eq-transparent public

module Fin-yoga {ℓ₁ ℓ₂} where
  {- Given a predicate P : Fin (1+ n) → Type and i < n for some n, sometimes we
  want to show that P holds for i by showing that P ∘ Fin-S holds for i : Fin n,
  and then lifting that witness back to Fin (1+ n).

  More generally, sometimes we have a higher-order predicate
    B : (n : ℕ) (P : (Fin n → Type) → Fin n → Type
  and want to lift a proof of
    B n (P ∘ Fin-S) i
  to one of
    B (1+ n) P (Fin-S i).
  -}

  module _
    (B : (n : ℕ) (P : (Fin n) → Type ℓ₁) → Fin n → Type ℓ₂)
    (n : ℕ)
    (P : Fin (1+ n) → Type ℓ₁)
    where
    Σ-Fin-S :
      (∀ i → B n (P ∘ Fin-S) i → B (1+ n) P (Fin-S i))
      → Σ (Fin n) (B n (P ∘ Fin-S))
      → Σ (Fin (1+ n)) (B (1+ n) P)
    Σ-Fin-S f (i , b) = Fin-S i , f i b

open Fin-yoga public

module Fin-predicates where
  _restricted-to_ : ∀ {ℓ} {n} (P : Fin n → Type ℓ) (i : Fin n)
    → Fin (to-ℕ i) → Type ℓ
  P restricted-to (_ , ltS) = P ∘ Fin-S
  P restricted-to (i , ltSR u) = P ∘ Fin-S restricted-to (i , u)

  ∀-Fin-extend :
    ∀ {ℓ} {n} {P : Fin (1+ n) → Type ℓ}
    → ((i : Fin n) → P (Fin-S i))
    → P (n , ltS)
    → ∀ i → P i
  ∀-Fin-extend {n = O} {P} _ PO _ = transp P (Fin1-has-all-paths _ _) PO
  ∀-Fin-extend {n = 1+ n} {P} f PSn (i , i<) =
     case (<S-≤ i<)
       (λ{ idp → transp P (Fin= idp) PSn })
       (λ i<Sn → transp P (Fin= idp) (f (i , i<Sn)))

open Fin-predicates public

module Fin-< {n : ℕ} where
  _<-Fin_ : (i j : Fin n) → Type₀
  i <-Fin j = to-ℕ i < to-ℕ j

  _≤-Fin_ : (i j : Fin n) → Type₀
  i ≤-Fin j = to-ℕ i ≤ to-ℕ j

  _<?-Fin_ : Decidable (_<-Fin_)
  (i , _) <?-Fin (j , _) = i <? j

  _≤?-Fin_ : Decidable (_≤-Fin_)
  (i , _) ≤?-Fin (j , _) = i ≤? j

  ≤-Fin-trans : {i j k : Fin n} → i ≤-Fin j → j ≤-Fin k → i ≤-Fin k
  ≤-Fin-trans (inl idp) (inl idp) = inl idp
  ≤-Fin-trans (inr u) (inl idp) = inr u
  ≤-Fin-trans (inl idp) (inr v) = inr v
  ≤-Fin-trans (inr u) (inr v) = inr (<-trans u v)

  ≰-to>-Fin : (i j : Fin n) → ¬ (i ≤-Fin j) → j <-Fin i
  ≰-to>-Fin i j = ≰-to-> {to-ℕ i} {to-ℕ j}

  ¬≤> : (i j : Fin n) → (i ≤-Fin j) → (j <-Fin i) → ⊥
  ¬≤> i j (inl idp) j<i = ¬<-self j<i
  ¬≤> i j (inr i<j) j<i = ¬<-self (<-trans i<j j<i)

open Fin-< public

abstract
  Fin-trichotomy : ∀ {k} (i j : Fin k) → (i == j) ⊔ (i <-Fin j) ⊔ (j <-Fin i)
  Fin-trichotomy (m , m<k) (n , n<k) = Fin-trichotomy-aux m n m<k n<k
    where
    Fin-trichotomy-aux :
      ∀ {k} (m n : ℕ) (m<k : m < k) (n<k : n < k)
      → ((m , m<k) == (n , n<k))
      ⊔ ((m , m<k) <-Fin (n , n<k))
      ⊔ ((n , n<k) <-Fin (m , m<k))
    Fin-trichotomy-aux O O _ _ = inl (Fin= idp)
    Fin-trichotomy-aux O (1+ n) _ _ = inr (inl (O<S n))
    Fin-trichotomy-aux (1+ m) O _ _ = inr (inr (O<S m))
    Fin-trichotomy-aux (1+ m) (1+ n) Sm<k Sn<k
     with Fin-trichotomy-aux m n (<-trans ltS Sm<k) (<-trans ltS Sn<k)
    ... | inl m=n = inl (Fin= (ap S (Fin=-elim m=n)))
    ... | inr (inl m<n) = inr (inl (<-ap-S m<n))
    ... | inr (inr n<m) = inr (inr (<-ap-S n<m))

Fin-trichotomy' : ∀ {k} (i j : Fin k) → (i ≤-Fin j) ⊔ (j <-Fin i)
Fin-trichotomy' i j with Fin-trichotomy i j
... | inl p = inl (inl (ap to-ℕ p))
... | inr (inl u) = inl (inr u)
... | inr (inr u) = inr u

-- This is a bit inconvenient to use, but in some cases we use it to avoid
-- having to lift universes.
module Fin-induction where
  Fin[_]-ind : ∀ {ℓ}
    → (n : ℕ) (P : Fin n → Type ℓ)
    → (∀ u → P (O , u))
    → ((i : ℕ) (v : 1+ i < n) → P (i , S<-< v) → P (1+ i , v))
    → (i : Fin n) → P i
  Fin[ n ]-ind P P₀ Pₛ (i , u) = aux i u
    where
    aux : (i : ℕ) (u : i < n) → P (i , u)
    aux O u = P₀ u
    aux (1+ i) u = Pₛ i u (aux i (S<-< u))

  Fin[_]-ind-from : ∀ {ℓ}
    → (n : ℕ) (i₀ : Fin n) (P : Fin n → Type ℓ)
    → P i₀
    → ( (j : ℕ) (v : 1+ j < n)
        → let i = (j , S<-< v)
              i+1 = (1+ j , v)
           in i₀ ≤-Fin i → P i → P i+1 )
    → (i : Fin n) → i₀ ≤-Fin i → P i
  Fin[ n ]-ind-from i₀ P P₀ Pₛ i (inl p) = transp P (Fin= p) P₀
  Fin[ n ]-ind-from i₀ P P₀ Pₛ (.(1+ (to-ℕ i₀)) , _) (inr ltS) =
    Pₛ (to-ℕ i₀) _ lteE (transp P (Fin= idp) P₀)
  Fin[ n ]-ind-from i₀ P P₀ Pₛ (1+ i , u) (inr (ltSR v)) =
    Pₛ i u (inr v) (Fin[ n ]-ind-from i₀ P P₀ Pₛ (i , S<-< u) (inr v))

open Fin-induction public

module Fin-decidability where
  ∀-Fin? :
    ∀ {ℓ} {n} (P : Fin n → Type ℓ)
    → ((i : Fin n) → Dec (P i))
    → Dec ((i : Fin n) → P i)
  ∀-Fin? {n = O} P _ = inl (λ ())
  ∀-Fin? {n = 1+ n} P ∀Fin-Sn-Dec-P =
   if ∀-Fin? (P ∘ Fin-S) (∀Fin-Sn-Dec-P ∘ Fin-S)
   then (λ ∀Fin-n-P →
     if ∀Fin-Sn-Dec-P (n , ltS)
     then (λ Pn →
       inl (∀-Fin-extend ∀Fin-n-P Pn))
     else λ ¬Pn →
       inr λ ∀Fin-Sn-P → ¬Pn (∀Fin-Sn-P (n , ltS)))
   else λ ¬∀Fin-n-P →
     inr λ ∀Fin-Sn-P → ¬∀Fin-n-P (∀Fin-Sn-P ∘ Fin-S)

  Σ-Fin? :
    ∀ {ℓ} {n} (P : Fin n → Type ℓ)
    → ((i : Fin n) → Dec (P i))
    → Dec (Σ[ i ﹕ Fin n ] P i)
  Σ-Fin? {n = 0} _ _ = inr (λ ())
  Σ-Fin? {n = 1} P ∀Fin-Sn-Dec-P =
    if (∀Fin-Sn-Dec-P 0)
       (λ  P0 → inl (0 , P0))
       (λ ¬P0 → inr λ{ ((O , ltS) , P0) → ¬P0 P0
                     ; ((1+ _ , ltSR ()) , _) })
  Σ-Fin? {n = 2+ n} P ∀Fin-Sn-Dec-P =
    if Σ-Fin? (P ∘ Fin-S) (∀Fin-Sn-Dec-P ∘ Fin-S)
    then (λ{ (i , Pi) →
      inl ((Fin-S i) , Pi) })
    else λ ¬ΣFin-n-P →
      if ∀Fin-Sn-Dec-P (1+ n , ltS)
      then (λ PSn →
        inl ((1+ n , ltS) , PSn))
      else (λ ¬PSn →
        inr λ{ ((i , i<2+n) , Pi) →
               ⊔-elim
                 (λ i≤Sn →
                 ⊔-elim
                   (λ i=Sn → ¬PSn (transp P (Fin= i=Sn) Pi))
                   (λ i<Sn → ¬ΣFin-n-P ((i , i<Sn) , (transp P (Fin= idp) Pi)))
                   i≤Sn)
                 (λ Sn<i → ¬<-self (≤-<-< (<-S≤ Sn<i) i<2+n))
                 (ℕ-trichotomy' i (1+ n)) })

  {- Negation -}

  ¬∀Fin¬ :
    ∀ {ℓ} n (P : Fin n → Type ℓ)
    → ((i : Fin n) → Dec (P i))
    → ¬ (∀ i → ¬ (P i))
    → Σ (Fin n) P
  ¬∀Fin¬ n P dec ¬all¬ with Σ-Fin? P dec
  ... | inl yes = yes
  ... | inr no = ⊥-rec $ ¬all¬ (curry no)

  ¬ΣFin¬ :
    ∀ {ℓ} n (P : Fin n → Type ℓ)
    → ((i : Fin n) → Dec (P i))
    → ¬ (Σ (Fin n) (¬ ∘ P))
    → Π (Fin n) P
  ¬ΣFin¬ n P dec ¬ex¬ <n with dec <n
  ... | inl yes = yes
  ... | inr no = ⊥-rec $ ¬ex¬ (<n , no)

  ¬∀Fin :
    ∀ {ℓ} n (P : Fin n → Type ℓ)
    → ((i : Fin n) → Dec (P i))
    → ¬ (∀ i → P i)
    → Σ (Fin n) (¬ ∘ P)
  ¬∀Fin n P dec ¬all with Σ-Fin? (¬ ∘ P) (¬-dec-fiberwise dec)
  ... | inl yes = yes
  ... | inr no = ⊥-rec $ ¬all (¬ΣFin¬ n P dec no)

  -- Deciding fibers of maps between finite types
  Fin-hfiber-dec : ∀ {m n} (f : Fin m → Fin n) (j : Fin n) → Dec (hfiber f j)
  Fin-hfiber-dec {O} {n} f j = inr ((≮O _) ∘ snd ∘ fst)
  Fin-hfiber-dec {1+ m} {n} f j =
    if Fin-hfiber-dec (f ∘ Fin-S) j
    then (λ{ (x@(i , i<m) , fi=j) →
      inl (Fin-S x , ap f (Fin= idp) ∙ fi=j) })
    else λ h →
    if f (m , ltS) ≟-Fin j
    then (λ fm=j →
      inl ((m , ltS) , fm=j))
    else λ fm≠j →
      inr λ{ ((i , i<Sm) , fi=j) →
             ⊔-elim
               (λ i=m → fm≠j (ap f (Fin= (! i=m)) ∙ fi=j))
               (λ i<m → h ((i , i<m) , ap f (Fin= idp) ∙ fi=j))
               (<S-≤ i<Sm) }

open Fin-decidability public

module Fin-minimization where
  is-smallest-Fin : ∀ {ℓ} {n} → (Fin n → Type ℓ) → Fin n → Type ℓ
  is-smallest-Fin {n = n} P i = P i × ((j : Fin n) → P j → i ≤-Fin j)

  Fin-smallest-witness :
    ∀ {ℓ} {n} {P : Fin n → Type ℓ}
    → ((i : Fin n) → Dec (P i))
    → (i : Fin n) → P i
    → Σ (Fin n) (is-smallest-Fin P)
  Fin-smallest-witness {n = 1} dec i@(O , _) Pi = i , Pi , λ _ _ → O≤ _
  Fin-smallest-witness {n = 1} dec (1+ _ , ltSR ())
  Fin-smallest-witness {ℓ} {2+ n} {P} dec i Pi =
    let
      i-smallest-witness? =
        ∀-Fin?
          (λ (j : Fin (2+ n)) → P j → i ≤-Fin j)
          (λ j → →-dec (dec j) (i ≤?-Fin j))
    in
      case i-smallest-witness?
      then (λ yes → i , Pi , yes)
      else (λ no →
        let rec = Fin-smallest-witness {n = 1+ n} (dec ∘ Fin-S) (j' no) (Pj' no)
        in Σ-Fin-S B (1+ n) P B-lifts rec)
    where
      B : ∀ n → (P : (Fin n) → Type ℓ) → Fin n → Type ℓ
      B n P i = P i × ((j : Fin n) → P j → i ≤-Fin j)

      B-lifts : ∀ i → B (1+ n) (P ∘ Fin-S) i → B (2+ n) P (Fin-S i)
      B-lifts (i , u) (p , w) = p , ∀-Fin-extend w λ _ → inr u

      module _ (no : ¬ ((j : Fin (2+ n)) → P j → i ≤-Fin j)) where
        imp : ∀ j → ¬ (P j → i ≤-Fin j) → P j × (j <-Fin i)
        imp j = ×-fmap-r (P j) (≰-to>-Fin i j) ∘ ¬imp (dec j) (i ≤?-Fin j)

        smaller-witness : Σ[ j ﹕ Fin (2+ n) ] (P j × (j <-Fin i))
        smaller-witness = Σ-fmap-r imp $
          ¬∀Fin (2+ n) (λ j → P j → i ≤-Fin j)
            (λ j → →-dec (dec j) (i ≤?-Fin j)) no

        j = fst smaller-witness
        Pj = 2nd smaller-witness
        j<i = 3rd smaller-witness

        j' : Fin (1+ n)
        j' = to-ℕ j , j<1+n
          where j<1+n = <-≤-< j<i $ <S-≤ $ snd i

        Pj' : (P ∘ Fin-S) j'
        Pj' = transp P (Fin= idp) Pj

open Fin-minimization public

{-
module Fin-counting where
  -- The number of (k : Fin n) in the range [i, j) satisfying P.
  #-Fin_from_to_,_and_st :
    ∀ {ℓ} n
    → (i : Fin n)
    → (j : ℕ) (v : j ≤ n)
    → to-ℕ i < j
    → (P : Fin n → Type ℓ) → ((i : Fin n) → Dec (P i))
    → ℕ
  #-Fin n from i to .(1+ (to-ℕ i)) , _ and ltS st P P? =
    if P? i
    then (λ _ → 1)
    else (λ _ → O)
  #-Fin n from i to 1+ j , v and ltSR u st P P? =
    #-Fin n from i to j , <-≤-≤ ltS v and u st P P?
      + #-Fin n from j , S≤-< v to 1+ j , v and ltS st P P?

  abstract
    #-Fin-range-1 :
      ∀ {ℓ} n (i : Fin n) (u : 1+ (to-ℕ i) ≤ n)
        (P : Fin n → Type ℓ) (P? : (i : Fin n) → Dec (P i))
      → #-Fin n from i to 1+ (to-ℕ i) , u and ltS st P P? ≤ 1
    #-Fin-range-1 n i u P P? with P? i
    ... | inl _ = lteE
    ... | inr _ = O≤ _

    #-Fin-ub :
      ∀ {ℓ} n (i : Fin n) (j : ℕ) (v : j ≤ n) (u : to-ℕ i < j)
        (P : Fin n → Type ℓ) (P? : (i : Fin n) → Dec (P i))
      → to-ℕ i + #-Fin n from i to j , v and u st P P? ≤ j
    #-Fin-ub n i .(1+ (to-ℕ i)) v ltS P P? =
      ≤-+-l (to-ℕ i) (#-Fin-range-1 n _ v P P?)
      ◂$ transp (to-ℕ i + #-Fin n from i to 1+ (to-ℕ i) , v and ltS st P P? ≤_)
                (+-comm (to-ℕ i) 1)
    #-Fin-ub n i (1+ j) v (ltSR u) P P? =
      +-assocr-≤
        (to-ℕ i)
        (#-Fin n from i to j , <-≤-≤ ltS v and u st P P?)
        (#-Fin n from j , S≤-< v to 1+ j , v and ltS st P P?)
      $ ≤-trans
          (≤-+ (#-Fin-ub n i j _ u P P?) (#-Fin-range-1 n _ v P P?))
          (inl (+-comm j 1))

    #-Fin-lb :
      ∀ {ℓ} n (O<n : O < n) (j : ℕ) (v : j ≤ n) (u : O < j)
        (P : Fin n → Type ℓ) (P? : (i : Fin n) → Dec (P i))
      → ((k : Fin n) → to-ℕ k < j → P k)
      → j ≤ #-Fin n from (O , O<n) to j , v and u st P P?
    #-Fin-lb n O<n .1 v ltS P P? all-P with P? (O , O<n)
    ... | inl _ = lteE
    ... | inr ¬PO = ⊥-rec (¬PO (all-P _ ltS))
    #-Fin-lb n O<n (1+ j) v (ltSR u) P P? all-P =
      +-comm-≤ j 1
        (≤-+ (#-Fin-lb n O<n j (<-≤-≤ ltS v) u P P? all-P') Pj-lem)
      where
        all-P' : (k : Fin n) → to-ℕ k < j → P k
        all-P' k = all-P k ∘ ltSR

        Pj-lem : 1 ≤ if P? (j , S≤-< v) then (λ _ → 1) else (λ _ → O)
        Pj-lem with P? (j , S≤-< v)
        ... | inl _ = lteE
        ... | inr ¬Pj = ⊥-rec (¬Pj (all-P _ ltS))

  {-
  -- (#-Fin n from i to j ...) is antitone in i and monotone in j.
  -- Can also use this to prove #-Fin-coarse-ub.
  #-Fin-antitone-1st :
    ∀ {ℓ} n {i₁ i₂} (j : ℕ) (v : j ≤ n)
      (u₁ : to-ℕ i₁ < j) (u₂ : to-ℕ i₂ < j)
      (P : Fin n → Type ℓ) (P? : (i : Fin n) → Dec (P i))
    → i₁ ≤-Fin i₂
    → #-Fin n from i₂ to j , v and u₂ st P P?
      ≤ #-Fin n from i₁ to j , v and u₁ st P P?
  #-Fin-antitone-1st n j v u₁ u₂ P P? (inl idp) = {!!}
  #-Fin-antitone-1st n j v u₁ u₂ P P? (inr x) = {!!}
  -}

  #-Fin-coarse-ub :
    ∀ {ℓ} n (i : Fin n) (j : ℕ) (v : j ≤ n) (u : to-ℕ i < j)
      (P : Fin n → Type ℓ) (P? : (i : Fin n) → Dec (P i))
    → #-Fin n from i to j , v and u st P P? ≤ n
  #-Fin-coarse-ub n i j v u P P? = ≤-trans (+-≤-dropl (#-Fin-ub n i j v u P P?)) v

open Fin-counting public
-}
