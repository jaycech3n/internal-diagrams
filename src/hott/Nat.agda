{-# OPTIONS --without-K #-}

module hott.Nat where

open import hott.Base public

pattern 1+ n = S n
pattern 2+ n = S (S n)

module Nat-instances {n : ℕ} where
  -- All instance declarations here will be visible to any module that imports
  -- hott.Nat (this is apparently intended behavior, see GitHub issue #1265)
  instance
    O<S-inst : O < 1+ n
    O<S-inst = O<S n

private
  module trichotomy where
    ℕ-trichotomy' : (m n : ℕ) → (m ≤ n) ⊔ (n < m)
    ℕ-trichotomy' m n with ℕ-trichotomy m n
    ... | inl m=n = inl (inl m=n)
    ... | inr (inl m<n) = inl (inr m<n)
    ... | inr (inr n<m) = inr n<m

  module one-arg-lemmas {n : ℕ} where
    ¬< : ¬ (n < n)
    ¬< u = <-to-≠ u idp

    <1-=O : n < 1 → n == O
    <1-=O ltS = idp

  open one-arg-lemmas

  module two-arg-lemmas {m n : ℕ} where
    =-cancel-S : 1+ m == 1+ n :> ℕ → m == n
    =-cancel-S idp = idp

    <-S≤ : m < n → 1+ m ≤ n
    <-S≤ ltS = lteE
    <-S≤ (ltSR u) = inr (<-ap-S u)

    <S-≤ : m < 1+ n → m ≤ n
    <S-≤ ltS = lteE
    <S-≤ (ltSR u) = inr u

    S≤-≤ : 1+ m ≤ n → m ≤ n
    S≤-≤ = ≤-trans lteS

    no-between : m < n → n < 1+ m → ⊥
    no-between u v with <-S≤ u
    ... | inl idp = ¬< v
    ... | inr w = ¬< (<-trans v w)

  module three-arg-lemmas {k m n : ℕ} where
    ≤-<-< : k ≤ m → m < n → k < n
    ≤-<-< (inl idp) u' = u'
    ≤-<-< (inr u) u' = <-trans u u'

    3-comm-2 : k + m + n == m + k + n
    3-comm-2 = +-comm k m |in-ctx (_+ n)

open trichotomy public
open one-arg-lemmas public
open two-arg-lemmas public
open three-arg-lemmas public

module monus where
  infixl 80 _∸_
  _∸_ : ℕ → ℕ → ℕ
  O ∸ n = O
  1+ m ∸ O = 1+ m
  1+ m ∸ 1+ n = m ∸ n

  ∸-unit-r : ∀ n → n ∸ O == n
  ∸-unit-r O = idp
  ∸-unit-r (1+ n) = idp

  S∸ : ∀ n → 1+ n ∸ n == 1
  S∸ O = idp
  S∸ (1+ n) = S∸ n

  ∸-nonzero : ∀ {m n} → n < m → O < m ∸ n
  ∸-nonzero {1+ m} {.m} ltS rewrite S∸ m = O<S _
  ∸-nonzero {1+ m} {O} (ltSR u) = O<S _
  ∸-nonzero {1+ m} {1+ n} (ltSR u) = ∸-nonzero (<-trans ltS u)

  abstract
    <∸-+< : ∀ {k m} n → k < m ∸ n → k + n < m
    <∸-+< {k} {1+ m} O u rewrite +-unit-r k = u
    <∸-+< {k} {1+ m} (1+ n) u = transp (_< 1+ m) (! (+-βr k n)) (<-ap-S (<∸-+< n u))

  ∸=S-∸S= : ∀ {k} m n → m ∸ n == 1+ k → m ∸ 1+ n == k
  ∸=S-∸S= (1+ m) (1+ n) u = ∸=S-∸S= m n u
  ∸=S-∸S= (1+ O) O u = =-cancel-S u
  ∸=S-∸S= (2+ m) O u = =-cancel-S u

  β∸1 : ∀ {n} → O < n → n == 1+ (n ∸ 1)
  β∸1 {.1} ltS = idp
  β∸1 {1+ n} (ltSR _) rewrite ∸-unit-r n = idp

open monus public