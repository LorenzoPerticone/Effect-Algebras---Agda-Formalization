{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Integers where
  open import Naturals renaming (zero to ℕ-zero; succ to ℕ-succ)

  private variable
    ℓ : Level

  data ℤ : Set where
    zero : ℤ
    pls : ℕ → ℤ
    mns : ℕ → ℤ

  pls1 : ℤ
  pls1 = pls ℕ-zero

  mns1 : ℤ
  mns1 = mns ℕ-zero

  ℤ-ind : (P : ℤ → Set ℓ) →
          P zero →
          P pls1 →
          ((n : ℕ) → P (pls n) → P (pls (ℕ-succ n))) →
          P mns1 →
          ((n : ℕ) → P (mns n) → P (mns (ℕ-succ n))) →
          (n : ℤ) →
          P n
  ℤ-ind P p0 _ _ _ _ zero      = p0
  ℤ-ind P _ p+1 ps _ _ (pls n) = ℕ-ind (P ∘ pls) p+1 ps n
  ℤ-ind P _ _ _ p-1 pp (mns n) = ℕ-ind (P ∘ mns) p-1 pp n

  ℤ-rec : (X : Set ℓ) →
          X →
          X →
          (X → X) →
          X →
          (X → X) →
          ℤ →
          X
  ℤ-rec X x0 x+1 xs x-1 xp = ℤ-ind (const X) x0 x+1 (const xs) x-1 (const xp)

  succ : ℤ → ℤ
  succ zero             = pls1
  succ (pls x)          = pls (ℕ-succ x)
  succ (mns ℕ-zero)     = zero
  succ (mns (ℕ-succ x)) = mns x

  pred : ℤ → ℤ
  pred zero             = mns1
  pred (pls ℕ-zero)     = zero
  pred (pls (ℕ-succ x)) = pls x
  pred (mns x)          = mns (ℕ-succ x)
