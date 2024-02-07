{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Integers-arith where
  open import Naturals renaming (zero to ℕ-zero; succ to ℕ-succ)
  open import Integers

  neg : ℤ → ℤ
  neg zero = zero
  neg (pls x) = mns x
  neg (mns x) = pls x

  _+_ : ℤ → ℤ → ℤ
  zero           + n = n
  pls ℕ-zero     + n = succ n
  pls (ℕ-succ m) + n = succ (pls m + n)
  mns ℕ-zero     + n = pred n
  mns (ℕ-succ m) + n = pred (mns m + n)

  _-_ : ℤ → ℤ → ℤ
  m - n = m + (neg n)
  
  _×_ : ℤ → ℤ → ℤ
  zero           × n = zero
  pls ℕ-zero     × n = n
  pls (ℕ-succ x) × n = ((pls x) × n) + n
  mns ℕ-zero     × n = neg n
  mns (ℕ-succ x) × n = ((mns x) × n) - n
