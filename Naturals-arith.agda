{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Naturals-arith where
  open import Naturals

  _+_ : ℕ → ℕ → ℕ
  zero + n = n
  succ m + n = succ (m + n)

  _×_ : ℕ → ℕ → ℕ
  zero × n = zero
  succ m × n = (m × n) + n
