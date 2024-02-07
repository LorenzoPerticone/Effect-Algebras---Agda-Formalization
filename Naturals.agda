{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Naturals where
  open import Functions public

  private variable
    ℓ : Level

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  one = succ zero

  ℕ-ind : (P : ℕ → Set ℓ) →
          P zero →
          ((n : ℕ) → P n → P (succ n)) →
          (n : ℕ) →
          P n
  ℕ-ind P p0 ps zero     = p0
  ℕ-ind P p0 ps (succ n) = ps n (ℕ-ind P p0 ps n)

  ℕ-rec : (Y : Set ℓ) →
          Y →
          (Y → Y) →
          ℕ →
          Y
  ℕ-rec Y y f n = ℕ-ind (const Y) y (const f) n
