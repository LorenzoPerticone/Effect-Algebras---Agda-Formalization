{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Empty where
  open import Functions public

  private variable
    ℓ : Level

  data 𝟘 : Set where

  𝟘-ind : (P : 𝟘 → Set ℓ) →
          (x : 𝟘) →
          P x
  𝟘-ind P ()

  𝟘-rec : (X : Set ℓ) → 𝟘 → X
  𝟘-rec X ⊥ = 𝟘-ind (const X) ⊥

  ¬ : Set ℓ → Set ℓ
  ¬ X = X → 𝟘
