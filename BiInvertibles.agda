{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module BiInvertibles where
  open import Sigma
  open import Homotopies

  infixr 10 _≃_

  private variable
    ℓ ℓ₁ ℓ₂ : Level
    X Y : Set ℓ

  is-bi-inv : (X → Y) → Set _
  is-bi-inv f = (section f) × (retract f)

  equiv : Set ℓ₁ → Set ℓ₂ → Set _
  equiv X Y = Σ[ f ∈ (X → Y) ], is-bi-inv f

  _≃_ : Set ℓ₁ → Set ℓ₂ → Set _
  X ≃ Y = equiv X Y
