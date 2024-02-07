{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Invertibles where
  open import Sigma
  open import Equalities
  open import Homotopies

  private variable
    ℓ ℓ₁ ℓ₂ : Level
    X Y Z : Set ℓ

  is-iso : (X → Y) → Set _
  is-iso f = Σ[ g ∈ _ ], (is-section f g) × (is-retract f g)

  iso→inv : (f : X → Y) → is-iso f → Y → X
  iso→inv _ (g , _) = g

  iso : Set ℓ₁ → Set ℓ₂ → Set _
  iso X Y = Σ[ f ∈ (X → Y) ], is-iso f

