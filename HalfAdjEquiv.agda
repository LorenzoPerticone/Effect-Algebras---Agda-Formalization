{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module HalfAdjEquiv where
  open import Sigma
  open import Homotopies

  private variable
    ℓ : Level
    X Y : Set ℓ

  is-hae : (f : X → Y) → Set _
  is-hae {X = X} {Y = Y} f =
    Σ[ g ∈ (Y → X) ], Σ[ sect ∈ is-section f g ], Σ[ retr ∈ is-retract f g ], (f ▶ sect ~ retr ◀ f)
