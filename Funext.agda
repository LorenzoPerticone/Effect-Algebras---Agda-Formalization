{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Funext where
  open import Sigma
  open import Pi
  open import Equalities
  open import Homotopies
  open import BiInvertibles

  funap : (ℓ₁ ℓ₂ : Level) → (X : Set ℓ₁) → (A : X → Set ℓ₂) → (f g : Π[ x ∈ X ], A x) → f ≡ g → f ~ g
  funap ℓ₁ ℓ₂ X A f g refl = ~refl

  funext : (ℓ₁ ℓ₂ : Level) → (X : Set ℓ₁) → (A : X → Set ℓ₂) → (f g : Π[ x ∈ X ], A x) → Set (ℓ₁ ⊔ ℓ₂)
  funext ℓ₁ ℓ₂ X A f g = is-bi-inv (funap ℓ₁ ℓ₂ X A f g)
