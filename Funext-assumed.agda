{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Funext

module Funext-assumed (funext-ax : ∀ {ℓ₁} {ℓ₂} {X} {A} {f} {g} → funext ℓ₁ ℓ₂ X A f g) where
  open import Pi
  open import Sigma
  open import Equalities
  open import Homotopies

  funext1 : {ℓ₁ ℓ₂ : Level}
            {X : Set ℓ₁}
            {A : X → Set ℓ₂}
            {f g : Π[ x ∈ X ], A x} →
            f ~ g → f ≡ g
  funext1 = π₁ (π₁ funext-ax)

  funext2 : {ℓ₁ ℓ₂ ℓ₃ : Level}
            {X : Set ℓ₁} → 
            {A : X → Set ℓ₂} → 
            {Γ : (x : X) → A x → Set ℓ₃} → 
            {f g : (x : X) → (a : A x) → Γ x a} →
            ((x : X) → f x ~ g x ) →
            f ≡ g
  funext2 prf = funext1 (λ x → funext1 (λ a → prf x a))
  
  funext3 : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} →
            {X : Set ℓ₁} → 
            {A : X → Set ℓ₂} →
            {Γ : (x : X) → A x → Set ℓ₃} → 
            {Ξ : (x : X) → (a : A x) → Γ x a → Set ℓ₄} →
            {f g : (x : X) → (a : A x) → (g : Γ x a) → Ξ x a g} →
            ((x : X) → (a : A x) → f x a ~ g x a) →
            f ≡ g
  funext3 prf = funext1 (λ x → funext2 (λ a g → prf x a g))
