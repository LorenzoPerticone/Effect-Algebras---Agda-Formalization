{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Sigma where
  open import Functions public

  infixl -1 -Σ
  infixl 20 _×_

  private variable
    ℓ ℓ₁ ℓ₂ : Level
    X Y : Set ℓ
    A B : X → Set ℓ

  -- Sigmas
  data -Σ (X : Set ℓ₁) (A : X → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    _,_ : (x : X) → A x → -Σ X A

  syntax -Σ X (λ x → Y) = Σ[ x ∈ X ], Y

  Σ-ind : (P : Σ[ x ∈ X ], A x → Set ℓ) →
          ((x : X) → (a : A x) → P (x , a)) →
          (p : Σ[ x ∈ X ], A x) →
          P p
  Σ-ind P f (x , a) = f x a

  Σ-rec : (Y : Set ℓ) →
          ((x : X) → A x → Y) →
          Σ[ x ∈ X ], A x →
          Y
  Σ-rec Y f p = Σ-ind (const Y) f p

  π₁ : Σ[ x ∈ X ], A x → X
  π₁ {X = X} p = Σ-rec X const p

  π₂ : (p : Σ[ x ∈ X ], A x) → A (π₁ p)
  π₂ {A = A} p = Σ-ind (A ∘ π₁) (λ _ → id) p

  -- Products
  _×_ : Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
  X × Y = Σ[ _ ∈ X ], Y

  ×-ind : (P : X × Y → Set ℓ) →
          ((x : X) → (y : Y) → P (x , y)) →
          (p : X × Y) →
          P p
  ×-ind P f p = Σ-ind P f p

  ×-rec : (Z : Set ℓ) →
          (X → Y → Z) →
          X × Y →
          Z
  ×-rec Z f p = ×-ind (const Z) f p

  p₁ : X × Y → X
  p₁ = π₁

  p₂ : X × Y → Y
  p₂ = π₂
