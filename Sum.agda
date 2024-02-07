{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Sum where
  open import Functions public

  infixl 20 _+_

  private variable
    ℓ ℓ₁ ℓ₂ : Level
    X Y : Set ℓ

  data _+_ (X : Set ℓ₁) (Y : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    ι₁ : X → X + Y
    ι₂ : Y → X + Y

  +-ind : (P : X + Y → Set ℓ) →
          ((x : X) → P (ι₁ x)) →
          ((y : Y) → P (ι₂ y)) →
          (v : X + Y) →
          P v
  +-ind P f _ (ι₁ x) = f x
  +-ind P _ g (ι₂ y) = g y

  +-rec : (Z : Set ℓ) →
          (X → Z) →
          (Y → Z) →
          X + Y →
          Z
  +-rec Z f g v = +-ind (const Z) f g v
