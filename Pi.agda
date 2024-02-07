{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Pi where
  open import Functions public

  infixl -1 -Π

  private variable
    ℓ ℓ₁ ℓ₂ : Level
    X Y : Set ℓ
    A B : X → Set ℓ

  -Π : (X : Set ℓ₁) → (X → Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
  -Π X A = (x : X) → A x

  syntax -Π X (λ x → Y) = Π[ x ∈ X ], Y

  Π-ind : Π[ x ∈ X ], A x → (x : X) → A x
  Π-ind = _$_
