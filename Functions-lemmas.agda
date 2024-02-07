{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Functions-lemmas where
  open import Functions public
  open import Equalities

  private variable
    ℓ : Level
    W X Y Z : Set ℓ

  ∘-assoc : (f : Y → Z) → (g : X → Y) → (h : W → X) →
            (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
  ∘-assoc f g h = refl

  ∘-l-unit : (f : X → Y) → id ∘ f ≡ f
  ∘-l-unit f = refl

  ∘-r-unit : (f : X → Y) → f ∘ id ≡ f
  ∘-r-unit f = refl
