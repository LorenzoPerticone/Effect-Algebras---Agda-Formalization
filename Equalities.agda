{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Equalities where
  open import Functions public
  open import Pi

  infixr 10 _≡_
  infixr 20 _·_
  infixr 21 _⁻¹
  infixr 0 _≡⟨_⟩_
  infixr 1 _∎

  private variable
    ℓ : Level
    X Y : Set ℓ
    w x y z : X

  data _≡_ {X : Set ℓ} (x : X) : X → Set ℓ where
    refl : x ≡ x

  _⁻¹ : x ≡ y → y ≡ x
  refl ⁻¹ = refl

  _·_ : x ≡ y → y ≡ z → x ≡ z
  p · refl = p

  _≡⟨_⟩_ : (x : X) → {y z : X} → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ p ⟩ q = p · q

  _∎ : (x : X) → x ≡ x
  _ ∎ = refl

  ap : (f : X → Y) → x ≡ y → f x ≡ f y
  ap f refl = refl

  transport : (A : X → Set ℓ) → x ≡ y → A x → A y
  transport A refl = id

  apd : (A : X → Set ℓ) →
        (f : Π[ x ∈ X ], A x) →
        (p : x ≡ y) →
        transport A p (f x) ≡ f y
  apd A f refl = refl

