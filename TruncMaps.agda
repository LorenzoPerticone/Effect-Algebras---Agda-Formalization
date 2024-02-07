{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module TruncMaps where
  open import Sigma
  open import Pi
  open import Equalities
  open import Truncations

  private variable
    ℓ : Level
    X Y : Set ℓ

  fib : (X → Y) → Y → Set _
  fib {X = X} f y = Σ[ x ∈ X ], f x ≡ y

  is_trunc-map_ : TruncLevel → (X → Y) → Set _
  is n trunc-map f = Π[ y ∈ _ ], is n trunc (fib f y)

  contr-map : (X → Y) → Set _
  contr-map f = is neg2 trunc-map f

  prop-map : (X → Y) → Set _
  prop-map f = is (succ neg2) trunc-map f
