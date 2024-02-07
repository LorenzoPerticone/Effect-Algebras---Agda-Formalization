{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Truncations where
  open import Equalities
  open import Sigma
  open import Pi

  private variable
    ℓ : Level
    X Y : Set ℓ
    A B : X → Set ℓ

  data TruncLevel : Set where
    neg2 : TruncLevel
    succ : TruncLevel → TruncLevel

  is-contr : Set ℓ → Set ℓ
  is-contr X = Σ[ c ∈ X ], Π[ x ∈ X ], c ≡ x

  is_trunc_ : TruncLevel → Set ℓ → Set ℓ
  is neg2     trunc X = is-contr X
  is (succ n) trunc X = Π[ x ∈ X ], Π[ y ∈ X ], is n trunc (x ≡ y)

  is-prop′ : Set ℓ → Set ℓ
  is-prop′ X = is (succ neg2) trunc X

  is-prop : Set ℓ → Set ℓ
  is-prop X = Π[ x ∈ X ], Π[ y ∈ X ], x ≡ y

  is_type_ : TruncLevel → Set ℓ → Set ℓ
  is neg2          type X = is-contr X
  is succ neg2     type X = is-prop X
  is succ (succ n) type X = Π[ x ∈ X ], Π[ y ∈ X ], is (succ n) type (x ≡ y)

  is-set : Set ℓ → Set ℓ
  is-set X = is (succ (succ neg2)) type X
