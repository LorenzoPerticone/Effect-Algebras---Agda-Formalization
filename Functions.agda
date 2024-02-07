{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Functions where
  open import Agda.Primitive public

  infixl 20 _∘_
  infixl 20 _$_

  private variable
    ℓ : Level
    W X Y Z : Set ℓ
    A : X → Set ℓ
    Γ : (x : X) → A x → Set ℓ

  id : X → X
  id x = x

  const : (x : X) → A x → X
  const x _ = x

  _∘_ : ({x : X} → (a : A x) → Γ x a) → (g : (x : X) → A x) → (x : X) → Γ x (g x)
  _∘_ f g x = f (g x)

  _$_ : ((x : X) → A x) → (x : X) → A x
  _$_ = id

  _`_`_ : (x : X) → ((x : X) → (a : A x) → Γ x a) → (a : A x) → Γ x a
  x ` f ` a = f x a
