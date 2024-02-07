{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Funext

module Truncations-lemmas-funext (funext-ax : ∀ {ℓ₁} {ℓ₂} {X} {A} {f} {g} → funext ℓ₁ ℓ₂ X A f g) where
  open import Unit
  open import Empty
  open import Sigma
  open import Pi
  open import Equalities
  open import Truncations
  open import TruncMaps

  open import Equalities-lemmas
  open import Sigma-lemmas
  open import Invertible-BiInvertible
  open import Truncations-lemmas

  open import Funext-assumed funext-ax

  private variable
    ℓ : Level
    X Y : Set ℓ
    A B : X → Set ℓ
    Γ Δ : (x : X) → A x → Set ℓ

  func-contr→contr-func : Π[ x ∈ X ], is-contr (A x) → is-contr (Π[ x ∈ X ], A x)
  func-contr→contr-func cntr =
    (λ x → π₁ (cntr x)) ,
    (λ f → funext1 (λ x → π₂ (cntr x) (f x)))

  func-prop→prop-func : Π[ x ∈ X ], is-prop (A x) → is-prop (Π[ x ∈ X ], A x)
  func-prop→prop-func prp = λ f g → funext1 (λ x → prp x (f x) (g x))

  isProp-isContr : (X : Set ℓ) → is-prop (is-contr X)
  isProp-isContr X (c₁ , C₁) (c₂ , C₂) =
    let c₁≡c₂ : c₁ ≡ c₂
        c₁≡c₂ = C₁ c₂
        C₁≡C₂ : transport (λ v → (x : X) → v ≡ x) (c₁≡c₂) C₁ ≡ C₂
        C₁≡C₂ = func-prop→prop-func (prop→set (contr→prop (c₁ , C₁)) c₂)
                                    (transport (λ x → (y : X) → x ≡ y) c₁≡c₂ C₁)
                                    C₂
    in Σ-decode (c₁ , C₁) (c₂ , C₂) (c₁≡c₂ , C₁≡C₂)

  isProp-isProp : (X : Set ℓ) → is-prop (is-prop X)
  isProp-isProp X X-prp₁ X-prp₂ = funext2 (λ x y → prop→set X-prp₁ x y (X-prp₁ x y) (X-prp₂ x y))

  isProp-trunc : (X : Set ℓ) → (n : TruncLevel) → is-prop (is n trunc X)
  isProp-trunc X neg2     = isProp-isContr X
  isProp-trunc X (succ n) = λ X-trunc₁ X-trunc₂ → funext2 (λ x y → isProp-trunc (x ≡ y) n (X-trunc₁ x y) (X-trunc₂ x y))

  isProp-ntype : (X : Set ℓ) → (n : TruncLevel) → is-prop (is n type X)
  isProp-ntype X neg2            = isProp-isContr X
  isProp-ntype X (succ neg2)     = isProp-isProp X
  isProp-ntype X (succ (succ n)) = λ X-ntype₁ X-ntype₂ → funext2 (λ x y → isProp-ntype (x ≡ y) (succ n) (X-ntype₁ x y) (X-ntype₂ x y))
