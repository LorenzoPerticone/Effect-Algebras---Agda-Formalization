{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Homotopies where
  open import Functions public
  open import Sigma
  open import Pi
  open import Equalities
  open import Equalities-lemmas

  infixr 11 _~_
  infixr 21 _~·_
  infixr 21 _~⁻¹
  infixr 2 _~⟨_⟩_
  infixr 3 _■
  infixr 31 _▶_
  infixr 32 _◀_

  private variable
    ℓ : Level
    X Y Z : Set ℓ
    A : X → Set ℓ
    f g h : Π[ x ∈ X ], A x

  _~_ : (Π[ x ∈ X ], A x) → (Π[ x ∈ X ], A x) → Set _
  f ~ g = Π[ x ∈ _ ], f x ≡ g x

  ~refl : f ~ f
  ~refl = λ _ → refl

  _~·_ : f ~ g → g ~ h → f ~ h
  ϕ ~· ψ = λ x → ϕ x · ψ x

  _~⁻¹ : f ~ g → g ~ f
  ϕ ~⁻¹ = λ x → ϕ x ⁻¹

  _~⟨_⟩_ : (f : Π[ x ∈ X ], A x) → {g h : Π[ x ∈ X ], A x} → f ~ g → g ~ h → f ~ h
  _ ~⟨ ϕ ⟩ ψ = ϕ ~· ψ

  _■ : (f : X → Y) → f ~ f
  f ■ = ~refl

  _▶_ : (f : Y → Z) → {g h : X → Y} → g ~ h → (f ∘ g) ~ (f ∘ h)
  f ▶ ϕ = λ x → ap f (ϕ x)

  _◀_ : {f g : Y → Z} → f ~ g → (h : X → Y) → (f ∘ h) ~ (g ∘ h)
  ϕ ◀ h = ϕ ∘ h

  is-section : (X → Y) → (Y → X) → Set _
  is-section f g = g ∘ f ~ id

  is-retract : (X → Y) → (Y → X) → Set _
  is-retract f g = f ∘ g ~ id

  section : (X → Y) → Set _
  section f = Σ[ g ∈ _ ], is-section f g

  retract : (X → Y) → Set _
  retract f = Σ[ g ∈ _ ], is-retract f g

  ~-natural : (f g : X → Y) → (ϕ : f ~ g) → (x y : X) → (p : x ≡ y) →
              (ϕ x) · (ap g p) ≡ (ap f p) · (ϕ y)
  ~-natural f g ϕ x .x refl = ·-l-unit (ϕ x) ⁻¹

  ~-whisk-comm : (f : X → X) → (ϕ : f ~ id) →
                 (ϕ ◀ f) ~ (f ▶ ϕ)
  ~-whisk-comm f ϕ x =
    let p : (ϕ ◀ f) ~· ϕ ~ (f ▶ ϕ) ~· ϕ
        p x = ϕ (f x) · ϕ x         ≡⟨ ap (ϕ (f x) ·_) (ap-id (ϕ x) ⁻¹) ⟩
              ϕ (f x) · ap id (ϕ x) ≡⟨ ~-natural f id ϕ (f x) x (ϕ x) ⟩
              ap f (ϕ x) · ϕ x      ∎
    in ϕ (f x)                       ≡⟨ ap (ϕ (f x) ·_) (·-r-inv (ϕ x) ⁻¹) ⟩
       ϕ (f x) · (ϕ x · (ϕ x ⁻¹))    ≡⟨ ·-assoc (ϕ (f x)) (ϕ x) (ϕ x ⁻¹) ⁻¹ ⟩
       (ϕ (f x) · ϕ x) · (ϕ x ⁻¹)    ≡⟨ ap (_· (ϕ x ⁻¹)) (p x) ⟩
       (ap f (ϕ x) · ϕ x) · (ϕ x ⁻¹) ≡⟨ ·-assoc (ap f (ϕ x)) (ϕ x) (ϕ x ⁻¹) ⟩
       ap f (ϕ x) · (ϕ x · (ϕ x ⁻¹)) ≡⟨ ap (ap f (ϕ x) ·_) (·-r-inv (ϕ x)) ⟩
       ap f (ϕ x)                    ∎
