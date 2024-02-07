{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Sigma-lemmas where
  open import Sigma
  open import Pi
  open import Equalities
  open import Homotopies
  open import Invertible-BiInvertible

  private variable
    ℓ : Level
    X Y : Set ℓ
    A B : X → Set ℓ

  ap-π₁ : (p q : Σ[ x ∈ X ], A x) → p ≡ q → π₁ p ≡ π₁ q
  ap-π₁ (x , a) (y , b) p = ap π₁ p

  ap-π₂ : (p q : Σ[ x ∈ X ], A x) → (r : p ≡ q) → transport (A ∘ π₁) r (π₂ p) ≡ π₂ q
  ap-π₂ {A = A} (x , a) (y , b) p = apd (A ∘ π₁) π₂ p

  -- Sigma
  Σ-code : (Σ[ x ∈ X ], A x) → (Σ[ x ∈ X ], A x) → Set _
  Σ-code {A = A} s t = Σ[ p ∈ (π₁ s ≡ π₁ t) ], transport A p (π₂ s) ≡ (π₂ t)

  Σ-code-refl : {t : Σ[ x ∈ X ], A x} → Σ-code t t
  Σ-code-refl = (refl , refl)

  Σ-encode : (s t : Σ[ x ∈ X ], A x) → s ≡ t → Σ-code s t
  Σ-encode {A = A} s .s refl = Σ-code-refl {t = s}

  Σ-decode : (s t : Σ[ x ∈ X ], A x) → Σ-code s t → s ≡ t
  Σ-decode (x , a) (.x , .a) (refl , refl) = refl

  Σ-encode-decode-section : (s t : Σ[ x ∈ X ], A x) → is-section (Σ-encode s t) (Σ-decode s t)
  Σ-encode-decode-section (x , a) .(x , a) refl = refl

  Σ-encode-decode-retract : (s t : Σ[ x ∈ X ], A x) → is-retract (Σ-encode s t) (Σ-decode s t)
  Σ-encode-decode-retract (x , a) (.x , .a) (refl , refl) = refl

  Σ-code-≡ : Π[ s ∈ (Σ[ x ∈ X ], A x) ], Π[ t ∈ (Σ[ y ∈ X ], A y) ], (s ≡ t) ≃ (Σ-code s t)
  Σ-code-≡ s t =
    let f = Σ-encode s t
        g = Σ-decode s t
        ϕ = Σ-encode-decode-section s t
        ψ = Σ-encode-decode-retract s t
    in iso→equiv (s ≡ t) (Σ-code s t) (f , (g , (ϕ , ψ)))

  -- Product
  ×-code : X × Y → X × Y → Set _
  ×-code a b = (p₁ a ≡ p₁ b) × (p₂ a ≡ p₂ b)

  ×-code-refl : (t : X × Y) → ×-code t t
  ×-code-refl (x , y) = (refl , refl)

  ×-encode : (t s : X × Y) → t ≡ s → ×-code t s
  ×-encode t .t refl = ×-code-refl t

  ×-decode : (s t : X × Y) → ×-code s t → s ≡ t
  ×-decode (x₁ , y₁) (.x₁ , .y₁) (refl , refl) = refl

  ×-encode-decode-section : (s t : X × Y) → is-section (×-encode s t) (×-decode s t)
  ×-encode-decode-section (x , y) .(x , y) refl = refl

  ×-encode-decode-retract : (s t : X × Y) → is-retract (×-encode s t) (×-decode s t)
  ×-encode-decode-retract (x , y) (.x , .y) (refl , refl) = refl

  ×-code-≡ : (s t : X × Y) → (s ≡ t) ≃ (×-code s t)
  ×-code-≡ s t =
    let f = ×-encode s t
        g = ×-decode s t
        ϕ = ×-encode-decode-section s t
        ψ = ×-encode-decode-retract s t
    in iso→equiv (s ≡ t) (×-code s t) (f , (g , (ϕ , ψ)))
