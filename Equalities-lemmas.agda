{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Equalities-lemmas where
  open import Equalities

  private variable
    ℓ : Level
    W X Y Z : Set ℓ
    A : X → Set ℓ
    w x y z : X

  inv-inv-id : (p : x ≡ y) → (p ⁻¹) ⁻¹ ≡ p
  inv-inv-id refl = refl

  ·-l-unit : (p : x ≡ y) → refl · p ≡ p
  ·-l-unit refl = refl

  ·-r-unit : (p : x ≡ y) → p · refl ≡ p
  ·-r-unit p = refl

  ·-l-inv : (p : x ≡ y) → (p ⁻¹) · p ≡ refl
  ·-l-inv refl = refl

  ·-r-inv : (p : x ≡ y) → p · (p ⁻¹) ≡ refl
  ·-r-inv refl = refl

  ·-inv-swap : (p : x ≡ y) → (q : y ≡ z) → (p · q) ⁻¹ ≡ (q ⁻¹) · (p ⁻¹)
  ·-inv-swap p refl = ·-l-unit (p ⁻¹) ⁻¹

  ·-assoc : (p : w ≡ x) → (q : x ≡ y) → (r : y ≡ z) →
            (p · q) · r ≡ p · (q · r)
  ·-assoc refl refl refl = refl

  ap-· : (f : X → Y) → (p : x ≡ y) → (q : y ≡ z) →
         ap f (p · q) ≡ (ap f p) · (ap f q)
  ap-· f p refl = refl

  ap-∘ : (f : Y → Z) → (g : X → Y) → (p : x ≡ y) →
         ap f (ap g p) ≡ ap (f ∘ g) p
  ap-∘ f g refl = refl

  ap-id : (p : x ≡ y) → ap id p ≡ p
  ap-id refl = refl

  ap-inv : (f : X → Y) → (p : x ≡ y) → (ap f p ⁻¹) ≡ ap f (p ⁻¹)
  ap-inv f refl = refl

  transport-· : (p : x ≡ y) → (q : y ≡ z) → (a : A x) →
                transport A (p · q) a ≡ transport A q (transport A p a)
  transport-· p refl a = refl

  transport-≡-l : (p : x ≡ y) → (q : x ≡ z) →
                  transport (λ w → w ≡ z) p q ≡ (p ⁻¹) · q
  transport-≡-l refl q = ·-l-unit q ⁻¹

  transport-≡-r : (p : x ≡ y) → (q : w ≡ x) →
                  transport (λ z → w ≡ z) p q ≡ q · p
  transport-≡-r refl q = refl

  transport-≡-b : (p : x ≡ y) → (q : x ≡ x) →
                  transport (λ w → w ≡ w) p q ≡ (p ⁻¹) · q · p
  transport-≡-b refl q = ·-l-unit q ⁻¹

  transport-d : {x y : W} → (f : W → X) → (p : x ≡ y) → (a : A (f x)) →
                transport (A ∘ f) p a ≡ transport A (ap f p) a
  transport-d f refl a = refl

  paths-r-cancel : (p q : x ≡ y) → (r : y ≡ z) → (p · r) ≡ (q · r) → p ≡ q
  paths-r-cancel p q r ϕ = p               ≡⟨ ap (p ·_) (·-r-inv r) ⁻¹ ⟩
                           p · r · (r ⁻¹)   ≡⟨ ·-assoc p r (r ⁻¹) ⁻¹ ⟩
                           (p · r) · (r ⁻¹) ≡⟨ ap (_· (r ⁻¹)) ϕ ⟩
                           (q · r) · (r ⁻¹) ≡⟨ ·-assoc q r (r ⁻¹) ⟩
                           q · r · (r ⁻¹)   ≡⟨ ap (q ·_) (·-r-inv r) ⟩
                           q               ∎

  paths-l-cancel : (r : x ≡ y) → (p q : y ≡ z) → (r · p) ≡ (r · q) → p ≡ q
  paths-l-cancel r p q ϕ = p                ≡⟨ ·-l-unit p ⁻¹ ⟩
                           refl · p         ≡⟨ ap (_· p) (·-l-inv r) ⁻¹ ⟩
                           ((r ⁻¹) · r) · p ≡⟨ ·-assoc (r ⁻¹) r p ⟩
                           (r ⁻¹) · (r · p) ≡⟨ ap ((r ⁻¹) ·_) ϕ ⟩
                           (r ⁻¹) · (r · q) ≡⟨ ·-assoc (r ⁻¹) r q ⁻¹ ⟩
                           ((r ⁻¹) · r) · q ≡⟨ ap (_· q) (·-l-inv r) ⟩
                           refl · q         ≡⟨ ·-l-unit q ⟩
                           q                ∎
