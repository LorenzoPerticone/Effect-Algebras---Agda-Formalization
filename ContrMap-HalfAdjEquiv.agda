{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module ContrMap-HalfAdjEquiv where
  open import Sigma
  open import Pi
  open import Equalities
  open import Homotopies
  open import Truncations
  open import Invertible-BiInvertible

  open import Equalities-lemmas
  open import Sigma-lemmas
  
  open import TruncMaps public
  open import HalfAdjEquiv public

  private variable
    ℓ : Level
    X Y : Set ℓ
    A B : X → Set ℓ
    Γ Δ : (x : X) → A x → Set ℓ

  contr-map→is-iso : (f : X → Y) → contr-map f → is-iso f
  contr-map→is-iso f f-contr =
    let g y = π₁ (π₁ (f-contr y))
        x∈fib-f-x : (x : _) → fib f (f x)
        x∈fib-f-x x = x , refl
        contr : (x : _) → (p : fib f (f x)) → π₁ (f-contr (f x)) ≡ p
        contr x p =  π₂ (f-contr (f x)) p
        ϕ x = g (f x) ≡⟨ ap π₁ (contr x (x∈fib-f-x x)) ⟩
              x ∎
        ψ y = π₂ (π₁ (f-contr y))
    in g , (ϕ , ψ)

  contr-map→is-bi-inv : (f : X → Y) → contr-map f → is-bi-inv f
  contr-map→is-bi-inv f f-contr = is-iso→is-bi-inv f (contr-map→is-iso f f-contr)

  is-hae-sym : (f : X → Y) → (f-hae : is-hae f) → is-hae (π₁ f-hae)
  is-hae-sym f (g , (ϕ , (ψ , G))) =
    let lemma y = ap (g ∘ f ∘ g) (ψ y) · ap g (ψ y)     ≡⟨ ap (_· ap g (ψ y)) (ap-∘ g (f ∘ g) (ψ y) ⁻¹) ⟩
                  ap g (ap (f ∘ g) (ψ y)) · ap g (ψ y) ≡⟨ ap-· g (ap (f ∘ g) (ψ y)) (ψ y) ⁻¹ ⟩
                  ap g (ap (f ∘ g) (ψ y) · (ψ y))      ≡⟨ ap (λ p → ap g (p · ψ y)) (~-whisk-comm (f ∘ g) ψ y ⁻¹) ⟩
                  ap g (ψ (f (g y)) · ψ y)             ≡⟨ ap-· g (ψ (f (g y))) (ψ y) ⟩
                  ap g (ψ (f (g y))) · ap g (ψ y)      ≡⟨ ap (λ p → ap g p · ap g (ψ y)) (G (g y) ⁻¹) ⟩
                  ap g (ap f (ϕ (g y))) · ap g (ψ y)   ≡⟨ ap (_· ap g (ψ y)) (ap-∘ g f (ϕ (g y))) ⟩
                  ap (g ∘ f) (ϕ (g y)) · ap g (ψ y)    ≡⟨ ap (_· ap g (ψ y)) (~-whisk-comm (g ∘ f) ϕ (g y) ⁻¹) ⟩
                  ϕ (g (f (g y))) · ap g (ψ y)         ≡⟨ ap (ϕ (g (f (g y))) ·_) (ap-id (ap g (ψ y))) ⁻¹ ⟩
                  ϕ (g (f (g y))) · ap id (ap g (ψ y)) ≡⟨ ~-natural (g ∘ f) id ϕ (g (f (g y))) (g y) (ap g (ψ y)) ⟩
                  ap (g ∘ f) (ap g (ψ y)) · ϕ (g y)    ≡⟨ ap (_· ϕ (g y)) (ap-∘ (g ∘ f) g (ψ y)) ⟩
                  ap (g ∘ f ∘ g) (ψ y) · ϕ (g y)        ∎
        H : g ▶ ψ ~ ϕ ◀ g
        H y = ap g (ψ y) ≡⟨ paths-l-cancel (ap (g ∘ f ∘ g) (ψ y)) (ap g (ψ y)) (ϕ (g y)) (lemma y) ⟩
              ϕ (g y)    ∎
    in f , (ψ , (ϕ ,  H))

  is-hae→is-iso : (f : X → Y) → is-hae f → is-iso f
  is-hae→is-iso f (g , (ϕ , (ψ , H))) = (g , (ϕ , ψ))

  is-hae→is-bi-inv : (f : X → Y) → is-hae f → is-bi-inv f
  is-hae→is-bi-inv f f-hae = is-iso→is-bi-inv f (is-hae→is-iso f f-hae)

  is-hae→contr-map : (f : X → Y) → is-hae f → contr-map f
  is-hae→contr-map f (g , (ϕ , (ψ , H))) =
    λ y → ((g y) , (ψ y)) ,
          (λ { (x , refl) → Σ-decode (g (f x) , ψ (f x))
                                     (x , refl)
                                     (ϕ x ,
                                      (transport (λ v → f v ≡ f x) (ϕ x) (ψ (f x))      ≡⟨ transport-d f (ϕ x) (ψ (f x)) ⟩
                                       transport (λ u → u ≡ f x) (ap f (ϕ x)) (ψ (f x)) ≡⟨ transport-≡-l (ap f (ϕ x)) (ψ (f x)) ⟩
                                       (ap f (ϕ x) ⁻¹) · (ψ (f x))                       ≡⟨ ap (λ p → (p ⁻¹) · ψ (f x)) (H x) ⟩
                                       (ψ (f x) ⁻¹) · (ψ (f x))                          ≡⟨ ·-l-inv (ψ (f x)) ⟩
                                       refl                                             ∎)) } )

  is-iso→is-hae : (f : X → Y) → is-iso f → is-hae f
  is-iso→is-hae f (g , (ϕ , ψ)) =
    let ψ′ = (ψ ◀ (f ∘ g) ~⁻¹) ~· (f ▶ ϕ ◀ g) ~· ψ
        H x = ap f (ϕ x)                                                 ≡⟨ ·-l-unit (ap f (ϕ x)) ⁻¹ ⟩
              refl · ap f (ϕ x)                                          ≡⟨ ap (_· ap f (ϕ x)) (·-l-inv (ψ (f (g (f x)))) ⁻¹) ⟩
              ((ψ (f (g (f x))) ⁻¹) · ψ (f (g (f x)))) · ap f (ϕ x)      ≡⟨ ·-assoc (ψ (f (g (f x))) ⁻¹) (ψ (f (g (f x)))) (ap f (ϕ x)) ⟩
              (ψ (f (g (f x))) ⁻¹) · ψ (f (g (f x))) · ap f (ϕ x)        ≡⟨ ap ((ψ (f (g (f x))) ⁻¹) ·_) (~-natural (f ∘ g ∘ f) f (ψ ◀ f) (g (f x)) x (ϕ x)) ⟩
              (ψ (f (g (f x))) ⁻¹) · (ap (f ∘ g ∘ f) (ϕ x)) · ψ (f x)     ≡⟨ ap (λ p → (ψ (f (g (f x))) ⁻¹) · (p · ψ (f x))) (ap-∘ f (g ∘ f) (ϕ x)) ⁻¹ ⟩
              (ψ (f (g (f x))) ⁻¹) · (ap f (ap (g ∘ f) (ϕ x))) · ψ (f x) ≡⟨ ap (λ p → (ψ (f (g (f x))) ⁻¹) · (ap f p) · ψ (f x)) (~-whisk-comm (g ∘ f) ϕ x) ⁻¹ ⟩
              (ψ (f (g (f x))) ⁻¹) · (ap f (ϕ (g (f x)))) · ψ (f x)      ≡⟨ refl ⟩
              ψ′ (f x)                                                   ∎
    in g , (ϕ , (ψ′ , H))

  is-bi-inv→is-hae : (f : X → Y) → is-bi-inv f → is-hae f
  is-bi-inv→is-hae f f-equiv = is-iso→is-hae f (is-bi-inv→is-iso f f-equiv)

  is-bi-inv→contr-map : (f : X → Y) → is-bi-inv f → contr-map f
  is-bi-inv→contr-map f f-equiv = is-hae→contr-map f (is-bi-inv→is-hae f f-equiv)
