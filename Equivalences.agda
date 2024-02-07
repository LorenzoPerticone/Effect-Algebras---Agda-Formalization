{-# OPTIONS --cubical-compatible --exact-split --safe #-}

open import Funext

module Equivalences (funext-ax : ∀ {ℓ₁} {ℓ₂} {X} {A} {f} {g} → funext ℓ₁ ℓ₂ X A f g) where
  open import Sigma
  open import Pi
  open import Equalities
  open import Homotopies
  open import Truncations
  open import Invertible-BiInvertible
  open import ContrMap-HalfAdjEquiv

  open import Equalities-lemmas
  open import Sigma-lemmas
  open import Truncations-lemmas

  open import Funext-assumed funext-ax
  open import Truncations-lemmas-funext funext-ax

  private variable
    ℓ ℓ₁ ℓ₂ : Level
    X Y Z : Set ℓ
    A B : X → Set ℓ

  X-contr+Y-contr→f-equiv : (f : X → Y) → is-contr X → is-contr Y → is-bi-inv f
  X-contr+Y-contr→f-equiv f (X-c , X-C) Y-contr =
    let g y = X-c
        g-sect x = X-C x
        g-retr y = contr→prop Y-contr (f (g y)) y
    in is-iso→is-bi-inv f (g , (g-sect , g-retr))

  X-contr+f-equiv→Y-contr : (f : X → Y) → is-contr X → is-bi-inv f → is-contr Y
  X-contr+f-equiv→Y-contr f (c , C) (_ , (h , retr)) =
    let Y-c = f c
        Y-C y = f c     ≡⟨ ap f (C (h y)) ⟩
                f (h y) ≡⟨ retr y ⟩
                y       ∎
    in Y-c , Y-C

  Y-contr+f-equiv→X-contr : (f : X → Y) → is-contr Y → is-bi-inv f → is-contr X
  Y-contr+f-equiv→X-contr f (c , C) ((g , sect) , _) =
    let X-c = g c
        X-C x = g c     ≡⟨ ap g (C (f x)) ⟩
                g (f x) ≡⟨ sect x ⟩
                x       ∎
    in X-c , X-C

  X↔Y+prop→iso : (X → Y) → (Y → X) → is-prop X → is-prop Y → iso X Y
  X↔Y+prop→iso f g X-prop Y-prop =
    let sect = λ x → X-prop (g (f x)) x
        retr = λ y → Y-prop (f (g y)) y
    in f , (g , (sect , retr))

  X↔Y+prop→≃ : (X → Y) → (Y → X) → is-prop X → is-prop Y → X ≃ Y
  X↔Y+prop→≃ f g X-prop Y-prop = iso→equiv _ _ (X↔Y+prop→iso f g X-prop Y-prop)

  iso→iso-pre-comp : (f : X → Y) → is-iso f → is-iso {X = Z → X} {Y = Z → Y} (f ∘_)
  iso→iso-pre-comp f (g , (ϕ , ψ)) =
    let L h = funext1 (ϕ ◀ h)
        R h = funext1 (ψ ◀ h)
    in (g ∘_) , (L , R)

  iso→iso-post-comp : (f : X → Y) → is-iso f → is-iso {X = Y → Z} {Y = X → Z} (_∘ f)
  iso→iso-post-comp f (g , (ϕ , ψ)) =
    let L h = funext1 (h ▶ ψ)
        R h = funext1 (h ▶ ϕ)
    in (_∘ g) , (L , R)

  Π-≃→≃-Σ : (Π[ x ∈ X ], (A x ≃ B x)) → (Σ[ x ∈ X ], A x) ≃ (Σ[ x ∈ X ], B x)
  Π-≃→≃-Σ x→equiv =
    let f x = π₁ (x→equiv x)
        g x = π₁ (π₁ (π₂ (x→equiv x)))
        h x = π₁ (π₂ (π₂ (x→equiv x)))
        sect x = π₂ (π₁ (π₂ (x→equiv x)))
        retr x = π₂ (π₂ (π₂ (x→equiv x)))
        f′ = λ { (x , a) → x , f x a }
        g′ = λ { (x , b) → x , g x b }
        h′ = λ { (x , b) → x , h x b }
        sect′ = λ { (x , a) → Σ-decode (g′ (f′ (x , a))) (x , a) (refl , sect x a) }
        retr′ = λ { (x , b) → Σ-decode (f′ (h′ (x , b))) (x , b) (refl , retr x b) }
    in f′ , ((g′ , sect′) , (h′ , retr′))

  iso→contr-section : (f : X → Y) → is-iso f → is-contr (section f)
  iso→contr-section {X = X} {Y = Y} f f-iso@(g , (ϕ , ψ)) =
    let g-section : (h : _) → (h ∘ f ~ id) ≃ (h ∘ f ≡ id)
        g-section h = ≃-sym (h ∘ f ≡ id) (h ∘ f ~ id) (funap _ _ _ _ (h ∘ f) id , funext-ax)
        fact1 : (Σ[ s ∈ _ ], (s ∘ f ~ id)) ≃ fib (_∘ f) id
        fact1 = Π-≃→≃-Σ g-section
        fact2 : is-contr (fib (_∘ f) id)
        fact2 = is-hae→contr-map (_∘ f) (is-iso→is-hae (_∘ f) (iso→iso-post-comp f f-iso)) id
    in Y-contr+f-equiv→X-contr (π₁ fact1) fact2 (π₂ fact1)

  iso→contr-retract : (f : X → Y) → is-iso f → is-contr (retract f)
  iso→contr-retract f f-iso@(g , (ϕ , ψ)) =
    let g-retract : (h : _) → (f ∘ h ~ id) ≃ (f ∘ h ≡ id)
        g-retract h = ≃-sym (f ∘ h ≡ id) (f ∘ h ~ id) (funap _ _ _ _ (f ∘ h) id , funext-ax)
        fact1 : (Σ[ r ∈ _ ], (f ∘ r ~ id)) ≃ fib (f ∘_) id
        fact1 = Π-≃→≃-Σ g-retract
        fact2 : is-contr (fib (f ∘_) id)
        fact2 = is-hae→contr-map (f ∘_) (is-iso→is-hae (f ∘_) (iso→iso-pre-comp f f-iso)) id
    in Y-contr+f-equiv→X-contr (π₁ fact1) fact2 (π₂ fact1)

  prop-bi-inv : (f : X → Y) → is-prop (is-bi-inv f)
  prop-bi-inv f =
    let equiv→contr-equiv : is-bi-inv f → is-contr (is-bi-inv f)
        equiv→contr-equiv f-equiv = let f-iso = is-bi-inv→is-iso f f-equiv
                                        contr-section : is-contr (section f)
                                        contr-section = iso→contr-section f f-iso
                                        contr-retract : is-contr (retract f)
                                        contr-retract = iso→contr-retract f f-iso
                                    in ×-contr-contr contr-section contr-retract
    in contr-if-pointed→prop equiv→contr-equiv

  tot : (f : Π[ x ∈ X ], (A x → B x)) → Σ[ x ∈ X ], A x → Σ[ x ∈ X ], B x
  tot f (x , a) = x , f x a

  fib-tot-fib : (f : Π[ x ∈ X ], (A x → B x)) →
                (t : Σ[ x ∈ X ], B x) →
                fib (tot f) t ≃ fib (f (π₁ t)) (π₂ t)
  fib-tot-fib {X = X} {A = A} {B = B} f t = iso→equiv _ _ (ϕ t , (ψ t , (sect t , retr t)))
    where ϕ : (t : Σ[ x ∈ X ], B x) → fib (tot f) t → fib (f (π₁ t)) (π₂ t)
          ϕ .(tot f (x , a)) ((x , a) , refl) = a , refl
          ψ : (t : Σ[ x ∈ X ], B x) → fib (f (π₁ t)) (π₂ t) → fib (tot f) t
          ψ (x , .(f x a)) (a , refl) = (x , a) , refl
          sect : (t : Σ[ x ∈ X ], B x) → (ψ t) ∘ (ϕ t) ~ id
          sect .(tot f (x , a)) ((x , a) , refl) = refl
          retr : (t : Σ[ x ∈ X ], B x) → (ϕ t) ∘ (ψ t) ~ id
          retr (x , .(f x a)) (a , refl) = refl

  equiv→tot-equiv : (f : Π[ x ∈ X ], (A x → B x)) →
                    Π[ x ∈ X ], is-bi-inv (f x) →
                    is-bi-inv (tot f)
  equiv→tot-equiv {X = X} {A = A} {B = B} f x→equiv =
    let contr-tot : contr-map (tot f)
        contr-tot t = Y-contr+f-equiv→X-contr (π₁ (fib-tot-fib f t))
                                              (is-bi-inv→contr-map (f (π₁ t)) (x→equiv (π₁ t)) (π₂ t))
                                              (π₂ (fib-tot-fib f t))
    in contr-map→is-bi-inv (tot f) contr-tot

  prop-contr-map : {X : Set ℓ₁} {Y : Set ℓ₂} → (f : X → Y) → is-prop (contr-map f)
  prop-contr-map f = func-prop→prop-func (λ y → isProp-isContr (fib f y))

  bi-inv≃contr-map : (f : X → Y) → (is-bi-inv f) ≃ (contr-map f)
  bi-inv≃contr-map f = X↔Y+prop→≃ (is-bi-inv→contr-map f) (contr-map→is-bi-inv f) (prop-bi-inv f) (prop-contr-map f)

