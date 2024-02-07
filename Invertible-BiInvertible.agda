{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Invertible-BiInvertible where
  open import Sigma
  open import Homotopies

  open import Invertibles public
  open import BiInvertibles public

  private variable
    ℓ ℓ₁ ℓ₂ : Level
    X Y : Set ℓ

  -- Invertible lemmas
  is-iso-sym : (f : X → Y) → (f-iso : is-iso f) → is-iso (iso→inv f f-iso)
  is-iso-sym f (g , (sect , retr)) = (f , (retr , sect))

  iso-sym : (X : Set ℓ₁) → (Y : Set ℓ₂) → iso X Y → iso Y X
  iso-sym X Y (f , f-iso@(g , _)) = g , is-iso-sym f f-iso

  id-iso : is-iso {X = X} id
  id-iso = id , (~refl , ~refl)

  iso-refl : iso X X
  iso-refl = id , id-iso

  -- BiInvertible lemmas
  bi-inv→sect : (f : X → Y) → is-bi-inv f → Y → X
  bi-inv→sect _ ((g , _) , _) = g
    
  bi-inv→retr : (f : X → Y) → is-bi-inv f → Y → X
  bi-inv→retr _ (_ , (h , _)) = h

  bi-inv→sect~retr : (f : X → Y) → (f-equiv : is-bi-inv f) →
                     (bi-inv→sect f f-equiv) ~ (bi-inv→retr f f-equiv)
  bi-inv→sect~retr f ((g , sect) , (h , retr)) = g        ~⟨ g ▶ retr ~⁻¹ ⟩
                                                 g ∘ f ∘ h ~⟨ sect ◀ h ⟩
                                                 h        ■

  bi-inv→inv : (f : X → Y) → is-bi-inv f → Y → X
  bi-inv→inv = bi-inv→sect

  is-iso→is-bi-inv : (f : X → Y) → is-iso f → is-bi-inv f
  is-iso→is-bi-inv f (g , (g-section , g-retract)) = (g , g-section) , (g , g-retract)

  is-bi-inv→is-iso : (f : X → Y) → is-bi-inv f → is-iso f
  is-bi-inv→is-iso f f-equiv@((g , sect) , (h , retr′)) =
    let retr : is-retract f g
        retr = f ∘ g ~⟨ f ▶ bi-inv→sect~retr f f-equiv ⟩
               f ∘ h ~⟨ retr′ ⟩
               id    ■
    in g , (sect , retr)

  bi-inv-sym : (f : X → Y) → (f-equiv : is-bi-inv f) → is-bi-inv (bi-inv→inv f f-equiv)
  bi-inv-sym f ((g , sect) , (h , retr)) =
    is-iso→is-bi-inv g (is-iso-sym f (is-bi-inv→is-iso f ((g , sect) , (h , retr))))

  iso→equiv : (X : Set ℓ₁) → (Y : Set ℓ₂) → iso X Y → equiv X Y
  iso→equiv X Y (f , f-iso) = f , is-iso→is-bi-inv f f-iso

  equiv→iso : (X : Set ℓ₁) → (Y : Set ℓ₂) → equiv X Y → iso X Y
  equiv→iso X Y (f , f-equiv) = f , is-bi-inv→is-iso f f-equiv

  id-bi-inv : is-bi-inv {X = X} id
  id-bi-inv = ((id , ~refl) , (id , ~refl))

  ≃-sym : (X : Set ℓ₁) → (Y : Set ℓ₂) → X ≃ Y → Y ≃ X
  ≃-sym X Y eqv = iso→equiv Y X (iso-sym X Y (equiv→iso X Y eqv))

