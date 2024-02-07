{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Unit where
  open import Functions public

  private variable
    ℓ : Level

  data 𝟙 : Set where
    pt : 𝟙

  𝟙-ind : (P : 𝟙 → Set ℓ) →
          P pt →
          (x : 𝟙) →
          P x
  𝟙-ind P p pt = p

  𝟙-rec : (Y : Set ℓ) →
          Y →
          𝟙 →
          Y
  𝟙-rec Y y x = 𝟙-ind (const Y) y x
