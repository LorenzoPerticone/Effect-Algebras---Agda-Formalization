{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Truncations-lemmas where
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

  private variable
    ℓ : Level
    X Y Z : Set ℓ
    A B : X → Set ℓ

  𝟙-contr : is-contr 𝟙
  𝟙-contr = pt , λ { pt → refl }

  𝟘-prop : is-prop 𝟘
  𝟘-prop = 𝟘-ind (λ x → (y : 𝟘) → x ≡ y)

  singleton : (x : X) → is-contr (Σ[ y ∈ X ], x ≡ y)
  singleton x = (x , refl) , λ { (.x , refl) → refl }

  contr→prop′ : is-contr X → is-prop′ X
  contr→prop′ (c , C) x y =
    let c′ : x ≡ y
        c′ = x ≡⟨ C x ⁻¹ ⟩
             c ≡⟨ C y ⟩
             y ∎
        C′ : Π[ p ∈ (x ≡ y) ], c′ ≡ p
        C′ = λ { refl → (C x ⁻¹) · C x ≡⟨ ·-l-inv (C x) ⟩
                        refl ∎ }
    in c′ , C′

  pointed-prop→contr : X → is-prop X → is-contr X
  pointed-prop→contr x X-prop = x , (X-prop x)

  contr-if-pointed→prop : (X → is-contr X) → is-prop X
  contr-if-pointed→prop x→contr x y =
    let c = π₁ (x→contr x)
        C = π₂ (x→contr x)
    in x ≡⟨ C x ⁻¹ ⟩
       c ≡⟨ C y ⟩
       y ∎

  prop′→prop : is-prop′ X → is-prop X
  prop′→prop X-prop′ = λ x y → π₁ (X-prop′ x y)

  contr→prop : is-contr X → is-prop X
  contr→prop X-contr = prop′→prop (contr→prop′ X-contr)

  trunc→trunc-succ : (X : Set ℓ) → (n : TruncLevel) → is n trunc X → is (succ n) trunc X
  trunc→trunc-succ X neg2     X-contr = contr→prop′ X-contr
  trunc→trunc-succ X (succ n) X-trunc = λ x y → trunc→trunc-succ (x ≡ y) n (X-trunc x y)
  
  prop→prop′ : is-prop X → is-prop′ X
  prop→prop′ {X = X} X-prop x y = c x y , C x y
    where c : (x y : X) → x ≡ y
          c a b = a ≡⟨ X-prop a x ⟩
                  x ≡⟨ X-prop b x ⁻¹ ⟩
                  b ∎
          C : (a b : X) → (p : a ≡ b) → (c a b) ≡ p
          C a .a refl = (X-prop a x) · (X-prop a x ⁻¹) ≡⟨ ·-r-inv (X-prop a x) ⟩
                        refl ∎

  prop→set : is-prop X → is-set X
  prop→set X-prop = λ x y → contr→prop (prop→prop′ X-prop x y)

  ntype→ntype-succ : (X : Set ℓ) → (n : TruncLevel) → is n type X → is (succ n) type X
  ntype→ntype-succ X neg2            X-contr = contr→prop X-contr
  ntype→ntype-succ X (succ neg2)     X-prop  = prop→set X-prop
  ntype→ntype-succ X (succ (succ n)) X-trunc = λ x y → ntype→ntype-succ (x ≡ y) (succ n) (X-trunc x y)

  ×-contr-contr : is-contr X → is-contr Y → is-contr (X × Y)
  ×-contr-contr (x , X-contr) (y , Y-contr) = (x , y) , (λ { (x′ , y′) → ×-decode (x , y) (x′ , y′) (X-contr x′ , Y-contr y′) } )

  ×-prop-prop : is-prop X → is-prop Y → is-prop (X × Y)
  ×-prop-prop X-prop Y-prop (x₁ , y₁) (x₂ , y₂) = ×-decode (x₁ , y₁) (x₂ , y₂) ((X-prop x₁ x₂) , (Y-prop y₁ y₂))

  ×-set-set : is-set X → is-set Y → is-set (X × Y)
  ×-set-set {X = X} {Y = Y} X-set Y-set (x₁ , y₁) (x₂ , y₂) p q =
    let p₁ = ap π₁ p
        p₂ = ap π₂ p
        q₁ = ap π₁ q
        q₂ = ap π₂ q
        π12≡encode : (a b : X × Y) → (r : a ≡ b) → ×-encode a b r ≡ (ap π₁ r , ap π₂ r)
        π12≡encode = λ { (x , y) .(x , y) refl → refl }
        1≡1 : p₁ ≡ q₁
        1≡1 = X-set x₁ x₂ p₁ q₁
        2≡2 : p₂ ≡ q₂
        2≡2 = Y-set y₁ y₂ p₂ q₂
        p12≡q12 : (p₁ , p₂) ≡ (q₁ , q₂)
        p12≡q12 = ×-decode (p₁ , p₂) (q₁ , q₂) (1≡1 , 2≡2)
        decode-p≡q : (×-decode (x₁ , y₁) (x₂ , y₂) (p₁ , p₂)) ≡ (×-decode (x₁ , y₁) (x₂ , y₂) (q₁ , q₂))
        decode-p≡q = ap (×-decode (x₁ , y₁) (x₂ , y₂)) p12≡q12
    in p                                                             ≡⟨ ×-encode-decode-section (x₁ , y₁) (x₂ , y₂) p ⁻¹ ⟩
       ×-decode (x₁ , y₁) (x₂ , y₂) (×-encode (x₁ , y₁) (x₂ , y₂) p) ≡⟨ ap (×-decode (x₁ , y₁) (x₂ , y₂)) (π12≡encode (x₁ , y₁) (x₂ , y₂) p) ⟩
       ×-decode (x₁ , y₁) (x₂ , y₂) (p₁ , p₂)                        ≡⟨ decode-p≡q ⟩
       ×-decode (x₁ , y₁) (x₂ , y₂) (q₁ , q₂)                        ≡⟨ ap (×-decode (x₁ , y₁) (x₂ , y₂)) (π12≡encode (x₁ , y₁) (x₂ , y₂) q) ⁻¹ ⟩
       ×-decode (x₁ , y₁) (x₂ , y₂) (×-encode (x₁ , y₁) (x₂ , y₂) q) ≡⟨ ×-encode-decode-section (x₁ , y₁) (x₂ , y₂) q ⟩
       q                                                             ∎
