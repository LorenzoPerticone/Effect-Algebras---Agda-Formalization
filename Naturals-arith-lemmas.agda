{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Naturals-arith-lemmas where
  open import Naturals
  open import Naturals-arith
  open import Equalities

  +-l-unit : (n : ℕ) → zero + n ≡ n
  +-l-unit n = refl

  +-r-unit : (n : ℕ) → n + zero ≡ n
  +-r-unit zero     = refl
  +-r-unit (succ n) = ap succ (+-r-unit n)

  +-assoc : (l m n : ℕ) → (l + m) + n ≡ l + (m + n)
  +-assoc zero m n     = refl
  +-assoc (succ l) m n = ap succ (+-assoc l m n)

  +-l-succ : (m n : ℕ) → (succ m) + n ≡ succ (m + n)
  +-l-succ m n = refl

  +-r-succ : (m n : ℕ) → m + (succ n) ≡ succ (m + n)
  +-r-succ zero n     = refl
  +-r-succ (succ m) n = ap succ (+-r-succ m n)

  +-comm : (m n : ℕ) → m + n ≡ n + m
  +-comm zero     n = zero + n     ≡⟨ +-l-unit n ⟩
                      n            ≡⟨ +-r-unit n ⁻¹ ⟩
                      n + zero     ∎
  +-comm (succ m) n = (succ m) + n ≡⟨ +-l-succ m n ⟩
                      succ (m + n) ≡⟨ ap succ (+-comm m n) ⟩
                      succ (n + m) ≡⟨ +-r-succ n m ⁻¹ ⟩
                      n + (succ m) ∎

  ×-l-succ : (m n : ℕ) → (succ m) × n ≡ (m × n) + n
  ×-l-succ m n = refl

  ×-l-absorb : (n : ℕ) → zero × n ≡ zero
  ×-l-absorb n = refl

  ×-r-succ : (m n : ℕ) → m × (succ n) ≡ m + (m × n)
  ×-r-succ zero     n = zero × (succ n)           ≡⟨ ×-l-absorb (succ n) ⟩
                        zero                      ≡⟨ +-l-unit zero ⟩
                        zero + zero               ≡⟨ ap (zero +_) (×-l-absorb n) ⟩
                        zero + (zero × n)         ∎
  ×-r-succ (succ m) n = (succ m) × (succ n)       ≡⟨ ×-l-succ m (succ n) ⟩
                        (m × (succ n)) + (succ n) ≡⟨ +-r-succ (m × (succ n)) n ⟩
                        succ ((m × (succ n)) + n) ≡⟨ ap (λ k → succ (k + n)) (×-r-succ m n) ⟩
                        succ ((m + (m × n)) + n)  ≡⟨ ap succ (+-assoc m (m × n) n) ⟩
                        succ (m + ((m × n) + n))  ≡⟨ ap (λ k → succ (m + k)) (×-l-succ m n ⁻¹) ⟩
                        succ (m + ((succ m) × n)) ≡⟨ +-l-succ m ((succ m) × n) ⟩
                        (succ m) + ((succ m) × n) ∎

  ×-r-absorb : (n : ℕ) → n × zero ≡ zero
  ×-r-absorb zero     = refl
  ×-r-absorb (succ n) = (succ n) × zero   ≡⟨ ×-l-succ n zero ⟩
                        (n × zero) + zero ≡⟨ +-r-unit (n × zero) ⟩
                        n × zero          ≡⟨ ×-r-absorb n ⟩
                        zero              ∎

  ×-l-unit : (n : ℕ) → one × n ≡ n
  ×-l-unit n = refl

  ×-r-unit : (n : ℕ) → n × one ≡ n
  ×-r-unit n = n × (succ zero) ≡⟨ ×-r-succ n zero ⟩
               n + (n × zero)  ≡⟨ ap (n +_) (×-r-absorb n) ⟩
               n + zero        ≡⟨ +-r-unit n ⟩
               n               ∎

  ×-l-dist : (l m n : ℕ) → (l + m) × n ≡ (l × n) + (m × n)
  ×-l-dist zero     m n = (zero + m) × n           ≡⟨ ap (_× n) (+-l-unit m) ⟩
                          m × n                    ≡⟨ +-l-unit (m × n) ⁻¹ ⟩
                          zero + (m × n)           ≡⟨ ap (_+ (m × n)) (×-l-absorb n ⁻¹) ⟩
                          (zero × n) + (m × n)     ∎
  ×-l-dist (succ l) m n = ((succ l) + m) × n       ≡⟨ ap (_× n) (+-l-succ l m) ⟩
                          (succ (l + m) × n)       ≡⟨ ×-l-succ (l + m) n ⟩
                          ((l + m) × n) + n        ≡⟨ ap (_+ n) (×-l-dist l m n) ⟩
                          ((l × n) + (m × n)) + n  ≡⟨ +-assoc (l × n) (m × n) n ⟩
                          (l × n) + ((m × n) + n)  ≡⟨ ap ((l × n) +_) (+-comm (m × n) n) ⟩
                          (l × n) + (n + (m × n))  ≡⟨ +-assoc (l × n) n (m × n) ⁻¹ ⟩
                          ((l × n) + n) + (m × n)  ≡⟨ ap (_+ (m × n)) (×-l-succ l n ⁻¹) ⟩
                          ((succ l) × n) + (m × n) ∎

  ×-r-dist : (l m n : ℕ) → l × (m + n) ≡ (l × m) + (l × n)
  ×-r-dist zero     m n = refl
  ×-r-dist (succ l) m n = (succ l) × (m + n)              ≡⟨ ×-l-succ l (m + n) ⟩
                          (l × (m + n)) + (m + n)         ≡⟨ ap (_+ (m + n)) (×-r-dist l m n) ⟩
                          ((l × m) + (l × n)) + (m + n)   ≡⟨ +-assoc (l × m) (l × n) (m + n) ⟩
                          (l × m) + ((l × n) + (m + n))   ≡⟨ ap ((l × m) +_)
                                                                 ((l × n) + (m + n) ≡⟨ +-assoc (l × n) m n ⁻¹ ⟩
                                                                 ((l × n) + m) + n  ≡⟨ ap (_+ n) (+-comm (l × n) m) ⟩
                                                                 (m + (l × n)) + n  ≡⟨ +-assoc m (l × n) n ⟩
                                                                 m + ((l × n) + n)  ∎) ⟩
                          (l × m) + (m + ((l × n) + n))   ≡⟨ +-assoc (l × m) m ((l × n) + n) ⁻¹ ⟩
                          ((l × m) + m) + ((l × n) + n)   ≡⟨ ap (_+ ((l × n) + n)) (×-l-succ l m) ⟩
                          ((succ l) × m) + ((l × n) + n)  ≡⟨ ap ((succ l × m) +_) (×-l-succ l n) ⟩
                          ((succ l) × m) + ((succ l) × n) ∎

  ×-assoc : (l m n : ℕ) → (l × m) × n ≡ l × (m × n)
  ×-assoc zero     m n = (zero × m) × n          ≡⟨ ap (_× n) (×-l-absorb m) ⟩
                         zero × n                ≡⟨ ×-l-absorb n ⟩
                         zero                    ≡⟨ ×-l-absorb (m × n) ⁻¹ ⟩
                         zero × (m × n)          ∎
  ×-assoc (succ l) m n = ((succ l) × m) × n      ≡⟨ ap (_× n) (×-l-succ l m) ⟩
                         ((l × m) + m) × n       ≡⟨ ×-l-dist (l × m) m n ⟩
                         ((l × m) × n) + (m × n) ≡⟨ ap (_+ (m × n)) (×-assoc l m n) ⟩
                         (l × (m × n)) + (m × n) ≡⟨ ×-l-succ l (m × n) ⁻¹ ⟩
                         (succ l) × (m × n)      ∎

  ×-comm : (m n : ℕ) → m × n ≡ n × m
  ×-comm zero     n = zero × n     ≡⟨ ×-l-absorb n ⟩
                      zero         ≡⟨ ×-r-absorb n ⁻¹ ⟩
                      n × zero     ∎
  ×-comm (succ m) n = (succ m) × n ≡⟨ ×-l-succ m n ⟩
                      (m × n) + n  ≡⟨ ap (_+ n) (×-comm m n) ⟩
                      (n × m) + n  ≡⟨ +-comm (n × m) n ⟩
                      n + (n × m)  ≡⟨ ×-r-succ n m ⁻¹ ⟩
                      n × (succ m) ∎
