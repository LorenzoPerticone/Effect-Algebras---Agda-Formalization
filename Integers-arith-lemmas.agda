{-# OPTIONS --cubical-compatible --exact-split --safe #-}

module Integers-arith-lemmas where
  open import Naturals renaming (zero to ℕ-zero; succ to ℕ-succ)
  open import Integers
  open import Integers-arith
  open import Equalities

  succ-pred : (n : ℤ) → succ (pred n) ≡ n
  succ-pred zero             = refl
  succ-pred (pls ℕ-zero)     = refl
  succ-pred (pls (ℕ-succ n)) = refl
  succ-pred (mns n)          = refl

  pred-succ : (n : ℤ) → pred (succ n) ≡ n
  pred-succ zero             = refl
  pred-succ (pls n)          = refl
  pred-succ (mns ℕ-zero)     = refl
  pred-succ (mns (ℕ-succ n)) = refl

  succ-zero≡pls1 : succ zero ≡ pls1
  succ-zero≡pls1 = refl

  pred-zero≡mns1 : pred zero ≡ mns1
  pred-zero≡mns1 = refl

  neg-pls1≡mns1 : neg pls1 ≡ mns1
  neg-pls1≡mns1 = neg (pls ℕ-zero) ≡⟨ refl ⟩
                  mns ℕ-zero ∎

  neg-mns1≡pls1 : neg mns1 ≡ pls1
  neg-mns1≡pls1 = neg (mns ℕ-zero) ≡⟨ refl ⟩
                  pls ℕ-zero ∎

  neg-succ-pred-neg : (n : ℤ) → neg (succ n) ≡ pred (neg n)
  neg-succ-pred-neg zero             = refl
  neg-succ-pred-neg (pls ℕ-zero)     = refl
  neg-succ-pred-neg (pls (ℕ-succ n)) = refl
  neg-succ-pred-neg (mns ℕ-zero)     = refl
  neg-succ-pred-neg (mns (ℕ-succ n)) = refl
    
  neg-pred-succ-neg : (n : ℤ) → neg (pred n) ≡ succ (neg n)
  neg-pred-succ-neg zero             = refl
  neg-pred-succ-neg (pls ℕ-zero)     = refl
  neg-pred-succ-neg (pls (ℕ-succ n)) = refl
  neg-pred-succ-neg (mns ℕ-zero)     = refl
  neg-pred-succ-neg (mns (ℕ-succ n)) = refl

  neg-neg : (n : ℤ) → neg (neg n) ≡ n
  neg-neg zero             = refl
  neg-neg (pls ℕ-zero)     = refl
  neg-neg (pls (ℕ-succ n)) = neg (neg (succ (pls n))) ≡⟨ ap neg (neg-succ-pred-neg (pls n)) ⟩
                             neg (pred (neg (pls n))) ≡⟨ neg-pred-succ-neg (neg (pls n)) ⟩
                             succ (neg (neg (pls n))) ≡⟨ ap succ (neg-neg (pls n)) ⟩
                             succ (pls n)             ∎
  neg-neg (mns ℕ-zero)     = refl
  neg-neg (mns (ℕ-succ n)) = neg (neg (pred (mns n))) ≡⟨ ap neg (neg-pred-succ-neg (mns n)) ⟩
                             neg (succ (neg (mns n))) ≡⟨ neg-succ-pred-neg (neg (mns n)) ⟩
                             pred (neg (neg (mns n))) ≡⟨ ap pred (neg-neg (mns n)) ⟩
                             pred (mns n)             ∎

  +-l-succ : (m n : ℤ) → (succ m) + n ≡ succ (m + n)
  +-l-succ zero             n = refl
  +-l-succ (pls m)          n = refl
  +-l-succ (mns ℕ-zero)     n = succ-pred n ⁻¹
  +-l-succ (mns (ℕ-succ m)) n = succ-pred (mns m + n) ⁻¹
    
  +-r-succ : (m n : ℤ) → m + (succ n) ≡ succ (m + n)
  +-r-succ zero             n = refl
  +-r-succ (pls ℕ-zero)     n = refl
  +-r-succ (pls (ℕ-succ m)) n = ap succ (+-r-succ (pls m) n)
  +-r-succ (mns ℕ-zero)     n = pred (succ n)           ≡⟨ pred-succ n ⟩
                                n                       ≡⟨ succ-pred n ⁻¹ ⟩
                                succ (pred n)           ∎
  +-r-succ (mns (ℕ-succ m)) n = pred (mns m + succ n)   ≡⟨ ap pred (+-r-succ (mns m) n) ⟩
                                pred (succ (mns m + n)) ≡⟨ pred-succ (mns m + n) ⟩
                                mns m + n               ≡⟨ succ-pred (mns m + n) ⁻¹ ⟩
                                succ (pred (mns m + n)) ∎
    
  +-l-pred : (m n : ℤ) → (pred m) + n ≡ pred (m + n)
  +-l-pred zero    n          = refl
  +-l-pred (pls ℕ-zero) n     = pred-succ n ⁻¹
  +-l-pred (pls (ℕ-succ m)) n = pred-succ (pls m + n) ⁻¹
  +-l-pred (mns m) n          = refl
    
  +-r-pred : (m n : ℤ) → m + (pred n) ≡ pred (m + n)
  +-r-pred zero             n = refl
  +-r-pred (pls ℕ-zero)     n = succ (pred n)           ≡⟨ succ-pred n ⟩
                                n                       ≡⟨ pred-succ n ⁻¹ ⟩
                                pred (succ n)           ∎
  +-r-pred (pls (ℕ-succ m)) n = succ (pls m + pred n)   ≡⟨ ap succ (+-r-pred (pls m) n) ⟩
                                succ (pred (pls m + n)) ≡⟨ succ-pred (pls m + n) ⟩
                                pls m + n               ≡⟨ pred-succ (pls m + n) ⁻¹ ⟩
                                pred (succ (pls m + n)) ∎
  +-r-pred (mns ℕ-zero)     n = refl
  +-r-pred (mns (ℕ-succ m)) n = ap pred (+-r-pred (mns m) n)

  +-l-unit : (n : ℤ) → zero + n ≡ n
  +-l-unit n = refl
  
  +-r-unit : (n : ℤ) → n + zero ≡ n
  +-r-unit zero             = refl
  +-r-unit (pls ℕ-zero)     = refl
  +-r-unit (pls (ℕ-succ n)) = ap succ (+-r-unit (pls n))
  +-r-unit (mns ℕ-zero)     = refl
  +-r-unit (mns (ℕ-succ n)) = ap pred (+-r-unit (mns n))

  neg-+ : (m n : ℤ) → neg (m + n) ≡ neg m + neg n
  neg-+ zero             n = neg (zero + n)             ≡⟨ ap neg (+-l-unit n) ⟩
                             neg n                      ≡⟨ +-l-unit (neg n) ⁻¹ ⟩
                             zero + neg n               ≡⟨ refl ⟩
                             neg zero + neg n           ∎
  neg-+ (pls ℕ-zero)     n = neg (pls1 + n)             ≡⟨ refl ⟩
                             neg (succ n)               ≡⟨ neg-succ-pred-neg n ⟩
                             pred (neg n)               ≡⟨ refl ⟩
                             mns1 + neg n               ≡⟨ refl ⟩
                             neg pls1 + neg n           ∎
  neg-+ (pls (ℕ-succ m)) n = neg (succ (pls m) + n)     ≡⟨ ap neg (+-l-succ (pls m) n) ⟩
                             neg (succ (pls m + n))     ≡⟨ neg-succ-pred-neg (pls m + n) ⟩
                             pred (neg (pls m + n))     ≡⟨ ap pred (neg-+ (pls m) n) ⟩
                             pred (neg (pls m) + neg n) ≡⟨ +-l-pred (neg (pls m)) (neg n) ⁻¹ ⟩
                             pred (neg (pls m)) + neg n ≡⟨ ap (_+ neg n) (neg-succ-pred-neg (pls m)) ⁻¹ ⟩
                             neg (succ (pls m)) + neg n ∎
  neg-+ (mns ℕ-zero)     n = neg (mns1 + n)             ≡⟨ refl ⟩
                             neg (pred n)               ≡⟨ neg-pred-succ-neg n ⟩
                             succ (neg n)               ≡⟨ refl ⟩
                             pls1 + neg n               ≡⟨ refl ⟩
                             neg mns1 + neg n           ∎
  neg-+ (mns (ℕ-succ m)) n = neg (pred (mns m) + n)     ≡⟨ ap neg (+-l-pred (mns m) n) ⟩
                             neg (pred (mns m + n))     ≡⟨ neg-pred-succ-neg (mns m + n) ⟩
                             succ (neg (mns m + n))     ≡⟨ ap succ (neg-+ (mns m) n) ⟩
                             succ (neg (mns m) + neg n) ≡⟨ +-l-succ (neg (mns m)) (neg n) ⁻¹ ⟩
                             succ (neg (mns m)) + neg n ≡⟨ ap (_+ neg n) (neg-pred-succ-neg (mns m)) ⁻¹ ⟩
                             neg (pred (mns m)) + neg n ∎

  +-l-inv : (n : ℤ) → (neg n) + n ≡ zero
  +-l-inv zero             = refl
  +-l-inv (pls ℕ-zero)     = refl
  +-l-inv (pls (ℕ-succ n)) = (pred (mns n)) + (succ (pls n)) ≡⟨ +-l-pred (mns n) (succ (pls n)) ⟩
                             pred (mns n + succ (pls n))     ≡⟨ ap pred (+-r-succ (mns n) (pls n)) ⟩
                             pred (succ (mns n + pls n))     ≡⟨ pred-succ (mns n + pls n) ⟩
                             mns n + pls n                   ≡⟨ +-l-inv (pls n) ⟩
                             zero                            ∎
  +-l-inv (mns ℕ-zero)     = refl
  +-l-inv (mns (ℕ-succ n)) = (succ (pls n)) + (pred (mns n)) ≡⟨ +-l-succ (pls n) (pred (mns n)) ⟩
                             succ (pls n + pred (mns n))     ≡⟨ ap succ (+-r-pred (pls n) (mns n)) ⟩
                             succ (pred (pls n + mns n))     ≡⟨ succ-pred (pls n + mns n) ⟩
                             pls n + mns n                   ≡⟨ +-l-inv (mns n) ⟩
                             zero                            ∎
  
  +-r-inv : (n : ℤ) → n + (neg n) ≡ zero
  +-r-inv zero             = refl
  +-r-inv (pls ℕ-zero)     = refl
  +-r-inv (pls (ℕ-succ n)) = (succ (pls n)) + (pred (mns n)) ≡⟨ +-l-succ (pls n) (pred (mns n)) ⟩
                             succ (pls n + pred (mns n))     ≡⟨ ap succ (+-r-pred (pls n) (mns n)) ⟩
                             succ (pred (pls n + mns n))     ≡⟨ succ-pred (pls n + mns n) ⟩
                             pls n + mns n                   ≡⟨ +-r-inv (pls n) ⟩
                             zero                            ∎
  +-r-inv (mns ℕ-zero)     = refl
  +-r-inv (mns (ℕ-succ n)) = (pred (mns n)) + (succ (pls n)) ≡⟨ +-l-pred (mns n) (succ (pls n)) ⟩
                             pred (mns n + succ (pls n))     ≡⟨ ap pred (+-r-succ (mns n) (pls n)) ⟩
                             pred (succ (mns n + pls n))     ≡⟨ pred-succ (mns n + pls n) ⟩
                             mns n + pls n                   ≡⟨ +-r-inv (mns n) ⟩
                             zero                            ∎
    
  +-assoc : (l m n : ℤ) → (l + m) + n ≡ l + (m + n)
  +-assoc zero             m n = (zero + m) + n         ≡⟨ ap (_+ n) (+-l-unit m) ⟩
                                 m + n                  ≡⟨ +-l-unit (m + n) ⟩
                                 zero + (m + n)         ∎
  +-assoc (pls ℕ-zero)     m n = (succ m) + n           ≡⟨ +-l-succ m n ⟩
                                 succ (m + n)           ∎
  +-assoc (pls (ℕ-succ l)) m n = (succ (pls l) + m) + n ≡⟨ ap (_+ n) (+-l-succ (pls l) m) ⟩
                                 succ (pls l + m) + n   ≡⟨ +-l-succ (pls l + m) n ⟩
                                 succ ((pls l + m) + n) ≡⟨ ap succ (+-assoc (pls l) m n) ⟩
                                 succ (pls l + (m + n)) ≡⟨ +-l-succ (pls l) (m + n) ⁻¹ ⟩
                                 succ (pls l) + (m + n) ∎
  +-assoc (mns ℕ-zero)     m n = (pred m) + n           ≡⟨ +-l-pred m n ⟩
                                 pred (m + n)           ∎
  +-assoc (mns (ℕ-succ l)) m n = (pred (mns l) + m) + n ≡⟨ ap (_+ n) (+-l-pred (mns l) m) ⟩
                                 pred (mns l + m) + n   ≡⟨ +-l-pred (mns l + m) n ⟩
                                 pred ((mns l + m) + n) ≡⟨ ap pred (+-assoc (mns l) m n) ⟩
                                 pred (mns l + (m + n)) ≡⟨ +-l-pred (mns l) (m + n) ⁻¹ ⟩
                                 pred (mns l) + (m + n) ∎
    
  +-comm : (m n : ℤ) → m + n ≡ n + m
  +-comm zero             n = zero + n         ≡⟨ +-l-unit n ⟩
                              n                ≡⟨ +-r-unit n ⁻¹ ⟩
                              n + zero         ∎
  +-comm (pls ℕ-zero)     n = (succ zero) + n  ≡⟨ +-l-succ zero n ⟩
                              succ (zero + n)  ≡⟨ ap succ (+-l-unit n) ⟩
                              succ n           ≡⟨ ap succ (+-r-unit n) ⁻¹ ⟩
                              succ (n + zero)  ≡⟨ +-r-succ n zero ⁻¹ ⟩
                              n + (succ zero)  ∎
  +-comm (pls (ℕ-succ l)) n = succ (pls l) + n ≡⟨ +-l-succ (pls l) n ⟩
                              succ (pls l + n) ≡⟨ ap succ (+-comm (pls l) n) ⟩
                              succ (n + pls l) ≡⟨ +-r-succ n (pls l) ⁻¹ ⟩
                              n + succ (pls l) ∎
  +-comm (mns ℕ-zero)     n = (pred zero) + n  ≡⟨ +-l-pred zero n ⟩
                              pred (zero + n)  ≡⟨ ap pred (+-l-unit n) ⟩
                              pred n           ≡⟨ ap pred (+-r-unit n) ⁻¹ ⟩
                              pred (n + zero)  ≡⟨ +-r-pred n zero ⁻¹ ⟩
                              n + (pred zero)  ∎
  +-comm (mns (ℕ-succ l)) n = pred (mns l) + n ≡⟨ +-l-pred (mns l) n ⟩
                              pred (mns l + n) ≡⟨ ap pred (+-comm (mns l) n) ⟩
                              pred (n + mns l) ≡⟨ +-r-pred n (mns l) ⁻¹ ⟩
                              n + pred (mns l) ∎

  +-pls1-succ : (n : ℤ) → n + pls1 ≡ succ n
  +-pls1-succ zero             = refl
  +-pls1-succ (pls ℕ-zero)     = refl
  +-pls1-succ (pls (ℕ-succ n)) = succ (pls n) + pls1 ≡⟨ +-l-succ (pls n) pls1 ⟩
                                 succ (pls n + pls1) ≡⟨ ap succ (+-pls1-succ (pls n)) ⟩
                                 succ (succ (pls n)) ∎
  +-pls1-succ (mns ℕ-zero)     = refl
  +-pls1-succ (mns (ℕ-succ n)) = pred (mns n) + pls1 ≡⟨ +-l-pred (mns n) pls1 ⟩
                                 pred (mns n + pls1) ≡⟨ ap pred (+-pls1-succ (mns n)) ⟩
                                 pred (succ (mns n)) ≡⟨ pred-succ (mns n) ⟩
                                 mns n               ≡⟨ succ-pred (mns n) ⁻¹ ⟩
                                 succ (pred (mns n)) ∎

  +-mns1-pred : (n : ℤ) → n + mns1 ≡ pred n
  +-mns1-pred zero             = refl
  +-mns1-pred (pls ℕ-zero)     = refl
  +-mns1-pred (pls (ℕ-succ n)) = succ (pls n) + mns1 ≡⟨ +-l-succ (pls n) mns1 ⟩
                                 succ (pls n + mns1) ≡⟨ ap succ (+-mns1-pred (pls n)) ⟩
                                 succ (pred (pls n)) ≡⟨ succ-pred (pls n) ⟩
                                 pls n               ≡⟨ pred-succ (pls n) ⁻¹ ⟩
                                 pred (succ (pls n)) ∎
  +-mns1-pred (mns ℕ-zero)     = refl
  +-mns1-pred (mns (ℕ-succ n)) = pred (mns n) + mns1 ≡⟨ +-l-pred (mns n) mns1 ⟩
                                 pred (mns n + mns1) ≡⟨ ap pred (+-mns1-pred (mns n)) ⟩
                                 pred (pred (mns n)) ∎

  -pls1-pred : (n : ℤ) → n - pls1 ≡ pred n
  -pls1-pred n = n + mns1 ≡⟨ +-mns1-pred n ⟩
                 pred n   ∎

  -mns1-succ : (n : ℤ) → n - mns1 ≡ succ n
  -mns1-succ n = n + pls1 ≡⟨ +-pls1-succ n ⟩
                 succ n   ∎

  ×-l-absorb : (n : ℤ) → zero × n ≡ zero
  ×-l-absorb n = refl
  
  ×-r-absorb : (n : ℤ) → n × zero ≡ zero
  ×-r-absorb zero             = zero × zero           ≡⟨ ×-l-absorb zero ⟩
                                zero                  ∎
  ×-r-absorb (pls ℕ-zero)     = pls1 × zero           ≡⟨ refl ⟩
                                succ (zero) × zero    ≡⟨ refl ⟩
                                (zero × zero) + zero  ≡⟨ +-r-unit (zero × zero) ⟩
                                zero × zero           ≡⟨ ×-l-absorb zero ⟩
                                zero                  ∎
  ×-r-absorb (pls (ℕ-succ n)) = (pls n × zero) + zero ≡⟨ +-r-unit (pls n × zero) ⟩
                                pls n × zero          ≡⟨ ×-r-absorb (pls n) ⟩
                                zero                  ∎
  ×-r-absorb (mns ℕ-zero)     = mns1 × zero           ≡⟨ refl ⟩
                                pred (zero) × zero    ≡⟨ refl ⟩
                                (zero × zero) - zero  ≡⟨ refl ⟩
                                (zero × zero) + zero  ≡⟨ +-r-unit (zero × zero) ⟩
                                zero × zero           ≡⟨ ×-l-absorb zero ⟩
                                zero                  ∎
  ×-r-absorb (mns (ℕ-succ n)) = (mns n × zero) + zero ≡⟨ +-r-unit (mns n × zero) ⟩
                                mns n × zero          ≡⟨ ×-r-absorb (mns n) ⟩
                                zero                  ∎

  neg-× : (m n : ℤ) → (neg m) × n ≡ neg (m × n)
  neg-× zero             n = zero × n                    ≡⟨ ×-l-absorb n ⟩
                             zero                        ≡⟨ refl ⟩
                             neg zero                    ≡⟨ ap neg (×-l-absorb n) ⁻¹ ⟩
                             neg (zero × n)              ∎
  neg-× (pls ℕ-zero)     n = (neg pls1) × n              ≡⟨ refl ⟩
                             mns1 × n                    ≡⟨ refl ⟩
                             neg n                       ≡⟨ refl ⟩
                             neg (pls1 × n)              ∎
  neg-× (pls (ℕ-succ m)) n = neg (succ (pls m)) × n      ≡⟨ ap (_× n) (neg-succ-pred-neg (pls m)) ⟩
                             pred (neg (pls m)) × n      ≡⟨ refl ⟩
                             (neg (pls m) × n) - n       ≡⟨ ap (_- n) (neg-× (pls m) n) ⟩
                             (neg (pls m × n)) - n       ≡⟨ neg-+ (pls m × n) n ⁻¹ ⟩
                             neg ((pls m × n) + n)       ≡⟨ refl ⟩
                             neg (succ (pls m) × n)      ∎
  neg-× (mns ℕ-zero)     n = neg mns1 × n                ≡⟨ refl ⟩
                             pls1 × n                    ≡⟨ refl ⟩
                             n                           ≡⟨ neg-neg n ⁻¹ ⟩
                             neg (neg n)                 ≡⟨ refl ⟩
                             neg (mns1 × n)              ∎
  neg-× (mns (ℕ-succ m)) n = neg (pred (mns m)) × n      ≡⟨ ap (_× n) (neg-pred-succ-neg (mns m)) ⟩
                             succ (neg (mns m)) × n      ≡⟨ refl ⟩
                             (neg (mns m) × n) + n       ≡⟨ ap (_+ n) (neg-× (mns m) n) ⟩
                             (neg (mns m × n)) + n       ≡⟨ ap (neg (mns m × n) +_) (neg-neg n ⁻¹) ⟩
                             (neg (mns m × n)) - (neg n) ≡⟨ neg-+ (mns m × n) (neg n) ⁻¹ ⟩
                             neg ((mns m × n) - n)       ≡⟨ refl ⟩
                             neg (pred (mns m) × n)      ∎
    
  ×-l-unit : (n : ℤ) → pls1 × n ≡ n
  ×-l-unit n = pls1 × n        ≡⟨ refl ⟩
               succ (zero) × n ≡⟨ refl ⟩
               (zero × n) + n  ≡⟨ ap (_+ n) (×-l-absorb n) ⟩
               zero + n        ≡⟨ +-l-unit n ⟩
               n               ∎

  ×-l-neg : (n : ℤ) → mns1 × n ≡ neg n
  ×-l-neg n = mns1 × n        ≡⟨ refl ⟩
              pred (zero) × n ≡⟨ refl ⟩
              (zero × n) - n  ≡⟨ ap (_- n) (×-l-absorb n) ⟩
              zero - n        ≡⟨ +-l-unit (neg n) ⟩
              neg n           ∎
    
  ×-r-unit : (n : ℤ) → n × pls1 ≡ n
  ×-r-unit zero             = zero × pls1           ≡⟨ ×-l-absorb pls1 ⟩
                              zero                  ∎
  ×-r-unit (pls ℕ-zero)     = pls1 × pls1           ≡⟨ +-l-unit pls1 ⟩
                              pls1                  ∎
  ×-r-unit (pls (ℕ-succ n)) = (pls n × pls1) + pls1 ≡⟨ ap (_+ pls1) (×-r-unit (pls n)) ⟩
                              pls n + pls1          ≡⟨ +-pls1-succ (pls n) ⟩
                              succ (pls n)          ∎
  ×-r-unit (mns ℕ-zero)     = mns1 × pls1           ≡⟨ ×-l-neg pls1 ⟩
                              neg pls1              ≡⟨ refl ⟩
                              mns1                  ∎
  ×-r-unit (mns (ℕ-succ n)) = (mns n × pls1) - pls1 ≡⟨ ap (_- pls1) (×-r-unit (mns n)) ⟩
                              mns n - pls1          ≡⟨ -pls1-pred (mns n) ⟩
                              pred (mns n)          ∎

  ×-r-neg : (n : ℤ) → n × mns1 ≡ neg n
  ×-r-neg zero             = zero × mns1           ≡⟨ ×-l-absorb mns1 ⟩
                             zero                  ≡⟨ refl ⟩
                             neg zero              ∎
  ×-r-neg (pls ℕ-zero)     = pls1 × mns1           ≡⟨ ×-l-unit mns1 ⟩
                             mns1                  ∎
  ×-r-neg (pls (ℕ-succ n)) = (pls n × mns1) + mns1 ≡⟨ +-mns1-pred (pls n × mns1) ⟩
                             pred (pls n × mns1)   ≡⟨ ap pred (×-r-neg (pls n)) ⟩
                             pred (mns n)          ∎
  ×-r-neg (mns ℕ-zero)     = mns1 × mns1           ≡⟨ ×-l-neg mns1 ⟩
                             neg (mns1)            ≡⟨ refl ⟩
                             pls1                  ∎
  ×-r-neg (mns (ℕ-succ n)) = (mns n × mns1) - mns1 ≡⟨ -mns1-succ (mns n × mns1) ⟩
                             succ (mns n × mns1)   ≡⟨ ap succ (×-r-neg (mns n)) ⟩
                             succ (pls n)          ∎

  ×-l-succ : (m n : ℤ) → (succ m) × n ≡ (m × n) + n
  ×-l-succ zero             n = pls1 × n                  ≡⟨ refl ⟩
                                n                         ≡⟨ +-l-unit n ⟩
                                zero + n                  ≡⟨ ap (_+ n) (×-l-absorb n) ⟩
                                (zero × n) + n            ∎
  ×-l-succ (pls ℕ-zero)     n = succ pls1 × n             ≡⟨ refl ⟩
                                (pls1 × n) + n            ≡⟨ refl ⟩
                                n + n                     ∎
  ×-l-succ (pls (ℕ-succ m)) n = (succ (pls m) × n) + n    ≡⟨ ap (_+ n) (×-l-succ (pls m) n) ⟩
                                ((pls m × n) + n) + n     ∎
  ×-l-succ (mns ℕ-zero)     n = zero × n                  ≡⟨ ×-l-absorb n ⟩
                                zero                      ≡⟨ +-l-inv n ⁻¹ ⟩
                                (neg n) + n               ∎
  ×-l-succ (mns (ℕ-succ m)) n = succ (pred (mns m)) × n   ≡⟨ ap (_× n) (succ-pred (mns m)) ⟩
                                mns m × n                 ≡⟨ +-r-unit (mns m × n) ⁻¹ ⟩
                                (mns m × n) + zero        ≡⟨ ap ((mns m × n) +_) (+-l-inv n) ⁻¹ ⟩
                                (mns m × n) + (neg n + n) ≡⟨ +-assoc (mns m × n) (neg n) n ⁻¹ ⟩
                                ((mns m × n) - n) + n     ∎

  ×-l-pred : (m n : ℤ) → (pred m) × n ≡ (m × n) - n
  ×-l-pred zero             n = mns1 × n                ≡⟨ refl ⟩
                                neg n                   ≡⟨ +-l-unit (neg n) ⟩
                                zero - n                ≡⟨ ap (_- n) (×-l-absorb n) ⟩
                                (zero × n) - n          ∎
  ×-l-pred (pls ℕ-zero)     n = zero                    ≡⟨ +-r-inv n ⁻¹ ⟩
                                n - n                   ∎
  ×-l-pred (pls (ℕ-succ m)) n = pred (succ (pls m)) × n ≡⟨ ap (_× n) (pred-succ (pls m)) ⟩
                                pls m × n               ≡⟨ +-r-unit (pls m × n) ⁻¹ ⟩
                                (pls m × n) + zero      ≡⟨ ap ((pls m × n) +_) (+-r-inv n) ⁻¹ ⟩
                                (pls m × n) + (n - n)   ≡⟨ +-assoc (pls m × n) n (neg n) ⁻¹ ⟩
                                ((pls m × n) + n) - n   ∎
  ×-l-pred (mns ℕ-zero)     n = refl
  ×-l-pred (mns (ℕ-succ m)) n = refl

  ×-r-succ : (m n : ℤ) → m × (succ n) ≡ m + (m × n)
  ×-r-succ zero             n = zero × succ n                     ≡⟨ +-l-unit (zero × succ n) ⟩
                                zero + (zero × succ n)            ∎
  ×-r-succ (pls ℕ-zero)     n = pls1 × succ n                     ≡⟨ ×-l-unit (succ n) ⟩
                                succ n                            ≡⟨ refl ⟩
                                pls1 + n                          ≡⟨ ap (pls1 +_) (×-l-unit n) ⁻¹ ⟩
                                pls1 + (pls1 × n)                 ∎
  ×-r-succ (pls (ℕ-succ m)) n = succ (pls m) × succ n             ≡⟨ ×-l-succ (pls m) (succ n) ⟩
                                (pls m × succ n) + succ n         ≡⟨ ap (_+ succ n) (×-r-succ (pls m) n) ⟩
                                (pls m + (pls m × n)) + succ n    ≡⟨ +-r-succ (pls m + (pls m × n)) n ⟩
                                succ ((pls m + (pls m × n)) + n)  ≡⟨ ap succ (+-assoc (pls m) (pls m × n) n) ⟩
                                succ (pls m + ((pls m × n) + n))  ≡⟨ +-l-succ (pls m) ((pls m × n) + n) ⁻¹ ⟩
                                succ (pls m) + ((pls m × n) + n)  ≡⟨ ap (succ (pls m) +_) (×-l-succ (pls m) n) ⁻¹ ⟩
                                succ (pls m) + (succ (pls m) × n) ∎
  ×-r-succ (mns ℕ-zero)     n = mns1 × succ n                     ≡⟨ refl ⟩
                                neg (succ n)                      ≡⟨ neg-succ-pred-neg n ⟩
                                pred (neg n)                      ≡⟨ refl ⟩
                                mns1 + (neg n)                    ≡⟨ refl ⟩
                                mns1 + (mns1 × n)                 ∎
  ×-r-succ (mns (ℕ-succ m)) n = pred (mns m) × succ n             ≡⟨ ×-l-pred (mns m) (succ n) ⟩
                                (mns m × succ n) - succ n         ≡⟨ ap ((mns m × succ n) +_) (neg-succ-pred-neg n) ⟩
                                (mns m × succ n) + pred (neg n)   ≡⟨ +-r-pred (mns m × succ n) (neg n) ⟩
                                pred ((mns m × succ n) - n)       ≡⟨ ap (λ l → pred (l - n)) (×-r-succ (mns m) n) ⟩
                                pred ((mns m + (mns m × n)) - n)  ≡⟨ ap pred (+-assoc (mns m) (mns m × n) (neg n)) ⟩
                                pred (mns m + ((mns m × n) - n))  ≡⟨ +-l-pred (mns m) ((mns m × n) - n) ⁻¹ ⟩
                                pred (mns m) + ((mns m × n) - n)  ≡⟨ ap (pred (mns m) +_) (×-l-pred (mns m) n) ⁻¹ ⟩
                                pred (mns m) + (pred (mns m) × n) ∎

  ×-r-pred : (m n : ℤ) → m × (pred n) ≡ (neg m) + (m × n)
  ×-r-pred zero             n = zero × pred n                              ≡⟨ +-l-unit (zero × pred n) ⟩
                                zero + (zero × pred n)                     ∎
  ×-r-pred (pls ℕ-zero)     n = pls1 × pred n                              ≡⟨ refl ⟩
                                pred n                                     ≡⟨ refl ⟩
                                mns1 + n                                   ≡⟨ refl ⟩
                                mns1 + (pls1 × n)                          ∎
  ×-r-pred (pls (ℕ-succ m)) n = succ (pls m) × pred n                      ≡⟨ ×-l-succ (pls m) (pred n) ⟩
                                (pls m × pred n) + pred n                  ≡⟨ ap (_+ pred n) (×-r-pred (pls m) n) ⟩
                                (neg (pls m) + (pls m × n)) + pred n       ≡⟨ +-r-pred (neg (pls m) + (pls m × n)) n ⟩
                                pred ((neg (pls m) + (pls m × n)) + n)     ≡⟨ ap pred (+-assoc (neg (pls m)) (pls m × n) n) ⟩
                                pred (neg (pls m) + ((pls m × n) + n))     ≡⟨ +-l-pred (neg (pls m)) ((pls m × n) + n) ⁻¹ ⟩
                                pred (neg (pls m)) + ((pls m × n) + n)     ≡⟨ ap (pred (neg (pls m)) +_) (×-l-succ (pls m) n ⁻¹) ⟩
                                pred (neg (pls m)) + (succ (pls m) × n)    ≡⟨ ap (_+ (succ (pls m) × n)) (neg-succ-pred-neg (pls m) ⁻¹) ⟩
                                neg (succ (pls m)) + (succ (pls m) × n)    ∎
  ×-r-pred (mns ℕ-zero)     n = mns1 × (pred n)                            ≡⟨ refl ⟩
                                neg (pred n)                               ≡⟨ neg-pred-succ-neg n ⟩
                                succ (neg n)                               ≡⟨ refl ⟩
                                pls1 + (mns1 × n)                          ∎
  ×-r-pred (mns (ℕ-succ m)) n = pred (mns m) × pred n                      ≡⟨ ×-l-pred (mns m) (pred n) ⟩
                                (mns m × pred n) - (pred n)                ≡⟨ ap ((mns m × pred n) +_) (neg-pred-succ-neg n) ⟩
                                (mns m × pred n) + succ (neg n)            ≡⟨ ap (_+ succ (neg n)) (×-r-pred (mns m) n) ⟩
                                (neg (mns m) + (mns m × n)) + succ (neg n) ≡⟨ +-r-succ (neg (mns m) + (mns m × n)) (neg n) ⟩
                                succ ((neg (mns m) + (mns m × n)) - n)     ≡⟨ ap succ (+-assoc (neg (mns m)) (mns m × n) (neg n)) ⟩
                                succ (neg (mns m) + ((mns m × n) - n))     ≡⟨ +-l-succ (neg (mns m)) ((mns m × n) - n) ⁻¹ ⟩
                                succ (neg (mns m)) + ((mns m × n) - n)     ≡⟨ ap (succ (neg (mns m)) +_) (×-l-pred (mns m) n) ⁻¹ ⟩
                                succ (neg (mns m)) + (pred (mns m) × n)    ≡⟨ ap (_+ (pred (mns m) × n)) (neg-pred-succ-neg (mns m)) ⁻¹ ⟩
                                neg (pred (mns m)) + (pred (mns m) × n)    ∎
  
  ×-l-dist : (l m n : ℤ) → (l + m) × n ≡ (l × n) + (m × n)
  ×-l-dist zero             m n = (zero + m) × n                  ≡⟨ ap (_× n) (+-l-unit m) ⟩
                                  m × n                           ≡⟨ +-l-unit (m × n) ⁻¹ ⟩
                                  zero + (m × n)                  ≡⟨ ap (_+ (m × n)) (×-l-absorb n) ⟩
                                  (zero × n) + (m × n)            ∎
  ×-l-dist (pls ℕ-zero)     m n = succ m × n                      ≡⟨ ×-l-succ m n ⟩
                                  (m × n) + n                     ≡⟨ +-comm (m × n) n ⟩
                                  n + (m × n)                     ≡⟨ ap (_+ (m × n)) (×-l-unit n) ⟩
                                  (pls1 × n) + (m × n)            ∎
  ×-l-dist (pls (ℕ-succ l)) m n = (succ (pls l) + m) × n          ≡⟨ ap (_× n) (+-l-succ (pls l) m) ⟩
                                  succ (pls l + m) × n            ≡⟨ ×-l-succ (pls l + m) n ⟩
                                  ((pls l + m) × n) + n           ≡⟨ ap (_+ n) (×-l-dist (pls l) m n) ⟩
                                  ((pls l × n) + (m × n)) + n     ≡⟨ +-assoc (pls l × n) (m × n) n ⟩
                                  (pls l × n) + ((m × n) + n)     ≡⟨ ap ((pls l × n) +_) (+-comm (m × n) n) ⟩
                                  (pls l × n) + (n + (m × n))     ≡⟨ +-assoc (pls l × n) n (m × n) ⁻¹ ⟩
                                  ((pls l × n) + n) + (m × n)     ≡⟨ ap (_+ (m × n)) (×-l-succ (pls l) n) ⁻¹ ⟩
                                  (succ (pls l) × n) + (m × n)    ∎
  ×-l-dist (mns ℕ-zero)     m n = pred m × n                      ≡⟨ ×-l-pred m n ⟩
                                  (m × n) - n                     ≡⟨ +-comm (m × n) (neg n) ⟩
                                  neg n + (m × n)                 ∎
  ×-l-dist (mns (ℕ-succ l)) m n = (pred (mns l) + m) × n          ≡⟨ ap (_× n) (+-l-pred (mns l) m) ⟩
                                  pred (mns l + m) × n            ≡⟨ ×-l-pred (mns l + m) n ⟩
                                  ((mns l + m) × n) - n           ≡⟨ ap (_- n) (×-l-dist (mns l) m n) ⟩
                                  ((mns l × n) + (m × n)) - n     ≡⟨ +-assoc (mns l × n) (m × n) (neg n) ⟩
                                  (mns l × n) + ((m × n) - n)     ≡⟨ ap ((mns l × n) +_) (+-comm (m × n) (neg n)) ⟩
                                  (mns l × n) + (neg n + (m × n)) ≡⟨ +-assoc (mns l × n) (neg n) (m × n) ⁻¹ ⟩
                                  ((mns l × n) - n) + (m × n)     ≡⟨ ap (_+ (m × n)) (×-l-pred (mns l) n) ⁻¹ ⟩
                                  (pred (mns l) × n) + (m × n)    ∎
  
  ×-r-dist : (l m n : ℤ) → l × (m + n) ≡ (l × m) + (l × n)
  ×-r-dist zero             m n = zero × (m + n)                                ≡⟨ ×-l-absorb (m + n) ⟩
                                  zero                                          ≡⟨ +-l-unit zero ⟩
                                  zero + zero                                   ≡⟨ ap (_+ zero) (×-l-absorb m) ⁻¹ ⟩
                                  (zero × m) + zero                             ≡⟨ ap ((zero × m) +_) (×-l-absorb n) ⁻¹ ⟩
                                  (zero × m) + (zero × n)                       ∎
  ×-r-dist (pls ℕ-zero)     m n = pls1 × (m + n)                                ≡⟨ refl ⟩
                                  m + n                                         ≡⟨ refl ⟩
                                  (pls1 × m) + n                                ≡⟨ refl ⟩
                                  (pls1 × m) + (pls1 × n)                       ∎
  ×-r-dist (pls (ℕ-succ l)) m n = succ (pls l) × (m + n)                        ≡⟨ refl ⟩
                                  (pls l × (m + n)) + (m + n)                   ≡⟨ ap (_+ (m + n)) (×-r-dist (pls l) m n) ⟩
                                  ((pls l × m) + (pls l × n)) + (m + n)         ≡⟨ +-assoc (pls l × m) (pls l × n) (m + n) ⟩
                                  (pls l × m) + ((pls l × n) + (m + n))         ≡⟨ ap ((pls l × m) +_) (+-assoc (pls l × n) m n) ⁻¹ ⟩
                                  (pls l × m) + (((pls l × n) + m) + n)         ≡⟨ ap (λ k → (pls l × m) + (k + n)) (+-comm (pls l × n) m) ⟩
                                  (pls l × m) + ((m + (pls l × n)) + n)         ≡⟨ ap ((pls l × m) +_) (+-assoc m (pls l × n) n) ⟩
                                  (pls l × m) + (m + ((pls l × n) + n))         ≡⟨ +-assoc (pls l × m) m ((pls l × n) + n) ⁻¹ ⟩
                                  ((pls l × m) + m) + ((pls l × n) + n)         ≡⟨ refl ⟩
                                  (succ (pls l) × m) + (succ (pls l) × n)       ∎
  ×-r-dist (mns ℕ-zero)     m n = mns1 × (m + n)                                ≡⟨ refl ⟩
                                  neg (m + n)                                   ≡⟨ neg-+ m n ⟩
                                  neg m + neg n                                 ≡⟨ refl ⟩
                                  (mns1 × m) + neg n                            ≡⟨ refl ⟩
                                  (mns1 × m) + (mns1 × n)                       ∎
  ×-r-dist (mns (ℕ-succ l)) m n = pred (mns l) × (m + n)                        ≡⟨ refl ⟩
                                  (mns l × (m + n)) - (m + n)                   ≡⟨ ap ((mns l × (m + n)) +_) (neg-+ m n) ⟩
                                  (mns l × (m + n)) + (neg m + neg n)           ≡⟨ ap (_+ (neg m + neg n)) (×-r-dist (mns l) m n) ⟩
                                  ((mns l × m) + (mns l × n)) + (neg m + neg n) ≡⟨ +-assoc (mns l × m) (mns l × n) (neg m + neg n) ⟩
                                  (mns l × m) + ((mns l × n) + (neg m + neg n)) ≡⟨ ap ((mns l × m) +_) (+-assoc (mns l × n) (neg m) (neg n)) ⁻¹ ⟩
                                  (mns l × m) + (((mns l × n) - m) - n)         ≡⟨ ap (λ k → ((mns l × m) + (k - n))) (+-comm (mns l × n) (neg m)) ⟩
                                  (mns l × m) + ((neg m + (mns l × n)) - n)     ≡⟨ ap ((mns l × m) +_) (+-assoc (neg m) (mns l × n) (neg n)) ⟩
                                  (mns l × m) + (neg m + ((mns l × n) - n))     ≡⟨ +-assoc (mns l × m) (neg m) ((mns l × n) - n) ⁻¹ ⟩
                                  ((mns l × m) - m) + ((mns l × n) - n)         ≡⟨ refl ⟩
                                  (pred (mns l) × m) + (pred (mns l) × n)       ∎
  
  ×-assoc : (l m n : ℤ) → (l × m) × n ≡ l × (m × n)
  ×-assoc zero             m n = (zero × m) × n                  ≡⟨ ap (_× n) (×-l-absorb m) ⟩
                                 zero × n                        ≡⟨ ×-l-absorb n ⟩
                                 zero                            ≡⟨ ×-l-absorb (m × n) ⟩
                                 zero × (m × n)                  ∎
  ×-assoc (pls ℕ-zero)     m n = (pls1 × m) × n                  ≡⟨ refl ⟩
                                 m × n                           ≡⟨ refl ⟩
                                 pls1 × (m × n)                  ∎
  ×-assoc (pls (ℕ-succ l)) m n = (succ (pls l) × m) × n          ≡⟨ refl ⟩
                                 ((pls l × m) + m) × n           ≡⟨ ×-l-dist (pls l × m) m n ⟩
                                 ((pls l × m) × n) + (m × n)     ≡⟨ ap (_+ (m × n)) (×-assoc (pls l) m n) ⟩
                                 (pls l × (m × n)) + (m × n)     ≡⟨ refl ⟩
                                 succ (pls l) × (m × n)          ∎
  ×-assoc (mns ℕ-zero)     m n = (mns1 × m) × n                  ≡⟨ refl ⟩
                                 (neg m) × n                     ≡⟨ neg-× m n ⟩
                                 neg (m × n)                     ≡⟨ refl ⟩
                                 mns1 × (m × n)                  ∎
  ×-assoc (mns (ℕ-succ l)) m n = (pred (mns l) × m) × n          ≡⟨ refl ⟩
                                 ((mns l × m) - m) × n           ≡⟨ ×-l-dist (mns l × m) (neg m) n ⟩
                                 ((mns l × m) × n) + (neg m × n) ≡⟨ ap (((mns l × m) × n) +_) (neg-× m n) ⟩
                                 ((mns l × m) × n) - (m × n)     ≡⟨ ap (_- (m × n)) (×-assoc (mns l) m n) ⟩
                                 (mns l × (m × n)) - (m × n)     ≡⟨ refl ⟩
                                 pred (mns l) × (m × n)          ∎
    
  ×-comm : (m n : ℤ) → m × n ≡ n × m
  ×-comm zero             n = zero × n            ≡⟨ ×-l-absorb n ⟩
                              zero                ≡⟨ ×-r-absorb n ⁻¹ ⟩
                              n × zero            ∎
  ×-comm (pls ℕ-zero)     n = pls1 × n            ≡⟨ ×-l-unit n ⟩
                              n                   ≡⟨ ×-r-unit n ⁻¹ ⟩
                              n × pls1            ∎
  ×-comm (pls (ℕ-succ m)) n = succ (pls m) × n    ≡⟨ ×-l-succ (pls m) n ⟩
                              (pls m × n) + n     ≡⟨ +-comm (pls m × n) n ⟩
                              n + (pls m × n)     ≡⟨ ap (n +_) (×-comm (pls m) n) ⟩
                              n + (n × pls m)     ≡⟨ ×-r-succ n (pls m) ⁻¹ ⟩
                              n × succ (pls m)    ∎
  ×-comm (mns ℕ-zero)     n = mns1 × n            ≡⟨ ×-l-neg n ⟩
                              neg n               ≡⟨ ×-r-neg n ⁻¹ ⟩
                              n × mns1            ∎
  ×-comm (mns (ℕ-succ m)) n = pred (mns m) × n    ≡⟨ ×-l-pred (mns m) n ⟩
                              (mns m × n) - n     ≡⟨ +-comm (mns m × n) (neg n) ⟩
                              neg n + (mns m × n) ≡⟨ ap (neg n +_) (×-comm (mns m) n) ⟩
                              neg n + (n × mns m) ≡⟨ ×-r-pred n (mns m) ⁻¹ ⟩
                              n × pred (mns m)    ∎
