{-# OPTIONS --cubical --safe #-}

module Cubical.Foundations.Pentagon where

open import Cubical.Foundations.Everything


Comp : Typeω
Comp = ∀ {ℓ} → {A : Type ℓ} → {a₁ a₂ a₃ : A} → a₁ ≡ a₂ → a₂ ≡ a₃ → a₁ ≡ a₃

Assoc : Comp → Typeω 
Assoc _∘_ = ∀ {ℓ} → {A : Type ℓ} → {a₁ a₂ a₃ a₄ : A}
           → (p₁₂ : a₁ ≡ a₂) → (p₂₃ : a₂ ≡ a₃) → (p₃₄ : a₃ ≡ a₄)
           →  p₁₂ ∘ (p₂₃ ∘ p₃₄) ≡ (p₁₂ ∘ p₂₃) ∘ p₃₄ 

PentagonIdentity : (_∘_ : Comp) → (Assoc _∘_) → Typeω
PentagonIdentity _∘_ assoc =
           ∀ {ℓ} → {A : Type ℓ} → {a₁ a₂ a₃ a₄ a₅ : A}
           → (p₁₂ : a₁ ≡ a₂) → (p₂₃ : a₂ ≡ a₃) → (p₃₄ : a₃ ≡ a₄) → (p₄₅ : a₄ ≡ a₅)
           → _≡_ {A = (p₁₂ ∘ (p₂₃ ∘ (p₃₄ ∘ p₄₅))) ≡ (((p₁₂ ∘ p₂₃) ∘ p₃₄) ∘ p₄₅)} 
             (assoc _ _ _ ∘ assoc _ _ _)
            (((cong (_ ∘_) (assoc _ _ _)) ∘ assoc _ _ _) ∘ (cong (_∘ _) (assoc _ _ _)))
           
assoc' : Assoc _∙_
assoc' p q r k i =
  hcomp
    (λ j → λ
      { (i = i0) → p i0
      ; (i = i1) →
        hcomp
          (λ l → λ
            { (j = i0) → q k
            ; (j = i1) → r l
            ; (k = i1) → r (j ∧ l)
            })
          (q (j ∨ k))
      })
    (compPath-filler p q k i)


compPath-filler-in-filler : ∀ {ℓ} → {A : Type ℓ} → {x y z : A}
          → (p : _ ≡ y) → ∀ q
          -- → I → (Square (p ∙ q) (p ∙ q) (λ _ → x) (λ _ → z))
          → _≡_ {A = Square (p ∙ q) (p ∙ q) (λ _ → x) (λ _ → z)}
           (λ i j → hcomp
                      (λ { i₂ (j = i0) → x
                         ; i₂ (j = i1) → q (i₂ ∨ ~ i)
                         ; i₂ (i = i0) → (p ∙ q) j
                        })
                      (compPath-filler p q (~ i) j))
           (λ _ → p ∙ q)
compPath-filler-in-filler p q z i j =
   hcomp
     (λ k → λ {
        (j = i0) → p i0
      ; (j = i1) → q (k ∨ ~ i ∧ ~ z) 
      ; (i = i0) → hcomp
                   (λ i₂ → λ {
                     (j = i0) → p i0
                    ;(j = i1) → q ((k ∨  ~ z) ∧ i₂)
                    ;(z = i1) (k = i0) → p j
                   })
                  (p j)
      ; (i = i1) →  compPath-filler p (λ i₁ → q (k ∧ i₁)) k j
      ; (z = i0) → hfill
                     ((λ i₂ → λ { (j = i0) → p i0
                         ; (j = i1) → q (i₂ ∨ ~ i)
                         ; (i = i0) → (p ∙ q) j
                        }))
                     (inS ((compPath-filler p q (~ i) j))) k
      ; (z = i1) → compPath-filler p q k j 
     })
     (((compPath-filler p q (~ i ∧ (~ z)) j)))



pentagonIdentity : PentagonIdentity _∙_ assoc'
pentagonIdentity {a₁ = x} {y} {z} {w} {v} p q r s =

        (λ i →
              (λ j → cong (p ∙_) (assoc' q r s) (i ∧ j))
           ∙∙ (λ j → lemma₀₀ i j ∙ lemma₀₁ i j)
           ∙∙ (λ j → lemma₁₀ i j ∙ lemma₁₁ i j)
        )
        ∙ doubleCompPath-elim _ _ _

  where

    lemma₀₀ : ( i j : I) → _ ≡ _
    lemma₀₀ i j i₁ =
        (hcomp
        (λ k → λ {
         (j = i0) → p i₁ ;(i₁ = i0) → x
        ;(i₁ = i1) → hcomp
                     (λ k₁ → λ { (i = i0) → (q (j ∧ k)) ; (k = i0) → y ; (j = i0) → y
                               ; (j = i1)(k = i1) → r (k₁ ∧ i)})
                     (q (j ∧ k))  
        }) (p i₁))

    lemma₀₁ : ( i j : I) → hcomp
                       (λ k → λ {(i = i0) → q (j)
                               ; (j = i0) → y
                               ; (j = i1) → r (k ∧ i)
                          })
                       (q (j)) ≡ _
    lemma₀₁ i j i₁ =
     (hcomp
        (λ k → λ {
         (j = i1) → hcomp (
          (λ k₁ → λ {
            (i₁ = i0) → r i ;(k = i0) → r i ;(i = i1) → s (k₁ ∧  k ∧  i₁)
           ;(i₁ = i1)(k = i1) →  s k₁
           })) (r ((i₁ ∧ k) ∨ (i)))
        ;(i₁ = i0) → compPath-filler q r i j
        ;(i₁ = i1) → hcomp (
          (λ k₁ → λ {
            (k = i0) → r i ;(k = i1) → s k₁ ;(i = i1) → s (k ∧ k₁)   
           })) (r (i ∨ k))
        })
       (hfill (
         (λ k → λ {
            (j = i1) → r k ;(i₁ = i1) → r k ;(i₁ = i0)(j = i0) → y   
           })
        ) (inS (q (i₁ ∨ j))) i))



    lemma₁₁ : ( i j : I) → (r (i ∨ j)) ≡ _
    lemma₁₁ i j i₁ =
           hcomp
          (λ k → λ {
            (i = i1) → s (i₁ ∧ (k))
           ;(j = i1) → s (i₁ ∧ k)
           ;(i₁ = i0) → r (i ∨ j)
           ;(i₁ = i1) → s k
           }) (r (i ∨ j ∨ i₁))


    lemma₁₀-back : I → I → I → _
    lemma₁₀-back i j i₁ =
        hcomp 
         (λ k → λ {
           (i₁ = i0) → x
         ; (i₁ = i1) → hcomp
                       (λ k₁ → λ {
                          (k = i0) → q (j ∨ ~ i)
                       ;  (k = i1) → r (k₁ ∧ j)
                       ;  (j = i0) → q (k ∨ ~ i)
                       ;  (j = i1) → r (k₁ ∧ k)
                       ;  (i = i0) → r (k ∧ j ∧ k₁)
                       })
                       (q (k ∨ j ∨ (~ i)))
         ; (i = i0)(j = i0) → (p ∙ q) i₁
         })
        (hcomp
        (λ k → λ {
          (i₁ = i0) → x
         ;(i₁ = i1) → q ((j ∨ (~ i) ) ∧ k)
         ;(j = i0)(i = i1) → p i₁
        })
        (p i₁))


    lemma₁₀ : ( i j : I) → _ ≡ _
    lemma₁₀ i j i₁ =
       (hcomp
        λ k → λ {
          (i₁ = i0) → x
        ; (i₁ = i1) → r (i ∨ j)
        ; (j = i0) →  (hcomp
                        (λ k₁ → λ {
                          (i₁ = i0) → x
                        ; (i₁ = i1) → r i
                        ; (k = i0) → (p ∙ compPath-filler q r i) i₁
                        ; (k = i1) → (p ∙ compPath-filler q r i) i₁
                        ; (i = i0) → compPath-filler-in-filler p q (~ k₁) (~ k) i₁ 
                        ; (i = i1) → (p ∙ (q ∙ r)) i₁
                        })
                       ((p ∙ compPath-filler q r i) i₁))
        ; (j = i1) → (((p ∙ q) ∙ r)) i₁
        ; (i = i0) → lemma₁₀-back (~ k) j i₁
        ; (i = i1) → (assoc' p q r) j i₁
        })
       (((λ _ → x) ∙∙ compPath-filler p q j ∙∙
         (λ i₁ →
             hcomp
             (λ k → λ {
                  (i₁ = i0) → q j
               ;  (i₁ = i1) → r (k ∧ (j ∨ i))
               ;  (j = i0)(i = i0) → q (i₁)
               ;  (j = i1) → r (i₁ ∧ k)
            })
            (q (j ∨ i₁))
         )) i₁)         




