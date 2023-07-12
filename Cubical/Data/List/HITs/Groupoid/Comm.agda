{-# OPTIONS --safe #-}

module Cubical.Data.List.HITs.Groupoid.Comm where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Empty renaming (elim to ⊥elim ; rec to ⊥rec)

open import Cubical.Functions.FunExtEquiv

open import Cubical.Relation.Nullary

open import Cubical.Data.Nat.Order

open import Cubical.HITs.GroupoidTruncation


import Cubical.Data.List.Base as B
import Cubical.Data.List.Properties as BP

import Cubical.Functions.Logic as L

open import Cubical.Data.List.HITs.Groupoid.Base

private
  variable
    ℓ : Level


infixr 5 _⊙_

_∙∙₂_∙∙₂_ : {A : Type ℓ}
  {a₀₀ a₀₁ a₀₂ a₀₃ : A} {a₀₋ : a₀₀ ≡ a₀₁} {b₀₋ : a₀₁ ≡ a₀₂} {c₀₋ : a₀₂ ≡ a₀₃}
  {a₁₀ a₁₁ a₁₂ a₁₃ : A} {a₁₋ : a₁₀ ≡ a₁₁} {b₁₋ : a₁₁ ≡ a₁₂} {c₁₋ : a₁₂ ≡ a₁₃}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁} {a₋₂ : a₀₂ ≡ a₁₂}{a₋₃ : a₀₃ ≡ a₁₃}
  (p : Square a₀₋ a₁₋ a₋₀ a₋₁) (q : Square b₀₋ b₁₋ a₋₁ a₋₂)
   (r : Square c₀₋ c₁₋ a₋₂ a₋₃)
  → Square (a₀₋ ∙∙ b₀₋ ∙∙ c₀₋) (a₁₋ ∙∙ b₁₋ ∙∙ c₁₋) a₋₀ a₋₃
(p ∙∙₂ q ∙∙₂ r) i = p i ∙∙ q i ∙∙ r i 



data FCM₃ (A : Type ℓ) : Type ℓ where
 [] : FCM₃ A
 [_] : A → FCM₃ A
 _⊙_ : FCM₃ A → FCM₃ A → FCM₃ A
 ⊙-comm :  ∀ m n → m ⊙ n ≡ n ⊙ m
 ⊙-unit-r : (xs : FCM₃ A) → xs ⊙ [] ≡ xs
 ⊙-unit-l : (xs : FCM₃ A) → [] ⊙ xs ≡ xs
 ⊙-assoc : (xs ys zs : FCM₃ A) → (xs ⊙ ys) ⊙ zs ≡ xs ⊙ ys ⊙ zs
 ⊙-triangle : ∀ xs ys → Square {A = FCM₃ A}                     
                          (⊙-assoc xs [] ys)
                          (λ _ → xs ⊙ ys)
                          (cong (_⊙ ys) (⊙-unit-r xs))
                          (cong (xs ⊙_) (⊙-unit-l ys))
 ⊙-hex-diag : ∀ l c r →
      ((l ⊙ c) ⊙ r) ≡ (c ⊙ (r ⊙ l))
 ⊙-hex-up : ∀ l c r →
      Square 
        (⊙-comm l (c ⊙ r))
        (⊙-hex-diag l c r)
        (sym (⊙-assoc l c r))
        (⊙-assoc c r l)
 ⊙-hex-down :  ∀ l c r →
      Square 
        (⊙-hex-diag l c r)
        (⊙-assoc c l r)
        (cong (_⊙ r) (⊙-comm l c))
        (cong (c ⊙_) (⊙-comm r l))


 ⊙-pentagon-diag : (xs ys zs ws : FCM₃ A)
      → ((xs ⊙ ys) ⊙ zs) ⊙ ws ≡ xs ⊙ ys ⊙ zs ⊙ ws
 ⊙-pentagon-△ : (xs ys zs ws : FCM₃ A) →
       Square refl (⊙-pentagon-diag xs ys zs ws)
         (sym (⊙-assoc _ _ _)) (⊙-assoc _ _ _)
 ⊙-pentagon-□ : (xs ys zs ws : FCM₃ A) →
       Square (⊙-pentagon-diag xs ys zs ws)
          (⊙-assoc _ _ _)
          (cong (_⊙ ws) (⊙-assoc _ _ _))           
          (sym (cong (xs ⊙_) (⊙-assoc _ _ _)))

 trunc : isGroupoid (FCM₃ A)



-- pent-[] : {A : Type ℓ} → (a b : FCM₃ A) → Square
--           {A = FCM₃ A}
--              {!!}
--              {!!}
--              {!!}
--              {!!}
-- pent-[] a b = whiskSq.sq' (λ _ _ → FCM₃ _)
--     (⊙-pentagon-□ a [] [] b)
--     {!!}
--     (λ j i → ⊙-assoc a ({!!}) b j)
--     {!!}
--     {!!}

-- hlp0 : {A : Type ℓ} → (a b : FCM₃ A) → Square
--           {A = FCM₃ A}
--              ((sym (⊙-assoc [] a b))
--                  ∙∙ (λ i → ⊙-comm [] a i ⊙ b)
--                  ∙∙ λ i → ⊙-unit-r a i ⊙ b)
--              ((⊙-assoc a b [])
--                  ∙∙ (λ i → a ⊙ ⊙-comm b [] i)
--                  ∙∙ λ i → a ⊙ ⊙-unit-l b i)
--             (⊙-comm [] (a ⊙ b))
--             λ i → a ⊙ b
-- hlp0 a b = flipSquare (⊙-hex-up [] a b)
--        ∙∙₂ flipSquare (⊙-hex-down [] a b)
--         ∙∙₂ flipSquare (⊙-triangle a b)

-- hlp : {A : Type ℓ} → Square {A = FCM₃ A}
--                                 ({!!})
--                                 ({!!})
--                                 (λ i → {!!})
--                                 λ i → {!!}
-- hlp = whiskSq.sq' (λ _ _ → FCM₃ _)
--     (λ i j → {!!})
--       (λ j k → ⊙-hex-up [] [] [] j k)
--       (λ j k → ⊙-triangle [] [] (~ j) k )
--       (λ i k → {!!})
--       λ i k → ⊙-hex-down [] [] [] i k

-- ⊙-comm [] (⊙-unit-r [] i) j

-- ⊙-comm-[]-[] : {A : Type ℓ} → Square {A = FCM₃ A}
--                                 (⊙-comm [] []) refl refl refl
-- ⊙-comm-[]-[] =
--   whiskSq.sq' (λ _ _ → FCM₃ _)
--     (⊙-hex-up [] [] [])
--       (λ j i → ⊙-comm [] (⊙-unit-r [] i) j)
--       (λ j i → {!⊙-hex-down [] [] [] i j!})
--       {!!}
--       {!!}
 
 
⊙-pentagon : {A : Type ℓ} → (xs ys zs ws : FCM₃ A) → Square
           (⊙-assoc _ zs _ ∙∙ refl ∙∙ ⊙-assoc _ ys _)
           (⊙-assoc _ _ _)
           (cong (_⊙ ws) (⊙-assoc _ _ _))           
           (sym (cong (xs ⊙_) (⊙-assoc _ _ _)))
⊙-pentagon xs ys zs ws =
  (λ i j → hcomp
   (λ k → λ { (i = i1) → ⊙-pentagon-△ xs ys zs ws k j
            ; (j = i0) → ⊙-assoc (xs ⊙ ys) zs ws (~ k)
            ; (j = i1) → ⊙-assoc xs ys (zs ⊙ ws) k
            })
   ((xs ⊙ ys) ⊙ zs ⊙ ws))
   ◁ ⊙-pentagon-□ xs ys zs ws


module _ {A : Type ℓ} where

 module ElimFCM₃ {ℓb} (B : FCM₃ A → Type ℓb) where 

  record H1 : Type (ℓ-max ℓ ℓb) where
   no-eta-equality
   field
    b[] : B []
    b[_] : ∀ a → B [ a ]
    _b⊙_ : ∀ {xs ys} → B xs → B ys → B (xs ⊙ ys)


   record H2 : Type (ℓ-max ℓ ℓb) where
    no-eta-equality
    field
     b⊙-comm : ∀ {xs ys} → (bx : B xs) (by : B ys) 
                    → PathP (λ i → B (⊙-comm xs ys i))
                       (bx b⊙ by)
                       (by b⊙ bx)
     b⊙ur : ∀ {xs} → (b : B xs) →
               PathP (λ i → B (⊙-unit-r xs i)) (b b⊙ b[]) b
     b⊙ul : ∀ {xs} → (b : B xs) →
               PathP (λ i → B (⊙-unit-l xs i)) (b[] b⊙ b) b
     b⊙-assoc : ∀ {xs ys zs} → (bx : B xs) (by : B ys) (bz : B zs)
                    → PathP (λ i → B (⊙-assoc xs ys zs i))
                       ((bx b⊙ by) b⊙ bz)
                        (bx b⊙ (by b⊙ bz))

     b⊙-hex-diag : ∀ {xs ys zs} → (l : B xs) (c : B ys) (r : B zs)
                    → PathP (λ i → B (⊙-hex-diag xs ys zs i))
                            ((l b⊙ c) b⊙ r)
                            (c b⊙ (r b⊙ l))

      
     b⊙-pent-diag : ∀ {xs ys zs ws} → (bx : B xs) (by : B ys) (bz : B zs)(bw : B ws)
                    → PathP (λ i → B (⊙-pentagon-diag xs ys zs ws i))
                       (((bx b⊙ by) b⊙ bz) b⊙ bw)
                        (bx b⊙ (by b⊙ (bz b⊙ bw)))


    record H3 : Type (ℓ-max ℓ ℓb) where
     no-eta-equality
     field


      b⊙-hex-up : ∀ {xs ys zs} → (l : B xs) (c : B ys) (r : B zs)
                    → SquareP (λ i j → B (⊙-hex-up xs ys zs i j)) 
                         (b⊙-comm l (c b⊙ r))
                         (b⊙-hex-diag l c r)
                         (symP (b⊙-assoc l c r))
                         (b⊙-assoc c r l)
 
      b⊙-hex-down : ∀ {xs ys zs} → (l : B xs) (c : B ys) (r : B zs)
                    → SquareP (λ i j → B (⊙-hex-down xs ys zs i j))
                               (b⊙-hex-diag l c r)
                               (b⊙-assoc c l r)
                               (congP (λ _ → _b⊙ r) (b⊙-comm l c))
                               (congP (λ _ → c b⊙_) (b⊙-comm r l))



      b⊙-triangle : ∀ {xs ys} → (bx : B xs)(by : B ys)
                     → SquareP (λ i j → B (⊙-triangle xs ys i j))
                         (b⊙-assoc bx b[] by)
                         refl
                         (λ i → b⊙ur bx i b⊙ by)
                         λ i → bx b⊙ b⊙ul by i
      b⊙-pent-△ : ∀ {xs ys zs ws} → (bx : B xs) (by : B ys) (bz : B zs)(bw : B ws)
                     → SquareP (λ i j → B (⊙-pentagon-△ xs ys zs ws i j))
                         refl
                          (b⊙-pent-diag bx by bz bw)
                          (symP (b⊙-assoc _ _ _))
                          (b⊙-assoc _ _ _)
      b⊙-pent-□ : ∀ {xs ys zs ws} → (bx : B xs) (by : B ys) (bz : B zs)(bw : B ws)
                     → SquareP (λ i j → B (⊙-pentagon-□ xs ys zs ws i j))
                         (b⊙-pent-diag bx by bz bw)
                         (b⊙-assoc _ _ _)
                         (λ i → b⊙-assoc bx by bz i b⊙ bw)
                         λ i → bx b⊙ b⊙-assoc by bz bw (~ i)

     module _ (isGroupoidB : ∀ x → isGroupoid (B x)) where
      f₃ : ∀ x → B x
      f₃ [] = b[]
      f₃ [ a ] = b[ a ]
      f₃ (xs ⊙ ys) = f₃ xs b⊙ f₃ ys
      f₃ (⊙-comm xs ys i) =
        b⊙-comm (f₃ xs) (f₃ ys) i
      f₃ (⊙-unit-r x i) = b⊙ur (f₃ x) i
      f₃ (⊙-unit-l x i) = b⊙ul (f₃ x) i
      f₃ (⊙-assoc xs ys zs i) =
        b⊙-assoc (f₃ xs) (f₃ ys) (f₃ zs) i
      f₃ (⊙-triangle xs ys i j) =
        b⊙-triangle (f₃ xs) (f₃ ys) i j
      f₃ (⊙-pentagon-diag xs ys zs ws i) =
        b⊙-pent-diag (f₃ xs) (f₃ ys) (f₃ zs) (f₃ ws) i

      f₃ (⊙-hex-diag l c r i) =
        b⊙-hex-diag (f₃ l) (f₃ c) (f₃ r)  i

      f₃ (⊙-hex-up l c r i j) =
        b⊙-hex-up (f₃ l) (f₃ c) (f₃ r) i j 
      f₃ (⊙-hex-down l c r i j) =
        b⊙-hex-down (f₃ l) (f₃ c) (f₃ r) i j


      f₃ (⊙-pentagon-△ xs ys zs ws i j) =
        b⊙-pent-△ (f₃ xs) (f₃ ys) (f₃ zs) (f₃ ws) i j
      f₃ (⊙-pentagon-□ xs ys zs ws i j) =
        b⊙-pent-□ (f₃ xs) (f₃ ys) (f₃ zs) (f₃ ws) i j
      f₃ (trunc x y p q r s i₀ i₁ i₂) =
         (isOfHLevel→isOfHLevelDep (suc (suc (suc zero))) isGroupoidB)
              (f₃ x) (f₃ y)
              (cong f₃ p) (cong f₃ q)
              (λ i₃ i₄ → f₃ (r i₃ i₄)) (λ i₃ i₄ → f₃ (s i₃ i₄))
              (trunc x y p q r s) i₀ i₁ i₂
              
    open H3 using (f₃) public
     
    module _ (isSetB : ∀ x → isSet (B x)) where
     r₃ : H3
     H3.b⊙-triangle r₃ _ _ =
       isSet→SquareP (λ _ _ → isSetB _) _ _ _ _
     H3.b⊙-hex-up r₃ _ _ _ =
       isSet→SquareP (λ _ _ → isSetB _) _ _ _ _
     H3.b⊙-hex-down r₃ _ _ _ =
       isSet→SquareP (λ _ _ → isSetB _) _ _ _ _
     H3.b⊙-pent-△ r₃ _ _ _ _ = 
       isSet→SquareP (λ _ _ → isSetB _) _ _ _ _          
     H3.b⊙-pent-□ r₃ _ _ _ _ =
       isSet→SquareP (λ _ _ → isSetB _) _ _ _ _ 

     f₂ : ∀ x → B x
     f₂ = H3.f₃ r₃ (isSet→isGroupoid ∘ isSetB)


   module _ (isPropB : ∀ x → isProp (B x)) where
    r₂ : H2
    H2.b⊙-comm r₂ _ _ = isProp→PathP (λ _ → isPropB _) _ _
    H2.b⊙ur r₂ _ = isProp→PathP (λ _ → isPropB _) _ _
    H2.b⊙ul r₂ _ = isProp→PathP (λ _ → isPropB _) _ _
    H2.b⊙-assoc r₂ _ _ _ = isProp→PathP (λ _ → isPropB _) _ _
    H2.b⊙-hex-diag r₂ _ _ _ = isProp→PathP (λ _ → isPropB _) _ _
    H2.b⊙-pent-diag r₂ _ _ _ _ = isProp→PathP (λ _ → isPropB _) _ _
    
    f₁ : ∀ x → B x
    f₁ = H2.f₂ r₂ (isProp→isSet ∘ isPropB)


   open H2 using (f₂ ; H3 ; f₃) public 
  open H1 using (H2 ; f₂ ; H3 ; f₃ ; f₁) public

  ElimFCM₃ : HLevel → Type (ℓ-max ℓ ℓb)
  ElimFCM₃ 0 = Unit*
  ElimFCM₃ 1 = H1
  ElimFCM₃ 2 = Σ _ H2
  ElimFCM₃ (suc (suc (suc _))) = Σ (Σ _ H2) (H3 ∘ snd )



module _ {A : Type ℓ} {ℓb} (B : FCM₃ A → Type ℓb) where
 open ElimFCM₃

 elimFCM₃ : (n : HLevel) → ElimFCM₃ B n →
       if Dec→Bool (≤Dec n 3)
        then
        ((∀ x → isOfHLevel n (B x))

        → ∀ x →  B x)
        else Unit* --(∀ x → ∥ B x ∥₃)
 elimFCM₃ 0 _ = fst ∘_
 elimFCM₃ 1 = f₁
 elimFCM₃ 2 = uncurry λ _ → f₂ 
 elimFCM₃ 3 = uncurry (λ z → f₃)
 elimFCM₃ (suc (suc (suc (suc n)))) x = _
  --   f₃  (snd w) λ _ → squash₃
  -- where
  -- w : ElimFCM₃ (∥_∥₃ ∘ B) 3
  -- H1.b[] (fst (fst w)) = ∣ H1.b[] (fst (fst x)) ∣₃ 
  -- H1.b[ fst (fst w) ] = ∣_∣₃ ∘ H1.b[_] (fst (fst x))
  -- H1._b⊙_ (fst (fst w)) = {!!}
  -- snd (fst w) = {!!}
  -- snd w = {!!}

module _ {A : Type ℓ} where
 module RecFCM₃ {ℓb} (B : Type ℓb) where 

  record H1 : Type (ℓ-max ℓ ℓb) where
   no-eta-equality
   field
    b[] : B
    b[_] : A → B
    _b⊙_ : B → B → B
    

   record H2 : Type (ℓb) where
    no-eta-equality
    field
     b⊙-comm : ∀ bx by → (bx b⊙ by) ≡ (by b⊙ bx)
     b⊙ur : ∀ b → (b b⊙ b[]) ≡ b
     b⊙ul : ∀ b → (b[] b⊙ b) ≡ b
     b⊙-assoc : ∀ bx by bz → ((bx b⊙ by) b⊙ bz) ≡ (bx b⊙ (by b⊙ bz))
     b⊙-hex-diag : ∀ l c r → ((l b⊙ c) b⊙ r) ≡ (c b⊙ (r b⊙ l))

     b⊙-pent-diag : ∀ bx by bz bw →
                      (((bx b⊙ by) b⊙ bz) b⊙ bw)
                      ≡  (bx b⊙ (by b⊙ (bz b⊙ bw)))


    record H3 : Type (ℓb) where
     no-eta-equality
     field
      b⊙-triangle : ∀ bx by
                     → Square
                         (b⊙-assoc bx b[] by)
                         refl
                         (λ i → b⊙ur bx i b⊙ by)
                         λ i → bx b⊙ b⊙ul by i

      b⊙-hex-up : ∀ l c r
                     → Square
                           (b⊙-comm l (c b⊙ r))
                           (b⊙-hex-diag l c r)
                           (sym (b⊙-assoc l c r))
                           (b⊙-assoc c r l)
 
      b⊙-hex-down : ∀ l c r
                    → Square   (b⊙-hex-diag l c r)
                               (b⊙-assoc c l r)
                               (cong (_b⊙ r) (b⊙-comm l c))
                               (cong (c b⊙_) (b⊙-comm r l))


      b⊙-pent-△ : ∀ bx by bz bw →
                   Square
                         refl
                          (b⊙-pent-diag bx by bz bw)
                          (symP (b⊙-assoc _ _ _))
                          (b⊙-assoc _ _ _)
      b⊙-pent-□ : ∀ bx by bz bw →
                   Square
                         (b⊙-pent-diag bx by bz bw)
                         (b⊙-assoc _ _ _)
                         (λ i → b⊙-assoc bx by bz i b⊙ bw)
                         λ i → bx b⊙ b⊙-assoc by bz bw (~ i)

     module _ (isGroupoidB : isGroupoid B) where
      f₃ : FCM₃ A → B
      f₃ [] = b[]
      f₃ [ a ] = b[ a ]
      f₃ (xs ⊙ ys) = f₃ xs b⊙ f₃ ys
      f₃ (⊙-comm xs ys i) =
        b⊙-comm (f₃ xs) (f₃ ys) i
      f₃ (⊙-unit-r x i) = b⊙ur (f₃ x) i
      f₃ (⊙-unit-l x i) = b⊙ul (f₃ x) i
      f₃ (⊙-assoc xs ys zs i) =
        b⊙-assoc (f₃ xs) (f₃ ys) (f₃ zs) i
      f₃ (⊙-triangle xs ys i j) =
        b⊙-triangle (f₃ xs) (f₃ ys) i j
      f₃ (⊙-pentagon-diag xs ys zs ws i) =
        b⊙-pent-diag (f₃ xs) (f₃ ys) (f₃ zs) (f₃ ws) i

      f₃ (⊙-hex-diag l c r i) =
        b⊙-hex-diag (f₃ l) (f₃ c) (f₃ r) i
        

      f₃ (⊙-hex-up l c r i j) =
        b⊙-hex-up (f₃ l) (f₃ c) (f₃ r) i j
      f₃ (⊙-hex-down l c r i j) =
        b⊙-hex-down (f₃ l) (f₃ c) (f₃ r) i j

      f₃ (⊙-pentagon-△ xs ys zs ws i j) =
        b⊙-pent-△ (f₃ xs) (f₃ ys) (f₃ zs) (f₃ ws) i j
      f₃ (⊙-pentagon-□ xs ys zs ws i j) =
        b⊙-pent-□ (f₃ xs) (f₃ ys) (f₃ zs) (f₃ ws) i j
      f₃ (trunc x y p q r s i₀ i₁ i₂) =
         isGroupoidB
              (f₃ x) (f₃ y)
              (cong f₃ p) (cong f₃ q)
              (λ i₃ i₄ → f₃ (r i₃ i₄)) (λ i₃ i₄ → f₃ (s i₃ i₄))
               i₀ i₁ i₂
              
    open H3 public
     
    module _ (isSetB : isSet B) where
     r₃ : H3
     H3.b⊙-triangle r₃ _ _ =
       isSet→isSet' isSetB _ _ _ _
     H3.b⊙-hex-up r₃ _ _ _ =
       isSet→isSet' isSetB _ _ _ _
     H3.b⊙-hex-down r₃ _ _ _ =
       isSet→isSet' isSetB _ _ _ _
     H3.b⊙-pent-△ r₃ _ _ _ _ = 
       isSet→isSet' isSetB _ _ _ _          
     H3.b⊙-pent-□ r₃ _ _ _ _ =
       isSet→isSet' isSetB _ _ _ _ 

     f₂ : FCM₃ A → B
     f₂ = H3.f₃ r₃ (isSet→isGroupoid isSetB)


   module _ (isPropB : isProp B) where
    r₂ : H2
    H2.b⊙-comm r₂ _ _ = isPropB _ _
    H2.b⊙ur r₂ _ = isPropB _ _
    H2.b⊙ul r₂ _ = isPropB _ _
    H2.b⊙-assoc r₂ _ _ _ = isPropB _ _
    H2.b⊙-hex-diag r₂ _ _ _ = isPropB _ _ 
    H2.b⊙-pent-diag r₂ _ _ _ _ = isPropB _ _
    
    f₁ : FCM₃ A → B
    f₁ = H2.f₂ r₂ (isProp→isSet isPropB)


   open H2 public 
  open H1 public

  RecFCM₃ : HLevel → Type (ℓ-max ℓ ℓb)
  RecFCM₃ 0 = Unit*
  RecFCM₃ 1 = H1
  RecFCM₃ 2 = Σ _ H2
  RecFCM₃ (suc (suc (suc _))) = Σ (Σ _ H2) (H3 ∘ snd )

module _ {A : Type ℓ} {ℓb} (B : Type ℓb) where
 open RecFCM₃

 recFCM₃ : (n : HLevel) → RecFCM₃ {ℓ = ℓ} {A = A} B n →
       if Dec→Bool (≤Dec n 3)
        then
        ((isOfHLevel n B)

        → FCM₃ A →  B)
        else Unit* --(∀ x → ∥ B x ∥₃)
 recFCM₃ 0 _ (b , _) _ = b
 recFCM₃ 1 = f₁
 recFCM₃ 2 = uncurry λ _ → f₂ 
 recFCM₃ 3 = uncurry (λ z → f₃)
 recFCM₃ (suc (suc (suc (suc n)))) x = _




data ℙ {ℓ} (A : Type ℓ) : Type ℓ where
 𝕡base : List A → ℙ A
 𝕡loopL : ∀ xs ys zs ws →
    𝕡base ((xs ++ (ys ++ zs)) ++ ws) ≡ 𝕡base ((xs ++ (zs ++ ys)) ++ ws)
 𝕡loopR : ∀ xs ys zs ws →
    𝕡base (xs ++ (ys ++ zs) ++ ws) ≡ 𝕡base (xs ++ (zs ++ ys) ++ ws)
 𝕡loopAssoc : ∀ xs ys zs ws → Square
     (𝕡loopL xs ys zs ws)
     (𝕡loopR xs ys zs ws)
     (cong 𝕡base (++-assoc _ _ _))
     (cong 𝕡base (++-assoc _ _ _))

 𝕡involL : ∀ xs ys zs ws →
    𝕡loopL xs ys zs ws ≡ sym (𝕡loopL xs zs ys ws)


 𝕡hexDiagAB : ∀ ls xs ys zs rs  →
      𝕡base (ls ++ ((xs ++ ys) ++ zs) ++ rs) ≡
      𝕡base ((ls ++ ys ++ zs ++ xs) ++ rs)
 𝕡hexDiagBC : ∀ ls xs ys zs rs  →
      𝕡base (ls ++ (xs ++ ys) ++ (zs ++ rs)) ≡
      𝕡base (((ls ++ ys) ++ zs ++ xs) ++ rs)
 𝕡hexDiagCD : ∀ ls xs ys zs rs  →
      𝕡base ((ls ++ xs ++ ys) ++ zs ++ rs) ≡
      𝕡base (((ls ++ ys) ++ (xs ++ zs)) ++ rs)

 𝕡hexA : ∀ ls xs ys zs rs  →
   Square
     (𝕡loopL ls xs (ys ++ zs) rs)
     (𝕡hexDiagAB ls xs ys zs rs)
     (λ i → 𝕡base (++-assoc ls (++-assoc xs ys zs (~ i)) rs i))
     (λ i → 𝕡base ((ls ++ (++-assoc ys zs xs i)) ++ rs))

 𝕡hexB : ∀ ls xs ys zs rs  →
   Square
     (𝕡hexDiagAB ls xs ys zs rs)
     (𝕡hexDiagBC ls xs ys zs rs)
     (cong (𝕡base ∘ (ls ++_)) (++-assoc _ _ _))
     (cong (𝕡base ∘ (_++ rs)) (sym (++-assoc _ _ _)))
 𝕡hexC : ∀ ls xs ys zs rs  →
   Square
     (𝕡hexDiagBC ls xs ys zs rs)
     (𝕡hexDiagCD ls xs ys zs rs)
     (cong (𝕡base) (sym (++-assoc _ _ _)))
     (𝕡loopL (ls ++ ys) zs xs rs)

 𝕡hexD : ∀ ls xs ys zs rs  →
   Square
     (𝕡hexDiagCD ls xs ys zs rs)
     (λ i → 𝕡base ((++-assoc (++-assoc ls ys xs (~ i)) zs rs) (~ i)))
     (𝕡loopL ls xs ys (zs ++ rs))
     λ i → 𝕡base ((++-assoc (ls ++ ys) xs zs (~ i)) ++ rs)
 𝕡trunc : isGroupoid (ℙ A)


module _ {A : Type ℓ} where
 module Elimℙ {ℓb} (B : ℙ A → Type ℓb) where 

  record H1 : Type (ℓ-max ℓ ℓb) where
   no-eta-equality
   constructor h1
   field
    bbase : ∀ a → B (𝕡base a)

   record H2 : Type (ℓ-max ℓ ℓb) where
    no-eta-equality
    constructor h2
    field
     bloopL : ∀ xs ys zs ws →
        PathP (λ i → B (𝕡loopL xs ys zs ws i))
        (bbase ((xs ++ (ys ++ zs)) ++ ws))
        (bbase ((xs ++ (zs ++ ys)) ++ ws))
     bloopR : ∀ xs ys zs ws →
       PathP (λ i → B (𝕡loopR xs ys zs ws i))
        (bbase (xs ++ (ys ++ zs) ++ ws))
        (bbase (xs ++ (zs ++ ys) ++ ws))
     
     bhexDiagAB : ∀ ls xs ys zs rs  →
       PathP (λ i → B (𝕡hexDiagAB ls xs ys zs rs i))     
          (bbase (ls ++ ((xs ++ ys) ++ zs) ++ rs))
          (bbase ((ls ++ ys ++ zs ++ xs) ++ rs))
     bhexDiagBC :  ∀ ls xs ys zs rs  →
       PathP (λ i → B (𝕡hexDiagBC ls xs ys zs rs i))
          (bbase (ls ++ (xs ++ ys) ++ (zs ++ rs)))
          (bbase (((ls ++ ys) ++ zs ++ xs) ++ rs))
     bhexDiagCD :  ∀ ls xs ys zs rs  →
       PathP (λ i → B (𝕡hexDiagCD ls xs ys zs rs i))
          (bbase ((ls ++ xs ++ ys) ++ zs ++ rs))
          (bbase (((ls ++ ys) ++ (xs ++ zs)) ++ rs))

    record H3 : Type (ℓ-max ℓ ℓb) where
     no-eta-equality
     constructor h3
     field
      binvolL : ∀ xs ys zs ws →
        SquareP (λ i j → B (𝕡involL xs ys zs ws i j))
         (bloopL xs ys zs ws)
         (symP (bloopL xs zs ys ws))
         refl
         refl
      bloopAssoc : ∀ xs ys zs ws →
        SquareP (λ i j → B (𝕡loopAssoc xs ys zs ws i j))
         (bloopL xs ys zs ws)
         (bloopR xs ys zs ws)
         (cong bbase (++-assoc _ _ _))
         (cong bbase (++-assoc _ _ _))
      bhexA : ∀ ls xs ys zs rs  →
        SquareP (λ i j → B (𝕡hexA ls xs ys zs rs i j))
          (bloopL ls xs (ys ++ zs) rs)
          (bhexDiagAB ls xs ys zs rs)
          (λ i → bbase (++-assoc ls (++-assoc xs ys zs (~ i)) rs i))
          (λ i → bbase ((ls ++ (++-assoc ys zs xs i)) ++ rs))
      bhexB : ∀ ls xs ys zs rs  →
        SquareP (λ i j → B (𝕡hexB ls xs ys zs rs i j))
          (bhexDiagAB ls xs ys zs rs)
          (bhexDiagBC ls xs ys zs rs)
          (cong (bbase ∘ (ls ++_)) (++-assoc _ _ _))
          (cong (bbase ∘ (_++ rs)) (sym (++-assoc _ _ _)))
      bhexC : ∀ ls xs ys zs rs  →
        SquareP (λ i j → B (𝕡hexC ls xs ys zs rs i j))
          (bhexDiagBC ls xs ys zs rs)
          (bhexDiagCD ls xs ys zs rs)
          (cong (bbase) (sym (++-assoc _ _ _)))
          (bloopL (ls ++ ys) zs xs rs)

      bhexD : ∀ ls xs ys zs rs  →
        SquareP (λ i j → B (𝕡hexD ls xs ys zs rs i j))
          (bhexDiagCD ls xs ys zs rs)
          (λ i → bbase ((++-assoc (++-assoc ls ys xs (~ i)) zs rs) (~ i)))
          (bloopL ls xs ys (zs ++ rs))
          λ i → bbase ((++-assoc (ls ++ ys) xs zs (~ i)) ++ rs)

     module _ (isGroupoidB : ∀ x → isGroupoid (B x)) where
      f₃ : ∀ x → B x
      f₃ (𝕡base x) = bbase x
      f₃ (𝕡loopL xs ys zs ws i) =
        bloopL xs ys zs ws i
      f₃ (𝕡loopR xs ys zs ws i) =
        bloopR xs ys zs ws i
      f₃ (𝕡loopAssoc xs ys zs ws i i₁) =
        bloopAssoc xs ys zs ws i i₁
      f₃ (𝕡involL xs ys zs ws i i₁) =
        binvolL xs ys zs ws i i₁
      f₃ (𝕡hexDiagAB ls xs ys zs rs i) =
        bhexDiagAB ls xs ys zs rs i
      f₃ (𝕡hexDiagBC ls xs ys zs rs i) =
        bhexDiagBC ls xs ys zs rs i
      f₃ (𝕡hexDiagCD ls xs ys zs rs i) =
        bhexDiagCD ls xs ys zs rs i
      f₃ (𝕡hexA ls xs ys zs rs i i₁) =
        bhexA ls xs ys zs rs i i₁
      f₃ (𝕡hexB ls xs ys zs rs i i₁) =
        bhexB ls xs ys zs rs i i₁
      f₃ (𝕡hexC ls xs ys zs rs i i₁) =
        bhexC ls xs ys zs rs i i₁
      f₃ (𝕡hexD ls xs ys zs rs i i₁) =
        bhexD ls xs ys zs rs i i₁
      f₃ (𝕡trunc x y p q r s i₀ i₁ i₂) = 
         (isOfHLevel→isOfHLevelDep (suc (suc (suc zero))) isGroupoidB)
              (f₃ x) (f₃ y)
              (cong f₃ p) (cong f₃ q)
              (λ i₃ i₄ → f₃ (r i₃ i₄)) (λ i₃ i₄ → f₃ (s i₃ i₄))
              (𝕡trunc x y p q r s) i₀ i₁ i₂

    

    open H3 public

    private
     isOfHLevelH3' : ∀ n → (∀ x → isOfHLevel (suc (suc n)) (B x)) →
                          isOfHLevel n H3  
     isOfHLevelH3' n hLevB =
       isOfHLevelRetract
         n {B = _}
         (λ x → ((((x .binvolL , x .bloopAssoc ) ,
                     x .bhexA) , x .bhexB) , x .bhexC) , x .bhexD)
         (u u u u u h3)
         h
         (isOfHLevel× n
            (isOfHLevel× n
             (isOfHLevel× n (isOfHLevel× n (isOfHLevel× n
               (isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                  λ _ _ → isOfHLevelPathP' n
                           (isOfHLevelPathP' (suc n)
                               (λ _ _ → hLevB _ _ _) _ _) _ _  )
               ((isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                  λ _ _ → isOfHLevelPathP' n
                           (isOfHLevelPathP' (suc n)
                               (λ _ _ → hLevB _ _ _) _ _) _ _  )))
               ((isOfHLevelΠ n λ _ → isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                  λ _ _ → isOfHLevelPathP' n
                           (isOfHLevelPathP' (suc n)
                               (λ _ _ → hLevB _ _ _) _ _) _ _  )))
              ((isOfHLevelΠ n λ _ → isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                  λ _ _ → isOfHLevelPathP' n
                           (isOfHLevelPathP' (suc n)
                               (λ _ _ → hLevB _ _ _) _ _) _ _  )))
             ((isOfHLevelΠ n λ _ → isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                  λ _ _ → isOfHLevelPathP' n
                           (isOfHLevelPathP' (suc n)
                               (λ _ _ → hLevB _ _ _) _ _) _ _  )))
            ((isOfHLevelΠ n λ _ → isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                  λ _ _ → isOfHLevelPathP' n
                           (isOfHLevelPathP' (suc n)
                               (λ _ _ → hLevB _ _ _) _ _) _ _  )))
      where
       u_ = uncurry
       h : ∀ x → _
       binvolL (h x i) = binvolL x
       bloopAssoc (h x i) = bloopAssoc x
       bhexA (h x i) = bhexA x
       bhexB (h x i) = bhexB x
       bhexC (h x i) = bhexC x
       bhexD (h x i) = bhexD x

    isOfHLevelH3 = isOfHLevelH3'


    module _ (isSetB : ∀ x → isSet (B x)) where


     r₂ : H3
     binvolL r₂ _ _ _ _ = isSet→SquareP (λ _ _ → isSetB _) _ _ _ _
     bloopAssoc r₂ _ _ _ _ = isSet→SquareP (λ _ _ → isSetB _) _ _ _ _
     bhexA r₂ _ _ _ _ _ = isSet→SquareP (λ _ _ → isSetB _) _ _ _ _
     bhexB r₂ _ _ _ _ _ = isSet→SquareP (λ _ _ → isSetB _) _ _ _ _
     bhexC r₂ _ _ _ _ _ = isSet→SquareP (λ _ _ → isSetB _) _ _ _ _
     bhexD r₂ _ _ _ _ _ = isSet→SquareP (λ _ _ → isSetB _) _ _ _ _

     f₂ : ∀ x → B x
     f₂ = f₃ r₂ (isSet→isGroupoid ∘ isSetB)


   open H2 public

   private
    isOfHLevelH2' : ∀ n → (∀ x → isOfHLevel (suc n) (B x)) →
                         isOfHLevel n H2
    isOfHLevelH2' n hLevB =
      isOfHLevelRetract
        n {B = _}
        (λ x → ((((x .bloopL) , (x .bloopR)) ,
              (x .bhexDiagAB)) ,
              (x .bhexDiagBC)) ,
              (x .bhexDiagCD))
        (u u u u h2)
        h
        ((isOfHLevel× n
            (isOfHLevel× n (isOfHLevel× n (isOfHLevel× n
              (isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                 λ _ _ → isOfHLevelPathP' n (hLevB _) _ _  )
              ((isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                 λ _ _ → isOfHLevelPathP' n
                          (hLevB _) _ _  )))
              ((isOfHLevelΠ n λ _ → isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                 λ _ _ → isOfHLevelPathP' n
                          (hLevB _) _ _  )))
             ((isOfHLevelΠ n λ _ → isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                 λ _ _ → isOfHLevelPathP' n
                          (hLevB _) _ _  )))
            ((isOfHLevelΠ n λ _ → isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                 λ _ _ → isOfHLevelPathP' n
                          (hLevB _) _ _  ))))
     where
      u_ = uncurry
      h : ∀ x → _
      bloopL (h x i) = bloopL x
      bloopR (h x i) = bloopR x
      bhexDiagAB (h x i) = bhexDiagAB x
      bhexDiagBC (h x i) = bhexDiagBC x
      bhexDiagCD (h x i) = bhexDiagCD x

   isOfHLevelH2 = isOfHLevelH2'

   module _ (isPropB : ∀ x → isProp (B x)) where

    r₁ : H2
    bloopL r₁ _ _ _ _ = isProp→PathP (λ _ → isPropB _) _ _
    bloopR r₁ _ _ _ _ = isProp→PathP (λ _ → isPropB _) _ _
    bhexDiagAB r₁ _ _ _ _ _ = isProp→PathP (λ _ → isPropB _) _ _
    bhexDiagBC r₁ _ _ _ _ _ = isProp→PathP (λ _ → isPropB _) _ _
    bhexDiagCD r₁ _ _ _ _ _ = isProp→PathP (λ _ → isPropB _) _ _
    
    f₁ : ∀ x → B x
    f₁ = f₂ r₁ (isProp→isSet ∘ isPropB)
  open H1 public

  
  private
   isOfHLevelH1' : ∀ n → (∀ x → isOfHLevel n (B x)) →
                        isOfHLevel n H1
   isOfHLevelH1' n hLevB =
     isOfHLevelRetract n
       bbase
       h1
       h
       (isOfHLevelΠ n λ _ → hLevB _) 
    where
     h : ∀ x → _
     bbase (h x i) = bbase x
     
  isOfHLevelH1 = isOfHLevelH1'
module _ {A : Type ℓ} where
 module Recℙ {ℓb} (B : Type ℓb) where 

  record H1 : Type (ℓ-max ℓ ℓb) where
   no-eta-equality
   constructor h1
   field
    bbase : List A → B

   record H2 : Type (ℓ-max ℓ ℓb) where
    no-eta-equality
    constructor h2
    field
     bloopL : ∀ xs ys zs ws →
        bbase ((xs ++ (ys ++ zs)) ++ ws) ≡ bbase ((xs ++ (zs ++ ys)) ++ ws)
     bloopR : ∀ xs ys zs ws →
        bbase (xs ++ (ys ++ zs) ++ ws) ≡ bbase (xs ++ (zs ++ ys) ++ ws)
     
     bhexDiagAB : ∀ ls xs ys zs rs  →
          bbase (ls ++ ((xs ++ ys) ++ zs) ++ rs) ≡
          bbase ((ls ++ ys ++ zs ++ xs) ++ rs)
     bhexDiagBC : ∀ ls xs ys zs rs  →
          bbase (ls ++ (xs ++ ys) ++ (zs ++ rs)) ≡
          bbase (((ls ++ ys) ++ zs ++ xs) ++ rs)
     bhexDiagCD : ∀ ls xs ys zs rs  →
          bbase ((ls ++ xs ++ ys) ++ zs ++ rs) ≡
          bbase (((ls ++ ys) ++ (xs ++ zs)) ++ rs)

    record H3 : Type (ℓ-max ℓ ℓb) where
     no-eta-equality
     constructor h3
     field
      binvolL : ∀ xs ys zs ws →
         bloopL xs ys zs ws ≡ sym (bloopL xs zs ys ws)
      bloopAssoc : ∀ xs ys zs ws → Square
         (bloopL xs ys zs ws)
         (bloopR xs ys zs ws)
         (cong bbase (++-assoc _ _ _))
         (cong bbase (++-assoc _ _ _))

      bhexA : ∀ ls xs ys zs rs  →
        Square
          (bloopL ls xs (ys ++ zs) rs)
          (bhexDiagAB ls xs ys zs rs)
          (λ i → bbase (++-assoc ls (++-assoc xs ys zs (~ i)) rs i))
          (λ i → bbase ((ls ++ (++-assoc ys zs xs i)) ++ rs))

      bhexB : ∀ ls xs ys zs rs  →
        Square
          (bhexDiagAB ls xs ys zs rs)
          (bhexDiagBC ls xs ys zs rs)
          (cong (bbase ∘ (ls ++_)) (++-assoc _ _ _))
          (cong (bbase ∘ (_++ rs)) (sym (++-assoc _ _ _)))
      bhexC : ∀ ls xs ys zs rs  →
        Square
          (bhexDiagBC ls xs ys zs rs)
          (bhexDiagCD ls xs ys zs rs)
          (cong (bbase) (sym (++-assoc _ _ _)))
          (bloopL (ls ++ ys) zs xs rs)

      bhexD : ∀ ls xs ys zs rs  →
        Square
          (bhexDiagCD ls xs ys zs rs)
          (λ i → bbase ((++-assoc (++-assoc ls ys xs (~ i)) zs rs) (~ i)))
          (bloopL ls xs ys (zs ++ rs))
          λ i → bbase ((++-assoc (ls ++ ys) xs zs (~ i)) ++ rs)

     module _ (isGroupoidB : isGroupoid B) where
      f₃ : ℙ A → B
      f₃ (𝕡base x) = bbase x
      f₃ (𝕡loopL xs ys zs ws i) =
        bloopL xs ys zs ws i
      f₃ (𝕡loopR xs ys zs ws i) =
        bloopR xs ys zs ws i
      f₃ (𝕡loopAssoc xs ys zs ws i i₁) =
        bloopAssoc xs ys zs ws i i₁
      f₃ (𝕡involL xs ys zs ws i i₁) =
        binvolL xs ys zs ws i i₁
      f₃ (𝕡hexDiagAB ls xs ys zs rs i) =
        bhexDiagAB ls xs ys zs rs i
      f₃ (𝕡hexDiagBC ls xs ys zs rs i) =
        bhexDiagBC ls xs ys zs rs i
      f₃ (𝕡hexDiagCD ls xs ys zs rs i) =
        bhexDiagCD ls xs ys zs rs i
      f₃ (𝕡hexA ls xs ys zs rs i i₁) =
        bhexA ls xs ys zs rs i i₁
      f₃ (𝕡hexB ls xs ys zs rs i i₁) =
        bhexB ls xs ys zs rs i i₁
      f₃ (𝕡hexC ls xs ys zs rs i i₁) =
        bhexC ls xs ys zs rs i i₁
      f₃ (𝕡hexD ls xs ys zs rs i i₁) =
        bhexD ls xs ys zs rs i i₁
      f₃ (𝕡trunc x y p q r s i₀ i₁ i₂) = 
         isGroupoidB
              (f₃ x) (f₃ y)
              (cong f₃ p) (cong f₃ q)
              (λ i₃ i₄ → f₃ (r i₃ i₄)) (λ i₃ i₄ → f₃ (s i₃ i₄))
               i₀ i₁ i₂

    open H3 public
    
    private
     isOfHLevelH3' : ∀ n → (isOfHLevel (suc (suc n)) B) →
                          isOfHLevel n H3  
     isOfHLevelH3' n hLevB =
       isOfHLevelRetract
         n {B = _}
         (λ x → ((((x .binvolL , x .bloopAssoc ) ,
                     x .bhexA) , x .bhexB) , x .bhexC) , x .bhexD)
         (u u u u u h3)
         h
         (isOfHLevel× n
            (isOfHLevel× n
             (isOfHLevel× n (isOfHLevel× n (isOfHLevel× n
               (isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                  λ _ _ → isOfHLevelPathP' n
                           (isOfHLevelPathP' (suc n)
                               (λ _ _ → hLevB _ _) _ _) _ _  )
               ((isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                  λ _ _ → isOfHLevelPathP' n
                           (isOfHLevelPathP' (suc n)
                               (λ _ _ → hLevB _ _) _ _) _ _  )))
               ((isOfHLevelΠ n λ _ → isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                  λ _ _ → isOfHLevelPathP' n
                           (isOfHLevelPathP' (suc n)
                               (λ _ _ → hLevB _ _) _ _) _ _  )))
              ((isOfHLevelΠ n λ _ → isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                  λ _ _ → isOfHLevelPathP' n
                           (isOfHLevelPathP' (suc n)
                               (λ _ _ → hLevB _ _) _ _) _ _  )))
             ((isOfHLevelΠ n λ _ → isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                  λ _ _ → isOfHLevelPathP' n
                           (isOfHLevelPathP' (suc n)
                               (λ _ _ → hLevB _ _) _ _) _ _  )))
            ((isOfHLevelΠ n λ _ → isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                  λ _ _ → isOfHLevelPathP' n
                           (isOfHLevelPathP' (suc n)
                               (λ _ _ → hLevB _ _) _ _) _ _  )))
      where
       u_ = uncurry
       h : ∀ x → _
       binvolL (h x i) = binvolL x
       bloopAssoc (h x i) = bloopAssoc x
       bhexA (h x i) = bhexA x
       bhexB (h x i) = bhexB x
       bhexC (h x i) = bhexC x
       bhexD (h x i) = bhexD x

    isOfHLevelH3 = isOfHLevelH3'
    
    module _ (isSetB : isSet B) where

     isSetB' = isSet→isSet' isSetB

     r₂ : H3
     binvolL r₂ _ _ _ _ = isSetB _ _ _ _
     bloopAssoc r₂ _ _ _ _ = isSetB' _ _ _ _
     bhexA r₂ _ _ _ _ _ = isSetB' _ _ _ _
     bhexB r₂ _ _ _ _ _ = isSetB' _ _ _ _
     bhexC r₂ _ _ _ _ _ = isSetB' _ _ _ _
     bhexD r₂ _ _ _ _ _ = isSetB' _ _ _ _

     f₂ : ℙ A → B
     f₂ = f₃ r₂ (isSet→isGroupoid isSetB)


   open H2 public

   H2* : Type (ℓ-max ℓ ℓb)
   H2* = ∀ xs ys zs ws → bbase ((xs ++ (ys ++ zs)) ++ ws) ≡ bbase ((xs ++ (zs ++ ys)) ++ ws)

   fromH2* : H2* → H2
   bloopL (fromH2* x) = x
   bloopR (fromH2* x) xs ys zs ws =
     cong bbase (sym (++-assoc _ _ _))
      ∙∙ x xs ys zs ws ∙∙
     cong bbase  (++-assoc _ _ _)
   bhexDiagAB (fromH2* x) ls xs ys zs rs = 
      cong bbase (
              cong (λ x → ls ++ x ++ rs) (++-assoc _ _ _)  ∙
             sym (++-assoc _ _ _))
       ∙∙ x ls xs (ys ++ zs) rs ∙∙
      cong bbase (cong (λ x → (ls ++ x) ++ rs) (++-assoc _ _ _))
   bhexDiagBC (fromH2* x) ls xs ys zs rs =
     cong bbase (
        cong (ls ++_) (sym (++-assoc _ _ _))
        ∙∙ cong (ls ++_) (cong (_++ rs) (++-assoc _ _ _) ) ∙∙ (sym (++-assoc _ _ _))
          )
       ∙∙ x ls xs (ys ++ zs) rs ∙∙
        cong bbase (cong (_++ rs) (cong (ls ++_) (++-assoc _ _ _) ∙ sym (++-assoc _ _ _)))
   bhexDiagCD (fromH2* x) ls xs ys zs rs =
        x ls xs ys (zs ++ rs) ∙
        cong bbase (sym (++-assoc _ _ _) ∙∙
          cong (_++ rs) (cong (_++ zs) (sym (++-assoc _ _ _))) ∙∙ cong (_++ rs) (++-assoc _ _ _))



   private
    isOfHLevelH2' : ∀ n → (isOfHLevel (suc n) B) →
                         isOfHLevel n H2
    isOfHLevelH2' n hLevB =
      isOfHLevelRetract
        n {B = _}
        (λ x → ((((x .bloopL) , (x .bloopR)) ,
              (x .bhexDiagAB)) ,
              (x .bhexDiagBC)) ,
              (x .bhexDiagCD))
        (u u u u h2)
        h
        ((isOfHLevel× n
            (isOfHLevel× n (isOfHLevel× n (isOfHLevel× n
              (isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                 λ _ _ → isOfHLevelPathP' n (hLevB) _ _  )
              ((isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                 λ _ _ → isOfHLevelPathP' n
                          (hLevB) _ _  )))
              ((isOfHLevelΠ n λ _ → isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                 λ _ _ → isOfHLevelPathP' n
                          (hLevB) _ _  )))
             ((isOfHLevelΠ n λ _ → isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                 λ _ _ → isOfHLevelPathP' n
                          (hLevB) _ _  )))
            ((isOfHLevelΠ n λ _ → isOfHLevelΠ2 n λ _ _ → isOfHLevelΠ2 n
                 λ _ _ → isOfHLevelPathP' n
                          (hLevB) _ _  ))))
     where
      u_ = uncurry
      h : ∀ x → _
      bloopL (h x i) = bloopL x
      bloopR (h x i) = bloopR x
      bhexDiagAB (h x i) = bhexDiagAB x
      bhexDiagBC (h x i) = bhexDiagBC x
      bhexDiagCD (h x i) = bhexDiagCD x


   isOfHLevelH2 = isOfHLevelH2'
   
   module _ (isPropB : isProp B) where

    r₁ : H2
    bloopL r₁ _ _ _ _ = isPropB _ _
    bloopR r₁ _ _ _ _ = isPropB _ _
    bhexDiagAB r₁ _ _ _ _ _ = isPropB _ _
    bhexDiagBC r₁ _ _ _ _ _ = isPropB _ _
    bhexDiagCD r₁ _ _ _ _ _ = isPropB _ _
    
    f₁ : ℙ A → B
    f₁ = f₂ r₁ (isProp→isSet isPropB)



  open H1 public

  private
   isOfHLevelH1' : ∀ n → (isOfHLevel n B) →
                        isOfHLevel n H1
   isOfHLevelH1' n hLevB =
     isOfHLevelRetract n
       bbase
       h1
       h
       (isOfHLevelΠ n λ _ → hLevB) 
    where
     h : ∀ x → _
     bbase (h x i) = bbase x

  isOfHLevelH1 = isOfHLevelH1'

--  module Recℙ2 {ℓb} (B : Type ℓb) where

--   r11 : Recℙ.H1 (Recℙ.H1 B)
--   r11 = {!!}
 
--   r21 : Recℙ.H2 r11
--   r21 = {!!}
  
--   r31 : Recℙ.H3 r21
--   r31 = {!!}

--   r12 : Elimℙ.H1 (Recℙ.H2 ∘ Recℙ.f₁ r11 {!!})
--   r12 = {!!}

--   r13 : Elimℙ.H1 (Recℙ.H3 ∘ Elimℙ.H1.f₁ r12 {!!})
--   r13 = {!!}

--   r22 : Elimℙ.H2 r12
--   r22 = {!!}


-- -- -- --     open H3 public
     
-- -- -- --     module _ (isSetB : isSet B) where
-- -- -- --      r₃ : H3
-- -- -- --      H3.b⊙-triangle r₃ _ _ =
-- -- -- --        isSet→isSet' isSetB _ _ _ _
-- -- -- --      H3.b⊙-hex-up r₃ _ _ _ =
-- -- -- --        isSet→isSet' isSetB _ _ _ _
-- -- -- --      H3.b⊙-hex-down r₃ _ _ _ =
-- -- -- --        isSet→isSet' isSetB _ _ _ _
-- -- -- --      H3.b⊙-pent-△ r₃ _ _ _ _ = 
-- -- -- --        isSet→isSet' isSetB _ _ _ _          
-- -- -- --      H3.b⊙-pent-□ r₃ _ _ _ _ =
-- -- -- --        isSet→isSet' isSetB _ _ _ _ 

-- -- -- --      f₂ : FCM₃ A → B
-- -- -- --      f₂ = H3.f₃ r₃ (isSet→isGroupoid isSetB)


-- -- -- --    module _ (isPropB : isProp B) where
-- -- -- --     r₂ : H2
-- -- -- --     H2.b⊙-comm r₂ _ _ = isPropB _ _
-- -- -- --     H2.b⊙ur r₂ _ = isPropB _ _
-- -- -- --     H2.b⊙ul r₂ _ = isPropB _ _
-- -- -- --     H2.b⊙-assoc r₂ _ _ _ = isPropB _ _
-- -- -- --     H2.b⊙-hex-diag r₂ _ _ _ = isPropB _ _ 
-- -- -- --     H2.b⊙-pent-diag r₂ _ _ _ _ = isPropB _ _
    
-- -- -- --     f₁ : FCM₃ A → B
-- -- -- --     f₁ = H2.f₂ r₂ (isProp→isSet isPropB)


-- -- -- --    open H2 public 
-- -- -- --   open H1 public

-- -- -- --   RecFCM₃ : HLevel → Type (ℓ-max ℓ ℓb)
-- -- -- --   RecFCM₃ 0 = Unit*
-- -- -- --   RecFCM₃ 1 = H1
-- -- -- --   RecFCM₃ 2 = Σ _ H2
-- -- -- --   RecFCM₃ (suc (suc (suc _))) = Σ (Σ _ H2) (H3 ∘ snd )

-- -- -- -- module _ {A : Type ℓ} {ℓb} (B : Type ℓb) where
-- -- -- --  open RecFCM₃

-- -- -- --  recFCM₃ : (n : HLevel) → RecFCM₃ {ℓ = ℓ} {A = A} B n →
-- -- -- --        if Dec→Bool (≤Dec n 3)
-- -- -- --         then
-- -- -- --         ((isOfHLevel n B)

-- -- -- --         → FCM₃ A →  B)
-- -- -- --         else Unit* --(∀ x → ∥ B x ∥₃)
-- -- -- --  recFCM₃ 0 _ (b , _) _ = b
-- -- -- --  recFCM₃ 1 = f₁
-- -- -- --  recFCM₃ 2 = uncurry λ _ → f₂ 
-- -- -- --  recFCM₃ 3 = uncurry (λ z → f₃)
-- -- -- --  recFCM₃ (suc (suc (suc (suc n)))) x = _


-- module _ {ℓ} {A : Type ℓ} (l : List A) where
--  open Recℙ {A = A} (Σ (ℙ A × ℙ A) (uncurry _≡_))

--  ℙ++G1 : H1
--  fst (bbase ℙ++G1 x) = 𝕡base (l ++ x) , 𝕡base (x ++ l)
--  snd (bbase ℙ++G1 x) =
--   cong 𝕡base (λ i → ++-unit-r (++-unit-l (l ++ x) (~ i)) (~ i) )
--   ∙∙ 𝕡loopL [] l x [] ∙∙
--   cong 𝕡base (λ i → ++-unit-r (++-unit-l (x ++ l) (i)) (i) )

--  ℙ++G2 : H2 ℙ++G1
--  Recℙ.bloopL ℙ++G2 xs ys zs ws =
--    ΣPathP ((cong₂ _,_
--       (cong 𝕡base (sym (++-assoc l (xs ++ (ys ++ zs)) ws)
--               ∙' cong (_++ ws) (sym (++-assoc _ _ _)))
--             ∙∙ 𝕡loopL (l ++ xs) ys zs ws ∙∙
--           cong 𝕡base (cong (_++ ws) ((++-assoc _ _ _)) ∙ (++-assoc _ _ _)))
--       (cong 𝕡base (++-assoc _ _ _)
--         ∙∙ 𝕡loopL xs ys zs (ws ++ l) ∙∙
--         cong 𝕡base (sym (++-assoc _ _ _))))
--      , {!!}
--          -- (flipSquare
--          -- ({!!} ∙∙₂ refl ∙∙₂ {!!})
--          --  ∙∙₂ {!!} ∙∙₂
--          --  flipSquare
--          -- ({!!} ∙∙₂ refl ∙∙₂ {!!}) )
--          )
--  Recℙ.bloopR ℙ++G2 xs ys zs ws =
--    ΣPathP ((cong₂ _,_
--       (cong 𝕡base (sym (++-assoc _ _ _))
--          ∙∙ 𝕡loopR (l ++ xs) ys zs ws ∙∙
--        cong 𝕡base (++-assoc _ _ _))
--       (cong 𝕡base (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _) )
--          ∙∙ 𝕡loopR xs ys zs (ws ++ l) ∙∙
--        cong 𝕡base (sym (++-assoc _ _ _ ∙ cong (xs ++_) (++-assoc _ _ _)))))
--     , {!!})
--  Recℙ.bhexDiagAB ℙ++G2 ls xs ys zs rs =
--    ΣPathP ((cong₂ _,_
--       (cong 𝕡base (sym (++-assoc _ _ _))
--          ∙∙ 𝕡hexDiagAB (l ++ ls) xs ys zs rs ∙∙
--        cong 𝕡base (cong (_++ rs) (++-assoc _ _ _) ∙ ++-assoc _ _  _))
--       (cong 𝕡base (++-assoc _ _ _ ∙ cong (ls ++_) (++-assoc _ _ _))
--          ∙∙ 𝕡hexDiagAB ls xs ys zs (rs ++ l) ∙∙
--        cong 𝕡base (sym (++-assoc _ _ _))))
--     , {!!})
--  Recℙ.bhexDiagBC ℙ++G2 ls xs ys zs rs =
--    ΣPathP ((cong₂ _,_
--       (cong 𝕡base (sym (++-assoc _ _ _))
--          ∙∙ 𝕡hexDiagBC (l ++ ls) xs ys zs rs ∙∙
--        cong 𝕡base (cong (_++ rs) (++-pentagon-diag _ _ _ _)
--          ∙∙ (++-assoc _ _ _) ∙∙
--          cong (λ x → (l ++ x ++ rs)) (sym (++-assoc _ _ _))))
--       (cong 𝕡base (cong (λ x → ((ls ++ x) ++ l))
--                      (sym (++-assoc _ _ _))
--                     ∙∙ ++-assoc _ _ _ ∙∙
--                     cong (ls ++_) (++-pentagon-diag _ _ _ _))
--          ∙∙ 𝕡hexDiagBC ls xs ys zs (rs ++ l) ∙∙
--        cong 𝕡base (sym (++-assoc _ _ _))))
--     , {!!})
--  Recℙ.bhexDiagCD ℙ++G2 ls xs ys zs rs =
--    ΣPathP ((cong₂ _,_
--       (cong 𝕡base ((sym (++-assoc _ _ _) ∙'
--                   λ i → (++-assoc l ls (xs ++ ys) (~ i)) ++ zs ++ rs))
--          ∙∙ 𝕡hexDiagCD (l ++ ls) xs ys zs rs ∙∙
--        cong 𝕡base (cong ((_++ rs) ∘' (_++ (xs ++ zs))) (++-assoc _ _ _)
--             ∙∙ cong (_++ rs) (++-assoc _ _ _)
--             ∙∙ ++-assoc _ _ _))
--       (cong 𝕡base (++-assoc _ _ _ ∙ cong ((ls ++ xs ++ ys) ++_) (++-assoc _ _ _) )
--          ∙∙ 𝕡hexDiagCD ls xs ys zs (rs ++ l) ∙∙
--        cong 𝕡base (sym (++-assoc _ _ _))))
--     , {!!})

--  ℙ++G3 : H3 ℙ++G2
--  ℙ++G3 = {!!}

--  ℙ++ℙ : ℙ A → Σ (ℙ A × ℙ A) (uncurry _≡_)
--  ℙ++ℙ = f₃ ℙ++G3 {!!} 

--  _++ℙ_ : ℙ A → ℙ A
--  _++ℙ_ = fst ∘ fst ∘ ℙ++ℙ

--  _ℙ++'_ : ℙ A → ℙ A
--  _ℙ++'_ = snd ∘ fst ∘ ℙ++ℙ


-- _ℙ++_ : {A : Type ℓ} → ℙ A → List A → ℙ A
-- _ℙ++_ = flip _ℙ++'_
 

-- _⊙𝕡_ : {A : Type ℓ} → ℙ A → ℙ A  → ℙ A 
-- _⊙𝕡_ {A = A} =
--   LR.f₃
--     lr₃
--     (isGroupoidΠ λ _ → 𝕡trunc)
--  where
 
--  module LR = Recℙ {A = A} (ℙ A  → ℙ A)


--  lr₁ : LR.H1
--  Recℙ.bbase lr₁ = _++ℙ_


--  lr₂ : LR.H2 lr₁
--  Recℙ.bloopL lr₂ = {!!}
--  Recℙ.bloopR lr₂ = {!!}
--  Recℙ.bhexDiagAB lr₂ = {!!}
--  Recℙ.bhexDiagBC lr₂ = {!!}
--  Recℙ.bhexDiagCD lr₂ = {!!}


--  lr₃ : LR.H3 lr₂
--  lr₃ = {!!}



-- -- -- module _ {ℓ} {A : Type ℓ} (l : List A) where
-- -- --  open Recℙ {A = A} (ℙ A)

-- -- --  ℙ++G1 : H1
-- -- --  bbase ℙ++G1 x = 𝕡base (l ++ x)

-- -- --  ℙ++G2 : H2 ℙ++G1
-- -- --  bloopL ℙ++G2 xs ys zs ws = 
-- -- --    cong 𝕡base (sym (++-assoc l (xs ++ (ys ++ zs)) ws)
-- -- --        ∙' cong (_++ ws) (sym (++-assoc _ _ _)))
-- -- --      ∙∙ 𝕡loopL (l ++ xs) ys zs ws ∙∙
-- -- --    cong 𝕡base (cong (_++ ws) ((++-assoc _ _ _)) ∙ (++-assoc _ _ _))
-- -- --  bloopR ℙ++G2 xs ys zs ws =
-- -- --    cong 𝕡base (sym (++-assoc l xs ((ys ++ zs) ++ ws)))
-- -- --      ∙∙ 𝕡loopR _ _ _ _ ∙∙
-- -- --    cong 𝕡base (++-assoc _ _ _)
-- -- --  -- bloopAssoc ℙ++G2 xs ys zs ws i =
-- -- --  --   (λ j → 𝕡base (hlpSq l xs (ys ++ zs) ws j i))
-- -- --  --    ∙∙ 𝕡loopAssoc (l ++ xs) ys zs ws i ∙∙
-- -- --  --   λ j → 𝕡base (hlpSq l xs (zs ++ ys) ws (~ j) i)
   
-- -- --  bhexDiagAB ℙ++G2 ls xs ys zs rs =
-- -- --    cong 𝕡base (sym (++-assoc _ _ _))
-- -- --     ∙∙ 𝕡hexDiagAB (l ++ ls) xs ys zs rs ∙∙
-- -- --     cong 𝕡base (cong (_++ rs) (++-assoc _ _ _) ∙ ++-assoc _ _  _)


-- -- --  bhexDiagBC ℙ++G2 ls xs ys zs rs =
-- -- --     cong 𝕡base (sym (++-assoc _ _ _))
-- -- --     ∙∙ 𝕡hexDiagBC (l ++ ls) xs ys zs rs ∙∙
-- -- --      cong 𝕡base (
-- -- --          cong (_++ rs) (++-pentagon-diag _ _ _ _)
-- -- --           -- ∙ (λ i → ++-assoc l (++-assoc ls ys (zs ++ xs) (~ i)) rs i)
-- -- --          ∙∙ (++-assoc _ _ _) ∙∙
-- -- --          cong (λ x → (l ++ x ++ rs)) (sym (++-assoc _ _ _)))


-- -- --  bhexDiagCD ℙ++G2 ls xs ys zs rs =
-- -- --     cong 𝕡base (sym (++-assoc _ _ _) ∙'
-- -- --                   λ i → (++-assoc l ls (xs ++ ys) (~ i)) ++ zs ++ rs)
-- -- --     ∙∙ 𝕡hexDiagCD (l ++ ls) xs ys zs rs ∙∙
-- -- --     cong 𝕡base (
-- -- --        cong ((_++ rs) ∘' (_++ (xs ++ zs))) (++-assoc _ _ _)
-- -- --        ∙∙ cong (_++ rs) (++-assoc _ _ _)
-- -- --        ∙∙ ++-assoc _ _ _)


-- -- --  hlpSq : (l xs ys++zs ws : List A) →
-- -- --      Square
-- -- --         (sym (++-assoc l (xs ++ (ys++zs)) ws)
-- -- --        ∙' cong (_++ ws) (sym (++-assoc _ _ _)))
-- -- --         (sym (++-assoc l xs ((ys++zs) ++ ws)))
-- -- --          (λ i → (l ++ ++-assoc xs (ys++zs) ws i))
-- -- --         (++-assoc (l ++ xs) (ys++zs) ws)
-- -- --  hlpSq l xs ys++zs ws j i =
-- -- --    hcomp (λ k → λ {
-- -- --           (i = i0) → ++-pentagon-□ l xs ys++zs ws (~ j) k
-- -- --          ;(i = i1) → ++-assoc (l ++ xs) ys++zs ws j
-- -- --          ;(j = i1) → ++-pentagon-△ l xs ys++zs ws (~ i) k
-- -- --            }) (invSides-filler
-- -- --                  (++-assoc (l ++ xs) ys++zs ws)
-- -- --                  (cong (_++ ws) (++-assoc _ _ _))
-- -- --                  (~ i) j)


-- -- --  ℙ++G3 : H3 ℙ++G2
-- -- --  binvolL ℙ++G3 xs ys zs ws =
-- -- --    refl
-- -- --     ∙∙₂ 𝕡involL (l ++ xs) ys zs ws ∙∙₂
-- -- --     refl

-- -- --  bloopAssoc ℙ++G3 xs ys zs ws =
-- -- --     congSq 𝕡base (hlpSq l xs (ys ++ zs) ws)
-- -- --        ∙∙₂ 𝕡loopAssoc (l ++ xs) ys zs ws ∙∙₂
-- -- --      congSq 𝕡base (congP (λ _ → sym) (hlpSq l xs (zs ++ ys) ws))
   
-- -- --  bhexA ℙ++G3 ls xs ys zs rs =
-- -- --     congSq 𝕡base (λ i → hlpSq l ls (++-assoc xs ys zs (~ i)) rs i)
-- -- --        ∙∙₂ 𝕡hexA (l ++ ls) xs ys zs rs ∙∙₂
-- -- --      congSq 𝕡base
-- -- --        λ i j →
-- -- --           ((λ j → (++-assoc l ls (++-assoc ys zs xs i) j) ++ rs) ∙
-- -- --               ++-assoc l (ls ++ ++-assoc ys zs xs i) rs) j
   
-- -- --  bhexB ℙ++G3 ls xs ys zs rs =
-- -- --     congSq 𝕡base
-- -- --        (λ i → sym (++-assoc l ls (++-assoc (xs ++ ys) zs rs i)))
-- -- --        ∙∙₂ 𝕡hexB (l ++ ls) xs ys zs rs ∙∙₂
-- -- --      congSq 𝕡base {!!}

-- -- --  bhexC ℙ++G3 ls xs ys zs rs =
-- -- --    congSq 𝕡base (symP (hlpSq  l ls (xs ++ ys) (zs ++ rs)))
-- -- --      ∙∙₂  𝕡hexC (l ++ ls) xs ys zs rs  ∙∙₂
-- -- --        {!!}

-- -- --  bhexD ℙ++G3 ls xs ys zs rs = {!!}
-- -- --     -- congSq 𝕡base {!!}
-- -- --     --    ∙∙₂ 𝕡hexD (l ++ ls) xs ys zs rs ∙∙₂
-- -- --     --  congSq 𝕡base {!!}

-- -- --  _ℙ++_ : ℙ A → ℙ A 
-- -- --  _ℙ++_ = f₃ ℙ++G3 𝕡trunc



-- -- -- _⊙𝕡_ : {A : Type ℓ} → ℙ A → ℙ A  → ℙ A 
-- -- -- _⊙𝕡_ {A = A} =
-- -- --   LR.f₃
-- -- --     lr₃
-- -- --     (isGroupoidΠ λ _ → 𝕡trunc)
-- -- --  where
 
-- -- --  module LR = Recℙ {A = A} (ℙ A  → ℙ A)


-- -- --  lr₁ : LR.H1
-- -- --  Recℙ.bbase lr₁ = _ℙ++_


-- -- --  lr₂ : LR.H2 lr₁
-- -- --  Recℙ.bloopL lr₂ = {!!}
-- -- --  Recℙ.bloopR lr₂ = {!!}
-- -- --  Recℙ.bhexDiagAB lr₂ = {!!}
-- -- --  Recℙ.bhexDiagBC lr₂ = {!!}
-- -- --  Recℙ.bhexDiagCD lr₂ = {!!}


-- -- --  lr₃ : LR.H3 lr₂
-- -- --  lr₃ = {!!}
 
-- -- -- -- module _ {ℓ} (A : Type ℓ) where
-- -- -- --  open RecFCM₃ {A = A} (ℙ A)


-- -- -- --  toℙR₁ : H1 
-- -- -- --  b[] toℙR₁ = 𝕡base []
-- -- -- --  b[ toℙR₁ ] = 𝕡base ∘ [_]
-- -- -- --  _b⊙_ toℙR₁ = _⊙𝕡_

-- -- -- --  toℙR₂ : H2 toℙR₁
-- -- -- --  b⊙-comm toℙR₂ = {!!}
-- -- -- --  b⊙ur toℙR₂ = {!!}
-- -- -- --  b⊙ul toℙR₂ = {!!}
-- -- -- --  b⊙-assoc toℙR₂ = {!!}
-- -- -- --  b⊙-hex-diag toℙR₂ = {!!}
-- -- -- --  b⊙-pent-diag toℙR₂ = {!!}

-- -- -- --  toℙR₃ : H3 toℙR₂
-- -- -- --  b⊙-triangle toℙR₃ = {!!}
-- -- -- --  b⊙-hex-up toℙR₃ = {!!}
-- -- -- --  b⊙-hex-down toℙR₃ = {!!}
-- -- -- --  b⊙-pent-△ toℙR₃ = {!!}
-- -- -- --  b⊙-pent-□ toℙR₃ = {!!}


-- -- -- --  toℙ : FCM₃ A → ℙ A
-- -- -- --  toℙ = recFCM₃ _ 3 ((toℙR₁ , toℙR₂) , toℙR₃) 𝕡trunc


-- -- -- --  -- fromℙ : ℙ (List A) → FCM₃ A
-- -- -- --  -- fromℙ = {!!}




-- -- -- -- -- -- -- --   𝕡invol : (p₀₋ p₁₋ : AB n) → involGuard p₀₋ p₁₋
-- -- -- -- -- -- -- --             → Square {A = ℙrmₐ {trunc} n}
-- -- -- -- -- -- -- --                   (𝕡loop p₀₋)
-- -- -- -- -- -- -- --                   (sym (𝕡loop p₁₋))
-- -- -- -- -- -- -- --                   refl
-- -- -- -- -- -- -- --                   refl
-- -- -- -- -- -- -- --   𝕡hex : (p₀₋ p₁₋ p₋₁ : AB n) → hexGuard p₀₋ p₁₋ p₋₁
-- -- -- -- -- -- -- --     → Square {A = ℙrmₐ {trunc} n}
-- -- -- -- -- -- -- --        (𝕡loop p₀₋)
-- -- -- -- -- -- -- --        (𝕡loop p₁₋)
-- -- -- -- -- -- -- --        refl
-- -- -- -- -- -- -- --        (𝕡loop p₋₁)
-- -- -- -- -- -- -- --   𝕡comm : (pᵢ₋ p₋ᵢ : AB n) → commGuard pᵢ₋ p₋ᵢ
-- -- -- -- -- -- -- --      → Square {A = ℙrmₐ {trunc} n}
-- -- -- -- -- -- -- --        (𝕡loop pᵢ₋)
-- -- -- -- -- -- -- --        (𝕡loop pᵢ₋)
-- -- -- -- -- -- -- --        (𝕡loop p₋ᵢ)
-- -- -- -- -- -- -- --        (𝕡loop p₋ᵢ)

-- -- -- -- -- -- -- --   𝕡over : (p₀₋ p₁₋ p₋ᵢ : AB n) → overGuard p₀₋ p₁₋ p₋ᵢ
-- -- -- -- -- -- -- --      → Square {A = ℙrmₐ {trunc} n}
-- -- -- -- -- -- -- --        (𝕡loop p₀₋)
-- -- -- -- -- -- -- --        (𝕡loop p₁₋)
-- -- -- -- -- -- -- --        (𝕡loop p₋ᵢ)
-- -- -- -- -- -- -- --        (𝕡loop p₋ᵢ)



-- -- -- --  -- 𝕡loopCuAssoc : (xs ys zs ws : List A) → 
-- -- -- --  --   Square 
-- -- -- --  -- 𝕡loopCuDiag : (xs ys zs ws : List A) → 
   
-- -- -- --  --   Square

-- -- -- --   -- ++-pentagon-diag : (xs ys zs ws : List A)
-- -- -- --   --      → ((xs ++ ys) ++ zs) ++ ws ≡ xs ++ ys ++ zs ++ ws
-- -- -- --   -- ++-pentagon-△ : (xs ys zs ws : List A) →
-- -- -- --   --       Square refl (++-pentagon-diag xs ys zs ws)
-- -- -- --   --         (sym (++-assoc _ _ _)) (++-assoc _ _ _)
-- -- -- --   -- ++-pentagon-□ : (xs ys zs ws : List A) →
-- -- -- --   --       Square (++-pentagon-diag xs ys zs ws)
-- -- -- --   --          (++-assoc _ _ _)
-- -- -- --   --          (cong (_++ ws) (++-assoc _ _ _))           
-- -- -- --   --          (sym (cong (xs ++_) (++-assoc _ _ _)))

-- -- -- -- -- module _ {A : Type ℓ} where

-- -- -- -- --   rev : FCM₃ A → FCM₃ A
-- -- -- -- --   rev [] = []
-- -- -- -- --   rev [ x ] = [ x ]
-- -- -- -- --   rev (x ⊙ y) = rev y ⊙ rev x
-- -- -- -- --   rev (⊙-unit-r x i) = ⊙-unit-l (rev x) i
-- -- -- -- --   rev (⊙-unit-l x i) = ⊙-unit-r (rev x) i
-- -- -- -- --   rev (⊙-assoc x y z i) = ⊙-assoc (rev z) (rev y) (rev x) (~ i)
-- -- -- -- --   rev (⊙-triangle x y i j) = ⊙-triangle (rev y) (rev x) i (~ j)
-- -- -- -- --   rev (⊙-pentagon-diag x y z w i) = ⊙-pentagon-diag (rev w) (rev z) (rev y) (rev x) (~ i)
-- -- -- -- --   rev (⊙-pentagon-△ x y z w i j) = ⊙-pentagon-△ (rev w) (rev z) (rev y) (rev x) i (~ j)
-- -- -- -- --   rev (⊙-pentagon-□ x y z w i j) = ⊙-pentagon-□ (rev w) (rev z) (rev y) (rev x) i (~ j)
-- -- -- -- --   rev (trunc x y p q r s i₀ i₁ i₂) =
-- -- -- -- --     trunc (rev x) (rev y) (cong rev p) (cong rev q) (cong (cong rev) r) (cong (cong rev) s) i₀ i₁ i₂


-- -- -- -- --   lawCool-l : (xs ys : FCM₃ A)
-- -- -- -- --             → Square
-- -- -- -- --               (⊙-assoc [] xs ys) refl
-- -- -- -- --               (cong (_⊙ ys) (⊙-unit-l xs)) (⊙-unit-l (xs ⊙ ys))

-- -- -- -- --   lawCool-l xs ys =
-- -- -- -- --      congSq* ⊙-unit-l λ i j →
-- -- -- -- --       (hcomp (λ k →
-- -- -- -- --          λ { (i = i0) → hcomp (λ l →
-- -- -- -- --                          λ { (k = i1) → [] ⊙ ⊙-assoc [] xs ys (l ∧ j)
-- -- -- -- --                            ; (j = i1) → [] ⊙ ⊙-assoc [] xs ys l
-- -- -- -- --                            ; (k = i0) → ⊙-pentagon-□ [] [] xs ys (~ l) j
-- -- -- -- --                            }) ((⊙-assoc [] ([] ⊙ xs) ys (j ∨ k)))
-- -- -- -- --            ; (i = i1) → ⊙-assoc [] xs ys (k ∨ j) 
-- -- -- -- --            ; (j = i0) → hcomp (λ l → λ { (i = i1) → ⊙-assoc [] xs ys k
-- -- -- -- --                                        ; (k = i1) → [] ⊙ (⊙-unit-l xs i ⊙ ys)
-- -- -- -- --                                        ; (k = i0) → ⊙-triangle [] xs i (~ l) ⊙ ys
-- -- -- -- --                                        }) (⊙-assoc [] (⊙-unit-l xs i) ys k)
-- -- -- -- --            ; (j = i1) → [] ⊙ ⊙-unit-l (xs ⊙ ys) i
-- -- -- -- --             }) (hcomp (λ k →
-- -- -- -- --                    λ { (i = i0) → ⊙-pentagon-△ [] [] xs ys k j 
-- -- -- -- --                      ; (i = i1) → ⊙-assoc [] xs ys (~ k ∨ j) 
-- -- -- -- --                      ; (j = i0) → ⊙-assoc (⊙-unit-r [] i) xs ys (~ k)
-- -- -- -- --                      ; (j = i1) → ⊙-triangle [] (xs ⊙ ys) i k
-- -- -- -- --                       }) (⊙-unit-r [] i ⊙ xs ⊙ ys)))

-- -- -- -- --   lawCool-r' : (xs ys : FCM₃ A)
-- -- -- -- --             → Square
-- -- -- -- --               (⊙-assoc (rev (rev xs)) (rev (rev ys)) []) refl
-- -- -- -- --               (⊙-unit-r (rev (rev xs) ⊙ rev (rev ys)))
-- -- -- -- --                (cong (_ ⊙_) (⊙-unit-r (rev (rev ys))))

-- -- -- -- --   lawCool-r' xs ys i j = rev ((lawCool-l (rev ys) (rev xs)) i (~ j))
   
    

-- -- -- -- --   lawCool-r : (xs ys : FCM₃ A)
-- -- -- -- --             → Square
-- -- -- -- --               (⊙-assoc xs ys []) refl
-- -- -- -- --               (⊙-unit-r (xs ⊙ ys)) (cong (xs ⊙_) (⊙-unit-r ys))
-- -- -- -- --   lawCool-r xs ys =
-- -- -- -- --     congSq* ⊙-unit-r λ i j →
-- -- -- -- --       (hcomp (λ k →
-- -- -- -- --          λ { (i = i0) →  hcomp (λ l →
-- -- -- -- --                          λ { (k = i1) → ⊙-assoc xs ys [] (~ l ∨ j) ⊙ []
-- -- -- -- --                            ; (j = i0) → ⊙-assoc xs ys [] (~ l) ⊙ []
-- -- -- -- --                            ; (k = i0) → ⊙-pentagon-□ xs ys [] [] (~ l) j
-- -- -- -- --                            }) ((⊙-assoc xs (ys ⊙ []) [] (j ∧ ~ k)))
-- -- -- -- --            ; (i = i1) → ⊙-assoc xs ys [] (~ k ∧ j) 
-- -- -- -- --            ; (j = i1) →  hcomp (λ l →
-- -- -- -- --                            λ { (i = i1) → ⊙-assoc xs ys [] (~ k)
-- -- -- -- --                              ; (k = i1) → (xs ⊙ ⊙-unit-r ys i) ⊙ []
-- -- -- -- --                              ; (k = i0) → xs ⊙ ⊙-triangle ys [] i (l)
-- -- -- -- --                              }) (⊙-assoc xs (⊙-unit-r ys i) [] (~ k))
-- -- -- -- --            ; (j = i0) → ⊙-unit-r (xs ⊙ ys) i ⊙ []
-- -- -- -- --             }) (hcomp (λ k →
-- -- -- -- --                    λ { (i = i0) → ⊙-pentagon-△ xs ys [] [] k j 
-- -- -- -- --                      ; (i = i1) → ⊙-assoc xs ys [] (k ∧ j) 
-- -- -- -- --                      ; (j = i1) → ⊙-assoc xs ys (⊙-unit-l [] i) (k)
-- -- -- -- --                      ; (j = i0) → ⊙-triangle (xs ⊙ ys) [] i (~ k)
-- -- -- -- --                       }) ((xs ⊙ ys) ⊙ ⊙-unit-l [] i)))


-- -- -- -- --   ⊙-unit-lr[] : ⊙-unit-l {A = A} [] ≡ ⊙-unit-r [] 
-- -- -- -- --   ⊙-unit-lr[] =
-- -- -- -- --      congSq* ⊙-unit-r λ i j →
-- -- -- -- --             (hcomp (λ k →
-- -- -- -- --             λ { (i = i0) → lawCool-l [] [] j (~ k) 
-- -- -- -- --               ; (i = i1) → ⊙-triangle [] [] j (~ k) 
-- -- -- -- --               ; (j = i0) → ⊙-assoc [] [] [] (~ k)
-- -- -- -- --               ; (j = i1) → [] ⊙ []
-- -- -- -- --                })
-- -- -- -- --      ((lem-pqr λ i j → (⊙-unit-l (⊙-unit-l [] (~ j)) (~ i))) i (~ j)))




-- -- -- -- --   length : FCM₃ A → ℕ
-- -- -- -- --   length = recFCM₃ _ 2 w isSetℕ
-- -- -- -- --    where
-- -- -- -- --    open RecFCM₃
-- -- -- -- --    w : RecFCM₃.RecFCM₃ ℕ 2
-- -- -- -- --    H1.b[] (fst w) = zero
-- -- -- -- --    H1.b[ fst w ] _ = 1
-- -- -- -- --    H1._b⊙_ (fst w) = _+_
-- -- -- -- --    H2.b⊙ur (snd w) = +-zero
-- -- -- -- --    H2.b⊙ul (snd w) = λ _ → refl
-- -- -- -- --    H2.b⊙-assoc (snd w) n m o = sym (+-assoc n m o)
-- -- -- -- --    H2.b⊙-pent-diag (snd w) bx by bz bw =
-- -- -- -- --      sym (+-assoc (bx + by) bz bw) ∙∙ refl ∙∙ sym (+-assoc bx by (bz + bw))
  
-- -- -- -- --   rev-rev : ∀ x → rev (rev x) ≡ x
-- -- -- -- --   rev-rev [] = refl
-- -- -- -- --   rev-rev [ x ] = refl
-- -- -- -- --   rev-rev (x ⊙ y) = cong₂ _⊙_ (rev-rev x) (rev-rev y)
-- -- -- -- --   rev-rev (⊙-unit-r x i) j = ⊙-unit-r (rev-rev x j) i
-- -- -- -- --   rev-rev (⊙-unit-l x i) j = ⊙-unit-l (rev-rev x j) i
-- -- -- -- --   rev-rev (⊙-assoc x y z i) j = ⊙-assoc (rev-rev x j) (rev-rev y j) (rev-rev z j) i
-- -- -- -- --   rev-rev (⊙-triangle x y i j) k = (⊙-triangle (rev-rev x k) (rev-rev y k) i j)
-- -- -- -- --   rev-rev (⊙-pentagon-diag x y z w i) k =
-- -- -- -- --      ⊙-pentagon-diag (rev-rev x k) (rev-rev y k) (rev-rev z k) (rev-rev w k) i
-- -- -- -- --   rev-rev (⊙-pentagon-△ x y z w i j) k =
-- -- -- -- --      ⊙-pentagon-△ (rev-rev x k) (rev-rev y k) (rev-rev z k) (rev-rev w k) i j
-- -- -- -- --   rev-rev (⊙-pentagon-□ x y z w i j) k =
-- -- -- -- --      ⊙-pentagon-□ (rev-rev x k) (rev-rev y k) (rev-rev z k) (rev-rev w k) i j
-- -- -- -- --   rev-rev (trunc x y p q r s i₀ i₁ i₂) k =
-- -- -- -- --      (trunc (rev-rev x k) (rev-rev y k)
-- -- -- -- --              (λ j → (rev-rev (p j) k)) (λ j → (rev-rev (q j) k))
-- -- -- -- --              (λ j j' → (rev-rev (r j j') k)) (λ j j' → (rev-rev (s j j') k))
-- -- -- -- --              i₀ i₁ i₂)

-- -- -- -- --   Iso-rev : Iso (FCM₃ A) (FCM₃ A)
-- -- -- -- --   Iso.fun Iso-rev = rev
-- -- -- -- --   Iso.inv Iso-rev = rev
-- -- -- -- --   Iso.rightInv Iso-rev = rev-rev
-- -- -- -- --   Iso.leftInv Iso-rev = rev-rev


-- -- -- -- --   -- -- length0≡[] : ∀ {x} → length x ≡ 0 → x ≡ []
-- -- -- -- --   -- -- length0≡[] =
-- -- -- -- --   -- --   ElimSet.f
-- -- -- -- --   -- --      (λ x → isSetΠ λ _ → trunc x [])
-- -- -- -- --   -- --      (λ z → refl)
-- -- -- -- --   -- --      (λ a p → ⊥rec (snotz p))
-- -- -- -- --   -- --      (λ {xs} {ys} px py p →
-- -- -- -- --   -- --        let (px0 , py0) = m+n≡0→m≡0×n≡0 {length xs} {length ys} p
-- -- -- -- --   -- --        in cong₂ _⊙_ (px px0) (py py0) ∙' ⊙-unit-r [])
-- -- -- -- --   -- --      (λ {x} b → funExtDep λ p i j → hcomp (λ k →
-- -- -- -- --   -- --               λ { (i = i1) → ⊙-unit-r (b (p i) (j ∨ ~ k)) (j ∨ k)
-- -- -- -- --   -- --                 ; (j = i0) → ⊙-unit-r
-- -- -- -- --   -- --                         (b (isSetℕ _ _ (fst (m+n≡0→m≡0×n≡0 (p i0))) (p i1) i) (~ k))
-- -- -- -- --   -- --                         (i ∧ k)
-- -- -- -- --   -- --                 ; (j = i1) → [] }) (⊙-unit-r [] j))
-- -- -- -- --   -- --      (λ b i p j → hcomp (λ k →
-- -- -- -- --   -- --                   λ { (i = i1) → ⊙-unit-l (b p (j ∨ ~ k)) (j ∨ k) 
-- -- -- -- --   -- --                     ; (j = i0) → ⊙-unit-l (b p (~ k)) (i ∧ k)
-- -- -- -- --   -- --                     ; (j = i1) → [] }) (⊙-unit-lr[] (~ i) j))

-- -- -- -- --   -- --      (λ {x} {y} {z} bx by bz →
-- -- -- -- --   -- --        funExtDep λ p → congP (λ _ → _∙' ⊙-unit-r [])
-- -- -- -- --   -- --          λ j i → hcomp (λ k →
-- -- -- -- --   -- --             let (px , py , pz) = unglue (j ∨ ~ j)
-- -- -- -- --   -- --                      (assoc≡z {length x} {length y} {length z} (~ j) (p j))
-- -- -- -- --   -- --             in λ { (i = i0) → ⊙-assoc (bx px (~ k)) (by py (~ k)) (bz pz (~ k)) j
-- -- -- -- --   -- --                  ; (i = i1) → [] ⊙ []
-- -- -- -- --   -- --                  ; (j = i0) → doubleCompPath-filler
-- -- -- -- --   -- --                             (cong₂ _⊙_ (bx px) (by py))                              
-- -- -- -- --   -- --                             (⊙-unit-r []) refl k i ⊙ bz pz (i ∨ ~ k)
-- -- -- -- --   -- --                  ; (j = i1) → bx px (i ∨ ~ k) ⊙ doubleCompPath-filler
-- -- -- -- --   -- --                               (cong₂ _⊙_ (by py) (bz pz))                                
-- -- -- -- --   -- --                               (⊙-unit-lr[] k) refl k i})
-- -- -- -- --   -- --                  (⊙-triangle [] [] i j))
-- -- -- -- --   -- --       _
        
-- -- -- -- --   -- --     where
-- -- -- -- --   -- --      assoc≡z : ∀ {n m o} → PathP (λ i → +-assoc n m o i ≡ zero
-- -- -- -- --   -- --                               → ua (Σ-assoc-≃ {A = n ≡ zero}
-- -- -- -- --   -- --                                               {λ _ → m ≡ zero }
-- -- -- -- --   -- --                                               {λ _ _ → o ≡ zero}) (~ i) )
-- -- -- -- --   -- --                           (map-snd m+n≡0→m≡0×n≡0 ∘ m+n≡0→m≡0×n≡0)
-- -- -- -- --   -- --                           (map-fst m+n≡0→m≡0×n≡0 ∘ m+n≡0→m≡0×n≡0)
-- -- -- -- --   -- --      assoc≡z {zero} {m} {o} i x =
-- -- -- -- --   -- --        ua-gluePath Σ-assoc-≃ (λ _ → refl , m+n≡0→m≡0×n≡0 x ) (~ i)
-- -- -- -- --   -- --      assoc≡z {suc n} {m} {o} = funExtDep λ p → ⊥rec (snotz (p i0))



-- -- -- -- --   -- -- isContrLen0 : isContr (Σ (FCM₃ A) λ x → length x ≡ 0)
-- -- -- -- --   -- -- fst isContrLen0 = [] , refl
-- -- -- -- --   -- -- snd isContrLen0 = λ y → Σ≡Prop (λ _ → isSetℕ _ _) (sym (length0≡[] (snd y)))

-- -- -- -- --   -- -- isContr[]≡[] : isContr ([] ≡ [])
-- -- -- -- --   -- -- isContr[]≡[] = refl , λ p j i → length0≡[] {x = p i} (λ i₁ → length (p (i₁ ∨ i))) (~ j)


-- -- -- -- --   -- -- length0≡[]-sec : ∀ {x} → (b : x ≡ []) → length0≡[] (λ i → length (b i)) ≡ b
-- -- -- -- --   -- -- length0≡[]-sec {x} = 
-- -- -- -- --   -- --   ElimProp.f 
-- -- -- -- --   -- --     (λ x → isPropΠ λ b → trunc x [] (length0≡[] (λ i → length (b i))) b)
-- -- -- -- --   -- --     (snd isContr[]≡[])
-- -- -- -- --   -- --     (λ _ b → ⊥rec (snotz (cong length b)))
-- -- -- -- --   -- --     (λ _ _ b i j →  -- todo abstract as "unbending square" lemma
-- -- -- -- --   -- --              hcomp
-- -- -- -- --   -- --              (λ k →
-- -- -- -- --   -- --                  λ {  (i = i0) → length0≡[] {x = b (~ k)} (λ i' → length (b (~ k ∨  i'))) j  
-- -- -- -- --   -- --                     ; (i = i1) → b ((~ k) ∨ j)
-- -- -- -- --   -- --                     ; (j = i0) → b (~ k)
-- -- -- -- --   -- --                     ; (j = i1) → []
-- -- -- -- --   -- --                     }) [])
-- -- -- -- --   -- --     x 

-- -- -- -- --   -- -- Iso-length0≡[] : ∀ {x} → Iso (length x ≡ 0) (x ≡ [])
-- -- -- -- --   -- -- Iso.fun Iso-length0≡[] = length0≡[]
-- -- -- -- --   -- -- Iso.inv Iso-length0≡[] = cong length
-- -- -- -- --   -- -- Iso.rightInv Iso-length0≡[] = length0≡[]-sec
-- -- -- -- --   -- -- Iso.leftInv Iso-length0≡[] a = isSetℕ _ _ _ _

-- -- -- -- --   -- -- isProp≡[] : ∀ x → isProp (x ≡ [])
-- -- -- -- --   -- -- isProp≡[] x =
-- -- -- -- --   -- --   isPropRetract
-- -- -- -- --   -- --     (cong length) (length0≡[] {x = x})
-- -- -- -- --   -- --     length0≡[]-sec (isSetℕ _ _)


-- -- -- -- --   -- -- IsEmpty : FCM₃ A → hProp ℓ-zero
-- -- -- -- --   -- -- IsEmpty =
-- -- -- -- --   -- --    RecSet.f isSetHProp
-- -- -- -- --   -- --    L.⊤ (λ _ → L.⊥) L._⊓_
-- -- -- -- --   -- --    L.⊓-identityʳ  L.⊓-identityˡ (λ _ by bz → sym (L.⊓-assoc _ by bz))
-- -- -- -- --   -- --    λ bx by bz bw →
-- -- -- -- --   -- --      sym (L.⊓-assoc (bx L.⊓ by) bz bw) ∙∙ refl ∙∙ sym (L.⊓-assoc bx by (bz L.⊓ bw) )


-- -- -- -- --   -- -- data Uncons (x : FCM₃ A) : Type ℓ where
-- -- -- -- --   -- --   nil : x ≡ [] → Uncons x
-- -- -- -- --   -- --   cons : ∀ a xs → a ∷ xs ≡ x → Uncons x

-- -- -- -- --   -- -- Uncons-elim : ∀ {ℓ'} → {x : FCM₃ A} → (B : Uncons x → Type ℓ')
-- -- -- -- --   -- --                → (∀ p → B (nil p) )
-- -- -- -- --   -- --                → (∀ a xs p → B (cons a xs p))
-- -- -- -- --   -- --                → ∀ u → B u 
-- -- -- -- --   -- -- Uncons-elim B f _ (nil x₂) = f x₂
-- -- -- -- --   -- -- Uncons-elim B _ f (cons a xs x₂) = f a xs x₂

-- -- -- -- --   -- -- Uncons⊎ : (x : FCM₃ A) → Iso (Uncons x) ((x ≡ []) ⊎ (Σ[ (a , xs) ∈ (A × FCM₃ A) ] a ∷ xs ≡ x))
-- -- -- -- --   -- -- Iso.fun (Uncons⊎ x) (nil x₁) = inl x₁
-- -- -- -- --   -- -- Iso.fun (Uncons⊎ x) (cons a xs x₁) = inr ((a , xs) , x₁)
-- -- -- -- --   -- -- Iso.inv (Uncons⊎ x) (inl x₁) = nil x₁
-- -- -- -- --   -- -- Iso.inv (Uncons⊎ x) (inr ((a , xs) , x₁)) = cons a xs x₁
-- -- -- -- --   -- -- Iso.rightInv (Uncons⊎ x) (inl x₁) = refl
-- -- -- -- --   -- -- Iso.rightInv (Uncons⊎ x) (inr x₁) = refl
-- -- -- -- --   -- -- Iso.leftInv (Uncons⊎ x) (nil x₁) = refl
-- -- -- -- --   -- -- Iso.leftInv (Uncons⊎ x) (cons a xs x₁) = refl

-- -- -- -- --   -- -- isGroupoid-Uncons : isGroupoid A → (x : FCM₃ A) → isGroupoid (Uncons x)
-- -- -- -- --   -- -- isGroupoid-Uncons isGrpA x =
-- -- -- -- --   -- --    isOfHLevelRetractFromIso 3 (Uncons⊎ x)
-- -- -- -- --   -- --       (isOfHLevel⊎ 1 (isOfHLevelSuc 2 (trunc _ _))
-- -- -- -- --   -- --       (isOfHLevelΣ 3 (isOfHLevel× 3 isGrpA trunc) λ _ → isSet→isGroupoid (trunc _ _))) 

-- -- -- -- --   -- -- u⊙ : {xs ys : FCM₃ A} → Uncons xs → Uncons ys → Uncons (xs ⊙ ys)
-- -- -- -- --   -- -- u⊙ (nil x) (nil x₁) = nil (cong₂ _⊙_ x x₁ ∙  ⊙-unit-l [] )
-- -- -- -- --   -- -- u⊙ (nil x) (cons a xs x₁) = cons a xs (sym (⊙-unit-l (a ∷ xs)) ∙ cong₂ _⊙_ (sym x) x₁)
-- -- -- -- --   -- -- u⊙ {ys = ys} (cons a xs x) _ = cons a (xs ⊙ ys) (sym (⊙-assoc _ _ _) ∙ cong (_⊙ ys) x)

-- -- -- -- --   -- -- Uncons≡ : (x : I → FCM₃ A) → (x0 : Uncons (x i0)) (x1 : Uncons (x i1)) → Type ℓ
-- -- -- -- --   -- -- Uncons≡ x (nil p) (nil p') = Unit*
-- -- -- -- --   -- -- Uncons≡ _ (nil x) (cons a xs x₁) = ⊥*
-- -- -- -- --   -- -- Uncons≡ _ (cons a xs x) (nil x₁) = ⊥*
-- -- -- -- --   -- -- Uncons≡ x (cons a xs p) (cons a' xs' p') =
-- -- -- -- --   -- --   Σ ((a ≡ a') × (xs ≡ xs'))
-- -- -- -- --   -- --    λ axs → Square p p' (cong₂ _∷_ (fst axs) (snd axs)) (λ i → x i) 

-- -- -- -- --   -- -- Uncons≡refl : {x : FCM₃ A} → {u : Uncons x} → Uncons≡ (λ _ → x) u u
-- -- -- -- --   -- -- Uncons≡refl {x} {nil x₁} = tt*
-- -- -- -- --   -- -- Uncons≡refl {x} {cons a xs x₁} = (refl , refl) , refl
  
-- -- -- -- --   -- -- uncons≡ : ∀ x x0 x1 
-- -- -- -- --   -- --        → Uncons≡ x x0 x1
-- -- -- -- --   -- --        → PathP (λ i → Uncons (x i)) x0 x1
-- -- -- -- --   -- -- uncons≡ x (nil p0) (nil p1) _ i = nil (isProp→PathP (λ i → isProp≡[] (x i)) p0 p1 i)
-- -- -- -- --   -- -- uncons≡ x (cons a xs p) (cons a' xs' p') q i =
-- -- -- -- --   -- --   cons (fst (fst q) i) (snd (fst q) i) (snd q i)


-- -- -- -- --   -- -- UnconsCons : ∀ {x} → (a : A) → (xs : FCM₃ A) → (a ∷ xs ≡ x) → Uncons x →
-- -- -- -- --   -- --                (Σ[ (a , xs) ∈ (A × FCM₃ A) ] a ∷ xs ≡ x)
-- -- -- -- --   -- -- UnconsCons a xs s (nil x₁) = ⊥rec (snotz (cong length (s ∙ x₁)))
-- -- -- -- --   -- -- UnconsCons _ _ _ (cons a xs p) = (a , xs) , p


-- -- -- -- --   -- -- UnconsCons-sec : ∀ {x} → (a : A) → (xs : FCM₃ A) → (p : a ∷ xs ≡ x) →  (u : Uncons x) →
-- -- -- -- --   -- --                       cons (fst (fst (UnconsCons a xs p u)))
-- -- -- -- --   -- --                            (snd (fst (UnconsCons a xs p u)))
-- -- -- -- --   -- --                            (snd (UnconsCons a xs p u)) ≡ u
-- -- -- -- --   -- -- UnconsCons-sec a xs s (nil x₁) = ⊥rec (snotz (cong length (s ∙ x₁)))
-- -- -- -- --   -- -- UnconsCons-sec a xs p (cons a₁ xs₁ x) = refl

-- -- -- -- --   -- -- UnconsNil : ∀ {x} → x ≡ [] →  (xs : Uncons x) →
-- -- -- -- --   -- --                x ≡ []
-- -- -- -- --   -- -- UnconsNil _ (nil p) = p
-- -- -- -- --   -- -- UnconsNil x₁ (cons _ _ p') = ⊥rec (snotz (cong length (p' ∙ x₁)))

-- -- -- -- --   -- -- UnconsNil-sec : ∀ {x} → (p : x ≡ []) → (xs : Uncons x) →  nil (UnconsNil p xs) ≡ xs  
-- -- -- -- --   -- -- UnconsNil-sec p (nil x) = refl
-- -- -- -- --   -- -- UnconsNil-sec x₁ (cons _ _ p') = ⊥rec (snotz (cong length (p' ∙ x₁)))

-- -- -- -- --   -- -- Uncons→a,xs : ∀ {x} → Uncons x → Maybe (A × FCM₃ A) 
-- -- -- -- --   -- -- Uncons→a,xs (nil x) = nothing
-- -- -- -- --   -- -- Uncons→a,xs (cons a xs x) = just (a , xs)
  
-- -- -- -- --   -- -- ¬Nil≡Cons : {x : I → FCM₃ A} → ∀ {xi0≡[] a xs a∷xs≡xi1} 
-- -- -- -- --   -- --                   → PathP (λ i → Uncons (x i))
-- -- -- -- --   -- --                     (nil xi0≡[])
-- -- -- -- --   -- --                     (cons a xs a∷xs≡xi1)
-- -- -- -- --   -- --                     → ⊥
-- -- -- -- --   -- -- ¬Nil≡Cons p = ¬nothing≡just (congP (λ _ → Uncons→a,xs) p)
  
-- -- -- -- --   -- -- unconsSqNil : {x : I → I → FCM₃ A}
-- -- -- -- --   -- --                → ∀ {p00 p10 p01 p11}
-- -- -- -- --   -- --                → {p0j : PathP (λ j → x i0 j ≡ []) p00 p10}
-- -- -- -- --   -- --                → {p1j : PathP (λ j → x i1 j ≡ []) p01 p11}
-- -- -- -- --   -- --                → {pi0 : PathP (λ i → x i i0 ≡ []) p00 p01}
-- -- -- -- --   -- --                → {pi1 : PathP (λ i → x i i1 ≡ []) p10 p11}
-- -- -- -- --   -- --                → SquareP (λ i j → Uncons (x i j))
-- -- -- -- --   -- --                    (λ j → nil (p0j j))
-- -- -- -- --   -- --                    (λ j → nil (p1j j))
-- -- -- -- --   -- --                    (λ i → nil (pi0 i))
-- -- -- -- --   -- --                    (λ i → nil (pi1 i))
-- -- -- -- --   -- -- unconsSqNil = congSqP (λ _ _ → nil) (isGroupoid→isGroupoid' trunc _ _ _ _ _ _)

-- -- -- -- --   -- -- unconsSqCons : ∀ {x₀₀ x₀₁ x₀₋ x₁₀ x₁₁ x₁₋ x₋₀ x₋₁}
-- -- -- -- --   -- --                → {x : Square {A = FCM₃ A} {x₀₀} {x₀₁} x₀₋ {x₁₀} {x₁₁} x₁₋ x₋₀ x₋₁}
-- -- -- -- --   -- --                {a : A}
-- -- -- -- --   -- --                → ∀ {xs₀₀ xs₀₁ xs₀₋ xs₁₀ xs₁₁ xs₁₋ xs₋₀ xs₋₁}
-- -- -- -- --   -- --                → (xs : Square {A = FCM₃ A} {xs₀₀} {xs₀₁} xs₀₋ {xs₁₀} {xs₁₁} xs₁₋ xs₋₀ xs₋₁ )
-- -- -- -- --   -- --                → ∀ {p00 p10 p01 p11}
-- -- -- -- --   -- --                → {p0j : PathP (λ j → a ∷ xs i0 j ≡ x i0 j) p00 p10}
-- -- -- -- --   -- --                → {p1j : PathP (λ j → a ∷ xs i1 j ≡ x i1 j) p01 p11}
-- -- -- -- --   -- --                → {pi0 : PathP (λ i → a ∷ xs i i0 ≡ x i i0) p00 p01}
-- -- -- -- --   -- --                → {pi1 : PathP (λ i → a ∷ xs i i1 ≡ x i i1) p10 p11}
-- -- -- -- --   -- --                → SquareP (λ i j → Uncons (x i j))
-- -- -- -- --   -- --                    (λ j → cons a (xs i0 j) (p0j j))
-- -- -- -- --   -- --                    (λ j → cons a (xs i1 j) (p1j j))
-- -- -- -- --   -- --                    (λ i → cons a (xs i i0) (pi0 i))
-- -- -- -- --   -- --                    (λ i → cons a (xs i i1) (pi1 i))
-- -- -- -- --   -- -- unconsSqCons {a = a} sq =
-- -- -- -- --   -- --    congSqP₂ (λ i j → cons a) sq
-- -- -- -- --   -- --    (isGroupoid→isGroupoid' trunc _ _ _ _ _ _)

-- -- -- -- --   -- -- proper : (x : FCM₃ A) → singl x
-- -- -- -- --   -- -- proper =
-- -- -- -- --   -- --   ElimProp.f
-- -- -- -- --   -- --     (λ x → isContr→isProp (isContrSingl x))
-- -- -- -- --   -- --      ([] , refl) (λ a → _ , refl)
-- -- -- -- --   -- --      w
-- -- -- -- --   -- --   where
-- -- -- -- --   -- --     w : {xs ys : FCM₃ A} → singl xs → singl ys → singl (xs ⊙ ys)
-- -- -- -- --   -- --     w {xs} {ys} (xs' , xp) (ys' , yp) with (discreteℕ (length xs) zero) | (discreteℕ (length ys) zero)
-- -- -- -- --   -- --     ... | yes p | yes p₁ = [] , cong₂ _⊙_ (length0≡[] p) (length0≡[] p₁) ∙ ⊙-unit-l []
-- -- -- -- --   -- --     ... | yes p | no ¬p = ys' , cong (_⊙ ys) (length0≡[] p) ∙ λ i → ⊙-unit-l (yp i) i
-- -- -- -- --   -- --     ... | no ¬p | yes p = xs' , cong (xs ⊙_) (length0≡[] p) ∙ λ i → ⊙-unit-r (xp i) i
-- -- -- -- --   -- --     ... | no ¬p | no ¬p₁ = xs' ⊙ ys' , cong₂ _⊙_ xp yp

-- -- -- -- --   -- -- filter : (A → Maybe A) → FCM₃ A → FCM₃ A
-- -- -- -- --   -- -- filter f =
-- -- -- -- --   -- --   Elim.f (λ _ → trunc)
-- -- -- -- --   -- --    []
-- -- -- -- --   -- --    (w ∘ f) (_⊙_)
-- -- -- -- --   -- --    ⊙-unit-r ⊙-unit-l ⊙-assoc ⊙-triangle ⊙-pentagon-diag ⊙-pentagon-△ ⊙-pentagon-□

-- -- -- -- --   -- --   where
-- -- -- -- --   -- --     w : Maybe A → FCM₃ A
-- -- -- -- --   -- --     w nothing = []
-- -- -- -- --   -- --     w (just x) = [ x ]

-- -- -- -- --   -- -- bind : ∀ {ℓ'} → {B : Type ℓ'} → FCM₃ A → (A → FCM₃ B) → FCM₃ B
-- -- -- -- --   -- -- bind x f =
-- -- -- -- --   -- --   Elim.f (λ _ → trunc)
-- -- -- -- --   -- --    []
-- -- -- -- --   -- --    f (_⊙_)
-- -- -- -- --   -- --    ⊙-unit-r ⊙-unit-l ⊙-assoc ⊙-triangle ⊙-pentagon-diag ⊙-pentagon-△ ⊙-pentagon-□
-- -- -- -- --   -- --    x

-- -- -- -- --   -- -- map-FCM₃ : ∀ {ℓ'} → {B : Type ℓ'} → (A → B) → FCM₃ A → FCM₃ B
-- -- -- -- --   -- -- map-FCM₃ f =
-- -- -- -- --   -- --   Elim.f (λ _ → trunc)
-- -- -- -- --   -- --    []
-- -- -- -- --   -- --    ([_] ∘ f) (_⊙_)
-- -- -- -- --   -- --    ⊙-unit-r ⊙-unit-l ⊙-assoc ⊙-triangle ⊙-pentagon-diag ⊙-pentagon-△ ⊙-pentagon-□

  

-- -- -- -- --   -- -- uncons : isGroupoid A → ∀ x → Uncons x
-- -- -- -- --   -- -- uncons isGrpA =
-- -- -- -- --   -- --   Elim.f
-- -- -- -- --   -- --     (isGroupoid-Uncons isGrpA)
-- -- -- -- --   -- --     (nil refl)
-- -- -- -- --   -- --     (λ a → cons a [] (⊙-unit-r [ a ]))
-- -- -- -- --   -- --     u⊙
-- -- -- -- --   -- --     (λ b → uncons≡ _ _ _ (w1 b))
-- -- -- -- --   -- --     (λ b → uncons≡ _ _ _ (w2 b))
-- -- -- -- --   -- --     (λ bx by bz → uncons≡ _ _ _ (w3 bx by bz))      
-- -- -- -- --   -- --     w4
-- -- -- -- --   -- --     (λ bx by bz bw → uncons≡ _ _ _ (w5 bx by bz bw))
-- -- -- -- --   -- --     w6
-- -- -- -- --   -- --     w7

-- -- -- -- --   -- --   where
-- -- -- -- --   -- --     w1 : {xs : FCM₃ A} (b : Uncons xs) → _
-- -- -- -- --   -- --     w1 {xs} (nil x) = _
-- -- -- -- --   -- --     w1 (cons a xs x) = (refl , ⊙-unit-r xs) ,
-- -- -- -- --   -- --        λ i j → hcomp
-- -- -- -- --   -- --         (λ k →
-- -- -- -- --   -- --           λ { (i = i1) → x (j ∧ k)
-- -- -- -- --   -- --             ; (j = i0) → [ a ] ⊙ ⊙-unit-r xs i
-- -- -- -- --   -- --             ; (j = i1) → ⊙-unit-r (x k) i
-- -- -- -- --   -- --             })
-- -- -- -- --   -- --         (lawCool-r [ a ] xs i (~ j))


-- -- -- -- --   -- --     w2 : {xs : FCM₃ A} (b : Uncons xs) → _
-- -- -- -- --   -- --     w2 (nil x) = _
-- -- -- -- --   -- --     w2 (cons a xs x) = (refl , refl) ,
-- -- -- -- --   -- --          λ i j →
-- -- -- -- --   -- --         hcomp (λ k →
-- -- -- -- --   -- --            λ { (i = i1) → x (j ∧ k)
-- -- -- -- --   -- --              ; (j = i0) → x i0
-- -- -- -- --   -- --              ; (j = i1) → ⊙-unit-l (x k) i
-- -- -- -- --   -- --              }) (⊙-unit-l (x i0) (i ∨ ~ j))

-- -- -- -- --   -- --     w3 : {xs ys zs : FCM₃ A} (bx : Uncons xs) (by : Uncons ys) (bz : Uncons zs) → _
-- -- -- -- --   -- --     w3 {xs} {ys} {zs} (nil px) (nil py) (nil pz) = _

-- -- -- -- --   -- --     w3 (nil px) (nil py) (cons a zs' pz) =
-- -- -- -- --   -- --        (refl , refl)
-- -- -- -- --   -- --        , congP (λ _ → sym (⊙-unit-l _) ∙_ )(
-- -- -- -- --   -- --               (λ i → cong₂-∙' _⊙_ (sym (⊙-unit-lr[] i)) (sym (cong₂ _⊙_ px py)) pz i)
-- -- -- -- --   -- --              ◁ (λ i → (λ j → (⊙-triangle [] (a ∷ zs') (~ j) i))
-- -- -- -- --   -- --                      ∙ λ k → ⊙-assoc (px (~ k)) (py (~ k)) (pz k) i)
-- -- -- -- --   -- --           ▷ sym (cong₂-∙'' _⊙_ _ _ (sym px)))


-- -- -- -- --   -- --     w3 {xs} {ys} {zs} (nil px) (cons a ys' ps) _ =
-- -- -- -- --   -- --        (refl , refl) ,
-- -- -- -- --   -- --          (((((cong ((sym (⊙-assoc [ a ] ys' zs)) ∙_)
-- -- -- -- --   -- --           (cong-∙ (_⊙ zs) _ _)) ∙ assoc _ _ _ )) 
-- -- -- -- --   -- --             )
-- -- -- -- --   -- --            ◁ ((λ i j →
-- -- -- -- --   -- --              hcomp
-- -- -- -- --   -- --               (λ k → λ { (j = i0) → ⊙-unit-l (a ∷ ys' ⊙ zs) (k ∨ (~ i))
-- -- -- -- --   -- --                        ; (j = i1) → ⊙-assoc (px (~ k)) (ps k) zs i
-- -- -- -- --   -- --                        })
-- -- -- -- --   -- --               (hcomp
-- -- -- -- --   -- --                  (λ k →
-- -- -- -- --   -- --                    λ { (i = i1) → ⊙-unit-l (⊙-assoc [ a ] ys' zs (~ j)) (~ k)
-- -- -- -- --   -- --                      ; (j = i0) → ⊙-unit-l (a ∷ ys' ⊙ zs) (~ i ∨ ~ k)
-- -- -- -- --   -- --                      ; (j = i1) → lawCool-l (a ∷ ys') zs (~ k) i
-- -- -- -- --   -- --                      })
-- -- -- -- --   -- --                  (⊙-assoc [ a ] ys' zs (~ j))))) ▷
                
-- -- -- -- --   -- --             (doubleCompPath-elim _ _ _ ∙∙ sym (assoc _ _ _) ∙∙   
-- -- -- -- --   -- --             cong ((λ i → ⊙-unit-l (a ∷ ys' ⊙ zs) (~ i)) ∙_)
-- -- -- -- --   -- --               ( ((cong ((λ i → cong ([] ⊙_) (λ i₁ → ⊙-assoc [ a ] ys' zs (~ i₁)) i) ∙_)
-- -- -- -- --   -- --                     (sym (cong₂-∙ (λ x y →  y ⊙ x)
-- -- -- -- --   -- --                       (λ i → ps i ⊙ zs)
-- -- -- -- --   -- --                       λ i → px (~ i)) ))
-- -- -- -- --   -- --                     ∙ assoc _ _ _
-- -- -- -- --   -- --                        ) ∙ cong (_∙ cong (λ y → y ⊙ ys ⊙ zs) (λ i → px (~ i)))
-- -- -- -- --   -- --                    (sym (cong-∙ ([] ⊙_) _ _))
-- -- -- -- --   -- --                    ∙ cong₂-∙ (λ x y →  y ⊙ x) _ _)))            


-- -- -- -- --   -- --     w3 {xs} {ys} {zs} (cons a xs' px) _ _ =
-- -- -- -- --   -- --       (refl , ⊙-assoc xs' _ _) ,
-- -- -- -- --   -- --         ((cong ((sym (⊙-assoc [ a ] (xs' ⊙ ys) zs)) ∙_)
-- -- -- -- --   -- --           (cong-∙ (_⊙ zs) _ _)) ∙ assoc _ _ _ )
-- -- -- -- --   -- --        ◁
-- -- -- -- --   -- --          (λ i j →
-- -- -- -- --   -- --          hcomp (λ k →
-- -- -- -- --   -- --            λ {  (j = i0) → a ∷ ⊙-assoc xs' ys zs i
-- -- -- -- --   -- --               ; (j = i1) → ⊙-assoc (px k) ys zs i
-- -- -- -- --   -- --               }) (hcomp (λ k →
-- -- -- -- --   -- --                   λ { (i = i0) →
-- -- -- -- --   -- --                       hcomp
-- -- -- -- --   -- --                         (λ l → λ { (j = i0) → a ∷ ⊙-assoc xs' ys zs (~ k)
-- -- -- -- --   -- --                                  ; (j = i1) →
-- -- -- -- --   -- --                                    invSides-filler
-- -- -- -- --   -- --                                      (⊙-pentagon-diag [ a ] xs' ys zs)
-- -- -- -- --   -- --                                      (cong (_⊙ zs) (⊙-assoc [ a ] xs' ys))
-- -- -- -- --   -- --                                      k l
-- -- -- -- --   -- --                                  ; (k = i0) → ⊙-pentagon-diag [ a ] xs' ys zs (~ j ∨ l)
-- -- -- -- --   -- --                                    })
-- -- -- -- --   -- --                         (⊙-pentagon-□ [ a ] xs' ys zs k (~ j))
-- -- -- -- --   -- --                     ; (i = i1) → ⊙-assoc [ a ] xs' (ys ⊙ zs) (~ j)
-- -- -- -- --   -- --                     ; (j = i0) → [ a ] ⊙ ⊙-assoc xs' ys zs (i ∨ ~ k)
-- -- -- -- --   -- --                     ; (j = i1) → (⊙-pentagon-△ [ a ] xs' ys zs (~ i) (~ k))
-- -- -- -- --   -- --                     }) (⊙-assoc [ a ] xs' (ys ⊙ zs) (~ i ∨ ~ j))))

-- -- -- -- --   -- --     w4 : {xs ys  : FCM₃ A} (bx : Uncons xs) (by : Uncons ys) → _
-- -- -- -- --   -- --     w4 (nil _) (nil _) = unconsSqNil
-- -- -- -- --   -- --     w4 {xs} {ys} (nil _) (cons _ ys' _) = unconsSqCons λ _ _ → ys'
-- -- -- -- --   -- --     w4 {_} {ys} (cons _ xs' _) _ = unconsSqCons (⊙-triangle xs' ys)

-- -- -- -- --   -- --     w5 : {xs ys zs ws : FCM₃ A} (bx : Uncons xs) (by : Uncons ys) (bz : Uncons zs) (bw : Uncons ws) → _
-- -- -- -- --   -- --     w5 (nil x) (nil x₁) (nil x₂) (nil x₃) = tt*
-- -- -- -- --   -- --     w5 {xs} {ys} {zs} {ws} (nil px) (nil py) (nil pz) (cons a ws' wp) = (refl , refl) ,
-- -- -- -- --   -- --       λ i j → 
-- -- -- -- --   -- --         hcomp
-- -- -- -- --   -- --           (λ k → λ {
-- -- -- -- --   -- --              (i = i0) → snd (w3 {ys = zs} {zs = ws} (u⊙ (nil px) (nil py)) (nil pz) (cons a ws' wp)) (~ k) j 
-- -- -- -- --   -- --             ;(i = i1) → snd (w3 {ys = ys} {zs = zs ⊙ ws} (nil px) (nil py) (u⊙ (nil pz) (cons a ws' wp))) k j
-- -- -- -- --   -- --             ;(j = i0) → [ a ] ⊙ ws'
-- -- -- -- --   -- --             ;(j = i1) → ⊙-pentagon-△ xs ys zs ws k i              
-- -- -- -- --   -- --            }) (snd (w3 {ys = zs} {zs = ws} (u⊙ (nil px) (nil py)) (nil pz) (cons a ws' wp)) i1 j )
         
-- -- -- -- --   -- --     w5 {xs} {ys} {zs} {ws} (nil px) (nil py) (cons a zs' pz) bw = (refl , refl) ,
-- -- -- -- --   -- --       λ i j → 
-- -- -- -- --   -- --         hcomp
-- -- -- -- --   -- --           (λ k → λ {
-- -- -- -- --   -- --              (i = i0) → snd (w3 {ys = zs} {zs = ws} (u⊙ (nil px) (nil py)) (cons a zs' pz) bw) (~ k) j 
-- -- -- -- --   -- --             ;(i = i1) → snd (w3 {ys = ys} {zs = zs ⊙ ws} (nil px) (nil py) (u⊙ (cons a zs' pz) bw)) k j
-- -- -- -- --   -- --             ;(j = i0) → a ∷ zs' ⊙ ws
-- -- -- -- --   -- --             ;(j = i1) → ⊙-pentagon-△ xs ys zs ws k i              
-- -- -- -- --   -- --            }) (snd (w3 {ys = zs} {zs = ws} (u⊙ (nil px) (nil py)) (cons a zs' pz) bw) i1 j )

-- -- -- -- --   -- --     w5 {xs} {ys} {zs} {ws} (nil x) (cons a ys' yp) bz bw =
-- -- -- -- --   -- --       (refl , ⊙-assoc ys' zs ws) , 
-- -- -- -- --   -- --        λ i j →
-- -- -- -- --   -- --          hcomp
-- -- -- -- --   -- --           (λ k → λ {
-- -- -- -- --   -- --              (i = i0) → snd (w3 {ys = zs} {zs = ws} (u⊙ (nil x) (cons a ys' yp)) bz bw) (~ k) j 
-- -- -- -- --   -- --             ;(i = i1) → snd (w3 {ys = ys} {zs = zs ⊙ ws} (nil x) (cons a ys' yp) (u⊙ bz bw)) k j
-- -- -- -- --   -- --             ;(j = i0) → a ∷ ⊙-assoc ys' zs ws ((~ k) ∨ i)
-- -- -- -- --   -- --             ;(j = i1) → ⊙-pentagon-△ xs ys zs ws k i              
-- -- -- -- --   -- --            }) (snd (w3 {ys = zs} {zs = ws} (u⊙ (nil x) (cons a ys' yp)) bz bw) i1 j)


-- -- -- -- --   -- --     w5 {xs} {ys} {zs} {ws} bx@(cons a xs' xp) by bz bw =
-- -- -- -- --   -- --       (refl , ⊙-pentagon-diag xs' ys zs ws ) ,
-- -- -- -- --   -- --        λ i j →
-- -- -- -- --   -- --          hcomp
-- -- -- -- --   -- --           (λ k → λ {
-- -- -- -- --   -- --              (i = i0) → snd (w3 {ys = zs} {zs = ws} (u⊙ bx by) bz bw) (~ k) j 
-- -- -- -- --   -- --             ;(i = i1) → snd (w3 {ys = ys} {zs = zs ⊙ ws} (cons a xs' xp) by (u⊙ bz bw)) k j
-- -- -- -- --   -- --             ;(j = i0) → a ∷ ⊙-pentagon-△ xs' ys zs ws (k) i
-- -- -- -- --   -- --             ;(j = i1) → ⊙-pentagon-△ xs ys zs ws k i              
-- -- -- -- --   -- --            }) (snd (w3 {ys = ys} {zs = zs ⊙ ws} (cons a xs' xp) by (u⊙ bz bw)) i0 j)
             
-- -- -- -- --   -- --     w6 : {xs ys zs ws : FCM₃ A} (bx : Uncons xs) (by : Uncons ys) (bz : Uncons zs) (bw : Uncons ws) → _
-- -- -- -- --   -- --     w6 (nil _) (nil _) (nil _) (nil _) = unconsSqNil
-- -- -- -- --   -- --     w6 (nil _) (nil _) (nil _) (cons _ ws _) = unconsSqCons λ _ _ → ws
-- -- -- -- --   -- --     w6 {_} {_} {_} {ws} (nil _) (nil _) (cons _ zs _) _ = unconsSqCons λ _ _ → zs ⊙ ws
-- -- -- -- --   -- --     w6 {_} {_} {zs} {ws} (nil x) (cons a ys x₁) _ _ = unconsSqCons λ i j → ⊙-assoc ys zs ws (j ∨ (~ i)) 
-- -- -- -- --   -- --     w6 (cons a xs x) _ _ _ = unconsSqCons (⊙-pentagon-△ _ _ _ _) 

-- -- -- -- --   -- --     w7 : {xs ys zs ws : FCM₃ A} (bx : Uncons xs) (by : Uncons ys) (bz : Uncons zs) (bw : Uncons ws) → _
-- -- -- -- --   -- --     w7 (nil x) (nil x₁) (nil x₂) (nil x₃) = unconsSqNil
-- -- -- -- --   -- --     w7 (nil _) (nil _) (nil _) (cons _ ws _) = unconsSqCons λ _ _ → ws
-- -- -- -- --   -- --     w7 {_} {_} {_} {ws} (nil _) (nil _) (cons _ zs' _) _ = unconsSqCons λ _ _ → zs' ⊙ ws
-- -- -- -- --   -- --     w7 {_} {_} {zs} {ws} (nil _) (cons _ ys' _) _ _ =
-- -- -- -- --   -- --                                 unconsSqCons λ i j → ⊙-assoc ys' zs ws (j ∧ (~ i))
-- -- -- -- --   -- --     w7 (cons _ _ _) _ _ _ = unconsSqCons (⊙-pentagon-□ _ _ _ _)

-- -- -- -- --   -- -- fromUncons : ∀ {x} → Uncons x → FCM₃ A
-- -- -- -- --   -- -- fromUncons (nil x) = []
-- -- -- -- --   -- -- fromUncons (cons a xs x) = a ∷ xs

-- -- -- -- --   -- -- unconsIso : (isGrpA : isGroupoid A) → Iso (Σ _ Uncons) (FCM₃ A)
-- -- -- -- --   -- -- Iso.fun (unconsIso isGrpA) = fromUncons ∘ snd
-- -- -- -- --   -- -- Iso.inv (unconsIso isGrpA) x = x , uncons isGrpA x
-- -- -- -- --   -- -- Iso.rightInv (unconsIso isGrpA) x =
-- -- -- -- --   -- --   Uncons-elim (λ u → fromUncons u ≡ x)
-- -- -- -- --   -- --     sym (λ _ _ p → p) (uncons isGrpA x) 
-- -- -- -- --   -- -- Iso.leftInv (unconsIso isGrpA) (_ , nil x) = ΣPathP ((sym x) , uncons≡ _ _ _ tt*)
-- -- -- -- --   -- -- Iso.leftInv (unconsIso isGrpA) (fst₁ , cons a xs x) =
-- -- -- -- --   -- --    ΣPathP (x , (uncons≡ _ _ _ ((refl , (⊙-unit-l xs)) ,
-- -- -- -- --   -- --      (leftright _ _ ◁ λ i j →
-- -- -- -- --   -- --        hcomp
-- -- -- -- --   -- --         (λ k → λ { (i = i1) → x (j ∧ k)
-- -- -- -- --   -- --                  ; (j = i0) → ⊙-triangle [ a ] xs i k
-- -- -- -- --   -- --                  ; (j = i1) → x (i ∧ k) })
-- -- -- -- --   -- --         (⊙-unit-r [ a ] (i ∨ j) ⊙ xs)))))


-- -- -- -- --   -- -- uncons-Iso-from : (Maybe (A × FCM₃ A)) → FCM₃ A
-- -- -- -- --   -- -- uncons-Iso-from nothing = []
-- -- -- -- --   -- -- uncons-Iso-from (just (a , xs)) = a ∷ xs



-- -- -- -- --   -- -- uncons-Iso : isGroupoid A → Iso (FCM₃ A) (Maybe (A × FCM₃ A))
-- -- -- -- --   -- -- Iso.fun (uncons-Iso isGrpA) x = Uncons→a,xs (uncons isGrpA x) 
-- -- -- -- --   -- -- Iso.inv (uncons-Iso isGrpA) = uncons-Iso-from    
-- -- -- -- --   -- -- Iso.rightInv (uncons-Iso isGrpA) nothing = refl
-- -- -- -- --   -- -- Iso.rightInv (uncons-Iso isGrpA) (just x) = cong (just ∘ (fst x ,_)) (⊙-unit-l (snd x))
-- -- -- -- --   -- -- Iso.leftInv (uncons-Iso isGrpA) a =
-- -- -- -- --   -- --   Uncons-elim (λ u → uncons-Iso-from (Uncons→a,xs u) ≡ a)
-- -- -- -- --   -- --               (λ p → sym p) (λ _ _ x → x) (uncons isGrpA a)


-- -- -- -- --   -- -- -- length0-≡-IsEmpty : ∀ x → ((length x ≡ 0) , isSetℕ _ _) ≡ (IsEmpty x)
-- -- -- -- --   -- -- -- length0-≡-IsEmpty =
-- -- -- -- --   -- -- --      ElimProp.f
-- -- -- -- --   -- -- --       (λ _ → isSetHProp _ _)
-- -- -- -- --   -- -- --       (L.⇔toPath (λ _ → _) λ _ → refl)
-- -- -- -- --   -- -- --       (λ _ → L.⇔toPath snotz ⊥rec)
-- -- -- -- --   -- -- --       {!!}
       


-- -- -- -- --   -- -- length' : Maybe (A × FCM₃ A) → ℕ
-- -- -- -- --   -- -- length' nothing = zero
-- -- -- -- --   -- -- length' (just x) = suc (length (snd x))

-- -- -- -- --   -- -- -- uncons-Iso-L' : isGroupoid A → ∀ k →
-- -- -- -- --   -- -- --                 Iso (Σ (FCM₃ A) (λ xs → k ≡ length xs))
-- -- -- -- --   -- -- --                     (Σ (Maybe (A × FCM₃ A)) (λ xs → k ≡ length' xs))
-- -- -- -- --   -- -- -- uncons-Iso-L' isGrpA _ =    
-- -- -- -- --   -- -- --       Σ-congProp-iso
-- -- -- -- --   -- -- --         (uncons-Iso isGrpA)
-- -- -- -- --   -- -- --         (λ _ → isSetℕ _ _)
-- -- -- -- --   -- -- --         (λ _ → isSetℕ _ _)
-- -- -- -- --   -- -- --         λ { (nothing ) → (λ x → x) , (λ x → x)
-- -- -- -- --   -- -- --           ; (just _) → (λ x → x) , (λ x → x) }


-- -- -- -- --   -- -- -- uncons-Iso-L : isGroupoid A → ∀ k →
-- -- -- -- --   -- -- --                 Iso (Σ (FCM₃ A) (λ xs → (suc k) ≡ length xs))
-- -- -- -- --   -- -- --                     (A × (Σ (FCM₃ A) (λ xs → k ≡ length xs)))
-- -- -- -- --   -- -- -- uncons-Iso-L isGrpA k =
-- -- -- -- --   -- -- --   compIso (uncons-Iso-L' isGrpA (suc k)) w

-- -- -- -- --   -- -- --    where
-- -- -- -- --   -- -- --      w : Iso _ _
-- -- -- -- --   -- -- --      Iso.fun w (nothing , p) = ⊥rec (snotz p)
-- -- -- -- --   -- -- --      Iso.fun w (just (a , l) , p) = a , l , injSuc p
-- -- -- -- --   -- -- --      Iso.inv w (a , l , p) = just (a , l) , cong suc p
-- -- -- -- --   -- -- --      Iso.rightInv w _ = ΣPathP (refl , Σ≡Prop (λ _ → isSetℕ _ _) refl)
-- -- -- -- --   -- -- --      Iso.leftInv w (nothing , p) = ⊥rec (snotz p)
-- -- -- -- --   -- -- --      Iso.leftInv w (just _ , _) = Σ≡Prop (λ _ → isSetℕ _ _) refl

-- -- -- -- --   -- -- -- -- -- head : isGroupoid A → ∀ l → 0 ≤ length l → A
-- -- -- -- --   -- -- -- -- -- head = {!!}

-- -- -- -- --   -- -- -- FCM₃-IsoL : isGroupoid A → ∀ k →
-- -- -- -- --   -- -- --                   Iso (Σ (FCM₃ A) (λ xs → k ≡ length xs))
-- -- -- -- --   -- -- --                       (Σ (B.FCM₃ A) (λ xs → k ≡ B.length xs))
-- -- -- -- --   -- -- -- Iso.fun (FCM₃-IsoL isGrpA zero) _ = B.[] , refl
-- -- -- -- --   -- -- -- Iso.inv (FCM₃-IsoL isGrpA zero) _ = [] , refl
-- -- -- -- --   -- -- -- Iso.rightInv (FCM₃-IsoL isGrpA zero) (B.[] , p) =
-- -- -- -- --   -- -- --    Σ≡Prop (λ _ → isSetℕ _ _) refl
-- -- -- -- --   -- -- -- Iso.rightInv (FCM₃-IsoL isGrpA zero) (x B.∷ l , p) = ⊥rec (znots p)
-- -- -- -- --   -- -- -- Iso.leftInv (FCM₃-IsoL isGrpA zero) (_ , p) = Σ≡Prop (λ _ → isSetℕ _ _)
-- -- -- -- --   -- -- --     (sym (length0≡[] (sym p)))
  
-- -- -- -- --   -- -- -- FCM₃-IsoL isGrpA (suc k) =
-- -- -- -- --   -- -- --   compIso (uncons-Iso-L isGrpA k) w 
-- -- -- -- --   -- -- --   where
-- -- -- -- --   -- -- --     w' : _
-- -- -- -- --   -- -- --     w' = FCM₃-IsoL isGrpA k 

-- -- -- -- --   -- -- --     w : Iso (A × Σ (FCM₃ A) (λ xs → k ≡ length xs))
-- -- -- -- --   -- -- --           (Σ (B.FCM₃ A) (λ xs → suc k ≡ B.length xs))
-- -- -- -- --   -- -- --     Iso.fun w (a , x) = a B.∷  fst (Iso.fun w' x)  , cong suc ((snd (Iso.fun w' x)))
-- -- -- -- --   -- -- --     Iso.inv w (B.[] , p) = ⊥rec (snotz p)
-- -- -- -- --   -- -- --     Iso.inv w (a B.∷ l , p) = a , (Iso.inv w' (l , injSuc p))
-- -- -- -- --   -- -- --     Iso.rightInv w (B.[] , p) = ⊥rec (snotz p)
-- -- -- -- --   -- -- --     Iso.rightInv w (a B.∷ l , p) =
-- -- -- -- --   -- -- --           Σ≡Prop (λ _ → isSetℕ _ _)
-- -- -- -- --   -- -- --            (cong (a B.∷_) (cong fst (Iso.rightInv w' (l , injSuc p))))

-- -- -- -- --   -- -- --     Iso.leftInv w _ = ΣPathP (refl ,  Iso.leftInv w' _)
