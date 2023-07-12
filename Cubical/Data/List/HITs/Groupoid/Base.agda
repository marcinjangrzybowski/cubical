{-# OPTIONS --safe #-}

module Cubical.Data.List.HITs.Groupoid.Base where

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


private
  variable
    ℓ : Level


infixr 5 _++_

cong-app : ∀ {ℓ} {A B : Type ℓ} → {a₀ a₁ : A}
     → (f : A → B) 
     → a₀ ≡ a₁ → f a₀ ≡ f a₁
cong-app f p i = f (p i)
{-# INLINE cong-app #-}

-- cong-app : ∀ {ℓ} {A B : Type ℓ} → {a₀ a₁ : A} → {f₀ f₁ : A → B} 
--      → (f : ∀ a → f₀ a ≡ f₁ a) → a₀ ≡ a₁ → f₀ a₀ ≡ f₁ a₁
-- cong-app f p i = f (p i) i
-- {-# INLINE cong-app #-}

-- congSqP : ∀ {ℓ ℓ'} {A : I → I → Type ℓ} {B : I → I → Type ℓ'}
--   {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁}
--   {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} {a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁}
--   {a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀} {a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁}
--   → (f : ∀ i j → A i j → B i j)
--   → SquareP A a₀₋ a₁₋ a₋₀ a₋₁
--   → SquareP B (congP (f i0) a₀₋) (congP (f i1) a₁₋)
--               (congP (λ i → f i i0) a₋₀) (congP (λ i → f i i1) a₋₁)
-- congSqP f sq i j = f i j (sq i j)
-- {-# INLINE congSqP #-}


congSqP₂ : ∀ {ℓ ℓ' ℓ''} {A : I → I → Type ℓ} {B : ∀ i j → A i j → Type ℓ'} {C : I → I → Type ℓ''}
  → (f : ∀ i j → ∀ a → B i j a → C i j)
  → ∀ {a₀₀ a₀₁ a₀₋ a₁₀ a₁₁ a₁₋ a₋₀ a₋₁}
  → (sqA : SquareP A {a₀₀} {a₀₁} a₀₋ {a₁₀} {a₁₁} a₁₋ a₋₀ a₋₁)
  → ∀ {b₀₀ b₀₁ b₀₋ b₁₀ b₁₁ b₁₋ b₋₀ b₋₁}
  → SquareP (λ i j → B i j (sqA i j)) {b₀₀} {b₀₁} b₀₋ {b₁₀} {b₁₁} b₁₋ b₋₀ b₋₁
  → SquareP C (congP₂ (f i0) a₀₋ b₀₋) (congP₂ (f i1) a₁₋ b₁₋)
              (congP₂ (λ i → f i i0) a₋₀ b₋₀) (congP₂ (λ i → f i i1) a₋₁ b₋₁)
congSqP₂ f sqA sqB i j = f i j (sqA i j) (sqB i j)
{-# INLINE congSqP₂ #-}




-- todo : better name
congSq* : ∀ {ℓ} {A B : Type ℓ} → {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁} {f₀ f₁ : A → B} 
     → (f : ∀ a → f₀ a ≡ f₁ a) 
  → Square (cong-app f₀ a₀₋) (cong-app f₀ a₁₋) (cong-app f₀ a₋₀) (cong-app f₀ a₋₁)
  → Square (cong-app f₁ a₀₋) (cong-app f₁ a₁₋) (cong-app f₁ a₋₀) (cong-app f₁ a₋₁)
congSq* {a₀₋ = a₀₋} {a₁₋ = a₁₋} {a₋₀ = a₋₀} {a₋₁ = a₋₁}   f sq i j =
      hcomp (λ k →
    λ { (i = i0) → f (a₀₋ j) k 
      ; (i = i1) → f (a₁₋ j) k 
      ; (j = i0) → f (a₋₀ i) k
      ; (j = i1) → f (a₋₁ i) k
       }) (sq i j)

   

congApp-∙ : {A B : Type ℓ}
        → {f f' : A → B} {x x' : A}
        → (p : f ≡ f') → (q : x ≡ x') 
        →  (cong f q) ∙ (λ i → p i x') ≡ λ i → p i (q i)
congApp-∙ p q i j =
  hcomp
    (λ k →
      λ { (i = i1) → p j (q j)
        ; (j = i0) → p i0 (q i0)
        ; (j = i1) → p (k ∨ i) (q i1) 
        })
    ( p (j ∧ i) (q j))


cong₂-∙' : {A B C : Type ℓ}
        → (f : A → B → C) {x x' x'' : A} {y y' : B}
        → (p : x ≡ x') (p' : x' ≡ x'') → (q : y ≡ y') 
        →  cong₂ f (p ∙' p') q ≡ cong (λ x → f x y) p ∙ (λ i → f (p' i) (q i))  
cong₂-∙' f p p' q i j =
   hcomp
     (λ k → λ { (i = i0) → f
                          (hcomp (λ l → λ { (j = i0) → p (~ l)
                                           ; (j = i1) → (p' k) 
                                           ; (k = i0) → p (~ l ∨ j)
                                           }) (p' (k ∧ j)))
                          (q (j ∧ k))
               ; (j = i0) → f (p i0) (q i0)
               ; (j = i1) → f (p' k) (q k)
               }) (f (p j) (q i0) ) 


cong₂-∙'' : {A B C : Type ℓ}
        → (f : B → A → C) {x x' x'' : A} {y y' : B}
        → (p : x ≡ x') (p' : x' ≡ x'') → (q : y ≡ y') 
        → cong₂ f q (p ∙ p') ≡ cong (f y) p ∙ (λ i → f (q i) (p' i) )  
cong₂-∙'' f p p' q i j =
      hcomp
     (λ k → λ { (i = i0) → f (q (j ∧ k)) (compPath-filler p p' k j)
               ; (j = i0) → f (q i0) (p i0)
               ; (j = i1) → f (q k) (p' k)
               }) (f (q i0) (p j))


cong₂-∙ : {A B C : Type ℓ}
        → (f : A → B → C) {x x' : A} {y y' : B}
        → (p : x ≡ x') → (q : y ≡ y') 
        →  cong (λ x → f x y) p ∙ cong (f x') q ≡ cong₂ f p q
cong₂-∙ f p q i j = 
  hcomp
    (λ k →
      λ { (i = i1) → f (p j) (q j)
        ; (j = i0) → f (p i0) (q i0)
        ; (j = i1) → f (p i1) (q (k ∨ i)) 
        })
    (f (p j) (q (j ∧ i)))


lem-pqr : ∀ {ℓ} {A : Type ℓ} → {x y z : A}
        → {p : x ≡ y} → {q r : y ≡ z}
        → Square p q p r
        → r ≡ q
lem-pqr {p = p} {q} {r} s i j  =
      hcomp (λ k →
    λ { (i = i0) → invSides-filler r (sym p) (~ k) j 
      ; (i = i1) → q j 
      ; (j = i0) → p (i ∨ k)
      ; (j = i1) → r (i ∨ k)
       }) (s i j)


lem-pqr' : ∀ {ℓ} {A : Type ℓ} → {x y z : A}
        → {p : x ≡ y} → {q r : y ≡ z}
        → r ≡ q
        → Square p q p r
        
lem-pqr' {p = p} {q} {r} s i j  =
      hcomp (λ k →
    λ { (i = i0) → invSides-filler r (sym p) (k) j 
      ; (i = i1) → q j 
      ; (j = i0) → p (i ∨ (~ k))
      ; (j = i1) → r (i ∨ (~ k))
       }) (s i j)


data List (A : Type ℓ) : Type ℓ where
  [] : List A
  [_] : A → List A
  _++_ : List A → List A → List A
  ++-unit-r : (xs : List A) → xs ++ [] ≡ xs
  ++-unit-l : (xs : List A) → [] ++ xs ≡ xs
  ++-assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ ys ++ zs
  ++-triangle : ∀ xs ys → Square {A = List A}                     
                           (++-assoc xs [] ys)
                           refl
                           (cong (_++ ys) (++-unit-r xs))
                           (cong (xs ++_) (++-unit-l ys))

  ++-pentagon-diag : (xs ys zs ws : List A)
       → ((xs ++ ys) ++ zs) ++ ws ≡ xs ++ ys ++ zs ++ ws
  ++-pentagon-△ : (xs ys zs ws : List A) →
        Square refl (++-pentagon-diag xs ys zs ws)
          (sym (++-assoc _ _ _)) (++-assoc _ _ _)
  ++-pentagon-□ : (xs ys zs ws : List A) →
        Square (++-pentagon-diag xs ys zs ws)
           (++-assoc _ _ _)
           (cong (_++ ws) (++-assoc _ _ _))           
           (sym (cong (xs ++_) (++-assoc _ _ _)))

  trunc : isGroupoid (List A)

++-pentagon : {A : Type ℓ} → (xs ys zs ws : List A) → Square
           (++-assoc _ zs _ ∙∙ refl ∙∙ ++-assoc _ ys _)
           (++-assoc _ _ _)
           (cong (_++ ws) (++-assoc _ _ _))           
           (sym (cong (xs ++_) (++-assoc _ _ _)))
++-pentagon xs ys zs ws =
  (λ i j → hcomp
   (λ k → λ { (i = i1) → ++-pentagon-△ xs ys zs ws k j
            ; (j = i0) → ++-assoc (xs ++ ys) zs ws (~ k)
            ; (j = i1) → ++-assoc xs ys (zs ++ ws) k
            })
   ((xs ++ ys) ++ zs ++ ws))
   ◁ ++-pentagon-□ xs ys zs ws


module _ {A : Type ℓ} where

 replicate^2 : ℕ → List A → List A
 replicate^2 k = iter k λ x → x ++ x 

 replicate^2' : ℕ → B.List A → B.List A
 replicate^2' k = iter k λ x → x B.++ x 


 infixr 5 _∷_
 infixr 5 _∷ʳ_

 _∷_ : A → List A → List A
 x ∷ xs = [ x ] ++ xs

 _∷ʳ_ : List A → A → List A
 xs ∷ʳ x = xs ++ [ x ]

 module ElimList {ℓb} (B : List A → Type ℓb) where 

  record H1 : Type (ℓ-max ℓ ℓb) where
   no-eta-equality
   field
    b[] : B []
    b[_] : ∀ a → B [ a ]
    _b++_ : ∀ {xs ys} → B xs → B ys → B (xs ++ ys)


   record H2 : Type (ℓ-max ℓ ℓb) where
    no-eta-equality
    field
     b++ur : ∀ {xs} → (b : B xs) →
               PathP (λ i → B (++-unit-r xs i)) (b b++ b[]) b
     b++ul : ∀ {xs} → (b : B xs) →
               PathP (λ i → B (++-unit-l xs i)) (b[] b++ b) b
     b++-assoc : ∀ {xs ys zs} → (bx : B xs) (by : B ys) (bz : B zs)
                    → PathP (λ i → B (++-assoc xs ys zs i))
                       ((bx b++ by) b++ bz)
                        (bx b++ (by b++ bz))
     b++-pent-diag : ∀ {xs ys zs ws} → (bx : B xs) (by : B ys) (bz : B zs)(bw : B ws)
                    → PathP (λ i → B (++-pentagon-diag xs ys zs ws i))
                       (((bx b++ by) b++ bz) b++ bw)
                        (bx b++ (by b++ (bz b++ bw)))


    record H3 : Type (ℓ-max ℓ ℓb) where
     no-eta-equality
     field
      b++-triangle : ∀ {xs ys} → (bx : B xs)(by : B ys)
                     → SquareP (λ i j → B (++-triangle xs ys i j))
                         (b++-assoc bx b[] by)
                         refl
                         (λ i → b++ur bx i b++ by)
                         λ i → bx b++ b++ul by i
      b++-pent-△ : ∀ {xs ys zs ws} → (bx : B xs) (by : B ys) (bz : B zs)(bw : B ws)
                     → SquareP (λ i j → B (++-pentagon-△ xs ys zs ws i j))
                         refl
                          (b++-pent-diag bx by bz bw)
                          (symP (b++-assoc _ _ _))
                          (b++-assoc _ _ _)
      b++-pent-□ : ∀ {xs ys zs ws} → (bx : B xs) (by : B ys) (bz : B zs)(bw : B ws)
                     → SquareP (λ i j → B (++-pentagon-□ xs ys zs ws i j))
                         (b++-pent-diag bx by bz bw)
                         (b++-assoc _ _ _)
                         (λ i → b++-assoc bx by bz i b++ bw)
                         λ i → bx b++ b++-assoc by bz bw (~ i)

     module _ (isGroupoidB : ∀ x → isGroupoid (B x)) where
      f₃ : ∀ x → B x
      f₃ [] = b[]
      f₃ [ a ] = b[ a ]
      f₃ (xs ++ ys) = f₃ xs b++ f₃ ys
      f₃ (++-unit-r x i) = b++ur (f₃ x) i
      f₃ (++-unit-l x i) = b++ul (f₃ x) i
      f₃ (++-assoc xs ys zs i) =
        b++-assoc (f₃ xs) (f₃ ys) (f₃ zs) i
      f₃ (++-triangle xs ys i j) =
        b++-triangle (f₃ xs) (f₃ ys) i j
      f₃ (++-pentagon-diag xs ys zs ws i) =
        b++-pent-diag (f₃ xs) (f₃ ys) (f₃ zs) (f₃ ws) i
      f₃ (++-pentagon-△ xs ys zs ws i j) =
        b++-pent-△ (f₃ xs) (f₃ ys) (f₃ zs) (f₃ ws) i j
      f₃ (++-pentagon-□ xs ys zs ws i j) =
        b++-pent-□ (f₃ xs) (f₃ ys) (f₃ zs) (f₃ ws) i j
      f₃ (trunc x y p q r s i₀ i₁ i₂) =
         (isOfHLevel→isOfHLevelDep (suc (suc (suc zero))) isGroupoidB)
              (f₃ x) (f₃ y)
              (cong f₃ p) (cong f₃ q)
              (λ i₃ i₄ → f₃ (r i₃ i₄)) (λ i₃ i₄ → f₃ (s i₃ i₄))
              (trunc x y p q r s) i₀ i₁ i₂
              
    open H3 using (f₃) public
     
    module _ (isSetB : ∀ x → isSet (B x)) where
     r₃ : H3
     H3.b++-triangle r₃ _ _ =
       isSet→SquareP (λ _ _ → isSetB _) _ _ _ _ 
     H3.b++-pent-△ r₃ _ _ _ _ = 
       isSet→SquareP (λ _ _ → isSetB _) _ _ _ _          
     H3.b++-pent-□ r₃ _ _ _ _ =
       isSet→SquareP (λ _ _ → isSetB _) _ _ _ _ 

     f₂ : ∀ x → B x
     f₂ = H3.f₃ r₃ (isSet→isGroupoid ∘ isSetB)




   module _ (isPropB : ∀ x → isProp (B x)) where
    r₂ : H2
    H2.b++ur r₂ _ = isProp→PathP (λ _ → isPropB _) _ _
    H2.b++ul r₂ _ = isProp→PathP (λ _ → isPropB _) _ _
    H2.b++-assoc r₂ _ _ _ = isProp→PathP (λ _ → isPropB _) _ _
    H2.b++-pent-diag r₂ _ _ _ _ = isProp→PathP (λ _ → isPropB _) _ _
    
    f₁ : ∀ x → B x
    f₁ = H2.f₂ r₂ (isProp→isSet ∘ isPropB)

   record H2' : Type (ℓ-max ℓ ℓb) where
    no-eta-equality
    field
     b++ur : ∀ {xs} → (b : B xs) →
               PathP (λ i → B (++-unit-r xs i)) (b b++ b[]) b
     b++ul : ∀ {xs} → (b : B xs) →
               PathP (λ i → B (++-unit-l xs i)) (b[] b++ b) b
     b++-assoc : ∀ {xs ys zs} → (bx : B xs) (by : B ys) (bz : B zs)
                    → PathP (λ i → B (++-assoc xs ys zs i))
                       ((bx b++ by) b++ bz)
                        (bx b++ (by b++ bz))

   fromH2' : (isSetB : ∀ x → isSet (B x)) → H2' → H2
   fromH2' isSetB x = w
    where
    open H2' x
    w : H2
    H2.b++ur w = b++ur
    H2.b++ul w = b++ul
    H2.b++-assoc w = b++-assoc
    H2.b++-pent-diag w {xs} {ys} {zs} {ws} bx by bz bw i =
      comp
       (λ j → B (++-pentagon-△ xs ys zs ws j i))
       (λ j → λ { (i = i0) → b++-assoc (bx b++ by) bz bw (~ j)
                ; (i = i1) → b++-assoc bx by (bz b++ bw) j } )
       ((bx b++ by) b++ (bz b++ bw))


   open H2 using (f₂ ; H3 ; f₃) public


  open H1 using (H2 ; H2' ; f₂ ; H3 ; f₃ ; f₁) public

  ElimList : HLevel → Type (ℓ-max ℓ ℓb)
  ElimList 0 = Unit*
  ElimList 1 = H1
  ElimList 2 = Σ H1 H2'
  ElimList (suc (suc (suc _))) = Σ (Σ _ H2) (H3 ∘ snd )



module _ {A : Type ℓ} {ℓb} (B : List A → Type ℓb) where
 open ElimList

 elimList : (n : HLevel) → ElimList B n →
       if Dec→Bool (≤Dec n 3)
        then
        ((∀ x → isOfHLevel n (B x))

        → ∀ x →  B x)
        else Unit* --(∀ x → ∥ B x ∥₃)
 elimList 0 _ = fst ∘_
 elimList 1 = f₁
 elimList 2 = uncurry λ _ y q → f₂ ((H1.fromH2' _ q) y) q
 elimList 3 = uncurry (λ z → f₃)
 elimList (suc (suc (suc (suc n)))) x = _
--   --   f₃  (snd w) λ _ → squash₃
--   -- where
--   -- w : ElimList (∥_∥₃ ∘ B) 3
--   -- H1.b[] (fst (fst w)) = ∣ H1.b[] (fst (fst x)) ∣₃ 
--   -- H1.b[ fst (fst w) ] = ∣_∣₃ ∘ H1.b[_] (fst (fst x))
--   -- H1._b++_ (fst (fst w)) = {!!}
--   -- snd (fst w) = {!!}
--   -- snd w = {!!}

module _ {A : Type ℓ} where
 module RecList {ℓb} (B : Type ℓb) where 

  record H1 : Type (ℓ-max ℓ ℓb) where
   no-eta-equality
   field
    b[] : B
    b[_] : A → B
    _b++_ : B → B → B
    

   record H2 : Type (ℓb) where
    no-eta-equality
    field
     b++ur : ∀ b → (b b++ b[]) ≡ b
     b++ul : ∀ b → (b[] b++ b) ≡ b
     b++-assoc : ∀ bx by bz → ((bx b++ by) b++ bz) ≡ (bx b++ (by b++ bz))
     b++-pent-diag : ∀ bx by bz bw →
                      (((bx b++ by) b++ bz) b++ bw)
                      ≡  (bx b++ (by b++ (bz b++ bw)))


    record H3 : Type (ℓb) where
     no-eta-equality
     field
      b++-triangle : ∀ bx by
                     → Square
                         (b++-assoc bx b[] by)
                         refl
                         (λ i → b++ur bx i b++ by)
                         λ i → bx b++ b++ul by i
      b++-pent-△ : ∀ bx by bz bw →
                   Square
                         refl
                          (b++-pent-diag bx by bz bw)
                          (symP (b++-assoc _ _ _))
                          (b++-assoc _ _ _)
      b++-pent-□ : ∀ bx by bz bw →
                   Square
                         (b++-pent-diag bx by bz bw)
                         (b++-assoc _ _ _)
                         (λ i → b++-assoc bx by bz i b++ bw)
                         λ i → bx b++ b++-assoc by bz bw (~ i)

     module _ (isGroupoidB : isGroupoid B) where
      f₃ : List A → B
      f₃ [] = b[]
      f₃ [ a ] = b[ a ]
      f₃ (xs ++ ys) = f₃ xs b++ f₃ ys
      f₃ (++-unit-r x i) = b++ur (f₃ x) i
      f₃ (++-unit-l x i) = b++ul (f₃ x) i
      f₃ (++-assoc xs ys zs i) =
        b++-assoc (f₃ xs) (f₃ ys) (f₃ zs) i
      f₃ (++-triangle xs ys i j) =
        b++-triangle (f₃ xs) (f₃ ys) i j
      f₃ (++-pentagon-diag xs ys zs ws i) =
        b++-pent-diag (f₃ xs) (f₃ ys) (f₃ zs) (f₃ ws) i
      f₃ (++-pentagon-△ xs ys zs ws i j) =
        b++-pent-△ (f₃ xs) (f₃ ys) (f₃ zs) (f₃ ws) i j
      f₃ (++-pentagon-□ xs ys zs ws i j) =
        b++-pent-□ (f₃ xs) (f₃ ys) (f₃ zs) (f₃ ws) i j
      f₃ (trunc x y p q r s i₀ i₁ i₂) =
         isGroupoidB
              (f₃ x) (f₃ y)
              (cong f₃ p) (cong f₃ q)
              (λ i₃ i₄ → f₃ (r i₃ i₄)) (λ i₃ i₄ → f₃ (s i₃ i₄))
               i₀ i₁ i₂
              
    open H3 using (f₃) public
     
    module _ (isSetB : isSet B) where
     r₃ : H3
     H3.b++-triangle r₃ _ _ =
       isSet→isSet' isSetB _ _ _ _ 
     H3.b++-pent-△ r₃ _ _ _ _ = 
       isSet→isSet' isSetB _ _ _ _          
     H3.b++-pent-□ r₃ _ _ _ _ =
       isSet→isSet' isSetB _ _ _ _ 

     f₂ : List A → B
     f₂ = H3.f₃ r₃ (isSet→isGroupoid isSetB)


   module _ (isPropB : isProp B) where
    r₂ : H2
    H2.b++ur r₂ _ = isPropB _ _
    H2.b++ul r₂ _ = isPropB _ _
    H2.b++-assoc r₂ _ _ _ = isPropB _ _
    H2.b++-pent-diag r₂ _ _ _ _ = isPropB _ _
    
    f₁ : List A → B
    f₁ = H2.f₂ r₂ (isProp→isSet isPropB)


   open H2 using (f₂ ; H3 ; f₃) public 
  open H1 using (H2 ; f₂ ; H3 ; f₃ ; f₁) public

  RecList : HLevel → Type (ℓ-max ℓ ℓb)
  RecList 0 = Unit*
  RecList 1 = H1
  RecList 2 = Σ _ H2
  RecList (suc (suc (suc _))) = Σ (Σ _ H2) (H3 ∘ snd )

module _ {A : Type ℓ} {ℓb} (B : Type ℓb) where
 open RecList

 recList : (n : HLevel) → RecList {ℓ = ℓ} {A = A} B n →
       if Dec→Bool (≤Dec n 3)
        then
        ((isOfHLevel n B)

        → List A →  B)
        else Unit* --(∀ x → ∥ B x ∥₃)
 recList 0 _ (b , _) _ = b
 recList 1 = f₁
 recList 2 = uncurry λ _ → f₂ 
 recList 3 = uncurry (λ z → f₃)
 recList (suc (suc (suc (suc n)))) x = _

module _ {A : Type ℓ} where

  rev : List A → List A
  rev [] = []
  rev [ x ] = [ x ]
  rev (x ++ y) = rev y ++ rev x
  rev (++-unit-r x i) = ++-unit-l (rev x) i
  rev (++-unit-l x i) = ++-unit-r (rev x) i
  rev (++-assoc x y z i) = ++-assoc (rev z) (rev y) (rev x) (~ i)
  rev (++-triangle x y i j) = ++-triangle (rev y) (rev x) i (~ j)
  rev (++-pentagon-diag x y z w i) = ++-pentagon-diag (rev w) (rev z) (rev y) (rev x) (~ i)
  rev (++-pentagon-△ x y z w i j) = ++-pentagon-△ (rev w) (rev z) (rev y) (rev x) i (~ j)
  rev (++-pentagon-□ x y z w i j) = ++-pentagon-□ (rev w) (rev z) (rev y) (rev x) i (~ j)
  rev (trunc x y p q r s i₀ i₁ i₂) =
    trunc (rev x) (rev y) (cong rev p) (cong rev q) (cong (cong rev) r) (cong (cong rev) s) i₀ i₁ i₂


  lawCool-l : (xs ys : List A)
            → Square
              (++-assoc [] xs ys) refl
              (cong (_++ ys) (++-unit-l xs)) (++-unit-l (xs ++ ys))

  lawCool-l xs ys =
     congSq* ++-unit-l λ i j →
      (hcomp (λ k →
         λ { (i = i0) → hcomp (λ l →
                         λ { (k = i1) → [] ++ ++-assoc [] xs ys (l ∧ j)
                           ; (j = i1) → [] ++ ++-assoc [] xs ys l
                           ; (k = i0) → ++-pentagon-□ [] [] xs ys (~ l) j
                           }) ((++-assoc [] ([] ++ xs) ys (j ∨ k)))
           ; (i = i1) → ++-assoc [] xs ys (k ∨ j) 
           ; (j = i0) → hcomp (λ l → λ { (i = i1) → ++-assoc [] xs ys k
                                       ; (k = i1) → [] ++ (++-unit-l xs i ++ ys)
                                       ; (k = i0) → ++-triangle [] xs i (~ l) ++ ys
                                       }) (++-assoc [] (++-unit-l xs i) ys k)
           ; (j = i1) → [] ++ ++-unit-l (xs ++ ys) i
            }) (hcomp (λ k →
                   λ { (i = i0) → ++-pentagon-△ [] [] xs ys k j 
                     ; (i = i1) → ++-assoc [] xs ys (~ k ∨ j) 
                     ; (j = i0) → ++-assoc (++-unit-r [] i) xs ys (~ k)
                     ; (j = i1) → ++-triangle [] (xs ++ ys) i k
                      }) (++-unit-r [] i ++ xs ++ ys)))

  lawCool-r' : (xs ys : List A)
            → Square
              (++-assoc (rev (rev xs)) (rev (rev ys)) []) refl
              (++-unit-r (rev (rev xs) ++ rev (rev ys)))
               (cong (_ ++_) (++-unit-r (rev (rev ys))))

  lawCool-r' xs ys i j = rev ((lawCool-l (rev ys) (rev xs)) i (~ j))
   
    

  lawCool-r : (xs ys : List A)
            → Square
              (++-assoc xs ys []) refl
              (++-unit-r (xs ++ ys)) (cong (xs ++_) (++-unit-r ys))
  lawCool-r xs ys =
    congSq* ++-unit-r λ i j →
      (hcomp (λ k →
         λ { (i = i0) →  hcomp (λ l →
                         λ { (k = i1) → ++-assoc xs ys [] (~ l ∨ j) ++ []
                           ; (j = i0) → ++-assoc xs ys [] (~ l) ++ []
                           ; (k = i0) → ++-pentagon-□ xs ys [] [] (~ l) j
                           }) ((++-assoc xs (ys ++ []) [] (j ∧ ~ k)))
           ; (i = i1) → ++-assoc xs ys [] (~ k ∧ j) 
           ; (j = i1) →  hcomp (λ l →
                           λ { (i = i1) → ++-assoc xs ys [] (~ k)
                             ; (k = i1) → (xs ++ ++-unit-r ys i) ++ []
                             ; (k = i0) → xs ++ ++-triangle ys [] i (l)
                             }) (++-assoc xs (++-unit-r ys i) [] (~ k))
           ; (j = i0) → ++-unit-r (xs ++ ys) i ++ []
            }) (hcomp (λ k →
                   λ { (i = i0) → ++-pentagon-△ xs ys [] [] k j 
                     ; (i = i1) → ++-assoc xs ys [] (k ∧ j) 
                     ; (j = i1) → ++-assoc xs ys (++-unit-l [] i) (k)
                     ; (j = i0) → ++-triangle (xs ++ ys) [] i (~ k)
                      }) ((xs ++ ys) ++ ++-unit-l [] i)))


  ++-unit-lr[] : ++-unit-l {A = A} [] ≡ ++-unit-r [] 
  ++-unit-lr[] =
     congSq* ++-unit-r λ i j →
            (hcomp (λ k →
            λ { (i = i0) → lawCool-l [] [] j (~ k) 
              ; (i = i1) → ++-triangle [] [] j (~ k) 
              ; (j = i0) → ++-assoc [] [] [] (~ k)
              ; (j = i1) → [] ++ []
               })
     ((lem-pqr λ i j → (++-unit-l (++-unit-l [] (~ j)) (~ i))) i (~ j)))




  length : List A → ℕ
  length = recList _ 2 w isSetℕ
   where
   open RecList
   w : RecList.RecList ℕ 2
   H1.b[] (fst w) = zero
   H1.b[ fst w ] _ = 1
   H1._b++_ (fst w) = _+_
   H2.b++ur (snd w) = +-zero
   H2.b++ul (snd w) = λ _ → refl
   H2.b++-assoc (snd w) n m o = sym (+-assoc n m o)
   H2.b++-pent-diag (snd w) bx by bz bw =
     sym (+-assoc (bx + by) bz bw) ∙∙ refl ∙∙ sym (+-assoc bx by (bz + bw))
  
  rev-rev : ∀ x → rev (rev x) ≡ x
  rev-rev [] = refl
  rev-rev [ x ] = refl
  rev-rev (x ++ y) = cong₂ _++_ (rev-rev x) (rev-rev y)
  rev-rev (++-unit-r x i) j = ++-unit-r (rev-rev x j) i
  rev-rev (++-unit-l x i) j = ++-unit-l (rev-rev x j) i
  rev-rev (++-assoc x y z i) j = ++-assoc (rev-rev x j) (rev-rev y j) (rev-rev z j) i
  rev-rev (++-triangle x y i j) k = (++-triangle (rev-rev x k) (rev-rev y k) i j)
  rev-rev (++-pentagon-diag x y z w i) k =
     ++-pentagon-diag (rev-rev x k) (rev-rev y k) (rev-rev z k) (rev-rev w k) i
  rev-rev (++-pentagon-△ x y z w i j) k =
     ++-pentagon-△ (rev-rev x k) (rev-rev y k) (rev-rev z k) (rev-rev w k) i j
  rev-rev (++-pentagon-□ x y z w i j) k =
     ++-pentagon-□ (rev-rev x k) (rev-rev y k) (rev-rev z k) (rev-rev w k) i j
  rev-rev (trunc x y p q r s i₀ i₁ i₂) k =
     (trunc (rev-rev x k) (rev-rev y k)
             (λ j → (rev-rev (p j) k)) (λ j → (rev-rev (q j) k))
             (λ j j' → (rev-rev (r j j') k)) (λ j j' → (rev-rev (s j j') k))
             i₀ i₁ i₂)

  Iso-rev : Iso (List A) (List A)
  Iso.fun Iso-rev = rev
  Iso.inv Iso-rev = rev
  Iso.rightInv Iso-rev = rev-rev
  Iso.leftInv Iso-rev = rev-rev


  length0≡[] : ∀ {x} → length x ≡ 0 → x ≡ []
  length0≡[] {x} =
    elimList (λ x → length x ≡ 0 → x ≡ []) 2
      (w , w') (λ x → isSetΠ λ _ → trunc _ _) x
     where
      open ElimList.H1
      w : ElimList.H1 (λ x₁ → length x₁ ≡ 0 → x₁ ≡ [])
      b[] w _ = refl
      b[ w ] _ p = ⊥rec (snotz p)
      _b++_ w {xs} {ys} px py p =
         let (px0 , py0) = m+n≡0→m≡0×n≡0 {length xs} {length ys} p
         in cong₂ _++_ (px px0) (py py0) ∙' ++-unit-r []

      assoc≡z : ∀ {n m o} → PathP (λ i → +-assoc n m o i ≡ zero
                               → ua (Σ-assoc-≃ {A = n ≡ zero}
                                               {λ _ → m ≡ zero }
                                               {λ _ _ → o ≡ zero}) (~ i) )
                           (map-snd m+n≡0→m≡0×n≡0 ∘ m+n≡0→m≡0×n≡0)
                           (map-fst m+n≡0→m≡0×n≡0 ∘ m+n≡0→m≡0×n≡0)
      assoc≡z {zero} {m} {o} i x =
        ua-gluePath Σ-assoc-≃ (λ _ → refl , m+n≡0→m≡0×n≡0 x ) (~ i)
      assoc≡z {suc n} {m} {o} = funExtDep λ p → ⊥rec (snotz (p i0))


      open ElimList.H2'
      w' : H2' w
      b++ur w' {x} b = funExtDep λ p i j → hcomp (λ k →
                λ { (i = i1) → ++-unit-r (b (p i) (j ∨ ~ k)) (j ∨ k)
                  ; (j = i0) → ++-unit-r
                          (b (isSetℕ _ _ (fst (m+n≡0→m≡0×n≡0 (p i0))) (p i1) i) (~ k))
                          (i ∧ k)
                  ; (j = i1) → [] }) (++-unit-r [] j)
      b++ul w' {x} b i p j = hcomp (λ k →
                    λ { (i = i1) → ++-unit-l (b p (j ∨ ~ k)) (j ∨ k) 
                      ; (j = i0) → ++-unit-l (b p (~ k)) (i ∧ k)
                      ; (j = i1) → [] }) (++-unit-lr[] (~ i) j)
      b++-assoc w' {x} {y} {z} bx by bz =
        funExtDep λ p → congP (λ _ → _∙' ++-unit-r [])
           λ j i → hcomp (λ k →
              let (px , py , pz) = unglue (j ∨ ~ j)
                       (assoc≡z {length x} {length y} {length z} (~ j) (p j))
              in λ { (i = i0) → ++-assoc (bx px (~ k)) (by py (~ k)) (bz pz (~ k)) j
                   ; (i = i1) → [] ++ []
                   ; (j = i0) → doubleCompPath-filler
                              (cong₂ _++_ (bx px) (by py))                              
                              (++-unit-r []) refl k i ++ bz pz (i ∨ ~ k)
                   ; (j = i1) → bx px (i ∨ ~ k) ++ doubleCompPath-filler
                                (cong₂ _++_ (by py) (bz pz))                                
                                (++-unit-lr[] k) refl k i})
                   (++-triangle [] [] i j)

  isContrLen0 : isContr (Σ (List A) λ x → length x ≡ 0)
  fst isContrLen0 = [] , refl
  snd isContrLen0 = λ y → Σ≡Prop (λ _ → isSetℕ _ _) (sym (length0≡[] (snd y)))

  isContr[]≡[] : isContr ([] ≡ [])
  isContr[]≡[] = refl , λ p j i → length0≡[] {x = p i} (λ i₁ → length (p (i₁ ∨ i))) (~ j)


  length0≡[]-sec : ∀ {x} → (b : x ≡ []) → length0≡[] (λ i → length (b i)) ≡ b
  length0≡[]-sec {x} = elimList
     (λ x → (b : x ≡ []) → length0≡[] (λ i → length (b i)) ≡ b)
     1
     w
     (λ _ → isPropΠ λ _ → trunc _ _ _ _)
     x
    where
    w : ElimList.ElimList
          (λ x₁ → (b : x₁ ≡ []) → length0≡[] (λ i → length (b i)) ≡ b) 1
    ElimList.H1.b[] w  = snd isContr[]≡[]
    ElimList.H1.b[ w ] _ b = ⊥rec (snotz (cong length b))
    ElimList.H1._b++_ w _ _ b i j =
            hcomp
               (λ k →
                   λ {  (i = i0) → length0≡[] {x = b (~ k)} (λ i' → length (b (~ k ∨  i'))) j  
                      ; (i = i1) → b ((~ k) ∨ j)
                      ; (j = i0) → b (~ k)
                      ; (j = i1) → []
                      }) []

  Iso-length0≡[] : ∀ {x} → Iso (length x ≡ 0) (x ≡ [])
  Iso.fun Iso-length0≡[] = length0≡[]
  Iso.inv Iso-length0≡[] = cong length
  Iso.rightInv Iso-length0≡[] = length0≡[]-sec
  Iso.leftInv Iso-length0≡[] a = isSetℕ _ _ _ _

  isProp≡[] : ∀ x → isProp (x ≡ [])
  isProp≡[] x =
    isPropRetract
      (cong length) (length0≡[] {x = x})
      length0≡[]-sec (isSetℕ _ _)


  IsEmpty : List A → hProp ℓ-zero
  IsEmpty =
    recList _ 2 w
      isSetHProp
   where
   w : RecList.RecList (hProp ℓ-zero) 2
   RecList.H1.b[] (fst w) = L.⊤
   RecList.H1.b[ fst w ] _ = L.⊥
   RecList.H1._b++_ (fst w) = L._⊓_
   RecList.H2.b++ur (snd w) = L.⊓-identityʳ 
   RecList.H2.b++ul (snd w) =  L.⊓-identityˡ 
   RecList.H2.b++-assoc (snd w) = (λ _ by bz → sym (L.⊓-assoc _ by bz))
   RecList.H2.b++-pent-diag (snd w) =
     λ bx by bz bw →
       sym (L.⊓-assoc (bx L.⊓ by) bz bw) ∙∙ refl ∙∙ sym (L.⊓-assoc bx by (bz L.⊓ bw) )


  data Uncons (x : List A) : Type ℓ where
    nil : x ≡ [] → Uncons x
    cons : ∀ a xs → a ∷ xs ≡ x → Uncons x

  Uncons-elim : ∀ {ℓ'} → {x : List A} → (B : Uncons x → Type ℓ')
                 → (∀ p → B (nil p) )
                 → (∀ a xs p → B (cons a xs p))
                 → ∀ u → B u 
  Uncons-elim B f _ (nil x₂) = f x₂
  Uncons-elim B _ f (cons a xs x₂) = f a xs x₂

  Uncons⊎ : (x : List A) → Iso (Uncons x) ((x ≡ []) ⊎ (Σ[ (a , xs) ∈ (A × List A) ] a ∷ xs ≡ x))
  Iso.fun (Uncons⊎ x) (nil x₁) = inl x₁
  Iso.fun (Uncons⊎ x) (cons a xs x₁) = inr ((a , xs) , x₁)
  Iso.inv (Uncons⊎ x) (inl x₁) = nil x₁
  Iso.inv (Uncons⊎ x) (inr ((a , xs) , x₁)) = cons a xs x₁
  Iso.rightInv (Uncons⊎ x) (inl x₁) = refl
  Iso.rightInv (Uncons⊎ x) (inr x₁) = refl
  Iso.leftInv (Uncons⊎ x) (nil x₁) = refl
  Iso.leftInv (Uncons⊎ x) (cons a xs x₁) = refl

  isGroupoid-Uncons : isGroupoid A → (x : List A) → isGroupoid (Uncons x)
  isGroupoid-Uncons isGrpA x =
     isOfHLevelRetractFromIso 3 (Uncons⊎ x)
        (isOfHLevel⊎ 1 (isOfHLevelSuc 2 (trunc _ _))
        (isOfHLevelΣ 3 (isOfHLevel× 3 isGrpA trunc) λ _ → isSet→isGroupoid (trunc _ _))) 

  u++ : {xs ys : List A} → Uncons xs → Uncons ys → Uncons (xs ++ ys)
  u++ (nil x) (nil x₁) = nil (cong₂ _++_ x x₁ ∙  ++-unit-l [] )
  u++ (nil x) (cons a xs x₁) = cons a xs (sym (++-unit-l (a ∷ xs)) ∙ cong₂ _++_ (sym x) x₁)
  u++ {ys = ys} (cons a xs x) _ = cons a (xs ++ ys) (sym (++-assoc _ _ _) ∙ cong (_++ ys) x)

  Uncons≡ : (x : I → List A) → (x0 : Uncons (x i0)) (x1 : Uncons (x i1)) → Type ℓ
  Uncons≡ x (nil p) (nil p') = Unit*
  Uncons≡ _ (nil x) (cons a xs x₁) = ⊥*
  Uncons≡ _ (cons a xs x) (nil x₁) = ⊥*
  Uncons≡ x (cons a xs p) (cons a' xs' p') =
    Σ ((a ≡ a') × (xs ≡ xs'))
     λ axs → Square p p' (cong₂ _∷_ (fst axs) (snd axs)) (λ i → x i) 

  Uncons≡refl : {x : List A} → {u : Uncons x} → Uncons≡ (λ _ → x) u u
  Uncons≡refl {x} {nil x₁} = tt*
  Uncons≡refl {x} {cons a xs x₁} = (refl , refl) , refl
  
  uncons≡ : ∀ x x0 x1 
         → Uncons≡ x x0 x1
         → PathP (λ i → Uncons (x i)) x0 x1
  uncons≡ x (nil p0) (nil p1) _ i = nil (isProp→PathP (λ i → isProp≡[] (x i)) p0 p1 i)
  uncons≡ x (cons a xs p) (cons a' xs' p') q i =
    cons (fst (fst q) i) (snd (fst q) i) (snd q i)


  UnconsCons : ∀ {x} → (a : A) → (xs : List A) → (a ∷ xs ≡ x) → Uncons x →
                 (Σ[ (a , xs) ∈ (A × List A) ] a ∷ xs ≡ x)
  UnconsCons a xs s (nil x₁) = ⊥rec (snotz (cong length (s ∙ x₁)))
  UnconsCons _ _ _ (cons a xs p) = (a , xs) , p


  UnconsCons-sec : ∀ {x} → (a : A) → (xs : List A) → (p : a ∷ xs ≡ x) →  (u : Uncons x) →
                        cons (fst (fst (UnconsCons a xs p u)))
                             (snd (fst (UnconsCons a xs p u)))
                             (snd (UnconsCons a xs p u)) ≡ u
  UnconsCons-sec a xs s (nil x₁) = ⊥rec (snotz (cong length (s ∙ x₁)))
  UnconsCons-sec a xs p (cons a₁ xs₁ x) = refl

  UnconsNil : ∀ {x} → x ≡ [] →  (xs : Uncons x) →
                 x ≡ []
  UnconsNil _ (nil p) = p
  UnconsNil x₁ (cons _ _ p') = ⊥rec (snotz (cong length (p' ∙ x₁)))

  UnconsNil-sec : ∀ {x} → (p : x ≡ []) → (xs : Uncons x) →  nil (UnconsNil p xs) ≡ xs  
  UnconsNil-sec p (nil x) = refl
  UnconsNil-sec x₁ (cons _ _ p') = ⊥rec (snotz (cong length (p' ∙ x₁)))

  Uncons→a,xs : ∀ {x} → Uncons x → Maybe (A × List A) 
  Uncons→a,xs (nil x) = nothing
  Uncons→a,xs (cons a xs x) = just (a , xs)
  
  ¬Nil≡Cons : {x : I → List A} → ∀ {xi0≡[] a xs a∷xs≡xi1} 
                    → PathP (λ i → Uncons (x i))
                      (nil xi0≡[])
                      (cons a xs a∷xs≡xi1)
                      → ⊥
  ¬Nil≡Cons p = ¬nothing≡just (congP (λ _ → Uncons→a,xs) p)
  
  unconsSqNil : {x : I → I → List A}
                 → ∀ {p00 p10 p01 p11}
                 → {p0j : PathP (λ j → x i0 j ≡ []) p00 p10}
                 → {p1j : PathP (λ j → x i1 j ≡ []) p01 p11}
                 → {pi0 : PathP (λ i → x i i0 ≡ []) p00 p01}
                 → {pi1 : PathP (λ i → x i i1 ≡ []) p10 p11}
                 → SquareP (λ i j → Uncons (x i j))
                     (λ j → nil (p0j j))
                     (λ j → nil (p1j j))
                     (λ i → nil (pi0 i))
                     (λ i → nil (pi1 i))
  unconsSqNil = congSqP (λ _ _ → nil) (isGroupoid→isGroupoid' trunc _ _ _ _ _ _)

  unconsSqCons : ∀ {x₀₀ x₀₁ x₀₋ x₁₀ x₁₁ x₁₋ x₋₀ x₋₁}
                 → {x : Square {A = List A} {x₀₀} {x₀₁} x₀₋ {x₁₀} {x₁₁} x₁₋ x₋₀ x₋₁}
                 {a : A}
                 → ∀ {xs₀₀ xs₀₁ xs₀₋ xs₁₀ xs₁₁ xs₁₋ xs₋₀ xs₋₁}
                 → (xs : Square {A = List A} {xs₀₀} {xs₀₁} xs₀₋ {xs₁₀} {xs₁₁} xs₁₋ xs₋₀ xs₋₁ )
                 → ∀ {p00 p10 p01 p11}
                 → {p0j : PathP (λ j → a ∷ xs i0 j ≡ x i0 j) p00 p10}
                 → {p1j : PathP (λ j → a ∷ xs i1 j ≡ x i1 j) p01 p11}
                 → {pi0 : PathP (λ i → a ∷ xs i i0 ≡ x i i0) p00 p01}
                 → {pi1 : PathP (λ i → a ∷ xs i i1 ≡ x i i1) p10 p11}
                 → SquareP (λ i j → Uncons (x i j))
                     (λ j → cons a (xs i0 j) (p0j j))
                     (λ j → cons a (xs i1 j) (p1j j))
                     (λ i → cons a (xs i i0) (pi0 i))
                     (λ i → cons a (xs i i1) (pi1 i))
  unconsSqCons {a = a} sq =
     congSqP₂ (λ i j → cons a) sq
     (isGroupoid→isGroupoid' trunc _ _ _ _ _ _)

  proper : (x : List A) → singl x
  proper = elimList _ 1 w λ x → isContr→isProp (isContrSingl x)
   where
   w : ElimList.ElimList singl 1
   ElimList.H1.b[] w = ([] , refl)
   ElimList.H1.b[ w ] = (λ a → _ , refl)
   ElimList.H1._b++_ w = w'
    where
      w' : {xs ys : List A} → singl xs → singl ys → singl (xs ++ ys)
      w' {xs} {ys} (xs' , xp) (ys' , yp) with (discreteℕ (length xs) zero) | (discreteℕ (length ys) zero)
      ... | yes p | yes p₁ = [] , cong₂ _++_ (length0≡[] p) (length0≡[] p₁) ∙ ++-unit-l []
      ... | yes p | no ¬p = ys' , cong (_++ ys) (length0≡[] p) ∙ λ i → ++-unit-l (yp i) i
      ... | no ¬p | yes p = xs' , cong (xs ++_) (length0≡[] p) ∙ λ i → ++-unit-r (xp i) i
      ... | no ¬p | no ¬p₁ = xs' ++ ys' , cong₂ _++_ xp yp

  -- filter : (A → Maybe A) → List A → List A
  -- filter f =
  --   Elim.f (λ _ → trunc)
  --    []
  --    (w ∘ f) (_++_)
  --    ++-unit-r ++-unit-l ++-assoc ++-triangle ++-pentagon-diag ++-pentagon-△ ++-pentagon-□

  --   where
  --     w : Maybe A → List A
  --     w nothing = []
  --     w (just x) = [ x ]

  bind : ∀ {ℓ'} → {B : Type ℓ'} → List A → (A → List B) → List B
  bind x f = f' x
   where
   f' : List _ → List _
   f' [] = []
   f' [ x ] = f x
   f' (x ++ x₁) = f' x ++ f' x₁ 
   f' (++-unit-r x i) = ++-unit-r (f' x) i
   f' (++-unit-l x i) = ++-unit-l (f' x) i
   f' (++-assoc x x₁ x₂ i) = ++-assoc (f' x) (f' x₁) (f' x₂) i
   f' (++-triangle x x₁ i i₁) = ++-triangle (f' x) (f' x₁) i i₁
   f' (++-pentagon-diag x x₁ x₂ x₃ i) = ++-pentagon-diag (f' x) (f' x₁) (f' x₂) (f' x₃) i
   f' (++-pentagon-△ x x₁ x₂ x₃ i i₁) = ++-pentagon-△ (f' x) (f' x₁) (f' x₂) (f' x₃) i i₁
   f' (++-pentagon-□ x x₁ x₂ x₃ i i₁) = ++-pentagon-□ (f' x) (f' x₁) (f' x₂) (f' x₃) i i₁
   f' (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) =
     trunc (f' x) (f' x₁)
            (λ i → f' (x₂ i) ) (λ i → f' (y i))
            (λ i j → f' (x₃ i j))
            (λ i j → f' (y₁ i j))
            i i₁ x₄

  -- map-List : ∀ {ℓ'} → {B : Type ℓ'} → (A → B) → List A → List B
  -- map-List f =
  --   Elim.f (λ _ → trunc)
  --    []
  --    ([_] ∘ f) (_++_)
  --    ++-unit-r ++-unit-l ++-assoc ++-triangle ++-pentagon-diag ++-pentagon-△ ++-pentagon-□


  uncons : isGroupoid A → ∀ x → Uncons x
  uncons isGrpA = elimList _ 3 ((w1 , w2) , w3) (isGroupoid-Uncons isGrpA)
   where
   w1 : ElimList.H1 Uncons
   ElimList.H1.b[] w1 = nil refl
   ElimList.H1.b[ w1 ] a = cons a [] (++-unit-r [ a ])
   ElimList.H1._b++_ w1 = u++


   ww1 : {xs : List A} (b : Uncons xs) → _
   ww1 {xs} (nil x) = _
   ww1 (cons a xs x) = (refl , ++-unit-r xs) ,
      λ i j → hcomp
       (λ k →
         λ { (i = i1) → x (j ∧ k)
           ; (j = i0) → [ a ] ++ ++-unit-r xs i
           ; (j = i1) → ++-unit-r (x k) i
           })
       (lawCool-r [ a ] xs i (~ j))

   ww2 : {xs : List A} (b : Uncons xs) → _
   ww2 (nil x) = _
   ww2 (cons a xs x) = (refl , refl) ,
        λ i j →
       hcomp (λ k →
          λ { (i = i1) → x (j ∧ k)
            ; (j = i0) → x i0
            ; (j = i1) → ++-unit-l (x k) i
            }) (++-unit-l (x i0) (i ∨ ~ j))


   ww3 : {xs ys zs : List A} (bx : Uncons xs) (by : Uncons ys) (bz : Uncons zs) → _
   ww3 {xs} {ys} {zs} (nil px) (nil py) (nil pz) = _

   ww3 (nil px) (nil py) (cons a zs' pz) =
      (refl , refl)
      , congP (λ _ → sym (++-unit-l _) ∙_ )(
             (λ i → cong₂-∙' _++_ (sym (++-unit-lr[] i)) (sym (cong₂ _++_ px py)) pz i)
            ◁ (λ i → (λ j → (++-triangle [] (a ∷ zs') (~ j) i))
                    ∙ λ k → ++-assoc (px (~ k)) (py (~ k)) (pz k) i)
         ▷ sym (cong₂-∙'' _++_ _ _ (sym px)))


   ww3 {xs} {ys} {zs} (nil px) (cons a ys' ps) _ =
      (refl , refl) ,
        (((((cong ((sym (++-assoc [ a ] ys' zs)) ∙_)
         (cong-∙ (_++ zs) _ _)) ∙ assoc _ _ _ )) 
           )
          ◁ ((λ i j →
            hcomp
             (λ k → λ { (j = i0) → ++-unit-l (a ∷ ys' ++ zs) (k ∨ (~ i))
                      ; (j = i1) → ++-assoc (px (~ k)) (ps k) zs i
                      })
             (hcomp
                (λ k →
                  λ { (i = i1) → ++-unit-l (++-assoc [ a ] ys' zs (~ j)) (~ k)
                    ; (j = i0) → ++-unit-l (a ∷ ys' ++ zs) (~ i ∨ ~ k)
                    ; (j = i1) → lawCool-l (a ∷ ys') zs (~ k) i
                    })
                (++-assoc [ a ] ys' zs (~ j))))) ▷

           (doubleCompPath-elim _ _ _ ∙∙ sym (assoc _ _ _) ∙∙   
           cong ((λ i → ++-unit-l (a ∷ ys' ++ zs) (~ i)) ∙_)
             ( ((cong ((λ i → cong ([] ++_) (λ i₁ → ++-assoc [ a ] ys' zs (~ i₁)) i) ∙_)
                   (sym (cong₂-∙ (λ x y →  y ++ x)
                     (λ i → ps i ++ zs)
                     λ i → px (~ i)) ))
                   ∙ assoc _ _ _
                      ) ∙ cong (_∙ cong (λ y → y ++ ys ++ zs) (λ i → px (~ i)))
                  (sym (cong-∙ ([] ++_) _ _))
                  ∙ cong₂-∙ (λ x y →  y ++ x) _ _)))            


   ww3 {xs} {ys} {zs} (cons a xs' px) _ _ =
     (refl , ++-assoc xs' _ _) ,
       ((cong ((sym (++-assoc [ a ] (xs' ++ ys) zs)) ∙_)
         (cong-∙ (_++ zs) _ _)) ∙ assoc _ _ _ )
      ◁
        (λ i j →
        hcomp (λ k →
          λ {  (j = i0) → a ∷ ++-assoc xs' ys zs i
             ; (j = i1) → ++-assoc (px k) ys zs i
             }) (hcomp (λ k →
                 λ { (i = i0) →
                     hcomp
                       (λ l → λ { (j = i0) → a ∷ ++-assoc xs' ys zs (~ k)
                                ; (j = i1) →
                                  invSides-filler
                                    (++-pentagon-diag [ a ] xs' ys zs)
                                    (cong (_++ zs) (++-assoc [ a ] xs' ys))
                                    k l
                                ; (k = i0) → ++-pentagon-diag [ a ] xs' ys zs (~ j ∨ l)
                                  })
                       (++-pentagon-□ [ a ] xs' ys zs k (~ j))
                   ; (i = i1) → ++-assoc [ a ] xs' (ys ++ zs) (~ j)
                   ; (j = i0) → [ a ] ++ ++-assoc xs' ys zs (i ∨ ~ k)
                   ; (j = i1) → (++-pentagon-△ [ a ] xs' ys zs (~ i) (~ k))
                   }) (++-assoc [ a ] xs' (ys ++ zs) (~ i ∨ ~ j))))

   ww4 : {xs ys  : List A} (bx : Uncons xs) (by : Uncons ys) → _
   ww4 (nil _) (nil _) = unconsSqNil
   ww4 {xs} {ys} (nil _) (cons _ ys' _) = unconsSqCons λ _ _ → ys'
   ww4 {_} {ys} (cons _ xs' _) _ = unconsSqCons (++-triangle xs' ys)


   ww5 : {xs ys zs ws : List A} (bx : Uncons xs) (by : Uncons ys) (bz : Uncons zs) (bw : Uncons ws) → _
   ww5 (nil x) (nil x₁) (nil x₂) (nil x₃) = tt*
   ww5 {xs} {ys} {zs} {ws} (nil px) (nil py) (nil pz) (cons a ws' wp) = (refl , refl) ,
     λ i j → 
       hcomp
         (λ k → λ {
            (i = i0) → snd (ww3 {ys = zs} {zs = ws} (u++ (nil px) (nil py)) (nil pz) (cons a ws' wp)) (~ k) j 
           ;(i = i1) → snd (ww3 {ys = ys} {zs = zs ++ ws} (nil px) (nil py) (u++ (nil pz) (cons a ws' wp))) k j
           ;(j = i0) → [ a ] ++ ws'
           ;(j = i1) → ++-pentagon-△ xs ys zs ws k i              
          }) (snd (ww3 {ys = zs} {zs = ws} (u++ (nil px) (nil py)) (nil pz) (cons a ws' wp)) i1 j )

   ww5 {xs} {ys} {zs} {ws} (nil px) (nil py) (cons a zs' pz) bw = (refl , refl) ,
     λ i j → 
       hcomp
         (λ k → λ {
            (i = i0) → snd (ww3 {ys = zs} {zs = ws} (u++ (nil px) (nil py)) (cons a zs' pz) bw) (~ k) j 
           ;(i = i1) → snd (ww3 {ys = ys} {zs = zs ++ ws} (nil px) (nil py) (u++ (cons a zs' pz) bw)) k j
           ;(j = i0) → a ∷ zs' ++ ws
           ;(j = i1) → ++-pentagon-△ xs ys zs ws k i              
          }) (snd (ww3 {ys = zs} {zs = ws} (u++ (nil px) (nil py)) (cons a zs' pz) bw) i1 j )

   ww5 {xs} {ys} {zs} {ws} (nil x) (cons a ys' yp) bz bw =
     (refl , ++-assoc ys' zs ws) , 
      λ i j →
        hcomp
         (λ k → λ {
            (i = i0) → snd (ww3 {ys = zs} {zs = ws} (u++ (nil x) (cons a ys' yp)) bz bw) (~ k) j 
           ;(i = i1) → snd (ww3 {ys = ys} {zs = zs ++ ws} (nil x) (cons a ys' yp) (u++ bz bw)) k j
           ;(j = i0) → a ∷ ++-assoc ys' zs ws ((~ k) ∨ i)
           ;(j = i1) → ++-pentagon-△ xs ys zs ws k i              
          }) (snd (ww3 {ys = zs} {zs = ws} (u++ (nil x) (cons a ys' yp)) bz bw) i1 j)


   ww5 {xs} {ys} {zs} {ws} bx@(cons a xs' xp) by bz bw =
     (refl , ++-pentagon-diag xs' ys zs ws ) ,
      λ i j →
        hcomp
         (λ k → λ {
            (i = i0) → snd (ww3 {ys = zs} {zs = ws} (u++ bx by) bz bw) (~ k) j 
           ;(i = i1) → snd (ww3 {ys = ys} {zs = zs ++ ws} (cons a xs' xp) by (u++ bz bw)) k j
           ;(j = i0) → a ∷ ++-pentagon-△ xs' ys zs ws (k) i
           ;(j = i1) → ++-pentagon-△ xs ys zs ws k i              
          }) (snd (ww3 {ys = ys} {zs = zs ++ ws} (cons a xs' xp) by (u++ bz bw)) i0 j)

   ww6 : {xs ys zs ws : List A} (bx : Uncons xs) (by : Uncons ys) (bz : Uncons zs) (bw : Uncons ws) → _
   ww6 (nil _) (nil _) (nil _) (nil _) = unconsSqNil
   ww6 (nil _) (nil _) (nil _) (cons _ ws _) = unconsSqCons λ _ _ → ws
   ww6 {_} {_} {_} {ws} (nil _) (nil _) (cons _ zs _) _ = unconsSqCons λ _ _ → zs ++ ws
   ww6 {_} {_} {zs} {ws} (nil x) (cons a ys x₁) _ _ = unconsSqCons λ i j → ++-assoc ys zs ws (j ∨ (~ i)) 
   ww6 (cons a xs x) _ _ _ = unconsSqCons (++-pentagon-△ _ _ _ _) 

   ww7 : {xs ys zs ws : List A} (bx : Uncons xs) (by : Uncons ys) (bz : Uncons zs) (bw : Uncons ws) → _
   ww7 (nil x) (nil x₁) (nil x₂) (nil x₃) = unconsSqNil
   ww7 (nil _) (nil _) (nil _) (cons _ ws _) = unconsSqCons λ _ _ → ws
   ww7 {_} {_} {_} {ws} (nil _) (nil _) (cons _ zs' _) _ = unconsSqCons λ _ _ → zs' ++ ws
   ww7 {_} {_} {zs} {ws} (nil _) (cons _ ys' _) _ _ =
                               unconsSqCons λ i j → ++-assoc ys' zs ws (j ∧ (~ i))
   ww7 (cons _ _ _) _ _ _ = unconsSqCons (++-pentagon-□ _ _ _ _)


   w2 : ElimList.H2 w1
   ElimList.H2.b++ur w2 = uncons≡ _ _ _ ∘ ww1
   ElimList.H2.b++ul w2 = uncons≡ _ _ _ ∘ ww2
   ElimList.H2.b++-assoc w2 bx by bz = uncons≡ _ _ _ (ww3 bx by bz)
   ElimList.H2.b++-pent-diag w2 bx by bz bw = uncons≡ _ _ _ (ww5 bx by bz bw)

   w3 : ElimList.H3 w2
   ElimList.H3.b++-triangle w3 = ww4
   ElimList.H3.b++-pent-△ w3 = ww6
   ElimList.H3.b++-pent-□ w3 = ww7
   



             

  fromUncons : ∀ {x} → Uncons x → List A
  fromUncons (nil x) = []
  fromUncons (cons a xs x) = a ∷ xs

  unconsIso : (isGrpA : isGroupoid A) → Iso (Σ _ Uncons) (List A)
  Iso.fun (unconsIso isGrpA) = fromUncons ∘ snd
  Iso.inv (unconsIso isGrpA) x = x , uncons isGrpA x
  Iso.rightInv (unconsIso isGrpA) x =
    Uncons-elim (λ u → fromUncons u ≡ x)
      sym (λ _ _ p → p) (uncons isGrpA x) 
  Iso.leftInv (unconsIso isGrpA) (_ , nil x) = ΣPathP ((sym x) , uncons≡ _ _ _ tt*)
  Iso.leftInv (unconsIso isGrpA) (fst₁ , cons a xs x) =
     ΣPathP (x , (uncons≡ _ _ _ ((refl , (++-unit-l xs)) ,
       (leftright _ _ ◁ λ i j →
         hcomp
          (λ k → λ { (i = i1) → x (j ∧ k)
                   ; (j = i0) → ++-triangle [ a ] xs i k
                   ; (j = i1) → x (i ∧ k) })
          (++-unit-r [ a ] (i ∨ j) ++ xs)))))


  uncons-Iso-from : (Maybe (A × List A)) → List A
  uncons-Iso-from nothing = []
  uncons-Iso-from (just (a , xs)) = a ∷ xs



  uncons-Iso : isGroupoid A → Iso (List A) (Maybe (A × List A))
  Iso.fun (uncons-Iso isGrpA) x = Uncons→a,xs (uncons isGrpA x) 
  Iso.inv (uncons-Iso isGrpA) = uncons-Iso-from    
  Iso.rightInv (uncons-Iso isGrpA) nothing = refl
  Iso.rightInv (uncons-Iso isGrpA) (just x) = cong (just ∘ (fst x ,_)) (++-unit-l (snd x))
  Iso.leftInv (uncons-Iso isGrpA) a =
    Uncons-elim (λ u → uncons-Iso-from (Uncons→a,xs u) ≡ a)
                (λ p → sym p) (λ _ _ x → x) (uncons isGrpA a)


  -- length0-≡-IsEmpty : ∀ x → ((length x ≡ 0) , isSetℕ _ _) ≡ (IsEmpty x)
  -- length0-≡-IsEmpty = elimList _ 1
  --      w
  --      (λ _ → isSetHProp _ _)
  --   where
  --   w : ElimList.ElimList
  --         (λ z → ((length z ≡ 0) , isSetℕ (length z) 0) ≡ IsEmpty z) 1
  --   ElimList.H1.b[] w = L.⇔toPath (λ _ → _) λ _ → refl
  --   ElimList.H1.b[ w ] _ = L.⇔toPath snotz ⊥rec
  --   ElimList.H1._b++_ w = {!!}
  --      -- ElimProp.f
  --      --  (λ _ → isSetHProp _ _)
  --      --  (L.⇔toPath (λ _ → _) λ _ → refl)
  --      --  (λ _ → L.⇔toPath snotz ⊥rec)
  --      --  {!!}
       


  length' : Maybe (A × List A) → ℕ
  length' nothing = zero
  length' (just x) = suc (length (snd x))

  uncons-≃-L' : isGroupoid A → ∀ k →
                       (Σ (Maybe (A × List A)) (λ xs → k ≡ length' xs))
                           ≃
                   (Σ (List A) (λ xs → k ≡ length xs))
  uncons-≃-L' isGrpA _ = Σ-cong-equiv-prop
            (isoToEquiv (invIso (uncons-Iso isGrpA)))
            (λ _ → isSetℕ _ _)
            (λ _ → isSetℕ _ _)
            w
            w'
   where
   w : (x : Maybe (A × List A)) →
         _ ≡ length' x →
         _ ≡ length (equivFun (isoToEquiv (invIso (uncons-Iso isGrpA))) x)
   w nothing x₁ = x₁
   w (just x) x₁ = x₁

   w' : (x : Maybe (A × List A)) →
          _ ≡ length (equivFun (isoToEquiv (invIso (uncons-Iso isGrpA))) x) →
          _ ≡ length' x
   w' nothing x₁ = x₁
   w' (just x) x₁ = x₁

  -- uncons-Iso-L' : isGroupoid A → ∀ k →
  --                 Iso (Σ (List A) (λ xs → k ≡ length xs))
  --                     (Σ (Maybe (A × List A)) (λ xs → k ≡ length' xs))
  -- uncons-Iso-L' isGrpA _ = {!!}   
  --       -- Σ-congProp-iso
  --       --   (uncons-Iso isGrpA)
  --       --   (λ _ → isSetℕ _ _)
  --       --   (λ _ → isSetℕ _ _)
  --       --   λ { (nothing ) → (λ x → x) , (λ x → x)
  --       --     ; (just _) → (λ x → x) , (λ x → x) }


  uncons-Iso-L : isGroupoid A → ∀ k →
                  Iso (Σ (List A) (λ xs → (suc k) ≡ length xs))
                      (A × (Σ (List A) (λ xs → k ≡ length xs)))
  uncons-Iso-L isGrpA k =
    compIso (invIso (equivToIso (uncons-≃-L' isGrpA (suc k)))) w

     where
       w : Iso _ _
       Iso.fun w (nothing , p) = ⊥rec (snotz p)
       Iso.fun w (just (a , l) , p) = a , l , injSuc p
       Iso.inv w (a , l , p) = just (a , l) , cong suc p
       Iso.rightInv w _ = ΣPathP (refl , Σ≡Prop (λ _ → isSetℕ _ _) refl)
       Iso.leftInv w (nothing , p) = ⊥rec (snotz p)
       Iso.leftInv w (just _ , _) = Σ≡Prop (λ _ → isSetℕ _ _) refl

  -- -- -- head : isGroupoid A → ∀ l → 0 ≤ length l → A
  -- -- -- head = {!!}

  List-IsoL : isGroupoid A → ∀ k →
                    Iso (Σ (List A) (λ xs → k ≡ length xs))
                        (Σ (B.List A) (λ xs → k ≡ B.length xs))
  Iso.fun (List-IsoL isGrpA zero) _ = B.[] , refl
  Iso.inv (List-IsoL isGrpA zero) _ = [] , refl
  Iso.rightInv (List-IsoL isGrpA zero) (B.[] , p) =
     Σ≡Prop (λ _ → isSetℕ _ _) refl
  Iso.rightInv (List-IsoL isGrpA zero) (x B.∷ l , p) = ⊥rec (znots p)
  Iso.leftInv (List-IsoL isGrpA zero) (_ , p) = Σ≡Prop (λ _ → isSetℕ _ _)
      (sym (length0≡[] (sym p)))
  
  List-IsoL isGrpA (suc k) =
    compIso (uncons-Iso-L isGrpA k) w 
    where
      w' : _
      w' = List-IsoL isGrpA k 

      w : Iso (A × Σ (List A) (λ xs → k ≡ length xs))
            (Σ (B.List A) (λ xs → suc k ≡ B.length xs))
      Iso.fun w (a , x) = a B.∷  fst (Iso.fun w' x)  , cong suc ((snd (Iso.fun w' x)))
      Iso.inv w (B.[] , p) = ⊥rec (snotz p)
      Iso.inv w (a B.∷ l , p) = a , (Iso.inv w' (l , injSuc p))
      Iso.rightInv w (B.[] , p) = ⊥rec (snotz p)
      Iso.rightInv w (a B.∷ l , p) =
            Σ≡Prop (λ _ → isSetℕ _ _)
             (cong (a B.∷_) (cong fst (Iso.rightInv w' (l , injSuc p))))

      Iso.leftInv w _ = ΣPathP (refl ,  Iso.leftInv w' _)
