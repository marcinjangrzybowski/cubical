{-# OPTIONS --safe --experimental-lossy-unification  #-}  
module Cubical.HITs.ListedFiniteSet.Base3CTab where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Foundations.Path

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)
open import Cubical.Data.Nat as Nat
open import Cubical.Data.Sigma
open import Cubical.Data.List

open import Cubical.Data.Unit
open import Cubical.Data.Bool as 𝟚

open import Cubical.Functions.Logic as L
open import Cubical.Foundations.Function

open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import Cubical.HITs.EilenbergMacLane1

open import Cubical.Data.FinData.Properties

open import Cubical.Data.Nat.Order.Recursive as R

open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary

import Cubical.Data.Nat.FinGenAut2 as A



open import Cubical.HITs.GroupoidTruncation as GT using (∥_∥₃ ; ∣_∣₃ ; squash₃) 

open import Cubical.HITs.GroupoidQuotients as GQ
  renaming ([_] to [_]// ; RelimProp to  RelimProp// ; Rrec to Rrec//)


open import Cubical.HITs.ListedFiniteSet.Base3C
open import Cubical.HITs.ListedFiniteSet.Base3CPermu

open import Cubical.HITs.Permutation.Group
open import Cubical.HITs.Permutation.Base hiding (ℙrm)

open import Cubical.Data.Nat.Order.Permutation

open import Cubical.Algebra.Group.Morphisms

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B : Type ℓ

module _ {A : Type ℓ} where
 module OnlyOne (P : A → Type ℓ') (isPropP : ∀ a → isProp (P a)) (P? : ∀ a → Dec (P a)) where

  Pₚ : A → hProp ℓ'
  Pₚ a = (P a , isPropP a)

  ¬Pₚ : A → hProp ℓ'
  ¬Pₚ = L.¬_ ∘ Pₚ

  noneOfₚ : FMSet2 A → hProp ℓ'
  noneOfₚ = RRec.ff w λ _ → isSet→isGroupoid isSetHProp
   where
    w : RRec (hProp ℓ')
    RRec.[]* w = ⊤
    (w RRec.∷* x) x₁ = ¬Pₚ x L.⊓ x₁
    RRec.comm* w _ _ _ = L.⇔toPath
         (λ (x , y , z) → y , x , z)
         (λ (x , y , z) → y , x , z)

    RRec.comm-inv* w _ _ _ =
      isSet→isSet' isSetHProp _ _ _ _
    RRec.commm* w x y z b =
     L.⇔toPath
         (λ (x , y , z , w) → y , z , x , w)
         (λ (x , y , z , w) → z , x , y , w)

    RRec.commp* w _ _ _ _ =
     isSet→isSet' isSetHProp _ _ _ _

    RRec.hex* w _ _ _ _ =
     isSet→isSet' isSetHProp _ _ _ _ 

  [_,_]_⊔ₓ*_ : ∀ a → (Dec (P a)) → (B C : hProp ℓ') → hProp ℓ'
  [ a , yes p ] B ⊔ₓ* C =  B
  [ a , no ¬p ] B ⊔ₓ* C = C


  -- [_]_⊔ₓ'_ : (a : A) (B C : hProp ℓ') → Type ℓ'
  -- [ a ] B ⊔ₓ' C = {!!}

  onlyOneₚ : FMSet2 A → hProp ℓ' 

  [_]_⊔ₓ_ : (a : A) (B C : hProp ℓ') → hProp ℓ'
  [ a ] B ⊔ₓ C = [ a , P? a ] B ⊔ₓ* C 


  -- ⊔ₓ-comm* : ∀ {x y b b' } → ∀ x' y' → ⟨ [ x , x' ] ((¬Pₚ y L.⊓ b)) ⊔ₓ*
  --          ([ y , y' ] (b) ⊔ₓ* b') ⟩ 
  --        → ⟨ [ y , y' ] ((¬Pₚ x L.⊓ b)) ⊔ₓ*
  --          ([ x , x' ] (b) ⊔ₓ* b') ⟩
  -- ⊔ₓ-comm* (yes p) (yes p₁) x = ⊥.rec (fst x p₁)
  -- ⊔ₓ-comm* (yes p) (no ¬p) x = snd x
  -- ⊔ₓ-comm* (no ¬p) (yes p) x = ¬p , x
  -- ⊔ₓ-comm* (no ¬p) (no ¬p₁) x = x

  ⊔ₓ-comm*Pa : ∀ {x y b b' } → ∀ x' y' →
        [ x , x' ] ((¬Pₚ y L.⊓ b)) ⊔ₓ*
           ([ y , y' ] (b) ⊔ₓ* b')  
         ≡  [ y , y' ] ((¬Pₚ x L.⊓ b)) ⊔ₓ*
           ([ x , x' ] (b) ⊔ₓ* b')
  ⊔ₓ-comm*Pa {b = b} (yes p) (yes p₁) =
    cong (_⊓ b) (L.⇔toPath (λ q → ⊥.rec (q p₁)) λ q → ⊥.rec (q p))
  ⊔ₓ-comm*Pa (yes p) (no ¬p) = L.⇔toPath snd (¬p ,_)
  ⊔ₓ-comm*Pa (no ¬p) (yes p) = L.⇔toPath (¬p ,_) snd
  ⊔ₓ-comm*Pa (no ¬p) (no ¬p₁) = refl
  -- ⊔ₓ-comm*Pa x' y' = L.⇔toPath ( ⊔ₓ-comm* x' y') ( ⊔ₓ-comm* y' x')

  -- ⊔ₓ-comm : ∀ {x y b b'} → ⟨ [ x ] ((¬Pₚ y L.⊓ b)) ⊔ₓ
  --          ([ y ] (b) ⊔ₓ b') ⟩ 
  --        → ⟨ [ y ] ((¬Pₚ x L.⊓ b)) ⊔ₓ
  --          ([ x ] (b) ⊔ₓ b') ⟩
  -- ⊔ₓ-comm = ⊔ₓ-comm* (P? _) (P? _)  

  ⊔ₓ-elim* : ∀ a b X Y → (⟨ Y ⟩ → Σ A P ) → ⟨ [ a , b ] X ⊔ₓ* Y ⟩ →  Σ A P
  ⊔ₓ-elim* a (yes p) X Y x x₁ = a , p
  ⊔ₓ-elim* a (no ¬p) X Y x x₁ = x x₁

  ⊔ₓ-elim : ∀ a X Y → (⟨ Y ⟩ → Σ A P ) → ⟨ [ a ] X ⊔ₓ Y ⟩ →  Σ A P
  ⊔ₓ-elim a = ⊔ₓ-elim* a (P? a) 


  onlyOneₚ = RElimSet.f w --λ _ → isSet→isGroupoid isSetHProp
   where
   w : RElimSet (λ _ → hProp ℓ')
   RElimSet.[]* w = ⊥* , isProp⊥*
   (w RElimSet.∷* x) {xs} x₁ = [ x ] noneOfₚ xs ⊔ₓ x₁
   RElimSet.comm* w x y {xs} b = ⊔ₓ-comm*Pa {x} {y} (P? x) (P? y)
     -- L.⇔toPath 
     -- (⊔ₓ-comm {x} {y} {noneOfₚ xs} {b})
     -- (⊔ₓ-comm {y} {x} {noneOfₚ xs} {b})

   RElimSet.trunc* w _ = isSetHProp



  fromOnlyOneₚ-comm : ∀ {x} {y} {xs} {B : hProp ℓ'} {b : ⟨ B ⟩ → Σ A P} (x' : Dec (P x)) → (y' : Dec (P y)) →
      PathP (λ i → ⟨ ⊔ₓ-comm*Pa {b = noneOfₚ xs} {b' = B} x' y' i ⟩ → Σ A P)
       (⊔ₓ-elim* x x' (noneOfₚ (y ∷2 xs)) ([ y , y' ] noneOfₚ xs ⊔ₓ* B) 
        (⊔ₓ-elim* y y' (noneOfₚ xs) (B) b))
       (⊔ₓ-elim* y y' (noneOfₚ (x ∷2 xs)) (([ x , x' ] noneOfₚ xs ⊔ₓ* B)) 
        (⊔ₓ-elim* x x' (noneOfₚ xs) (B) b))
  fromOnlyOneₚ-comm (yes p) (yes p₁) = funExtDep λ {x₁} → ⊥.rec (fst x₁ p₁)
  fromOnlyOneₚ-comm {x = x} (yes p) (no ¬p) = λ _ _ → x , p
  fromOnlyOneₚ-comm {y = y} (no ¬p) (yes p) = λ _ _ → y , p
  fromOnlyOneₚ-comm {xs = xs} {B = B} {b = b} (no ¬p) (no ¬p₁) = λ _ → b

  fromOnlyOneₚ-comm-inv : ∀ {x} {y} {xs}
     {b : ⟨ onlyOneₚ xs ⟩ → Σ A P}
     (x' : Dec (P x)) → (y' : Dec (P y)) →
      SquareP
       (λ i j →
           ⟨ isOfHLevel→isOfHLevelDep 2 (λ _ → isSetHProp)
               ([ x , x' ] noneOfₚ (y ∷2 xs) ⊔ₓ*
                 ([ y , y' ] noneOfₚ (xs) ⊔ₓ* onlyOneₚ xs))
                ([ y , y' ] noneOfₚ (x ∷2 xs) ⊔ₓ*
                 ([ x , x' ] noneOfₚ (xs) ⊔ₓ* onlyOneₚ xs))
                  (⊔ₓ-comm*Pa {b = noneOfₚ xs} {b' = onlyOneₚ xs} x' y')
                  (sym (⊔ₓ-comm*Pa {b = noneOfₚ xs} {b' = onlyOneₚ xs} y' x'))
               (comm-inv x y xs) i j ⟩ 
          -- {!⟨ onlyOneₚ (comm-inv x y xs i j) ⟩!}
          → Σ A P)
       (fromOnlyOneₚ-comm {x} {y} {xs} {b = b} x' y')
       (symP (fromOnlyOneₚ-comm {y} {x} {xs} {b = b}  y' x'))
       (λ _ → (⊔ₓ-elim* x x' (noneOfₚ (y ∷2 xs))
        ([ y , y' ] noneOfₚ xs ⊔ₓ* onlyOneₚ xs)
        (⊔ₓ-elim* y y' (noneOfₚ xs) (onlyOneₚ xs) b)))
       (λ _ → (⊔ₓ-elim* y y' (noneOfₚ (x ∷2 xs))
        ([ x , x' ] noneOfₚ xs ⊔ₓ* onlyOneₚ xs)
        (⊔ₓ-elim* x x' (noneOfₚ xs) (onlyOneₚ xs) b)))
  fromOnlyOneₚ-comm-inv (yes p) (yes p₁) = 
    toPathP (invEq (congEquiv (PathP≃Path _ _ _))
       (funExtSq _ _ _ _ λ x → ⊥.rec (fst x p)))

  fromOnlyOneₚ-comm-inv {x = x} (yes p) (no ¬p) _ _ _ = x , p
  fromOnlyOneₚ-comm-inv {y = y} (no ¬p) (yes p) _ _ _ = y , p
  fromOnlyOneₚ-comm-inv {xs = xs} {b = b} (no ¬p) (no ¬p₁) = 
    congSqP (λ i j → b ∘_)
      (isProp→SquareP (λ _ _ → isPropΠ λ _ → snd (onlyOneₚ xs) ) _ _ _ _) 

  onlyOne-commm : ∀ {x} {y} {z} {xs}
      {b : ⟨ onlyOneₚ xs ⟩ → Σ A P} (x' : Dec (P x)) → (y' : Dec (P y))
       → (z' : Dec (P z)) →
        -- onlyOneₚ (x ∷2 y ∷2 z ∷2 xs)
        [ x , x' ] noneOfₚ (y ∷2 z ∷2 xs) ⊔ₓ* ([ y , y' ] noneOfₚ (z ∷2 xs) ⊔ₓ*
           (([ z , z' ] noneOfₚ xs ⊔ₓ* onlyOneₚ xs)))
        ≡
        [ y , y' ] noneOfₚ (z ∷2 x ∷2 xs) ⊔ₓ* ([ z , z' ] noneOfₚ (x ∷2 xs) ⊔ₓ*
           ([ x , x' ] noneOfₚ xs ⊔ₓ* onlyOneₚ xs))
        -- onlyOneₚ (y ∷2 z ∷2 x ∷2 xs)
  onlyOne-commm {x} {y} {z} {xs} x' y' z' i =
   let onz = [ z , z' ] noneOfₚ xs ⊔ₓ* onlyOneₚ xs
       onx = [ x , x' ] noneOfₚ xs ⊔ₓ* onlyOneₚ xs
   in (comp (λ l → hProp ℓ')
                     (λ l → λ { (i = i0) →
                          ⊔ₓ-comm*Pa {x} {y} {noneOfₚ (z ∷2 xs)}
                            {onz} x' y' (~ l)
                              ; (i = i1) →
                            [ y , y' ]
                              noneOfₚ (comm z x xs (~ l))
                               ⊔ₓ* (⊔ₓ-comm*Pa {z} {x} {noneOfₚ xs} {onlyOneₚ xs}
                                      z' x' (~ l))
                       -- _ ∷* comm* _ _ b (~ l)
                              })
                     ([ y , y' ]
                              noneOfₚ (comm z x xs i1)
                               ⊔ₓ* (⊔ₓ-comm*Pa {z} {x} {noneOfₚ xs} {onlyOneₚ xs}
                                      z' x' i1)) )

  fromOnlyOneₚ-commm : ∀ {x} {y} {z} {xs}
      {b : ⟨ onlyOneₚ xs ⟩ → Σ A P} (x' : Dec (P x)) → (y' : Dec (P y))
       → (z' : Dec (P z)) →
      let onz = [ z , z' ] noneOfₚ xs ⊔ₓ* onlyOneₚ xs
          onx = [ x , x' ] noneOfₚ xs ⊔ₓ* onlyOneₚ xs
      in
         PathP (λ i → ⟨  onlyOne-commm {x} {y} {z} {xs} {b} x' y' z' i ⟩ → Σ A P)
          (⊔ₓ-elim* x x' (noneOfₚ (y ∷2 z ∷2 xs)) ([ y , y' ]
              noneOfₚ (z ∷2 xs) ⊔ₓ* onz)
           ((⊔ₓ-elim* y y' (noneOfₚ (z ∷2 xs)) onz
             ((⊔ₓ-elim* z z' (noneOfₚ xs) (onlyOneₚ xs) b)))))
          ((⊔ₓ-elim* y y' (noneOfₚ (z ∷2 x ∷2 xs)) ([ z , z' ]
              noneOfₚ (x ∷2 xs) ⊔ₓ* onx)
           ((⊔ₓ-elim* z z' (noneOfₚ (x ∷2 xs)) onx
             ((⊔ₓ-elim* x x' (noneOfₚ xs) (onlyOneₚ xs) b))))))
  fromOnlyOneₚ-commm (yes p) (yes p₁) z' = funExtDep λ {x₁} → ⊥.rec (fst x₁ p₁)
  fromOnlyOneₚ-commm (yes p) (no ¬p) (yes p₁) =
    funExtDep λ {x₁} → ⊥.rec (fst (snd x₁) p₁)
  fromOnlyOneₚ-commm (yes p) (no ¬p) (no ¬p₁) _ _ = _ , p
  fromOnlyOneₚ-commm (no ¬p) (yes p) (yes p₁) =
    funExtDep λ {x₁} → ⊥.rec (fst x₁ p₁)
  fromOnlyOneₚ-commm (no ¬p) (yes p) (no ¬p₁) _ _ = _ , p
  fromOnlyOneₚ-commm (no ¬p) (no ¬p₁) (yes p) _ _ = _ , p
  fromOnlyOneₚ-commm {xs = xs} {b = b} (no ¬p) (no ¬p₁) (no ¬p₂) =
   congP (λ _ → b ∘_)
     (isProp→PathP
       (λ i → isPropΠ λ _ → snd (onlyOneₚ xs))
          _ _)

  fromOnlyOneₚ-commp : ∀ {x} {y} {z} {xs}
      {b : ⟨ onlyOneₚ xs ⟩ → Σ A P} (x' : Dec (P x)) → (y' : Dec (P y))
       → (z' : Dec (P z)) →

       SquareP
         (λ i j → ⟨ isSet→SquareP (λ _ _ → isSetHProp)
             (λ i →
               ⊔ₓ-comm*Pa {z} {x} {noneOfₚ (y ∷2 xs)}
                 {[ y , y' ] noneOfₚ xs ⊔ₓ* onlyOneₚ xs} z' x' i)
             (λ i →
               [ x , x' ] noneOfₚ (comm y z xs i) ⊔ₓ*
                 (⊔ₓ-comm*Pa {y} {z} {noneOfₚ xs} {onlyOneₚ xs} y' z' i)
               )
             (onlyOne-commm {z} {x} {y} {xs} {b} z' x' y')
             (λ i →  ([ x , x' ] noneOfₚ (z ∷2 y ∷2 xs) ⊔ₓ*
                   ([ z , z' ] ¬Pₚ y ⊓ noneOfₚ xs ⊔ₓ*
                    ([ y , y' ] noneOfₚ xs ⊔ₓ* onlyOneₚ xs)))) i j ⟩ → Σ A P)
         (fromOnlyOneₚ-comm {z} {x} {y ∷2 xs}
            {[ y , y' ] noneOfₚ xs ⊔ₓ* onlyOneₚ xs}
              {⊔ₓ-elim* y y' (noneOfₚ xs) (onlyOneₚ xs) b} z' x')

         (congP (λ z₁ →
                ⊔ₓ-elim* x x' (noneOfₚ (comm y z xs z₁))
                  (⊔ₓ-comm*Pa {y} {z} {_} {onlyOneₚ xs} y' z' z₁))

            (fromOnlyOneₚ-comm {y} {z} {xs} {_} {b} y' z')
           )
         (fromOnlyOneₚ-commm {z} {x} {y} {xs} {b} z' x' y')
         λ _ → (⊔ₓ-elim* x x' (noneOfₚ (z ∷2 y ∷2 xs))
        ([ z , z' ] noneOfₚ (y ∷2 xs) ⊔ₓ*
         ([ y , y' ] noneOfₚ xs ⊔ₓ* onlyOneₚ xs))
        (⊔ₓ-elim* z z' (noneOfₚ (y ∷2 xs))
         ([ y , y' ] noneOfₚ xs ⊔ₓ* onlyOneₚ xs)
         (⊔ₓ-elim* y y' (noneOfₚ xs) (onlyOneₚ xs) b)))
         -- (λ i → {!!})
  fromOnlyOneₚ-commp (yes p) (yes p₁) qq =
       toPathP (invEq (congEquiv (PathP≃Path _ _ _))
       (funExtSq _ _ _ _ λ x → ⊥.rec (fst (snd x) p₁)))
  fromOnlyOneₚ-commp (yes p) (no ¬p) (yes p₁) =
     toPathP (invEq (congEquiv (PathP≃Path _ _ _))
       (funExtSq _ _ _ _ λ x → ⊥.rec (fst x p₁)))
  fromOnlyOneₚ-commp (yes p) (no ¬p) (no ¬p₁) _ _ _ = _ , p 
  fromOnlyOneₚ-commp (no ¬p) (yes p) (yes p₁) =
    toPathP (invEq (congEquiv (PathP≃Path _ _ _))
       (funExtSq _ _ _ _ λ x → ⊥.rec (fst x p)))
  fromOnlyOneₚ-commp (no ¬p) (yes p) (no ¬p₁) _ _ _ = _ , p
  fromOnlyOneₚ-commp (no ¬p) (no ¬p₁) (yes p) _ _ _ = _ , p
  fromOnlyOneₚ-commp {xs = xs} {b = b} (no ¬p) (no ¬p₁) (no ¬p₂) =
   congSqP (λ i j → b ∘_)
      (isProp→SquareP (λ _ _ → isPropΠ λ _ → snd (onlyOneₚ xs) ) _ _ _ _) 


  fromOnlyOneₚ-hex : ∀ {x} {y} {z} {xs}
      {b : ⟨ onlyOneₚ xs ⟩ → Σ A P} (x' : Dec (P x)) → (y' : Dec (P y))
       → (z' : Dec (P z)) →

       SquareP (λ i j → ⟨ isSet→SquareP (λ _ _ → isSetHProp)
             ((λ i →
               [ z , z' ] noneOfₚ (comm x y xs i) ⊔ₓ*
                 (⊔ₓ-comm*Pa {x} {y} {noneOfₚ xs} {onlyOneₚ xs} x' y' i)
               ))
             ((λ i →
               ⊔ₓ-comm*Pa {x} {y} {noneOfₚ (z ∷2 xs)}
                 {[ z , z' ] noneOfₚ xs ⊔ₓ* onlyOneₚ xs} x' y' i))
             (onlyOne-commm {z} {x} {y} {xs} {b} z' x' y')
             (onlyOne-commm {z} {y} {x} {xs} {b} z' y' x')
             i j ⟩ → Σ A P)
         (congP (λ z₁ →
                ⊔ₓ-elim* z z' (noneOfₚ (comm x y xs z₁))
                  (⊔ₓ-comm*Pa {x} {y} {_} {onlyOneₚ xs} x' y' z₁))

            (fromOnlyOneₚ-comm {x} {y} {xs} {_} {b} x' y')
           )
         (fromOnlyOneₚ-comm {x} {y} {z ∷2 xs}
            {[ z , z' ] noneOfₚ xs ⊔ₓ* onlyOneₚ xs}
              {⊔ₓ-elim* z z' (noneOfₚ xs) (onlyOneₚ xs) b} x' y')
         (fromOnlyOneₚ-commm {z} {x} {y} {xs} {b} z' x' y')
         (fromOnlyOneₚ-commm {z} {y} {x} {xs} {b} z' y' x')
  fromOnlyOneₚ-hex (yes p) (yes p₁) qq =
       toPathP (invEq (congEquiv (PathP≃Path _ _ _))
       (funExtSq _ _ _ _ λ x → ⊥.rec (fst x p)))
  fromOnlyOneₚ-hex (yes p) (no ¬p) (yes p₁) =
     toPathP (invEq (congEquiv (PathP≃Path _ _ _))
       (funExtSq _ _ _ _ λ x → ⊥.rec (fst x p₁)))
  fromOnlyOneₚ-hex (yes p) (no ¬p) (no ¬p₁) _ _ _ = _ , p 
  fromOnlyOneₚ-hex (no ¬p) (yes p) (yes p₁) =
    toPathP (invEq (congEquiv (PathP≃Path _ _ _))
       (funExtSq _ _ _ _ λ x → ⊥.rec (fst (snd x) p₁)))
  fromOnlyOneₚ-hex (no ¬p) (yes p) (no ¬p₁) _ _ _ = _ , p
  fromOnlyOneₚ-hex (no ¬p) (no ¬p₁) (yes p) _ _ _ = _ , p
  fromOnlyOneₚ-hex {xs = xs} {b = b} (no ¬p) (no ¬p₁) (no ¬p₂) =
   congSqP (λ i j → b ∘_)
      (isProp→SquareP (λ _ _ → isPropΠ λ _ → snd (onlyOneₚ xs) ) _ _ _ _) 


  fromOnlyOneₚ : isGroupoid A →  (𝕝 : FMSet2 A) → ⟨ onlyOneₚ 𝕝 ⟩ → Σ A P
  fromOnlyOneₚ isGrpA = RElim.ff w λ _ _ →
   isGroupoidΠ λ _ → isGroupoidΣ isGrpA
      λ _ → isSet→isGroupoid (isProp→isSet (isPropP _)) 
   where
   w : RElim (λ z → ⟨ onlyOneₚ z ⟩ → Σ A P)
   RElim.[]* w ()
   (w RElim.∷* x) {xs} x₁ =
     ⊔ₓ-elim _ (noneOfₚ xs) (onlyOneₚ xs) x₁ 

   RElim.comm* w x y {xs} b =
     fromOnlyOneₚ-comm {x} {y} {xs} {_} {b} (P? x) (P? y)

   RElim.comm-inv* w x y {xs} b =
     fromOnlyOneₚ-comm-inv {x} {y} {xs} {b} (P? x) (P? y)

   RElim.commm* w x y z {xs} b =
     fromOnlyOneₚ-commm {x} {y} {z} {xs} {b} (P? x) (P? y) (P? z)
   RElim.commp* w x y z {xs} b =
     fromOnlyOneₚ-commp {x} {y} {z} {xs} {b} (P? x) (P? y) (P? z)
   RElim.hex* w x y z {xs} b =
     fromOnlyOneₚ-hex {x} {y} {z} {xs} {b} (P? x) (P? y) (P? z)

module _ {A : Type ℓ} where
 open OnlyOne {A = A × Bool} (Bool→Type ∘ snd ) (λ _ → isPropBool→Type) (λ _ → DecBool→Type) public

𝕃addIndex-snd-false : (𝕝 : FMSet2 A) → (bs : Σ (𝕃Bool (<$tt 𝕝))
   (fst ∘ (𝕃allFalse (<$tt 𝕝))  )) →
   ⟨ noneOfₚ (𝕃addIndex-fst 𝕝 (fst bs)) ⟩
𝕃addIndex-snd-false = RElimProp.f w
 where
 w : RElimProp _
 RElimProp.[]* w _ = tt*
 (w RElimProp.∷* x) x₁ ((false , bs) , cs) = (λ ()) , x₁ (bs , cs) 
 RElimProp.trunc* w 𝕝 =
   isPropΠ λ bs →
     snd ( noneOfₚ (𝕃addIndex-fst 𝕝 (fst bs)) )

𝕃addIndex-snd : (𝕝 : FMSet2 A) → (bs : 𝕃Fin (<$tt 𝕝)) →
   ⟨ onlyOneₚ (𝕃addIndex-fst 𝕝 (fst bs)) ⟩
𝕃addIndex-snd = RElimProp.f w
 where
 w : RElimProp _
 RElimProp.[]* w ()
 (w RElimProp.∷* x) {xs} f ((false , bs) , snd₁) =
    f (bs , snd₁)
 (w RElimProp.∷* x) {xs} f ((true , bs) , snd₁) =
    𝕃addIndex-snd-false xs (bs , snd₁) 

 RElimProp.trunc* w 𝕝 = isPropΠ λ bs →
     snd ( onlyOneₚ (𝕃addIndex-fst 𝕝 (fst bs)) )

 
𝕃addIndex : (𝕝 : FMSet2 A) → 𝕃Fin (<$tt 𝕝) →
  Σ (FMSet2 (A × Bool)) λ xs → ⟨ onlyOneₚ xs ⟩  
𝕃addIndex 𝕝 x = 𝕃addIndex-fst 𝕝 (fst x) , 𝕃addIndex-snd 𝕝 x


∙∙-lem-set : {A : Type ℓ} → {B : Type ℓ'} →
             -- (C : Type ℓ'') →
              {a₀₀ a₀₁ : A} {a'₀₀ a'₀₁ : A}
                {a₀₀' : a₀₀ ≡ a'₀₀} {a₀₋ : a'₀₀ ≡ a'₀₁} {a₀₁' : a'₀₁ ≡ a₀₁}
              {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
              {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
              → (isSet A)
             → (f : A → B)
             → Square {A = B}
                 (((λ i → f (a₀₀' i))) ∙∙ (λ i → f (a₀₋ i)) ∙∙ λ i → f (a₀₁' i))
                 (λ i → f (a₁₋ i))
                 (λ i → f (a₋₀ i))
                 λ i → f (a₋₁ i)
∙∙-lem-set {a₀₀' = a₀₀'} {a₀₋} {a₀₁'} {a₁₋ = a₁₋} {a₋₀ = a₋₀} {a₋₁ = a₋₁} isSetA f i j =
  hcomp
   (λ k → λ {
        (i = i1) → f (a₁₋ j)
       ;(j = i0) → f (doubleCompPath-filler (sym a₀₀') a₋₀ refl (~ k) i)
       ;(j = i1) → f (doubleCompPath-filler (a₀₁') a₋₁ refl (~ k) i)
       })
     (f (isSet→isSet' isSetA a₀₋ a₁₋
            (sym a₀₀' ∙∙ a₋₀ ∙∙ refl)
            (a₀₁' ∙∙ a₋₁ ∙∙ refl) i j))

_∙∙P_∙∙P_ : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
             (p : w ≡ x)
             (q : x ≡ y)
             (r : y ≡ z)
             → w ≡ z

_∙∙P_∙∙P_ {A = A} p q r i =
  comp (λ _ → A) (doubleComp-faces p r i) (q i)

fixComp : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
             (p : w ≡ x)
             (q : x ≡ y)
             (r : y ≡ z)
             → (p ∙∙ q ∙∙ r) ≡ p ∙∙P q ∙∙P r 
fixComp {A = A} p q r j i =
       hcomp
       (doubleComp-faces (λ i₁ → transp (λ _ → A) (~ j ∨ ~ i₁) (p i₁))
        (λ i₁ → transp (λ _ → A) (~ j ∨ i₁) (r i₁)) i)
       (transp (λ _ → A) (~ j) (q i))

fixComp' : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
             (p : w ≡ x)
             (q : x ≡ y)
             (r : y ≡ z)
             → ((λ i → transp (λ _ → A) (~ i) (p i))
                ∙∙ cong (transport refl) q ∙∙
                (λ i → transp (λ _ → A) i (r i))) ≡ (p ∙∙ q ∙∙ r) 
fixComp' p q r = sym (fixComp p _ _)



module _ {A : I → Type ℓ} {x : A i0} {y : A i1} where
 symPIso : Iso (PathP A x y) (PathP (λ i → A (~ i)) y x)
 Iso.fun symPIso = symP
 Iso.inv symPIso = symP
 Iso.rightInv symPIso _ = refl
 Iso.leftInv symPIso _ = refl


-- Fin≃𝔽in : PathP (λ i → ua (isoToEquiv (Iso-FM2⊤-Σℙrm)) i → Type)
--             𝕃Fin
--             (uncurry 𝔽in)
-- Fin≃𝔽in = ua→ (isoToPath ∘ RElimSet.f w)
--  where
--   w : RElimSet
--         (λ z →
--           Iso (𝕃Fin z)
--            (uncurry 𝔽in (isoToEquiv Iso-FM2⊤-Σℙrm .fst z)))
--   RElimSet.[]* w = idIso
--   RElimSet._∷*_ w x {xs} = {!!}
--   RElimSet.comm* w = {!!}
--   RElimSet.trunc* w xs = isSet-SetsIso {!!} {!!} 


hhhPF'-lem : ∀ n k → suc (suc k) R.≤ n → ∀ x → fst (Fin×Snd n x) →
       ℕ→Fin× n
      (A.adjTransposition k
       (Fin×→ℕ n x))
      ≡ adjT×^ k x
hhhPF'-lem (suc n) (suc k) k< (false , xs) x₁ =
 cong′ (false ,_) (hhhPF'-lem n k k< xs x₁)
hhhPF'-lem (suc n) (suc k) k< (true , xs) x₁ =
  cong′ (true ,_)
     (allFalse→≡repeat-false n (adjT×^ k xs) (allFalse∘adjT× n k xs x₁))
hhhPF'-lem (suc (suc n)) zero k< (false , false , xs) x₁ =
  cong′ (λ xs → (false , false , xs)) (sec-ℕ→Fin×-ℕ→Fin× n xs x₁)
hhhPF'-lem (suc (suc n)) zero k< (false , true , xs) x₁ =
  cong′ (λ xs → (true , false , xs)) (allFalse→≡repeat-false n xs x₁)
hhhPF'-lem (suc (suc n)) zero k< (true , false , xs) x₁ =
  cong′ (λ xs → (false , true , xs)) (allFalse→≡repeat-false n xs x₁)

hhhPF' : ∀ n p' →
         (Iso.fun (IsoFinFin× n) ∘ 
         (permuteF' n
          p'
          ∘ (Iso.inv (IsoFinFin× n))))
      ≡ subst (𝔽in n) (sym
           ((equivFun ((isoToEquiv (fst (GIso-𝕡Ω₂-PermG n))))
           p')))
hhhPF' n = RelimProp.f w
 where
 w : RelimProp
       _
 RelimProp.isPropA w x =
   isSet→ (isSetFin× _) _ _
 RelimProp.εA w =
   funExt (λ x → Σ≡Prop (λ _ → snd (Fin×Snd n _)) (sec-ℕ→Fin×-ℕ→Fin× n (fst x) (snd x)))
   ∙∙ (λ _ → idfun _) ∙∙
   funExt λ x → sym (transportRefl x)
 RelimProp.∷A w k {xs} X =   
     cong (λ f → (Iso.fun (IsoFinFin× n) ∘ permuteF' n (k ∷ ε))
          ∘ f ∘
          permuteF' n xs ∘ Iso.inv (IsoFinFin× n))
           (funExt (sym ∘ Iso.leftInv (IsoFinFin× n))) ∙
   
   ( cong {x = Iso.fun (IsoFinFin× n) ∘
      permuteF' n (k ∷ ε) ∘ Iso.inv (IsoFinFin× n)} {y = subst (𝔽in n) q}
       (_∘' X i0)
       (funExt (λ x → Σ≡Prop (λ _ → snd (Fin×Snd n _))
         ((hhhPF'-lem n (fst k) (snd k) (fst x) (snd x)
           ∙ sym (uaβ (adjT×^≃ {n = n} (fst k)) (fst x)))
         ∙
           funExt⁻ (cong transport (sym (adjT×^≡-≡-ua n (fst k)))) (fst x)
            )
           
           ) ∙ cong′  (subst (𝔽in n)) {x = 𝕡loop k} {y = q}
          (doubleCompPath-filler refl _ _)) ∙ 
    cong (subst (𝔽in n) q ∘'_) -- {!!}
      (X ∙ cong′ (subst (𝔽in n))
         {x = sym (cong (toℙrm n) (emloop xs))}
         {y = p}
         
        (toℙrmInv n xs) )
      )

   ∙ sym (funExt (substComposite (𝔽in n) p q))
    ∙ cong′ (subst (𝔽in n)) {x = p ∙ q}  
     (  sym (IsGroupHom.pres· ((snd (GIso-𝕡Ω₂-PermG n)))
        (inv xs) (k ∷ ε)) 
      ∙ IsGroupHom.presinv (snd (GIso-𝕡Ω₂-PermG n)) (k ∷ xs))
   where
    p = _
    q = _




𝕃tab : ∀ 𝕝 → (𝕃Fin 𝕝 → A) → FMSet2 A
𝕃tab = RElim.ff w λ _ → λ _ → isGroupoidΠ λ _ → trunc
 where
 w : RElim (λ z → (𝕃Fin z → A) → FMSet2 A)
 RElim.[]* w _ = []
 (w RElim.∷* tt) {𝕝} X f =
   f (𝕃Fin0 𝕝) ∷2 X (f ∘' 𝕃Fin-suc 𝕝)
 RElim.comm* w tt tt {𝕝} X i f =
  let (f0 , f1) = 𝕃Fin-01 𝕝 i
  in comm (f f0) (f f1)
       (X (f ∘' λ x → 𝕃Fin-comm 𝕝 x i )) i
 RElim.comm-inv* w tt tt {𝕝} X =
   congSqP 
     {a₀₋ = (λ j → fst (𝕃Fin-01 𝕝 j) , snd (𝕃Fin-01 𝕝 j) , λ x → 𝕃Fin-comm 𝕝 x j)}
     {a₁₋ = (λ j → snd (𝕃Fin-01 𝕝 (~ j)) , (fst (𝕃Fin-01 𝕝 (~ j)))
                   , λ x → 𝕃Fin-comm 𝕝 x (~ j))}
     {λ _ → (𝕃Fin0 (tt ∷2 𝕝) ,
      𝕃Fin-suc (tt ∷2 𝕝) (𝕃Fin0 𝕝) ,
      (λ x → 𝕃Fin-suc (tt ∷2 𝕝) (𝕃Fin-suc 𝕝 x)))}
     {λ _ → (𝕃Fin-suc (tt ∷2 𝕝) (𝕃Fin0 𝕝) ,
      𝕃Fin0 (tt ∷2 𝕝) , (λ x → 𝕃Fin-suc (tt ∷2 𝕝) (𝕃Fin-suc 𝕝 x)))}
     (λ i j (f0 , f1 , fSS) g →
      comm-inv (g f0) (g f1) (X (g ∘ fSS)) i j)
     (isSet→SquareP
       (λ i j → isSet× (isSet𝕃Fin (comm-inv tt tt 𝕝 i j))
               (isSet× (isSet𝕃Fin (comm-inv tt tt 𝕝 i j))
                (isSet→ (isSet𝕃Fin (comm-inv tt tt 𝕝 i j)))))
        _ _ _ _)         
 RElim.commm* w tt tt tt {𝕝} X i f =
  let (f0 , f1 , f2) = 𝕃Fin-120 𝕝 i
  in commm (f f2) (f f0) (f f1) (X (f ∘' λ x → 𝕃Fin-commm 𝕝 x i)) i
 RElim.commp* w tt tt tt {𝕝} X = 

    congSqP
     {a₀₋ = λ j → _ , _ , _ , λ x → _} 
     {a₁₋ = λ j → _ , _ , _ , λ x → _ }
     {λ j → let (f0 , f1 , f2) = 𝕃Fin-120 𝕝 j
            in f0 , f1 , f2 , λ x → 𝕃Fin-commm 𝕝 x j}
     {λ _ → (𝕃Fin0 (tt ∷2 tt ∷2 𝕝) ,
      𝕃Fin-suc (tt ∷2 tt ∷2 𝕝) (𝕃Fin-suc (tt ∷2 𝕝) (𝕃Fin0 𝕝)) ,
      𝕃Fin-suc (tt ∷2 tt ∷2 𝕝) (𝕃Fin0 (tt ∷2 𝕝)) ,
      (λ x →
         𝕃Fin-suc (tt ∷2 tt ∷2 𝕝) (𝕃Fin-suc (tt ∷2 𝕝) (𝕃Fin-suc 𝕝 x))))}
     (λ i j (f0 , f1 , f2 , fSSS) g →
      commp (g f0) (g f1) (g f2) (X (g ∘ fSSS)) i j)
     (isSet→SquareP
       (λ i j → isSet× (isSet𝕃Fin (commp tt tt tt 𝕝 i j))
               (isSet× (isSet𝕃Fin (commp tt tt tt 𝕝 i j))
                (isSet× (isSet𝕃Fin (commp tt tt tt 𝕝 i j))
                 (isSet→ (isSet𝕃Fin (commp tt tt tt 𝕝 i j))))
                ))
        _ _ _ _)

 RElim.hex* w tt tt tt {𝕝} X =
        congSqP
     {a₀₋ = λ j → _ , _ , _ , λ x → _} 
     {a₁₋ = λ j → _ , _ , _ , λ x → _}
     {λ j → let (f0 , f1 , f2) = 𝕃Fin-120 𝕝 j
            in f0 , f1 , f2 , λ x → 𝕃Fin-commm 𝕝 x j}
     {λ j → let (f0 , f1 , f2) = 𝕃Fin-120 𝕝 j
            in f1 , f0 , f2 , λ x → 𝕃Fin-commm 𝕝 x j}
     (λ i j (f0 , f1 , f2 , fSSS) g →
      hex (g f0) (g f1) (g f2) (X (g ∘ fSSS)) i j)
     (isSet→SquareP
       (λ i j → isSet× (isSet𝕃Fin (hex tt tt tt 𝕝 i j))
               (isSet× (isSet𝕃Fin (hex tt tt tt 𝕝 i j))
                (isSet× (isSet𝕃Fin (hex tt tt tt 𝕝 i j))
                 (isSet→ (isSet𝕃Fin (hex tt tt tt 𝕝 i j))))
                ))
        _ _ _ _)




--  module 𝕃ook' (isGroupoidA : isGroupoid A) where

--   𝕃look : (𝕝 : FMSet2 A) → (𝕃Fin (<$tt 𝕝) → A)
--   𝕃look 𝕝 b = 
--     let (x , y) = 𝕃addIndex 𝕝 b
--     in fst (fst (fromOnlyOneₚ
--           (Bool→Type ∘ snd )
--           (λ _ → isPropBool→Type)
--           (λ _ → DecBool→Type)
--           (isGroupoidΣ isGroupoidA (λ _ → isSet→isGroupoid isSetBool))
--             x y))

--   𝕃look-comm : ∀ x y xs → 
--        Square {A = 𝕃Fin (<$tt xs) → A}
--         (λ i x' → 𝕃look (comm x y xs i) (𝕃Fin-comm (<$tt xs) x' i))
--         (λ _ → 𝕃look xs)
--         (λ _ → 𝕃look xs)
--         (λ _ → 𝕃look xs)
--   𝕃look-comm x y xs =
--     congSq {A = ∀ b → ⟨
--       onlyOneₚ (λ x₁ → Bool→Type (snd x₁)) (λ z → isPropBool→Type)
--       (λ z → DecBool→Type) (fst (𝕃addIndex xs b))
--       ⟩} {B = 𝕃Fin (<$tt xs) → A}
--        (λ q b →
--          fst (fst (fromOnlyOneₚ
--           (Bool→Type ∘ snd )
--           (λ _ → isPropBool→Type)
--           (λ _ → DecBool→Type)
--            ((isGroupoidΣ isGroupoidA (λ _ → isSet→isGroupoid isSetBool)))
--            ((fst (𝕃addIndex xs b))) (q b))))
--          (isProp→SquareP
--            (λ _ _ → isPropΠ λ b →
--              snd (onlyOneₚ (λ x₁ → Bool→Type (snd x₁)) (λ z → isPropBool→Type)
--                (λ z → DecBool→Type) (fst (𝕃addIndex xs b))))
--              _ _ _ _)
      
   

--   look-tab : section (uncurry 𝕃tab) (λ 𝕝 → <$tt 𝕝 , 𝕃look 𝕝)
--   look-tab = RElimSet.f w
--    where
--    w : RElimSet (λ z → uncurry 𝕃tab (<$tt z , 𝕃look z) ≡ z)
--    RElimSet.[]* w = refl
--    (w RElimSet.∷* x) = cong (x ∷2_)
--    RElimSet.comm* w x y {xs} b = ww
--     where

--     wwJ0 wwJ0' : x ∷2 y ∷2 𝕃tab (<$tt xs) (𝕃look xs)
--          ≡ y ∷2 x ∷2 𝕃tab (<$tt xs) (𝕃look xs)
--     wwJ0 i =
--      let (f0 , f1) = 𝕃Fin-01 (<$tt xs) i
--          f = 𝕃look (comm x y xs i)
--          -- ltb = comm ? ?
--          --         (𝕃tab {!!} (f ∘' λ x → 𝕃Fin-comm xs x i )) i
--      in comm x y (𝕃tab (<$tt xs) (f ∘ λ x → 𝕃Fin-comm (<$tt xs) x i)) i

--     wwJ0' i =
--      comm x y (𝕃tab (<$tt xs) (𝕃look xs)) i


--     wwJ0= : wwJ0 ≡ wwJ0'
--     wwJ0= j i = comm x y (𝕃tab (<$tt xs) (𝕃look-comm x y xs j i)) i

--     ww : Square
--            (λ j → x ∷2 y ∷2 b j)
--            (λ j → y ∷2 x ∷2 b j)
--            wwJ0
--            (comm x y xs)
--     ww = 
--       flipSquare
--        ( wwJ0=
--          ◁ λ i j → comm x y (b i) j)

--    RElimSet.trunc* w xs = trunc _ _

--   -- tab-look-∷ : ∀ xs (x₁ : (y₁ : 𝕃Fin xs → A) →
--   --      Path ? (<$tt (uncurry 𝕃tab (xs , y₁)) , 𝕃look (uncurry 𝕃tab (xs , y₁)))
--   --       (xs , y₁)) y →
--   --      (<$tt (uncurry 𝕃tab (tt ∷2 xs , y)) ,
--   --      𝕃look (uncurry 𝕃tab (tt ∷2 xs , y)))
--   --     ≡ (tt ∷2 xs , y)
--   -- tab-look-∷ xs x₁ y = 
--   --         ΣPathP ((λ i → tt ∷2 fst (z i)) , ww)
--   --   where
--   --    z = x₁ (y ∘ 𝕃Fin-suc xs)

--   --    ww : PathP (λ i → 𝕃Fin (tt ∷2 fst (z i)) → A)
--   --           (𝕃look (uncurry 𝕃tab (tt ∷2 xs , y))) y
--   --    ww i ((false , snd₂) , snd₁) = snd (z i) (snd₂ , snd₁)
--   --    ww i ((true , snd₂) , snd₁) =
--   --     let zwz = (coei→1 (λ i → Σ _ (λ v → ⟨ 𝕃allFalse (fst (z i)) v ⟩)) i (snd₂ , snd₁))
--   --     in y ((true ,
--   --          allFalse→≡repeat-false-𝔽 xs zwz (~ i)
--   --          ) , isProp→PathP
--   --                (λ i →
--   --                    snd
--   --                     (𝕃FinSnd (tt ∷2 xs)
--   --                      (true ,
--   --                       allFalse→≡repeat-false-𝔽 xs zwz (~ i) )))
--   --                (repeat𝕃allFalse xs) (snd zwz) i)

-- --   tab-look : retract (uncurry 𝕃tab) (λ 𝕝 → <$tt 𝕝 , 𝕃look 𝕝)
-- --   tab-look = uncurry (RElimSet.f w)
-- --    where
-- --    w : RElimSet _
-- --    fst (RElimSet.[]* w y i) = []
-- --    snd (RElimSet.[]* w y i) ()
-- --    (w RElimSet.∷* tt) {xs} x₁ y = ?
-- --      -- tab-look-∷ xs x₁ y

-- --    RElimSet.comm* w tt tt {xs} b = ?
-- --     --  congP (λ _ → funExt⁻) wwq
-- --     -- where
-- --     --  wwq : {!!}
-- --     --  wwq = {!!}
-- --     -- funExtDep ww
-- --     -- where
-- --     -- ww : {x₀ x₁ : 𝕃Fin (tt ∷2 tt ∷2 xs) → A}
-- --     --   (p : PathP (λ z → 𝕃Fin (comm tt tt xs z) → A) x₀ x₁) →
-- --     --   PathP _ _ _
-- --     -- fst (ww p i j) = comm tt tt (fst (b (p i ∘ λ v → 𝕃Fin-comm xs v i) j)) i
-- --     -- snd (ww p i j) qq =
-- --     --   let zz = (b (p i ∘ λ v → 𝕃Fin-comm xs v i) j)
-- --     --       (bo , bo' , bos) = ua-unglue Σ-swap-01-≃ i (fst qq)
-- --     --       (x* , y*) = 𝕃addIndex (𝕃tab 
-- --     --                        {!!}
-- --     --                        {!!})
-- --     --                     ({!bos!} , {!!})

-- --     --   in fst (fst (fromOnlyOneₚ-comm (λ x₁ → Bool→Type (snd x₁)) (λ z → isPropBool→Type)
-- --     --            (λ z → DecBool→Type)
-- --     --            {x = _ , bo} {_ , bo'} {x*} {{!!}} {!!} {!!} i {!!}))
    
-- --    RElimSet.trunc* w = {!!}

-- -- -- --  module _ (isGroupoidA : isGroupoid A) where

-- -- -- --   𝕃look : (𝕝 : FMSet2 A) → (𝕃Fin (<$tt 𝕝) → A)
-- -- -- --   𝕃look = RElim.ff
-- -- -- --      w λ _ _ → isGroupoidΠ λ _ → isGroupoidA
-- -- -- --    where

-- -- -- --    open RElim

-- -- -- --    w∷ : (x : A) (xs : FMSet2C A) → 
-- -- -- --          (𝕃Fin (<$tt xs) → A) →
-- -- -- --           𝕃Fin (<$tt (x ∷2 xs)) → A
-- -- -- --    w∷ _ _ f ((false , bs) , p) = f (bs , p)
-- -- -- --    w∷ a _ _ ((true , _) , _) = a

-- -- -- --    w-comm : (a a' : A) (xs : FMSet2C A) → 
-- -- -- --          (f : 𝕃Fin (<$tt xs) → A) →
-- -- -- --           Path (𝕃Fin (<$tt (a ∷2 a' ∷2 xs)) → A) (w∷ a (a' ∷2 xs) (w∷ a' xs f))
-- -- -- --           (λ x →
-- -- -- --             w∷ a' (a ∷2 xs) (w∷ a xs f)
-- -- -- --             (𝕃Fin-swap01 (<$tt xs) x))
-- -- -- --    w-comm a a' xs f i ((false , false , bs) , snd₁) = f (bs , snd₁)
-- -- -- --    w-comm a a' xs f i ((false , true , bs) , snd₁) = a'
-- -- -- --    w-comm a a' xs f i ((true , false , bs) , snd₁) = a

-- -- -- --    w-comm-inv : (a a' : A) (𝕝 : FMSet2C A) → 
-- -- -- --          (b : 𝕃Fin (<$tt 𝕝) → A) →
-- -- -- --            Square {A = (𝕃Fin (<$tt (a ∷2 a' ∷2 𝕝)) → A)}
-- -- -- --              (w-comm a a' 𝕝 b)
-- -- -- --              (cong (_∘ (𝕃Fin-swap01 (<$tt 𝕝))) (sym (w-comm a' a 𝕝 b)))
-- -- -- --              (cong {x = idfun _}
-- -- -- --                {y = 𝕃Fin-swap01 (<$tt 𝕝) ∘ 𝕃Fin-swap01 (<$tt 𝕝)}
-- -- -- --                 (w∷ a (a' ∷2 𝕝) (w∷ a' 𝕝 b) ∘'_)
-- -- -- --                 (funExt (𝕃Fin-swap01-invol (<$tt 𝕝))))
-- -- -- --              refl
-- -- -- --    -- w-comm-inv = {!!}
-- -- -- --    w-comm-inv a a' xs f i j ((false , false , bs) , snd₁) =
-- -- -- --      f {!!}
-- -- -- --    w-comm-inv a a' xs f i j ((false , true , bs) , snd₁) = a'
-- -- -- --    w-comm-inv a a' xs f i j ((true , false , bs) , snd₁) = a

-- -- -- --    w : RElim (λ z → 𝕃Fin (<$tt z) → A)
-- -- -- --    []* w ()
-- -- -- --    (w ∷* x) {xs} = w∷ x xs
-- -- -- --    comm* w a a' {𝕝} b =
-- -- -- --       w-comm a a' 𝕝 b
-- -- -- --        ◁ (λ i → w∷ a' (a ∷2 𝕝) (w∷ a 𝕝 b)
-- -- -- --             ∘ (𝕃Fin-comm-unglue (<$tt 𝕝) i)) 

-- -- -- --    comm-inv* w a a' {𝕝} b =
-- -- -- --        {!!}
-- -- -- --    commm* w = {!!}
-- -- -- --    commp* w = {!!}
-- -- -- --    hex* w = {!!}
 
-- -- -- -- --   -- look-tab : section (uncurry 𝕃tab)
-- -- -- -- --   --     (λ 𝕝 → <$tt 𝕝 , 𝕃look 𝕝)
-- -- -- -- --   -- look-tab = RElimSet.f w
-- -- -- -- --   --  where
-- -- -- -- --   --  w : RElimSet
-- -- -- -- --   --        (λ z →
-- -- -- -- --   --           uncurry 𝕃tab (<$tt z , 𝕃look z) ≡ z)
-- -- -- -- --   --  RElimSet.[]* w = refl
-- -- -- -- --   --  (w RElimSet.∷* a) x₁ = cong (a ∷2_) x₁
-- -- -- -- --   --  RElimSet.comm* w a a' {xs} b =
-- -- -- -- --   --    flipSquareP (
-- -- -- -- --   --      ({!!})
-- -- -- -- --   --      ◁ λ i j → comm-inv a a' (b i) (~ i) j)
-- -- -- -- --   --  RElimSet.trunc* w _ = trunc _ _

-- -- -- -- --   tab-look-fst : (x : FM2⊤) → (y : 𝕃Fin x → A) →
-- -- -- -- --      mapFM2 (idfun Unit) (λ _ → tt) (uncurry 𝕃tab (x , y)) ≡ x

-- -- -- -- --   tab-look-fst = RElimSet.f w
-- -- -- -- --    where
-- -- -- -- --    w : RElimSet
-- -- -- -- --          (λ z →
-- -- -- -- --             (y : 𝕃Fin z → A) →
-- -- -- -- --             <$tt (uncurry 𝕃tab (z , y)) ≡ z)
-- -- -- -- --    RElimSet.[]* w _ = refl
-- -- -- -- --    (w RElimSet.∷* x ) {xs} x₁ y = cong (x ∷2_) (x₁ (y ∘ 𝕃Fin-suc xs)) 
-- -- -- -- --    RElimSet.comm* w tt tt {xs} b i y j =
-- -- -- -- --       comm tt tt (b (λ x → y (𝕃Fin-comm xs x i)) j) i 
-- -- -- -- --    RElimSet.trunc* w xs =
-- -- -- -- --      isSetΠ λ y → trunc _ _


-- -- -- -- --   repF-tab-lem : ∀ xs (y : 𝕃Fin xs → A) →
-- -- -- -- --                let qq = tab-look-fst xs y i0
-- -- -- -- --             in ∀ (snd₁ : 𝕃Bool qq) → ⟨ 𝕃allFalse qq snd₁ ⟩ →  (repeatF xs) ≡
-- -- -- -- --         transport
-- -- -- -- --         (λ i → 𝕃Bool (tab-look-fst xs y i))
-- -- -- -- --         (snd₁)
-- -- -- -- --   repF-tab-lem = RElimProp.f w
-- -- -- -- --    where
-- -- -- -- --    w : RElimProp
-- -- -- -- --          (λ z →
-- -- -- -- --             (y : 𝕃Fin z → A) (snd₁ : 𝕃Bool (tab-look-fst z y i0)) →
-- -- -- -- --              ⟨ 𝕃allFalse (tab-look-fst z y i0) snd₁ ⟩ → 
-- -- -- -- --             repeatF z ≡ transport (λ i → 𝕃Bool (tab-look-fst z y i)) snd₁)
-- -- -- -- --    RElimProp.[]* w _ _ _ _ = tt* 
-- -- -- -- --    (w RElimProp.∷* tt) x₁ y (false , snd₁) qq =
-- -- -- -- --      cong₂ _,_ refl (x₁ _ snd₁ qq)
-- -- -- -- --    RElimProp.trunc* w xs =
-- -- -- -- --      isPropΠ3 λ _ _ _ → isSet𝕃₂ _ (isSetBool) xs _ _

-- -- -- -- --   𝕃Fin0-tab-lem : ∀ xs y (snd₁ : _) →
-- -- -- -- --      (⟨ 𝕃FinSnd (tt ∷2 tab-look-fst xs y i0) (true , snd₁) ⟩ ) →  (true , repeatF xs) ≡
-- -- -- -- --         transport
-- -- -- -- --         (λ i → 𝕃Bool (tt ∷2 tab-look-fst xs y i))
-- -- -- -- --         (true , snd₁)
-- -- -- -- --   𝕃Fin0-tab-lem xs y snd₁ qq = cong₂ _,_ refl (repF-tab-lem xs y snd₁ qq)
  
-- -- -- -- --   tab-look-snd : (x : FM2⊤) → (y : 𝕃Fin x → A) →
-- -- -- -- --      PathP (λ i → 𝕃Fin (tab-look-fst x y i) → A)
-- -- -- -- --        (𝕃look (uncurry 𝕃tab (x , y))) y     

-- -- -- -- --   tab-look-snd x y =  --toPathP ∘ ? ∘  (RElimSet.f w x)
-- -- -- -- --     let z = RElimSet.f w x y
-- -- -- -- --         z' = sym (funExt (uncurry z))
-- -- -- -- --     in symP (toPathP {!   z'!})
-- -- -- -- --    where
-- -- -- -- --     -- w : RElimSet (λ x →
-- -- -- -- --     --       (y : 𝕃Fin x → A) →
-- -- -- -- --     --       ( -- transport (λ i → 𝕃Fin (tab-look-fst x y i) → A)
-- -- -- -- --     --         Path (𝕃Fin x → A) (𝕃look (𝕃tab x y) ∘ (
-- -- -- -- --     --             (transport (λ i → 𝕃Fin (tab-look-fst x y (~ i)))
-- -- -- -- --     --               ))) (y)))
-- -- -- -- --     -- RElimSet.[]* w y i ()
-- -- -- -- --     -- (w RElimSet.∷* x) x₁ y i ((false , xs) , ys) = ?
-- -- -- -- --     -- (w RElimSet.∷* x) x₁ y i ((true , xs) , ys) = ?
-- -- -- -- --     -- RElimSet.comm* w = {!!}
-- -- -- -- --     -- RElimSet.trunc* w = {!!}
-- -- -- -- --     w : RElimSet (λ x →
-- -- -- -- --              (y : 𝕃Fin x → A) →
-- -- -- -- --              ( -- transport (λ i → 𝕃Fin (tab-look-fst x y i) → A)
-- -- -- -- --                ∀ v v' → (𝕃look (𝕃tab x y) (v , v')) ≡ y (
-- -- -- -- --                    (transport (λ i → 𝕃Fin (tab-look-fst x y i))
-- -- -- -- --                      ((v , v'))))))
-- -- -- -- --     RElimSet.[]* w y v ()
-- -- -- -- --     (w RElimSet.∷* x) x₁ y (false , snd₁) v' =
-- -- -- -- --        x₁ _ snd₁ v'
-- -- -- -- --     (w RElimSet.∷* tt) {xs} x₁ y (true , snd₁) v' =
-- -- -- -- --       cong′ y 
-- -- -- -- --         (Σ≡Prop (snd ∘ (𝕃FinSnd (tt ∷2 xs)))
-- -- -- -- --           (𝕃Fin0-tab-lem xs (λ x₂ → y (𝕃Fin-suc xs x₂)) snd₁ v') )
-- -- -- -- --     -- RElimSet.comm* w tt tt {xs} b i y v v' j =
-- -- -- -- --     --   let qq = (𝕃Fin-comm-unglue
-- -- -- -- --     --                 ((<$tt (𝕃tab (xs)
-- -- -- -- --     --                      (y ∘' λ x → 𝕃Fin-comm xs x i))))
-- -- -- -- --     --                 i (v , v'))
-- -- -- -- --     --       q = b (y ∘' λ x → 𝕃Fin-comm xs x i)
-- -- -- -- --     --            (snd (snd (fst qq)))
-- -- -- -- --     --   in {!!}
-- -- -- -- --     RElimSet.comm* w tt tt {xs} b =
-- -- -- -- --       -- let q : PathP (λ i → (y : (𝕃Fin (comm tt tt xs i)) → A) →
-- -- -- -- --       --                ∀ v v' → _ ≡ _)
-- -- -- -- --       --            (λ y → b (λ x₁ → y ((false , false , fst x₁) , snd x₁)))
-- -- -- -- --       --             (λ y → b (λ x₁ → y ((false , false , fst x₁) , snd x₁)))
-- -- -- -- --       --     q = λ i y → b (y ∘' λ x → 𝕃Fin-comm xs x i)
-- -- -- -- --       -- in
-- -- -- -- --          congP (λ _ → curry ∘ curry)
-- -- -- -- --            (funTypePathP _ _ _ _ (funExt ww''))
           
-- -- -- -- --      where
-- -- -- -- --       ww'' : (x : Σ (Σ _ _) _) → _ ≡ _ 
-- -- -- -- --       ww'' ((fst₁ , false , false , bb'') , snd₁) =
-- -- -- -- --         {!!}
-- -- -- -- --       ww'' ((f , false , true , bb'') , snd₁) i j = {!!}
-- -- -- -- --        --  ((
-- -- -- -- --        --   (((λ i → transp (λ _ → A) (~ i) (f (p₀ i) )) ∙
-- -- -- -- --        --           cong (transport refl ∘ f) p₁)
-- -- -- -- --        --        ∙∙P (cong (transport refl ∘ f) p₂) ∙∙P
-- -- -- -- --        --        (λ i → transp (λ _ → A) i (f (p₃ i))))
-- -- -- -- --        --   ≡⟨ (λ j →
-- -- -- -- --        --      fixComp (((λ i → transp (λ _ → A) ((~ i) ∨ j) (f (p₀ i))))
-- -- -- -- --        --           ∙ ( (cong (transp (λ _ → A) (j) ∘ f) p₁)))
-- -- -- -- --        --         ((cong (transp (λ _ → A) (j) ∘ f) p₂))
-- -- -- -- --        --         ((λ i → transp (λ _ → A) (i ∨ j) (f (p₃ i)))) (~ j))
-- -- -- -- --        --      ∙∙ 
-- -- -- -- --        --          (λ j → (cong-∙ f p₀ p₁ (~ j)  ) ∙∙ (cong f p₂) ∙∙ (cong f p₃))
-- -- -- -- --        --          ∙∙ (sym (cong-∙∙ f (p₀ ∙ p₁) p₂ p₃))
-- -- -- -- --        --          ⟩

-- -- -- -- --        --    (cong f ((p₀ ∙ p₁) ∙∙ p₂ ∙∙ p₃)) ∎ ))

-- -- -- -- --        --    ◁ congSq f
-- -- -- -- --        --       (isSet→isSet' (isSet𝕃Fin (tt ∷2 tt ∷2 xs))
-- -- -- -- --        --         ((p₀ ∙ p₁) ∙∙ p₂ ∙∙ p₃) _ _ _)
-- -- -- -- --        -- where
-- -- -- -- --        --  p₀ : Path (𝕃Fin (tt ∷2 tt ∷2 xs))
-- -- -- -- --        --        (𝕃Fin-suc (tt ∷2 xs) (𝕃Fin0 xs))
-- -- -- -- --        --        (transp (λ j → 𝕃Fin (comm tt tt xs (i0 ∨ ~ (i0 ∨ ~ j)))) i0
-- -- -- -- --        --          (fst (𝕃Fin-01 xs i0)))
-- -- -- -- --        --  p₀ = ?

-- -- -- -- --        --  p₁ : Path (𝕃Fin (tt ∷2 tt ∷2 xs)) _ _
-- -- -- -- --        --  p₁ = _

-- -- -- -- --        --  p₂ : Path (𝕃Fin (tt ∷2 tt ∷2 xs)) _ _
-- -- -- -- --        --  p₂ = _

-- -- -- -- --        --  p₃ : Path (𝕃Fin (tt ∷2 tt ∷2 xs)) _ _
-- -- -- -- --        --  p₃ = _

-- -- -- -- --       ww'' ((fst₁ , true , false , bb'') , snd₁)  = {!!}
          
-- -- -- -- --         --  -- -- (λ i j → hcomp
-- -- -- -- --         --  -- --      (λ k → λ {
-- -- -- -- --         --  -- --           (i = i1) → fst₁ {!!}
-- -- -- -- --         --  -- --          ;(j = i0) → fst₁ {!!}
-- -- -- -- --         --  -- --          ;(j = i1) → fst₁ {!!}
-- -- -- -- --         --  -- --          })
-- -- -- -- --         --  -- --      (fst₁ {!!}))
-- -- -- -- --         --  -- (λ i j → fst₁
-- -- -- -- --         --  --  (fill (λ _ → 𝕃Fin (tt ∷2 tt ∷2 xs))
-- -- -- -- --         --  --      (λ k → 
-- -- -- -- --         --  --        (λ { (j = i0) →
-- -- -- -- --         --  --            (true , repeatF (tt ∷2 xs)) , repeat𝕃allFalse (tt ∷2 xs)
-- -- -- -- --         --  --           ; (j = i1) →
-- -- -- -- --         --  --           {!transport
-- -- -- -- --         --  --             (λ i₁ → 𝕃Fin (tab-look-fst (tt ∷2 tt ∷2 xs) fst₁ i₁)) 
-- -- -- -- --         --  --               ((true , false , bb'') , snd₁)!}
-- -- -- -- --         --  --           }))
-- -- -- -- --         --  --    (inS {!!}) (~ i)))
-- -- -- -- --         --     ({!!} ) ◁ congSq fst₁
-- -- -- -- --         --      (isSet→isSet' (isSet𝕃Fin (tt ∷2 tt ∷2 xs)) _ _ _ _)
-- -- -- -- --         -- -- congSq fst₁ {!!}
        
           
-- -- -- -- --     RElimSet.trunc* w xs =
-- -- -- -- --       isSetΠ3 λ _ _ _ → isGroupoidA _ _

   
-- -- -- -- -- --   Iso-look-tab : Iso (Σ FM2⊤ λ 𝕝 → (𝕃Fin 𝕝 → A)) (FMSet2 A)
-- -- -- -- -- --   Iso.fun Iso-look-tab = uncurry 𝕃tab
-- -- -- -- -- --   Iso.inv Iso-look-tab =
-- -- -- -- -- --     λ 𝕝 → (mapFM2 (idfun _) (λ _ → _) 𝕝) , 𝕃look 𝕝
-- -- -- -- -- --   Iso.rightInv Iso-look-tab = look-tab
-- -- -- -- -- --   fst (Iso.leftInv Iso-look-tab (x , y) i) = tab-look-fst x y i
-- -- -- -- -- --   snd (Iso.leftInv Iso-look-tab (x , y) i) = tab-look-snd x y i


-- -- -- -- -- --   -- Iso-×^ : Iso (Σ (Σ ℕ ℙrm) λ (n , p) → fst (𝕍₂ Bool isSetBool n p))
-- -- -- -- -- --   --              (Σ _ (𝕃Bool))
-- -- -- -- -- --   -- Iso-×^ = Σ-cong-iso (invIso Iso-FM2⊤-Σℙrm) (uncurry λ n → R𝕡elimSet'.f (w n))
-- -- -- -- -- --   --  where

-- -- -- -- -- --   --  wIso : ∀ n → Iso (fst (𝕍₂ Bool isSetBool n 𝕡base))
-- -- -- -- -- --   --                   (𝕃Bool (toFM2⊤ (n , 𝕡base)))
-- -- -- -- -- --   --  wIso zero = idIso
-- -- -- -- -- --   --  wIso (suc n) = prodIso idIso (wIso n)

-- -- -- -- -- --   --  w : ∀ n → R𝕡elimSet'
-- -- -- -- -- --   --              (λ z →
-- -- -- -- -- --   --                 Iso (fst (𝕍₂ Bool isSetBool n z))
-- -- -- -- -- --   --                 (𝕃Bool (Iso.fun (invIso Iso-FM2⊤-Σℙrm) (n , z))))
-- -- -- -- -- --   --  R𝕡elimSet'.isSetA (w n) x =
-- -- -- -- -- --   --   isSet-SetsIso
-- -- -- -- -- --   --    (snd (𝕍₂ Bool isSetBool n x))
-- -- -- -- -- --   --    (isSet𝕃₂ Bool isSetBool (toFM2⊤ (n , x)))
-- -- -- -- -- --   --  R𝕡elimSet'.abase (w n) = wIso n
-- -- -- -- -- --   --  R𝕡elimSet'.aloop (w (suc n)) (suc k , k<) =
-- -- -- -- -- --   --   congP (λ _ z → prodIso idIso z)
-- -- -- -- -- --   --     (R𝕡elimSet'.aloop (w n) (k , k<))
-- -- -- -- -- --   --  Iso.fun (R𝕡elimSet'.aloop (w (suc (suc n))) (zero , k<) i) =
-- -- -- -- -- --   --    ua-gluePathExt Σ-swap-01-≃ i
-- -- -- -- -- --   --     ∘' (map-snd (map-snd (Iso.fun (wIso n))))
-- -- -- -- -- --   --     ∘' (swap-01 ∘' (ua-ungluePathExt Σ-swap-01-≃ i))
-- -- -- -- -- --   --  Iso.inv (R𝕡elimSet'.aloop (w (suc (suc n))) (zero , k<) i) =
-- -- -- -- -- --   --   ua-gluePathExt Σ-swap-01-≃ i
-- -- -- -- -- --   --     ∘' (map-snd (map-snd (Iso.inv (wIso n))))
-- -- -- -- -- --   --     ∘' (swap-01 ∘' (ua-ungluePathExt Σ-swap-01-≃ i))
-- -- -- -- -- --   --  Iso.rightInv (R𝕡elimSet'.aloop (w (suc (suc n))) (zero , k<) i) =
-- -- -- -- -- --   --    {!!}
-- -- -- -- -- --   --  Iso.leftInv (R𝕡elimSet'.aloop (w (suc (suc n))) (zero , k<) i) = {!!}


-- -- -- -- -- --   Iso-Fin×→ : Iso (Σ (Σ ℕ ℙrm) λ (n , p) → 𝔽in n p → A)
-- -- -- -- -- --                (Σ _ (λ 𝕝 → 𝕃Fin 𝕝 → A))
-- -- -- -- -- --   Iso-Fin×→ = Σ-cong-iso (invIso Iso-FM2⊤-Σℙrm)
-- -- -- -- -- --       (λ (n , 𝕡) → domIso (Σ-cong-iso (R𝕡elimSet'.f (w n) 𝕡) {!!}))
-- -- -- -- -- --    where

-- -- -- -- -- --     wIso : ∀ n → Iso (fst (𝕍₂ Bool isSetBool n 𝕡base))
-- -- -- -- -- --                      (𝕃Bool (toFM2⊤ (n , 𝕡base)))
-- -- -- -- -- --     wIso zero = idIso
-- -- -- -- -- --     wIso (suc n) = prodIso idIso (wIso n)

-- -- -- -- -- --     w : ∀ n → R𝕡elimSet'
-- -- -- -- -- --                 (λ z →
-- -- -- -- -- --                    Iso (fst (𝕍₂ Bool isSetBool n z))
-- -- -- -- -- --                    (𝕃Bool (Iso.fun (invIso Iso-FM2⊤-Σℙrm) (n , z))))
-- -- -- -- -- --     R𝕡elimSet'.isSetA (w n) x =
-- -- -- -- -- --      isSet-SetsIso
-- -- -- -- -- --       (snd (𝕍₂ Bool isSetBool n x))
-- -- -- -- -- --       (isSet𝕃₂ Bool isSetBool (toFM2⊤ (n , x)))
-- -- -- -- -- --     R𝕡elimSet'.abase (w n) = wIso n
-- -- -- -- -- --     R𝕡elimSet'.aloop (w (suc n)) (suc k , k<) =
-- -- -- -- -- --      congP (λ _ z → prodIso idIso z)
-- -- -- -- -- --        (R𝕡elimSet'.aloop (w n) (k , k<))
-- -- -- -- -- --     Iso.fun (R𝕡elimSet'.aloop (w (suc (suc n))) (zero , k<) i) =
-- -- -- -- -- --       ua-gluePathExt Σ-swap-01-≃ i
-- -- -- -- -- --        ∘' (map-snd (map-snd (Iso.fun (wIso n))))
-- -- -- -- -- --        ∘' (swap-01 ∘' (ua-ungluePathExt Σ-swap-01-≃ i))
-- -- -- -- -- --     Iso.inv (R𝕡elimSet'.aloop (w (suc (suc n))) (zero , k<) i) =
-- -- -- -- -- --      ua-gluePathExt Σ-swap-01-≃ i
-- -- -- -- -- --        ∘' (map-snd (map-snd (Iso.inv (wIso n))))
-- -- -- -- -- --        ∘' (swap-01 ∘' (ua-ungluePathExt Σ-swap-01-≃ i))
-- -- -- -- -- --     Iso.rightInv (R𝕡elimSet'.aloop (w (suc (suc n))) (zero , k<) i) =
-- -- -- -- -- --       {!!}
-- -- -- -- -- --     Iso.leftInv (R𝕡elimSet'.aloop (w (suc (suc n))) (zero , k<) i) = {!!}


-- -- -- -- -- --    -- w : ∀ n → R𝕡elimSet'
-- -- -- -- -- --    --             (λ z → {!!})
-- -- -- -- -- --    -- w = {!!}


-- -- -- -- -- --   look-tab-≃ = isoToEquiv Iso-look-tab
 

-- -- -- -- -- --   lookup× : (l : List A) → Fin× (length l) → A
-- -- -- -- -- --   lookup× (a ∷ l) = Fin×cases a (lookup× l)

-- -- -- -- -- --   tab×L : ∀ n → (Fin× n → A) → List A
-- -- -- -- -- --   tab×L zero _ = []
-- -- -- -- -- --   tab×L (suc n) x = x Fin×0 ∷ tab×L n (x ∘ sucFin×)

-- -- -- -- -- --   -- lookup×-iso : Iso (List A) (Σ _ (λ n → Fin× n → A))
-- -- -- -- -- --   -- lookup×-iso = w
-- -- -- -- -- --   --  where

-- -- -- -- -- --   --   ri : ∀ n f → _ ≡ _
-- -- -- -- -- --   --   fst (ri zero f i) = zero
-- -- -- -- -- --   --   snd (ri zero f i) ()
-- -- -- -- -- --   --   ri (suc n) f = {!!}

-- -- -- -- -- --   --   w : Iso (List A) (Σ ℕ (λ n → Fin× n → A))
-- -- -- -- -- --   --   Iso.fun w l = _ , lookup× l
-- -- -- -- -- --   --   Iso.inv w = uncurry tab×L
-- -- -- -- -- --   --   Iso.rightInv w = uncurry ri
-- -- -- -- -- --   --   Iso.leftInv w = {!!}

-- -- -- -- -- --   lookup×-lem : (x : List A) →  lookup (List-perm.List→×^ x) ≡
-- -- -- -- -- --       equivFun (preCompEquiv (isoToEquiv (IsoFinFin× (length x))))
-- -- -- -- -- --       (lookup× x)
-- -- -- -- -- --   lookup×-lem [] i ()
-- -- -- -- -- --   lookup×-lem (x ∷ l) = funExt (uncurry w)
-- -- -- -- -- --    where
-- -- -- -- -- --     w : (x₁ : ℕ) (y : x₁ < length (x ∷ l)) →
-- -- -- -- -- --           lookup (List-perm.List→×^ (x ∷ l)) (x₁ , y) ≡
-- -- -- -- -- --           equivFun (preCompEquiv (isoToEquiv (IsoFinFin× (length (x ∷ l)))))
-- -- -- -- -- --           (lookup× (x ∷ l)) (x₁ , y)
-- -- -- -- -- --     w zero y = refl
-- -- -- -- -- --     w (suc x₁) y =
-- -- -- -- -- --       funExt⁻ (lookup×-lem l) (x₁ , y)
  
-- -- -- -- -- --   tab-fromList-fst : (l : List A) →
     
-- -- -- -- -- --        (fst (equivFun (invEquiv look-tab-≃ ∙ₑ isoToEquiv (invIso Iso-Fin×→))
-- -- -- -- -- --         (fromList l))) ≡
-- -- -- -- -- --      (length l , 𝕡base)
-- -- -- -- -- --   fst (tab-fromList-fst [] i) = zero
-- -- -- -- -- --   fst (tab-fromList-fst (x ∷ l) i) = suc (fst (tab-fromList-fst l i))
-- -- -- -- -- --   snd (tab-fromList-fst [] i) = 𝕡base
-- -- -- -- -- --   snd (tab-fromList-fst (x ∷ l) i) =
-- -- -- -- -- --     sucℙrm _ (snd (tab-fromList-fst l i))

-- -- -- -- -- --   tab-fromList-snd' : ∀ l f → ((snd
-- -- -- -- -- --       (equivFun (invEquiv look-tab-≃ ∙ₑ isoToEquiv (invIso Iso-Fin×→))
-- -- -- -- -- --        (fromList l))
-- -- -- -- -- --       ∘
-- -- -- -- -- --       subst
-- -- -- -- -- --       (λ (x , y) →
-- -- -- -- -- --          𝔽in x y)
-- -- -- -- -- --       (sym (tab-fromList-fst l))) f)
-- -- -- -- -- --       ≡ lookup× l f
-- -- -- -- -- --   tab-fromList-snd' [] ()
-- -- -- -- -- --   tab-fromList-snd' (x ∷ l) ((false , bs) , z) = {!!}
-- -- -- -- -- --   tab-fromList-snd' (x ∷ l) ((true , bs) , _) = {!!}

-- -- -- -- -- --   tab-fromList-snd : (l : List A) →
-- -- -- -- -- --     PathP (λ i → 𝔽in (fst (tab-fromList-fst l i))
-- -- -- -- -- --                      (snd (tab-fromList-fst l i)) → A)
-- -- -- -- -- --       (snd ((equivFun (invEquiv look-tab-≃ ∙ₑ isoToEquiv (invIso Iso-Fin×→))
-- -- -- -- -- --         (fromList l))))
-- -- -- -- -- --       (lookup× l)
-- -- -- -- -- --   tab-fromList-snd l =
-- -- -- -- -- --     funTypeTransp' (λ (x , y) → 𝔽in x y) A (tab-fromList-fst l) _
-- -- -- -- -- --      ▷ funExt (tab-fromList-snd' l)

-- -- -- -- -- --   tab-fromList : (l : List A) →
     
-- -- -- -- -- --        (equivFun (invEquiv look-tab-≃ ∙ₑ isoToEquiv (invIso Iso-Fin×→))
-- -- -- -- -- --         (fromList l)) ≡
-- -- -- -- -- --      ((length l , 𝕡base) , lookup× l)
-- -- -- -- -- --   tab-fromList l = ΣPathP ( tab-fromList-fst l , tab-fromList-snd l)

-- -- -- -- -- --   ≃nm-help : (A : (n m : ℕ) → n ≡ m → Type ℓ)
-- -- -- -- -- --      → ∀ n m →
-- -- -- -- -- --         Iso (Σ (n ≡ m) (A n m)) ((n ≡ m) × A n n refl)
-- -- -- -- -- --      -- → (∀ n → A n n ≃ B n n)
-- -- -- -- -- --      -- → ∀ n m → (A n m) ≃ (B n m)
-- -- -- -- -- --   ≃nm-help = {!!}

-- -- -- -- -- --   Σ-Iso-look-tabΩ-fst : ∀ n m →
-- -- -- -- -- --        Iso (Path (Σ ℕ ℙrm) (n , 𝕡base) (m , 𝕡base))
-- -- -- -- -- --            ((Path (ℙrm n) 𝕡base 𝕡base) × (n ≡ m))
-- -- -- -- -- --   Σ-Iso-look-tabΩ-fst n m = w
-- -- -- -- -- --     -- ≃nm-help _ _ {!!}
-- -- -- -- -- --     --  λ n → invEquiv ΣPath≃PathΣ ∙ₑ
-- -- -- -- -- --     --         Σ-cong-equiv {!!} {!!}
-- -- -- -- -- --     --          ∙ₑ Σ-swap-≃
-- -- -- -- -- --    where

-- -- -- -- -- --    w→ : Path (Σ ℕ ℙrm) (n , 𝕡base) (m , 𝕡base) →
-- -- -- -- -- --           Path (ℙrm n) 𝕡base 𝕡base × (n ≡ m)
-- -- -- -- -- --    fst (w→ x) i = coei→0 (λ i → ℙrm (fst (x i))) i (snd (x i))
-- -- -- -- -- --    snd (w→ x) = cong fst x

-- -- -- -- -- --    w← : Path (ℙrm n) 𝕡base 𝕡base × (n ≡ m) →
-- -- -- -- -- --           Path (Σ ℕ ℙrm) (n , 𝕡base) (m , 𝕡base)
-- -- -- -- -- --    fst (w← x i) = snd x i 
-- -- -- -- -- --    snd (w← x i) = coe0→i (λ i → ℙrm (snd x i)) i (fst x i)

-- -- -- -- -- --    w : Iso (Path (Σ ℕ ℙrm) (n , 𝕡base) (m , 𝕡base))
-- -- -- -- -- --          (Path (ℙrm n) 𝕡base 𝕡base × (n ≡ m))
-- -- -- -- -- --    Iso.fun w = w→
-- -- -- -- -- --    Iso.inv w = w←
-- -- -- -- -- --    fst (Iso.rightInv w b j) = {!!}
-- -- -- -- -- --    snd (Iso.rightInv w b j) = snd b
-- -- -- -- -- --    fst (Iso.leftInv w a j i) = fst (a i)
-- -- -- -- -- --    snd (Iso.leftInv w a j i) = {!!}
   
-- -- -- -- -- --     -- invEquiv ΣPath≃PathΣ ∙ₑ {!isoTo!}


-- -- -- -- -- --   -- Iso-look-tabΩ :
-- -- -- -- -- --   --      (n : ℕ)
-- -- -- -- -- --   --     (x y : List A) → (length x ≡ n) → (length y ≡ n) → 
-- -- -- -- -- --   --   (fromList x ≡ fromList y) ≃
-- -- -- -- -- --   --     Σ (Perm (length x))
-- -- -- -- -- --   --      λ p →
-- -- -- -- -- --   --        List-perm.permuteList x p ≡ y
-- -- -- -- -- --   -- Iso-look-tabΩ n x y lx ly =
-- -- -- -- -- --   --    (fromList x ≡ fromList y)
-- -- -- -- -- --   --     ≃⟨ congEquiv {x = fromList x} {fromList y}
-- -- -- -- -- --   --     (invEquiv look-tab-≃ ∙ₑ isoToEquiv (invIso Iso-Fin×→)) ⟩
-- -- -- -- -- --   --        _
-- -- -- -- -- --   --     ≃⟨   compPathrEquiv {!!}
-- -- -- -- -- --   --       ∙ₑ compPathlEquiv (sym (tab-fromList x ∙
-- -- -- -- -- --   --              {!!}))
-- -- -- -- -- --   --       --   compPathrEquiv (tab-fromList y ∙
-- -- -- -- -- --   --       --    ΣPathP ((ΣPathP ((sym ((sym ly))) , (toPathP refl))) ,
-- -- -- -- -- --   --       --       toPathP {!!}))
-- -- -- -- -- --   --       -- ∙ₑ compPathlEquiv (sym (tab-fromList x) ∙ ?)
-- -- -- -- -- --   --       ⟩
-- -- -- -- -- --   --       Path (Σ (Σ ℕ ℙrm)
-- -- -- -- -- --   --              (λ (p , q) →
-- -- -- -- -- --   --                 𝔽in p q → A))
-- -- -- -- -- --   --         ((n , 𝕡base) , lookup× x ∘ subst Fin× (sym lx))
-- -- -- -- -- --   --         ((n , 𝕡base) , lookup× y ∘ subst Fin× (sym ly))
       
-- -- -- -- -- --   --    ≃⟨ {!!} ⟩
-- -- -- -- -- --   --      Path (Σ (ℙrm n) λ q → 𝔽in n q → A)
-- -- -- -- -- --   --         (𝕡base , lookup× x ∘ subst Fin× (sym lx))
-- -- -- -- -- --   --         (𝕡base , lookup× y ∘ subst Fin× (sym ly))
-- -- -- -- -- --   --    ≃⟨ invEquiv ΣPath≃PathΣ  ⟩
-- -- -- -- -- --   --      Σ (Path (ℙrm n) 𝕡base 𝕡base)
-- -- -- -- -- --   --          (λ q → PathP (λ i → 𝔽in n (q i) → A)
-- -- -- -- -- --   --                   (λ x₁ → lookup× x (subst Fin× (λ i → lx (~ i)) x₁))
-- -- -- -- -- --   --                   (λ x₁ → lookup× y (subst Fin× (λ i → ly (~ i)) x₁)))
-- -- -- -- -- --   --    ≃⟨ {!!} ⟩
-- -- -- -- -- --   --      _
-- -- -- -- -- --   --    ≃⟨ {!!} ⟩
-- -- -- -- -- --   --    _ ■
     
-- -- -- -- -- --   -- permuteList-lemma : (x y : List A) → (l= : length x ≡ length y) →
-- -- -- -- -- --   --     (p : Perm (length x)) →
-- -- -- -- -- --   --    PathP (λ i → isoToPath {!!} i)
-- -- -- -- -- --   --       {!!} {!!} ≃
-- -- -- -- -- --   --   (List-perm.permuteList x p ≡ y)
   


-- -- -- -- -- --   -- permuteList-lemma = {!!}



-- -- -- -- -- -- -- transport
-- -- -- -- -- -- --       (λ i →
-- -- -- -- -- -- --          𝔽in
-- -- -- -- -- -- --          (fst
-- -- -- -- -- --           -- (ΣPathP
-- -- -- -- -- --           --  ((λ i₁ → p (~ i₁)) ,
-- -- -- -- -- --           --   toPathP (λ _ → transport (λ i₁ → ℙrm (p (~ i₁))) 𝕡base))
-- -- -- -- -- --           --  i))
-- -- -- -- -- -- --          (snd
-- -- -- -- -- -- --           (ΣPathP
-- -- -- -- -- -- --            ((λ i₁ → p (~ i₁)) ,
-- -- -- -- -- -- --             toPathP (λ _ → transport (λ i₁ → ℙrm (p (~ i₁))) 𝕡base))
-- -- -- -- -- -- --            i)) →
-- -- -- -- -- -- --          A)
-- -- -- -- -- -- --       (lookup× y)
-- -- -- -- -- -- --       ≡ transport (λ i → 𝔽in (p (~ i)) 𝕡base → A) (lookup× y)

-- -- -- -- -- --   -- lemΣrefl : ∀ {ℓ} n → (A : ℕ → Type ℓ) → (a₀ a₁ : A n)
-- -- -- -- -- --   --              →     (Path (Σ ℕ A) (n , a₀) (n , a₁))
-- -- -- -- -- --   --                    ≃ (Path (A n) a₀ a₁)
-- -- -- -- -- --   -- lemΣrefl n A a₀ a₁ = invEquiv ΣPath≃PathΣ ∙ₑ
-- -- -- -- -- --   --     {!!}

-- -- -- -- -- --   lemΣrefl : ∀ {ℓ} n → (A : ℕ → Type ℓ) → (a₀ a₁ : A n)
-- -- -- -- -- --                → Iso (Path (Σ ℕ A) (n , a₀) (n , a₁))
-- -- -- -- -- --                      (Path (A n) a₀ a₁)
-- -- -- -- -- --   lemΣrefl n A a₀ a₁ = compIso (invIso ΣPathIsoPathΣ)
-- -- -- -- -- --      (Σ-contractFstIso (refl , (isSetℕ n n refl)))


-- -- -- -- -- --   -- hhh : ∀ (x y : List A) (p : length x ≡ length y) →
-- -- -- -- -- --   --       equivFun (isoToEquiv (invIso (Iso-×^-F→ (length x))))
-- -- -- -- -- --   --     (equivFun (preCompEquiv (isoToEquiv (IsoFinFin× (length x))))
-- -- -- -- -- --   --      (λ x₂ → lookup× y (subst Fin× p x₂)))
-- -- -- -- -- --   --     ≡
-- -- -- -- -- --   --     equivFun (isoToEquiv (invIso (Iso-×^-F→ (length x))))
-- -- -- -- -- --   --     (equivFun
-- -- -- -- -- --   --      (isoToEquiv
-- -- -- -- -- --   --       (compIso (List-perm.IsoListOfLen×^ (length x))
-- -- -- -- -- --   --        (Iso-×^-F→ (length x))))
-- -- -- -- -- --   --      (y , (λ i → p (~ i))))
-- -- -- -- -- --   -- hhh [] [] p = refl
-- -- -- -- -- --   -- hhh [] (x ∷ y) p = ⊥.rec (Nat.znots p)
-- -- -- -- -- --   -- hhh (x ∷ x₁) [] p = ⊥.rec (Nat.snotz p)
-- -- -- -- -- --   -- hhh (x ∷ []) (x₂ ∷ []) p = {!!}
-- -- -- -- -- --   -- hhh (x ∷ []) (x₂ ∷ x₁ ∷ y) p = {!!}
-- -- -- -- -- --   -- hhh (x ∷ x₁ ∷ x₃) (x₂ ∷ []) p = {!!}
-- -- -- -- -- --   -- hhh (x ∷ x₁ ∷ x₃) (x₂ ∷ x₄ ∷ y) p = {!!}
-- -- -- -- -- --   --    -- ΣPathP ({!!}
-- -- -- -- -- --   --    --        ,
-- -- -- -- -- --   --    --         ( cong tabulate
-- -- -- -- -- --   --    --            ((cong₂ _∘_
-- -- -- -- -- --   --    --               {!Fin×elimFunExt ? ?!} {!!})
-- -- -- -- -- --   --    --              ∙ {!!})
-- -- -- -- -- --   --    --          -- ({!Fin×elimFunExt ? ?!}
-- -- -- -- -- --   --    --          --   ∙ {!!})
-- -- -- -- -- --   --    --           ∙ hhh x₁ y (cong predℕ p) ))
   
-- -- -- -- -- -- -- Goal: (λ x₃ →
-- -- -- -- -- -- --          Fin×cases x₂ (lookup× y)
-- -- -- -- -- -- --          (transp (λ i → Σ (Bool ×^ p i) (λ x₄ → fst (Fin×Snd (p i) x₄))) i0
-- -- -- -- -- -- --           ((false , ℕ→Fin× (length x₁) (fst x₃)) ,
-- -- -- -- -- -- --            ℕ→Fin×-snd (length x₁) (fst x₃) (snd x₃))))
-- -- -- -- -- -- --       ≡
-- -- -- -- -- -- --       (λ x₃ →
-- -- -- -- -- -- --          lookup× y
-- -- -- -- -- -- --          (transp
-- -- -- -- -- -- --           (λ i →
-- -- -- -- -- -- --              Σ (Bool ×^ predℕ (p i)) (λ x₄ → fst (Fin×Snd (predℕ (p i)) x₄)))
-- -- -- -- -- -- --           i0
-- -- -- -- -- -- --           (ℕ→Fin× (length x₁) (fst x₃) ,
-- -- -- -- -- -- --            ℕ→Fin×-snd (length x₁) (fst x₃) (snd x₃))))


-- -- -- -- -- --   -- hhhXXX' : ∀ x₂ (y : List A) →
-- -- -- -- -- --   --      lookup× y ≡
-- -- -- -- -- --   --     (λ x₃ →
-- -- -- -- -- --   --        lookup
-- -- -- -- -- --   --        (Iso.fun (List-perm.IsoListOfLen×^ (suc (length y)))
-- -- -- -- -- --   --         (x₂ ∷ y , (λ _ → suc (length y))))
-- -- -- -- -- --   --        (Fin×→ℕ (suc (length y)) (fst x₃) ,
-- -- -- -- -- --   --         Fin×→ℕ-snd (suc (length y)) (fst x₃) (snd x₃)))
-- -- -- -- -- --   --     ∘' sucFin×
-- -- -- -- -- --   -- hhhXXX' x₂ y = funExt (uncurry (w y))
-- -- -- -- -- --   --  where
-- -- -- -- -- --   --  w : ∀ y → (x : Bool ×^ length y) (y₁ : fst (Fin×Snd (length y) x)) →
-- -- -- -- -- --   --        lookup× y (x , y₁) ≡
-- -- -- -- -- --   --        ((λ x₃ →
-- -- -- -- -- --   --            lookup
-- -- -- -- -- --   --            (Iso.fun (List-perm.IsoListOfLen×^ (suc (length y)))
-- -- -- -- -- --   --             (x₂ ∷ y , (λ _ → suc (length y))))
-- -- -- -- -- --   --            (Fin×→ℕ (suc (length y)) (fst x₃) ,
-- -- -- -- -- --   --             Fin×→ℕ-snd (suc (length y)) (fst x₃) (snd x₃)))
-- -- -- -- -- --   --         ∘' sucFin×)
-- -- -- -- -- --   --        (x , y₁)
-- -- -- -- -- --   --  w (x₁ ∷ y) (false , snd₁) y₁ = w y snd₁ y₁
-- -- -- -- -- --   --  w (x₁ ∷ y) (true , snd₁) y₁ = refl

-- -- -- -- -- --   hhhXXX : ∀ (x y : List A) (p : length x ≡ length y) → ∀ z z' → 
-- -- -- -- -- --                ((equivFun (preCompEquiv (isoToEquiv (IsoFinFin× (length x))))
-- -- -- -- -- --                (λ x₁ → lookup× y (subst Fin× p x₁))) (z , z'))
-- -- -- -- -- --                ≡
-- -- -- -- -- --                ((equivFun
-- -- -- -- -- --                (isoToEquiv
-- -- -- -- -- --                 (compIso (List-perm.IsoListOfLen×^ (length x))
-- -- -- -- -- --                  (Iso-×^-F→ (length x))))
-- -- -- -- -- --                (y , (λ i → p (~ i)))) (z , z'))
-- -- -- -- -- --   hhhXXX (x ∷ x₁) [] p z z' = ⊥.rec (Nat.snotz p)
-- -- -- -- -- --   hhhXXX (x ∷ x₁) (x₂ ∷ y) p zero z' = 
-- -- -- -- -- --         cong {x = (transp (λ i → Σ (Bool ×^ p i) (λ x₃ → fst (Fin×Snd (p i) x₃))) i0
-- -- -- -- -- --        ((true , repeat (length x₁) false) ,
-- -- -- -- -- --         allFalse-repeat-false (length x₁)))}
-- -- -- -- -- --              {y = (true , _) ,
-- -- -- -- -- --                    allFalseSubst {m =  (length y)} (cong predℕ p)
-- -- -- -- -- --                      (repeat (length x₁) false) (allFalse-repeat-false
-- -- -- -- -- --                       (length x₁))}
-- -- -- -- -- --              (Fin×cases x₂ (lookup× y))
-- -- -- -- -- --            (Σ≡Prop (snd ∘ (Fin×Snd (p i1))) (subst×^Suc p _ ))
-- -- -- -- -- --   hhhXXX (x ∷ x₁) (x₂ ∷ y) p (suc z) z' =
-- -- -- -- -- --     (cong (Fin×cases x₂ (lookup× y))
-- -- -- -- -- --          ((Σ≡Prop (snd ∘ (Fin×Snd (p i1))) 
-- -- -- -- -- --             (subst×^Suc p _ )))
-- -- -- -- -- --       )
-- -- -- -- -- --     ∙ hhhXXX x₁ y (cong predℕ p) z z'


-- -- -- -- -- --   hhhXX : ∀ x →
-- -- -- -- -- --        Path (Fin (length x) → A)
-- -- -- -- -- --        (equivFun
-- -- -- -- -- --       (isoToEquiv
-- -- -- -- -- --        (compIso (List-perm.IsoListOfLen×^ (length x))
-- -- -- -- -- --         (Iso-×^-F→ (length x))))
-- -- -- -- -- --       (x , (λ _ → length x)))
      
-- -- -- -- -- --       (λ x₁ →
-- -- -- -- -- --          lookup× x
-- -- -- -- -- --          (ℕ→Fin× (length x) (fst x₁) ,
-- -- -- -- -- --           ℕ→Fin×-snd (length x) (fst x₁) (snd x₁)))
-- -- -- -- -- --   hhhXX x = invEq (congEquiv (isoToEquiv (invIso (Iso-×^-F→ (length x)))))
-- -- -- -- -- --             (h x)
-- -- -- -- -- --    where
-- -- -- -- -- --     h : ∀ x → equivFun (isoToEquiv (invIso (Iso-×^-F→ (length x))))
-- -- -- -- -- --       (equivFun
-- -- -- -- -- --        (isoToEquiv
-- -- -- -- -- --         (compIso (List-perm.IsoListOfLen×^ (length x))
-- -- -- -- -- --          (Iso-×^-F→ (length x))))
-- -- -- -- -- --        (x , (λ _ → length x)))
-- -- -- -- -- --       ≡
-- -- -- -- -- --       equivFun (isoToEquiv (invIso (Iso-×^-F→ (length x))))
-- -- -- -- -- --       (λ x₁ →
-- -- -- -- -- --          lookup× x
-- -- -- -- -- --          (ℕ→Fin× (length x) (fst x₁) ,
-- -- -- -- -- --           ℕ→Fin×-snd (length x) (fst x₁) (snd x₁)))
-- -- -- -- -- --     h [] = refl
-- -- -- -- -- --     h (x ∷ x₁) = ΣPathP (refl , h x₁)
    
-- -- -- -- -- --   hhhX : ∀ x → (p' : Path (ℙrm (length x)) 𝕡base 𝕡base)
-- -- -- -- -- --       →
-- -- -- -- -- --       Path (Fin (length x) → A)
-- -- -- -- -- --         (λ x₁ →
-- -- -- -- -- --          equivFun
-- -- -- -- -- --          (isoToEquiv
-- -- -- -- -- --           (compIso (List-perm.IsoListOfLen×^ (length x))
-- -- -- -- -- --            (Iso-×^-F→ (length x))))
-- -- -- -- -- --          (x , (λ _ → length x))
-- -- -- -- -- --          (permuteF' (length x) (equivFun (invEquiv
-- -- -- -- -- --            (isoToEquiv ((fst (GIso-𝕡Ω₂-PermG (length x)))) )) p') x₁))
      
-- -- -- -- -- --       (equivFun (preCompEquiv (isoToEquiv (IsoFinFin× (length x))))
-- -- -- -- -- --       (transport (λ i → 𝔽in (length x) (p' i) → A) (lookup× x)))
-- -- -- -- -- --   hhhX x p' =
-- -- -- -- -- --      ( cong′ (_∘' (permuteF' (length x) 
-- -- -- -- -- --           (equivFun (invEquiv (isoToEquiv (fst (GIso-𝕡Ω₂-PermG (length x)))))
-- -- -- -- -- --            p')))
-- -- -- -- -- --           {x = equivFun
-- -- -- -- -- --          (isoToEquiv
-- -- -- -- -- --           (compIso (List-perm.IsoListOfLen×^ (length x))
-- -- -- -- -- --            (Iso-×^-F→ (length x))))
-- -- -- -- -- --          (x , (λ _ → length x))}
-- -- -- -- -- --           {y = lookup× x ∘ Iso.fun (IsoFinFin× (length x))}
-- -- -- -- -- --           (hhhXX x) ∙
-- -- -- -- -- --        cong (((lookup× x ∘
-- -- -- -- -- --          (Iso.fun (IsoFinFin× (length x)) ∘
-- -- -- -- -- --           (permuteF' (length x)
-- -- -- -- -- --             (equivFun
-- -- -- -- -- --               (invEquiv (isoToEquiv (fst (GIso-𝕡Ω₂-PermG (length x))))) p')))))
-- -- -- -- -- --           ∘_ ) (sym (funExt (Iso.leftInv (IsoFinFin× (length x))))))
     
-- -- -- -- -- --      ∙
-- -- -- -- -- --      cong
-- -- -- -- -- --        {x = lookup× x ∘ 
-- -- -- -- -- --              Iso.fun (IsoFinFin× (length x))
-- -- -- -- -- --             ∘ 
-- -- -- -- -- --             permuteF' (length x) (equivFun (invEquiv
-- -- -- -- -- --            (isoToEquiv ((fst (GIso-𝕡Ω₂-PermG (length x)))) )) p')
-- -- -- -- -- --             ∘ Iso.inv (IsoFinFin× (length x))}
-- -- -- -- -- --        {y = transport (λ i → 𝔽in (length x) (p' i) → A) (lookup× x)}
-- -- -- -- -- --        (equivFun (preCompEquiv (isoToEquiv (IsoFinFin× (length x)))))
-- -- -- -- -- --        ((cong (lookup× x ∘_) (hhhPF' (length x) ((equivFun (invEquiv
-- -- -- -- -- --            (isoToEquiv ((fst (GIso-𝕡Ω₂-PermG (length x)))) )) p'))
-- -- -- -- -- --             ∙ cong ((subst (𝔽in (length x)) ∘ sym))
-- -- -- -- -- --              (Iso.rightInv ((((fst (GIso-𝕡Ω₂-PermG (length x)))) )) p')))
-- -- -- -- -- --          ∙ sym (fromPathP {A = λ i → 𝔽in (length x) (p' i) → A}
-- -- -- -- -- --          (funTypeTransp' (𝔽in (length x)) A p' ((lookup× x)))))


-- -- -- -- -- --   Iso-look-tabΩ : (x y : List A) → (length x ≡ length y) → 
-- -- -- -- -- --     (fromList x ≡ fromList y) ≃
-- -- -- -- -- --       Σ (Perm (length x))
-- -- -- -- -- --        λ p →
-- -- -- -- -- --          List-perm.permuteList x p ≡ y
-- -- -- -- -- --   Iso-look-tabΩ x y p =
-- -- -- -- -- --        (fromList x ≡ fromList y)
-- -- -- -- -- --       ≃⟨ congEquiv {x = fromList x} {fromList y}
-- -- -- -- -- --       (invEquiv look-tab-≃ ∙ₑ isoToEquiv (invIso Iso-Fin×→)) ⟩
-- -- -- -- -- --        _
-- -- -- -- -- --       ≃⟨ compPathrEquiv (tab-fromList y ∙
-- -- -- -- -- --            ΣPathP ((ΣPathP ((sym p) , (toPathP refl))) ,
-- -- -- -- -- --               toPathP                
-- -- -- -- -- --                 (funExt⁻
-- -- -- -- -- --                 (cong transport
-- -- -- -- -- --                    (cong {A = Path (Σ ℕ ℙrm)
-- -- -- -- -- --                           (length y , 𝕡base) (length x , 𝕡base)} {x =
-- -- -- -- -- --                     λ i → (p (~ i)) ,
-- -- -- -- -- --                           toPathP {A = λ i → ℙrm (p (~ i))}
-- -- -- -- -- --                              {x = 𝕡base}
-- -- -- -- -- --                              (λ _ → transport (λ i₁ → ℙrm (p (~ i₁)))
-- -- -- -- -- --                             𝕡base) i}
-- -- -- -- -- --                          {y = λ i → (p (~ i)) , 𝕡base {n = p (~ i)}}
-- -- -- -- -- --                       (cong (λ X → uncurry 𝔽in X → A))
-- -- -- -- -- --                      zzz))
-- -- -- -- -- --                 (lookup× y))
-- -- -- -- -- --                 ))
-- -- -- -- -- --         ∙ₑ compPathlEquiv (sym (tab-fromList x)) ⟩
-- -- -- -- -- --         Path (Σ (Σ ℕ ℙrm)
-- -- -- -- -- --                (λ (p , q) →
-- -- -- -- -- --                   𝔽in p q → A))
-- -- -- -- -- --           ((length x , 𝕡base) , lookup× x)
-- -- -- -- -- --           ((length x , 𝕡base) , transport
-- -- -- -- -- --                                   (λ i →
-- -- -- -- -- --                                      𝔽in
-- -- -- -- -- --                                      (p (~ i))
-- -- -- -- -- --                                      𝕡base  →
-- -- -- -- -- --                                      A)
-- -- -- -- -- --                                   (lookup× y))
-- -- -- -- -- --       ≃⟨ congEquiv Σ-assoc-≃ ∙ₑ
-- -- -- -- -- --           (isoToEquiv
-- -- -- -- -- --             (lemΣrefl (length x) _ _ _))⟩
-- -- -- -- -- --       Path (Σ (ℙrm (length x)) λ q → 𝔽in (length x) q → A)
-- -- -- -- -- --          (𝕡base , lookup× x)
-- -- -- -- -- --          (𝕡base , transport (λ i → 𝔽in (p (~ i)) 𝕡base → A) (lookup× y))
-- -- -- -- -- --       ≃⟨ invEquiv ΣPath≃PathΣ ⟩
-- -- -- -- -- --         Σ (𝕡base ≡ 𝕡base)
-- -- -- -- -- --           (λ p₁ →
-- -- -- -- -- --              PathP (λ i → 𝔽in (length x) (p₁ i) → A)
-- -- -- -- -- --                    (lookup× x)
-- -- -- -- -- --                    (transport (λ i → 𝔽in (p (~ i)) 𝕡base → A) (lookup× y)))
-- -- -- -- -- --       ≃⟨ Σ-cong-equiv-snd (λ _ →
           
-- -- -- -- -- --             PathP≃Path _ _ _
-- -- -- -- -- --         ∙ₑ congEquiv (preCompEquiv (isoToEquiv (IsoFinFin× (length x))))
-- -- -- -- -- --         ) ⟩
-- -- -- -- -- --          _
-- -- -- -- -- --       ≃⟨ Σ-cong-equiv-snd (λ p' →
-- -- -- -- -- --            compPathrEquiv

-- -- -- -- -- --              (cong {x = (transport (λ i → Fin× (p (~ i)) → A) (lookup× y))}
-- -- -- -- -- --                    {y = lookup× y ∘' subst Fin× p}
-- -- -- -- -- --                (equivFun (preCompEquiv (isoToEquiv (IsoFinFin× (length x)))))
-- -- -- -- -- --                  (fromPathP {x = lookup× y} (funTypeTransp' Fin× A (sym p) _))
-- -- -- -- -- --               ∙ hhh* x y p  )
-- -- -- -- -- --         ∙ₑ compPathlEquiv (hhhX x p')) ⟩ 
-- -- -- -- -- --         _
-- -- -- -- -- --       ≃⟨ Σ-cong-equiv-fst (invEquiv pp) ∙ₑ
-- -- -- -- -- --          Σ-cong-equiv-snd (List-perm.permuteList-lemma x y p) ⟩
-- -- -- -- -- --       _ ■

-- -- -- -- -- --     where
-- -- -- -- -- --       pp :  (Perm (length x)) ≃ (_≡_ {A = ℙrm (length x)} 𝕡base 𝕡base)        
-- -- -- -- -- --       pp = isoToEquiv ((fst (GIso-𝕡Ω₂-PermG (length x)))) 

-- -- -- -- -- --       zzz : _ ≡ _
-- -- -- -- -- --       fst (zzz i x) = p (~ x)
-- -- -- -- -- --       snd (zzz i x) = (rUnit (λ _ → 𝕡base)) (~ i) x

-- -- -- -- -- --       hhh* : ∀ (x y : List A) (p : length x ≡ length y) →
-- -- -- -- -- --             equivFun (preCompEquiv (isoToEquiv (IsoFinFin× (length x))))
-- -- -- -- -- --             (λ x₁ → lookup× y (subst Fin× p x₁))
-- -- -- -- -- --             ≡
-- -- -- -- -- --             equivFun
-- -- -- -- -- --             (isoToEquiv
-- -- -- -- -- --              (compIso (List-perm.IsoListOfLen×^ (length x))
-- -- -- -- -- --               (Iso-×^-F→ (length x))))
-- -- -- -- -- --             (y , (λ i → p (~ i)))
-- -- -- -- -- --       hhh* x y p = funExt (uncurry (hhhXXX x y  p))

