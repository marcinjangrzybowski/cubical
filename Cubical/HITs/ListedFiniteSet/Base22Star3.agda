{-# OPTIONS --safe    #-} 
module Cubical.HITs.ListedFiniteSet.Base22Star3 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)
open import Cubical.Data.Nat
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Sigma

open import Cubical.Data.FinData.Transpositions

import Cubical.Functions.Logic as Lo
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv

open import Cubical.Foundations.Function
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path

open import Cubical.Foundations.Univalence


open import Cubical.HITs.EilenbergMacLane1

-- open import Cubical.Data.FinData

open import Cubical.Data.Nat.Order.Recursive

import Cubical.Data.SumFin as F


open import Cubical.HITs.ListedFiniteSet.Base3

-- open import Cubical.Data.FinData.GTrun

import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.GroupoidTruncation as GT
open import Cubical.HITs.SetTruncation as ST


open import Cubical.Functions.Involution

open import Cubical.Homotopy.EilenbergMacLane.Properties

open import Cubical.Data.FinSet


open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.SymmetricGroup
open import Cubical.Algebra.Group.Generators

open import Cubical.HITs.ListedFiniteSet.Base22Star2


private
  variable
    ℓ : Level
    A B : Type ℓ

module fm2Look' (isGroupoidA : isGroupoid A)  where

 fm⊤ : FMSet2 A → FMSet2 Unit
 fm⊤ = fm2Map (λ _ → _)


 lemmmH : (a a' a'' : A) → (xs : FMSet2 Unit) → (f : 𝔽in xs → A) →
         SquareP (λ i j → ua (swap0and1M (h𝔽in xs)) j →  A)
                (λ j → Mb.rec a' (Mb.rec a'' (Mb.rec a f)) ∘
                   swap0and1Mf (Mb^ 1 (h𝔽in xs)) ∘ just ∘ unglue (j ∨ ~ j))
                (λ j → Mb.rec a' (Mb.rec a f) ∘ unglue (j ∨ ~ j))
                _
                _

 lemmmH a a' a'' xs f =
     (λ i j → funExt {B = λ _ _ → A}
             {f = Mb.rec a' (Mb.rec a'' (Mb.rec a f)) ∘
                   swap0and1Mf (Mb^ 1 (h𝔽in xs)) ∘ just}
             {g = Mb.rec a' (Mb.rec a f)}
              ((λ { 
                  nothing _ → a'
                ; (just nothing) _ → a
                ; (just (just x)) _ → f x
                })) i ∘ unglue (j ∨ ~ j) )

 commmL-≡0 : ∀ (a a' a'' : A) → (xs : FMSet2 A) → (f : 𝔽in (fm⊤ xs) → A) → 
             Mb.rec a (Mb.rec a' (Mb.rec a'' f)) ≡
      (Mb.rec a' (Mb.rec a'' (Mb.rec a f))) ∘'
        map-Maybe (swap0and1Mf ((h𝔽in (fm⊤ xs))))
         ∘' swap0and1Mf (Mb^ 1 (h𝔽in (fm⊤ xs)))
 commmL-≡0 a a' a'' xs f i nothing = a
 commmL-≡0 a a' a'' xs f i (just nothing) = a'
 commmL-≡0 a a' a'' xs f i (just (just nothing)) = a''
 commmL-≡0 a a' a'' xs f i (just (just (just x))) = f x

 commmL-≡1 : ∀ (a a' a'' : A) → (xs : FMSet2 A) → (f : 𝔽in (fm⊤ xs) → A) →
      Mb.rec a' (Mb.rec a'' (Mb.rec a f)) ∘
       swap0and1Mf (Mb^ 1 (h𝔽in (fm⊤ xs)))
       ∘' map-Maybe (swap0and1Mf ((h𝔽in (fm⊤ xs))))
          ≡ Mb.rec a'' (Mb.rec a (Mb.rec a' f))
 commmL-≡1 a a' a'' xs f i nothing = a''
 commmL-≡1 a a' a'' xs f i (just nothing) = a
 commmL-≡1 a a' a'' xs f i (just (just nothing)) = a'
 commmL-≡1 a a' a'' xs f i (just (just (just x))) = f x

 commmR-≡0 : ∀ (a a' a'' : A) → (xs : FMSet2 A) → (f : 𝔽in (fm⊤ xs) → A) → 
             Mb.rec a (Mb.rec a' (Mb.rec a'' f)) ≡
      (Mb.rec a' (Mb.rec a'' (Mb.rec a f))) ∘'
        map-Maybe (swap0and1Mf ((h𝔽in (fm⊤ xs))))
         ∘' swap0and1Mf (Mb^ 1 (h𝔽in (fm⊤ xs)))
 commmR-≡0 a a' a'' xs f i nothing = a
 commmR-≡0 a a' a'' xs f i (just nothing) = a'
 commmR-≡0 a a' a'' xs f i (just (just nothing)) = a''
 commmR-≡0 a a' a'' xs f i (just (just (just x))) = f x

 look-commmpH : (a a' a'' : A) →
       (xs  : FMSet2 A) → (f : 𝔽in (fm⊤ xs) → A) →
     SquareP (λ i j → 𝔽in (fm⊤ (hex a a' a'' xs i j)) → A)
       ((λ i → swap-lem (fm⊤ (a'' ∷2 xs)) a' a (Mb.rec a'' f) (~ i)) ◁
       (λ i x → Mb.rec a' (Mb.rec a (Mb.rec a'' f)) (unglue (i ∨ ~ i) x)))
      (congP (λ z f₁ → Mb.rec a'' f₁)
       ((λ i → swap-lem (fm⊤ xs) a' a f (~ i)) ◁
        (λ i x → Mb.rec a' (Mb.rec a f) (unglue (i ∨ ~ i) x))))
      (commmL-≡0 a a' a'' xs f ◁
       (λ i x → Mb.rec a' (Mb.rec a'' (Mb.rec a f)) (unglue (i ∨ ~ i) x))
       ▷ commmL-≡1 a a' a'' xs f)
      ((λ i →
          mb^ext (map-Maybe (swap0and1Mf (h𝔽in (fm⊤ xs)))) f
          (λ z _ → just (just (just z))) a' a'' a (~ i))
       ◁
       (λ i x → Mb.rec a' (Mb.rec a'' (Mb.rec a f)) (unglue (i ∨ ~ i) x))
       ▷
       mb^ext
       (swap0and1Mf
        (Maybe (fst (h𝔽in (fm⊤ xs))) , isSetMaybe (snd (h𝔽in (fm⊤ xs)))))
       f (λ z _ → just (just (just z))) a' a'' a)

 look-commmpH a a' a'' xs f =
    sqWhisk' _
      _ _ _ _
      _ _ _ _
      (unglue-Sq-elim' (λ i j → i ∨ ~ i)
          (swapMlsq-H-sides (h𝔽in (fm⊤ xs)))
          λ i j → Mb.rec a' (Mb.rec a'' (Mb.rec a f)))
      {mb3≡ refl refl refl refl}
      {mb3≡ refl refl refl refl}
      {mb3≡ refl refl refl refl}
      {mb3≡ refl refl refl refl}
     (congP (λ i → funExt) (funExtDepMb^ 3 (h𝔽in (fm⊤ xs))
       λ { nothing →
            λ { nothing ()
             ; (just (nothing)) _ → PathP∙∙→compPathR' (λ _ _ → a)
             ; (just (just _)) ()
             }
          ; (just (nothing)) →
             λ { nothing _ → PathP∙∙→compPathR' (λ _ _ → a')
               ; (just _) ()
               }
          ; (just (just nothing)) →
            λ { nothing ()
             ; (just (nothing)) ()
             ; (just (just nothing)) _ → PathP∙∙→compPathR' (λ _ _ → a'')
             ; (just (just (just _))) ()
             }
          ; (just (just (just x))) →
             λ { nothing ()
             ; (just (nothing)) ()
             ; (just (just nothing)) ()
             ; (just (just (just x'))) _ →
                  PathP∙∙→compPathR' {p = refl} {q = refl} refl
             }
          }))
        (congP (λ i → funExt) (funExtDepMb^ 3 (h𝔽in (fm⊤ xs))
       λ { nothing →
          λ { nothing _ → refl
          ; (just _) ()}
          ; (just (nothing)) →
             λ { nothing ()
             ; (just (nothing)) ()
             ; (just (just nothing)) _ → PathP∙∙→compPathR' (λ _ _ → a)
             ; (just (just (just _))) ()
             }
          ; (just (just nothing)) →
             λ { nothing ()
              ; (just (nothing)) _ → PathP∙∙→compPathR' (λ _ _ → a')
              ; (just (just nothing)) () }
          ; (just (just (just x))) →
             λ { nothing ()
             ; (just (nothing)) ()
             ; (just (just nothing)) ()
             ; (just (just (just x'))) _ →
                  PathP∙∙→compPathR' {p = refl} {q = refl} refl
             }
          }))
        (congP (λ i → funExt) (funExtDepMb^ 3 (h𝔽in (fm⊤ xs))
         λ { nothing →
            λ { nothing ()
             ; (just (nothing)) _ → PathP∙∙→compPathR' (λ _ _ → a)
             ; (just (just _)) ()
             }

          ; (just (nothing)) →
            λ { nothing ()
             ; (just (nothing)) ()
             ; (just (just nothing)) _ → PathP∙∙→compPathR' (λ _ _ → a')
             ; (just (just (just _))) ()
             }

          ; (just (just nothing)) →
            λ { nothing _ → PathP∙∙→compPathR' (λ _ _ → a'')
             ; (just _) () }

          ; (just (just (just x))) →
             λ { nothing ()
             ; (just (nothing)) ()
             ; (just (just nothing)) ()
             ; (just (just (just x'))) _ →
                  PathP∙∙→compPathR' {p = refl} {q = refl} refl
             }
          }))
          (congP (λ i → funExt) (funExtDepMb^ 3 (h𝔽in (fm⊤ xs))
              λ { nothing →
                   λ { nothing ()
                    ; (just (nothing)) _ → PathP∙∙→compPathR' (λ _ _ → a')
                    ; (just (just _)) ()
                    }

                 ; (just (nothing)) →
                   λ { nothing ()
                    ; (just (nothing)) ()
                    ; (just (just nothing)) _ → PathP∙∙→compPathR' (λ _ _ → a)
                    ; (just (just (just _))) ()
                    }

                 ; (just (just nothing)) →
                   λ { nothing _ → PathP∙∙→compPathR' (λ _ _ → a'')
                    ; (just _) () }

               ; (just (just (just x))) →
                  λ { nothing ()
                  ; (just (nothing)) ()
                  ; (just (just nothing)) ()
                  ; (just (just (just x'))) _ →
                       PathP∙∙→compPathR' {p = refl} {q = refl} refl
                  }
               }))



 
 look-commmpL : (a a' a'' : A) →
       (xs  : FMSet2 A) → (f : 𝔽in (fm⊤ xs) → A) →
     SquareP (λ i j → 𝔽in (fm⊤ (commpL a a' a'' xs i j)) → A)
           (congP (λ z f₁ → Mb.rec a f₁)
            ((λ i → swap-lem (fm⊤ xs) a'' a' f (~ i)) ◁
             (λ i x → Mb.rec a'' (Mb.rec a' f) (unglue (i ∨ ~ i) x))))
           ((λ i → swap-lem (fm⊤ (a'' ∷2 xs)) a' a (Mb.rec a'' f) (~ i)) ◁
            (λ i x → Mb.rec a' (Mb.rec a (Mb.rec a'' f)) (unglue (i ∨ ~ i) x)))
           refl
           (commmL-≡0 a a'' a' xs f ◁
            (λ i x → Mb.rec a'' (Mb.rec a' (Mb.rec a f)) (unglue (i ∨ ~ i) x))
            ▷ commmL-≡1 a a'' a' xs f)
 look-commmpL a a' a'' xs f =
   sqWhisk' _
      _ _ _ _
      _ _ _ _
      (unglue-Sq-elim' (λ i j → i ∨ ~ i ∨ ~ j)
          (swapMlsq-L-sides (h𝔽in (fm⊤ xs)))
          λ i j → Mb.rec a (Mb.rec a' (Mb.rec a'' f)) ∘
                   λ x → swap-braidF (h𝔽in (fm⊤ xs)) x i)
      {mb3≡ refl refl refl refl}
      {mb3≡ refl refl refl refl}
      {mb3≡ refl refl refl refl}
      {mb3≡ refl refl refl refl}
      (
        (mbSqP _ _ _ _ refl
        (congP (λ i → funExt)
          (elimUaSwapPath→ (h𝔽in (fm⊤ xs)) _ _ _
             (flipSquare (PathP∙∙→compPathR (λ _ _ → a')))
             (flipSquare (PathP∙∙→compPathR (λ _ _ → a'')))
             (congP (λ i → funExt⁻)
                ((PathP∙∙→compPathR' (λ _ _ → f))))))))
       (congP (λ i → funExt) (funExtDepMb^ 3 (h𝔽in (fm⊤ xs))
         (Mb.elim _
           (Mb.elim _ (λ ())
             (Mb.elim _ (λ _ → flipSquare (compPathRefl {x = a}))
              (λ _ ())))
           (Mb.elim _ (Mb.elim _ (λ _ → flipSquare (compPathRefl {x = a'}))
             (λ _ ()))
            (Mb.elim _
              (Mb.elim _ (λ ()) (Mb.elim _ (λ ()) (Mb.elim _
                (λ _ → flipSquare (compPathRefl {x = a''})) (λ _ ()))))
              λ _ →
               λ { nothing () 
                 ; (just nothing) () 
                 ; (just (just nothing)) () 
                 ; (just (just (just _))) _ →
                    PathP∙∙→compPathR' {p = refl} {q = refl} refl
                    })))))         
      (mb3sq (λ _ _ → a) (λ _ _ → a') (λ _ _ → a'') λ _ _ → f)
      (congP (λ i → funExt) (funExtDepMb^ 3 (h𝔽in (fm⊤ xs))
         λ { nothing → λ { nothing ()
                   ; (just (nothing)) _ →
                      flipSquare (compPathRefl {x = a})
                   ; (just (just x)) ()}
             ; (just (nothing)) → λ { nothing ()
                   ; (just (nothing)) ()
                   ; (just (just nothing)) _ →
                      flipSquare (compPathRefl {x = a''})
                   ; (just (just (just x))) ()
                   }
             ; (just (just nothing)) → λ { nothing _ →
                      flipSquare (compPathRefl {x = a'})
                   ; (just _) () }
             ; (just (just (just x))) → λ { nothing ()
                   ; (just (nothing)) ()
                   ; (just (just nothing)) ()
                   ; (just (just (just x))) _ →
                     PathP∙∙→compPathR' {p = refl} {q = refl} refl
                   }
             }))
    

 ungluePath-commmR : (a a' a'' : A) →
      (xs  : FMSet2 A) → (f : 𝔽in (fm⊤ xs) → A) →
         PathP (λ i → 𝔽in (fm⊤ (commmR a a' a'' xs i)) → A)
     (Mb.rec a (Mb.rec a'' (Mb.rec a' f))
         ∘ fst (snd (swapMlsq-H-sides (h𝔽in (fm⊤ xs)) i0 i1 1=1)))
          (Mb.rec a (Mb.rec a'' (Mb.rec a' f))
         ∘ fst (snd (swapMlsq-H-sides (h𝔽in (fm⊤ xs)) i1 i1 1=1)))
 ungluePath-commmR a a' a'' xs f i =
    Mb.rec a (Mb.rec a'' (Mb.rec a' f)) ∘
      unglue (i ∨ ~ i)
  
 look-commmpR' : (a a' a'' : A) →
       (xs  : FMSet2 A) → (f : 𝔽in (fm⊤ xs) → A) →
        SquareP (λ _ i → 𝔽in (fm⊤ (commpR a a' a'' xs i i0)) → A)
      (λ i → Mb.rec a (Mb.rec a'' (Mb.rec a' f)) ∘ unglue (i ∨ ~ i ∨ i0))
      (λ i →
         (_◁_▷_ {A = λ i → 𝔽in (fm⊤ (commpR a a' a'' xs i i0)) → A} (λ i₁ →
             mb^ext (map-Maybe (swap0and1Mf (h𝔽in (fm⊤ xs)))) f
             (λ z _ → just (just (just z))) a a'' a' (~ i₁))
          
          (ungluePath-commmR a a' a'' xs f)
          
          (mb^ext
          (swap0and1Mf
           (Maybe (fst (h𝔽in (fm⊤ xs))) , isSetMaybe (snd (h𝔽in (fm⊤ xs)))))
          f (λ z _ → just (just (just z))) a a'' a'))
         i)
      (mb3≡ (λ i → a) (λ i → a') (λ i → a'') (λ i z → f z))
      (λ i → swap-lem (fm⊤ (a' ∷2 xs)) a a'' (Mb.rec a' f) (~ (~ i)))
 look-commmpR' a a' a'' xs f =
           (sqWhisk _  
         (ungluePath-commmR a a' a'' xs f)
           _ (λ _ → Mb.rec a (Mb.rec a'' (Mb.rec a' f)) ∘
                   map-Maybe (swap0and1Mf (h𝔽in (fm⊤ xs))))
                refl
         _ _ _ _
         (λ _ → ungluePath-commmR a a' a'' xs f)
         {p₁₁ = (mb^ext
          (swap0and1Mf
           (Maybe (fst (h𝔽in (fm⊤ xs))) , isSetMaybe (snd (h𝔽in (fm⊤ xs)))))
          f (λ z _ → just (just (just z))) a a'' a')}
         (λ _ → ungluePath-commmR a a' a'' xs f)
         (doubleWhiskFiller
                      (λ i₁ →
             mb^ext (map-Maybe (swap0and1Mf (h𝔽in (fm⊤ xs)))) f
             (λ z _ → just (just (just z))) a a'' a' (~ i₁))
          
          (ungluePath-commmR a a' a'' xs f) 
          (mb^ext
          (swap0and1Mf
           (Maybe (fst (h𝔽in (fm⊤ xs))) , isSetMaybe (snd (h𝔽in (fm⊤ xs)))))
          f (λ z _ → just (just (just z))) a a'' a'))
         (mb3sq refl refl refl refl)
         (mb3sq refl refl refl refl)
         )

 look-commmpR : (a a' a'' : A) →
       (xs  : FMSet2 A) → (f : 𝔽in (fm⊤ xs) → A) →
        SquareP (λ i j → 𝔽in (fm⊤ (commpR a a' a'' xs i j)) → A)
      (congP (λ z f₁ → Mb.rec a f₁)
       ((λ i → swap-lem (fm⊤ xs) a'' a' f (~ i)) ◁
        (λ i x → Mb.rec a'' (Mb.rec a' f) (unglue (i ∨ ~ i) x))))
      ((λ i → swap-lem (fm⊤ (a' ∷2 xs)) a a'' (Mb.rec a' f) (~ i)) ◁
       (λ i x → Mb.rec a (Mb.rec a'' (Mb.rec a' f)) (unglue (i ∨ ~ i) x)))
      ((λ i →
          mb^ext (map-Maybe (swap0and1Mf (h𝔽in (fm⊤ xs)))) f
          (λ z _ → just (just (just z))) a a'' a' (~ i))
       ◁
       (λ i x → Mb.rec a (Mb.rec a'' (Mb.rec a' f)) (unglue (i ∨ ~ i) x))
       ▷
       mb^ext
       (swap0and1Mf
        (Maybe (fst (h𝔽in (fm⊤ xs))) , isSetMaybe (snd (h𝔽in (fm⊤ xs)))))
       f (λ z _ → just (just (just z))) a a'' a')
      refl
 look-commmpR a a' a'' xs f =
     sqWhisk (λ z j → 𝔽in (fm⊤ (commpR a a' a'' xs z j)) → A)
       _ _ _ _
       _ _ _ _
       (unglue-Sq-elim' (λ i j → i ∨ ~ i ∨ j)
          (swapMlsq-R-sides (h𝔽in (fm⊤ xs)))
          λ i j → Mb.rec a (Mb.rec a'' (Mb.rec a' f)) )
       {mb3≡ refl refl refl refl}
       {mb3≡ refl refl refl refl}
       
       (sqWhisk _
           _ _
           sqI0L
           sqI0R
          _ _ _ _
          sqI0
         {refl} {refl}
         refl
         (congSqP (λ _ _ → Mb.rec a)
            (doubleWhiskFiller (sym (swap-lem (fm⊤ xs) a'' a' f))
                  (λ i x → Mb.rec a'' (Mb.rec a' f) (unglue (i ∨ ~ i) x))
                  refl))
         (mb3sq refl refl refl refl)
         (mb3sq refl refl refl refl)
         )
       (doubleWhiskFiller
             (λ i → swap-lem (fm⊤ (a' ∷2 xs)) a a'' (Mb.rec a' f) (~ i))
             (λ i x → Mb.rec a (Mb.rec a'' (Mb.rec a' f)) (unglue (i ∨ ~ i) x))
             refl)
       (look-commmpR' a a' a'' xs f)

       (mb3sq refl refl refl refl)
   where
    sqI0 : SquareP
         (λ _ j → 𝔽in (fm⊤ (commpR a a' a'' xs i0 j)) → A)
         _ _ _ _
    sqI0 i j nothing = a
    sqI0 i j (just x) = Mb.rec a'' (Mb.rec a' f)
      (ua-ungluePathExt (swap0and1M (h𝔽in (fm⊤ xs))) j x)
      
    sqI0L : _ ≡ _
    sqI0L i nothing = a
    sqI0L i (just x) = Mb.rec a'' (Mb.rec a' f)
          (swap0and1Mf
            ((h𝔽in (fm⊤ xs))) x)


    sqI0R : _ ≡ _
    sqI0R i nothing = a
    sqI0R i (just x) = Mb.rec a'' (Mb.rec a' f) x

 RFM2look' : RElim {A = A} (λ xs → 𝔽in (fm⊤ xs) → A)
 RElim.[]* RFM2look' ()
 (RFM2look' RElim.∷* a) f = Mb.rec a f
 RElim.comm* RFM2look' a a' {xs} f =
   sym (swap-lem (fm⊤ xs) a' a f)
   ◁ (λ i x → Mb.rec a' (Mb.rec a f) (unglue (i ∨ ~ i) x))
     
 RElim.comm-inv* RFM2look' a a' {xs} f i j = 
    ((λ j → (swap-lem (fm⊤ xs) a' a f) (~ (j ∧ ~ i)))
     ◁ comm-inv→sq  _ _ a a' (fm⊤ xs) f i ▷
      λ j → (swap-lem (fm⊤ xs) a a' f ((j ∨  ~ i) ))) j

 RElim.commmL* RFM2look' a a' a'' {xs} f = 
     commmL-≡0 a a' a'' xs f ◁
       (λ i x → Mb.rec a' (Mb.rec a'' (Mb.rec a f)) (unglue (i ∨ ~ i) x))
       ▷ commmL-≡1 a a' a'' xs f
 RElim.commmR* RFM2look' a a' a'' {xs} f = 
     sym (mb^ext (map-Maybe (swap0and1Mf (h𝔽in (fm⊤ xs))))
                     f (λ _ → refl) a a'' a') ◁
       (λ i x → Mb.rec a (Mb.rec a'' (Mb.rec a' f)) (unglue (i ∨ ~ i) x))
       ▷  (mb^ext ((swap0and1Mf (Mb^ 1 (h𝔽in (fm⊤ xs)))))
                     f (λ _ → refl) a a'' a')
 RElim.commpL* RFM2look' a a' a'' {xs} f = look-commmpL a a' a'' xs f
 RElim.commpR* RFM2look' a a' a'' {xs} f = look-commmpR a a' a'' xs f   
 RElim.hex* RFM2look' a a' a'' {xs} f = look-commmpH a a' a'' xs f
 RElim.trunc* RFM2look' xs = isGroupoidΠ λ _ → isGroupoidA

 FM2look' : ∀ xs → 𝔽in (fm⊤ xs) → A
 FM2look' = RElim.f RFM2look'

 lt-ret : RElimSet' λ (xs : FMSet2 A) → fm2tab (fm⊤ xs) (FM2look' xs) ≡ xs 
 RElimSet'.[]* lt-ret = refl
 (lt-ret RElimSet'.∷* a) {xs} p = cong (a ∷2_) p
 RElimSet'.comm* lt-ret a a' {xs} p i j =
    hcomp (λ z → primPOr (i ∨ ~ i ∨ j) (~ j) (λ _ → (comm a a' (p j) i))
     λ _ → comm
     (compPathRefl {x = a} z i)
     (compPathRefl {x = a'} z i)
     (fm2tab (fm⊤ xs) (compPathRefl {x = FM2look' xs} z i)) i)
     (comm a a' (p j) i)

 RElimSet'.trunc* lt-ret _ = trunc _ _

 lt-sec-fst : RElimSet' λ (xs : FMSet2 Unit) →
       ∀ f → Path (FMSet2 Unit)
         (fm⊤ (fm2tab xs f))
         (xs)
 RElimSet'.[]* lt-sec-fst f = refl
 (lt-sec-fst RElimSet'.∷* tt) p f =
   cong (tt ∷2_) (p _)
 RElimSet'.comm* lt-sec-fst x y {xs} b i f j =
   comm tt tt
     (b (f ∘ ua-gluePathExt (PCI.e {B = Unit} {A = A} xs) i ∘ just ∘ just) j) i
 RElimSet'.trunc* lt-sec-fst _ = isSetΠ λ _ → trunc _ _

 ∷-sec-snd : (x : Unit) {xs : FMSet2 Unit} →
      PathP
      (λ j → (f : 𝔽in xs → A) → 𝔽in (RElimSet'.f lt-sec-fst xs f j) → A)
      (λ f → FM2look' (fm2tab xs f)) (idfun (𝔽in xs → A)) →
      PathP
      (λ j →
         (f : 𝔽in (x ∷2 xs) → A) →
         𝔽in (RElimSet'.f lt-sec-fst (x ∷2 xs) f j) → A)
      (λ f → FM2look' (fm2tab (x ∷2 xs) f)) (idfun (𝔽in (x ∷2 xs) → A))
 ∷-sec-snd x {xs} p i f nothing = f nothing
 ∷-sec-snd x {xs} p i f (just x₁) = p i (f ∘ just) x₁ 


 comm-sec-snd-bot : (x y : Unit) {xs : FMSet2 Unit} →
          (X
       : PathP
         (λ j → (f : 𝔽in xs → A) → 𝔽in (RElimSet'.f lt-sec-fst xs f j) → A)
         (λ f → FM2look' (fm2tab xs f)) (idfun (𝔽in xs → A))) →
         SquareP (λ i j →  (f : 𝔽in (comm x y xs i) → A) →
            𝔽in (RElimSet'.f lt-sec-fst (comm x y xs i) f j) → A)
            (λ j f x' →
               (Mb.rec (f (just nothing))
                  (Mb.rec (f (nothing)) (X j (f ∘ just ∘ just)))) 
                   (swap0and1Mf
                      (RRec.f Rh𝔽in
                       (RElim.f (RElimSet'.fR lt-sec-fst) xs
                        (λ x → f (just (just x))) j))
                      x'))
            (λ j f x' → (Mb.rec (f (nothing))
                  (Mb.rec (f (just nothing)) (X j (f ∘ just ∘ just)))) 
                   x')
            (λ i f x' → Mb.rec ((f ∘ (ua-gluePathExt (swap0and1M (h𝔽in xs)) i))
                      (just nothing))
                (Mb.rec ((f ∘ (ua-gluePathExt (swap0and1M (h𝔽in xs)) i)) nothing) ((X i0 ((f ∘ ua-gluePathExt
                       (PCI.e {B = Unit} {A = A} xs) i ∘ just ∘ just)))))
                ((ua-unglue (swap0and1M (h𝔽in
                   (RElimSet'.f lt-sec-fst xs
                     (f ∘ ua-gluePathExt
                       (PCI.e {B = Unit} {A = A} xs) i ∘ just ∘ just) i0))) i
               x')))
            (swap0and1MfunSq A (h𝔽in xs) i0)
 comm-sec-snd-bot x y {xs} X i j f x' =
   (let f' = f ∘ (ua-gluePathExt (swap0and1M (h𝔽in xs)) i)
       in Mb.rec (f' (just nothing))
          (Mb.rec (f' nothing) (X j ((f ∘ ua-gluePathExt
                       (PCI.e {B = Unit} {A = A} xs) i ∘ just ∘ just))))
            (ua-unglue (swap0and1M (h𝔽in
                   (RElimSet'.f lt-sec-fst xs
                     (f ∘ ua-gluePathExt
                       (PCI.e {B = Unit} {A = A} xs) i ∘ just ∘ just) j))) i
               x')) 


 comm-sec-sndI1 : (x y : Unit) {xs : FMSet2 Unit}
      (X
       : PathP
         (λ j → (f : 𝔽in xs → A) → 𝔽in (RElimSet'.f lt-sec-fst xs f j) → A)
         (λ f → FM2look' (fm2tab xs f)) (idfun (𝔽in xs → A))) →
      SquareP (λ z j →  (f : 𝔽in (comm x y xs i1) → A) →
            𝔽in (RElimSet'.f lt-sec-fst (comm x y xs i1) f j) → A)
          (comm-sec-snd-bot x y {xs} X i1)
          ((∷-sec-snd y {_ ∷2 xs} (∷-sec-snd x {xs} X)))
          refl
          λ z → swap0and1MfunSq A (h𝔽in xs) z i1 
 comm-sec-sndI1 x y {xs} X z j f nothing = f nothing
 comm-sec-sndI1 x y {xs} X z j f (just nothing) = f (just nothing)
 comm-sec-sndI1 x y {xs} X z j f (just (just x₁)) =
   X j (λ x₂ → f (just (just x₂))) x₁


 comm-sec-sndI0 : (x y : Unit) {xs : FMSet2 Unit}
      (X
       : PathP
         (λ j → (f : 𝔽in xs → A) → 𝔽in (RElimSet'.f lt-sec-fst xs f j) → A)
         (λ f → FM2look' (fm2tab xs f)) (idfun (𝔽in xs → A))) →
      SquareP (λ z j →  (f : 𝔽in (comm x y xs i0) → A) →
            𝔽in (RElimSet'.f lt-sec-fst (comm x y xs i0) f j) → A)
          (comm-sec-snd-bot x y {xs} X i0)
          ((∷-sec-snd x {_ ∷2 xs} (∷-sec-snd x {xs} X)))
          (λ z f x' → swap-lem
             (fm⊤ ((fm2tab (xs) (f ∘ just ∘ just))))
                (f (just nothing)) (f nothing)
               (X i0 (f ∘ just ∘ just)) z x')
          λ z → swap0and1MfunSq A (h𝔽in xs) z i0

 comm-sec-sndI0 x y {xs} X i j f nothing = f nothing
 comm-sec-sndI0 x y {xs} X i j f (just nothing) = f (just nothing)
 comm-sec-sndI0 x y {xs} X i j f (just (just x₁)) =
   X j (λ x₂ → f (just (just x₂))) x₁
   

 comm-sec-snd : (x y : Unit) {xs : FMSet2 Unit}
      (X
       : PathP
         (λ j → (f : 𝔽in xs → A) → 𝔽in (RElimSet'.f lt-sec-fst xs f j) → A)
         (λ f → FM2look' (fm2tab xs f)) (idfun (𝔽in xs → A))) →
      PathP
      (λ i →
         PathP
         (λ j →
            (f : 𝔽in (comm x y xs i) → A) →
            𝔽in (RElimSet'.f lt-sec-fst (comm x y xs i) f j) → A)
         (λ f → FM2look' (fm2tab (comm x y xs i) f))
         (idfun (𝔽in (comm x y xs i) → A)))
      (∷-sec-snd x {_ ∷2 xs} (∷-sec-snd y {xs} X))
      (∷-sec-snd y {_ ∷2 xs} (∷-sec-snd x {xs} X))
 comm-sec-snd x y {xs} X =
   λ i j f x' →
            hcomp
          (λ z → λ {
           (i = i0) → comm-sec-sndI0 x y {xs} X z j f x'
          ;(i = i1) → comm-sec-sndI1 x y {xs} X z j f x'
          ;(j = i1) → swap0and1MfunSq A (h𝔽in xs) z i f x'
           }) (comm-sec-snd-bot x y {xs} X i j f x')


 -- comm-sec-sndI0 x y {xs} X i j f nothing = f nothing
 -- comm-sec-sndI0 x y {xs} X i j f (just nothing) = f (just nothing)
 -- comm-sec-sndI0 x y {xs} X i j f (just (just x₁)) =
 --   X j (λ x₂ → f (just (just x₂))) x₁
   
 --  comm-sec-sndI1 x y {xs} X z j f nothing = f nothing
 -- comm-sec-sndI1 x y {xs} X z j f (just nothing) = f (just nothing)
 -- comm-sec-sndI1 x y {xs} X z j f (just (just x₁)) =
 --   X j (λ x₂ → f (just (just x₂))) x₁
        

 lt-sec-snd : RElimSet' λ  (xs : FMSet2 Unit) →
       PathP
         (λ j → (f : 𝔽in xs → A) → 𝔽in (RElimSet'.f lt-sec-fst xs f j) → A)
          (λ f → FM2look' (fm2tab xs f))
          (idfun _)
 RElimSet'.[]* lt-sec-snd j f ()
 RElimSet'._∷*_ lt-sec-snd = ∷-sec-snd
 RElimSet'.comm* lt-sec-snd = comm-sec-snd
 RElimSet'.trunc* lt-sec-snd xs =
   isOfHLevelRespectEquiv 2 (invEquiv (PathP≃Path _ _ _))
     (isGroupoidΠ (λ _ → isGroupoidΠ λ _ → isGroupoidA) _ _)

 look-tab-Iso : Iso (FMSet2 A) (Σ𝔽→ A) --(Σ (FMSet2 Unit) λ xs → 𝔽in xs → A)
 Iso.fun look-tab-Iso xs = fm⊤ xs , FM2look' xs
 Iso.inv look-tab-Iso = uncurry fm2tab
 Iso.rightInv look-tab-Iso =
    uncurry λ xs f → ΣPathP
     (RElimSet'.f lt-sec-fst xs f ,
      λ i → RElimSet'.f lt-sec-snd xs i f)
 Iso.leftInv look-tab-Iso = RElimSet'.f lt-ret





