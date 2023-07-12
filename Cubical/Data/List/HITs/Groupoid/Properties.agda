{-# OPTIONS --safe #-}

module Cubical.Data.List.HIT2PProperties where

open import Cubical.Foundations.Everything
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sigma hiding (Σ-assoc-≃)
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Empty renaming (elim to ⊥elim ; rec to ⊥rec)

open import Cubical.Functions.FunExtEquiv

open import Cubical.Relation.Nullary


import Cubical.Data.List.Base as B
import Cubical.Data.List.Properties as BP


import Cubical.Functions.Logic as L


open import Cubical.Data.List.HIT2P

open import Cubical.Data.Sigma.Nested.SigmaCoh

open import Cubical.HITs.GroupoidTruncation renaming (elim to elim₃; rec to rec₃)

open import Cubical.Foundations.Equiv.Fiberwise

open import Cubical.Data.Sigma.Nested.SlipOutLemmasLean

open import Cubical.Reflection.StrictEquiv

open Iso



private
  variable
    ℓ : Level
    A : Type ℓ


fromList : B.List A → List A
fromList B.[] = []
fromList (x B.∷ xs) = x ∷ fromList xs


cong₂-∙-fst : {A B C : Type ℓ}
        → (f : A → B → C) {x x' x'' : A} {y y' : B}
        → (p : x ≡ x') (p' : x' ≡ x'') → (q : y ≡ y') 
        →  cong₂ f (p ∙ p') q ≡ cong (λ x → f x y) p ∙ (λ i → f (p' i) (q i))  
cong₂-∙-fst f p p' q i j =
   hcomp
     (λ k → λ { (i = i0) → f
                          (compPath-filler p p' k j)
                          (q (j ∧ k))
               ; (j = i0) → f (p i0) (q i0)
               ; (j = i1) → f (p' k) (q k)
               }) (f (p j) (q i0) ) 

module _ (isGroupoidA : isGroupoid A) where

  isGroupoidListA = BP.isOfHLevelList 1 isGroupoidA

  toList : List A → B.List A
  toList =
    Elim.f
     (λ _ → isGroupoidListA)
     B.[] B.[_] B._++_ BP.++-unit-r (λ _ → refl) BP.++-assoc
     (B.elimL (λ _ → refl) λ {a} → congSqP (λ _ _ → a B.∷_) ∘_)
     (B.elimL (BP.++-assoc) λ {a} {l} f _ _ → cong (a B.∷_) ∘ (f _ _))
     (B.elimL (λ by bz bw i j → BP.++-assoc by bz bw (j ∨ (~ i)))
       (λ {a} x _ _ → congSqP (λ _ _ → a B.∷_) ∘ (x _ _)))
     (B.elimL (λ by bz bw i j → BP.++-assoc by bz bw (j ∧ (~ i)))
       λ {a} x _ _ _ → congSqP (λ _ _ → a B.∷_) (x _ _ _))
     
  toList-fromList : ∀ l → toList (fromList l) ≡ l
  toList-fromList B.[] = refl
  toList-fromList (_ B.∷ l) = cong (_ B.∷_) (toList-fromList l)

  fromList-toList : ∀ l → fromList (toList l) ≡ l
  fromList-toList =
     ElimSet.f (λ _ → trunc _ _)
       refl
       (++-unit-r ∘ [_])
       (λ {xs} {ys} x y → h _ _ ∙ cong₂ _++_ x y)
       h1
       (λ b i j → hcomp
         (λ k →
           λ { (i = i1) → b (j ∧ k)
             ; (j = i0) → fromList (toList (b i1))
             ; (j = i1) → ++-unit-l (b k) i
              }) (++-unit-l (b i0) (i ∨  ~ j)))
       h3
  
   where

     h : ∀ (xs ys : B.List A) →
          fromList (xs B.++ ys) ≡ fromList xs ++ fromList ys 
     h = B.elimL (sym ∘ ++-unit-l ∘ fromList)
             ((_∙ (sym (++-assoc _ _ _)) ∘ cong (_ ∷_ )) ∘_)

     h1'' : (xs : B.List A) → 
             Square
               (h xs B.[])
               (refl {x = fromList xs})
               (cong fromList (BP.++-unit-r xs))
               (++-unit-r (fromList xs))
     h1'' B.[] i j = lem-pqr' {p = refl} {q = sym (++-unit-l [])} {sym (++-unit-r [])}
          (cong sym (sym ++-unit-lr[])) (~ i) j
        
     h1'' xs'@(x B.∷ xs) i j = 
       hcomp
         (λ k →
           λ { (i = i1) → fromList xs'
             ; (j = i0) → cong fromList (BP.++-unit-r xs') i
             ; (j = i1) → lawCool-r [ x ] (fromList xs) i (~ k)
              })
         ([ x ] ++ h1'' xs i j)

     
     h1 : {xs : List A} (b : fromList (toList xs) ≡ xs) → _
     h1 b i j =
       hcomp (λ k →
           λ { (i = i1) → b (j ∧ k)
             ; (j = i0) → fromList (BP.++-unit-r (toList (b i1)) i)
             ; (j = i1) → ++-unit-r (b k) i
              }) (h1'' (toList (b i1)) i j)

     h3' : (xs ys zs : B.List A) →
      Square
        (h (xs B.++ ys) zs ∙ cong (_++ _) (h xs ys))
        (h xs (ys B.++ zs) ∙ cong (_ ++_) (h ys zs))
        (cong (fromList) (BP.++-assoc xs ys zs))
        (++-assoc _ _ _)
     h3' B.[] by bz i j = hcomp
              (λ k → λ { (i = i1) →
                          hcomp
                          (λ l → λ { (k = i0) → (h by bz) (j ∧ l)
                                   ; (j = i0) → fromList (by B.++ bz)
                                   ; (j = i1) → ++-unit-l (h by bz l) (~ k)
                                   }) (++-unit-l (fromList (by B.++ bz)) (~ k ∨ ~ j))

                       ; (j = i0) → fromList (by B.++ bz)
                       ; (j = i1) → lawCool-l (fromList by) (fromList bz) (~ k) i
                       })
              (h by bz (j))

     h3' (x B.∷ bx) by bz = zz

        where

          zzPrev : Square
                     (h (bx B.++ by) bz ∙ cong (_++ fromList bz) (h bx by))
                     (h bx (by B.++ bz) ∙ cong (_++_ (fromList bx)) (h by bz))
                     (cong fromList (BP.++-assoc bx by bz))
                     (++-assoc (fromList bx) (fromList by) (fromList bz))
          zzPrev =
            h3' bx by bz
          


          -- zzPentU : PathP
          --             (λ i →
          --                sym (++-assoc ([ x ] ++ fromList bx) (fromList by) (fromList bz)) i
          --                ≡ ++-assoc [ x ] (fromList bx) (fromList by ++ fromList bz) i)
          --             refl
          --             (++-pentagon-diag [ x ] (fromList bx) (fromList by) (fromList bz))
          -- zzPentU =
          --   ++-pentagon-△
          --     [ x ]
          --     (fromList bx)
          --     (fromList by)
          --     (fromList bz)

          zz0' : ((λ i → [ x ] ++ h (bx B.++ by) bz i))
                  ∙ (sym (++-assoc [ x ] (fromList (bx B.++ by)) (fromList bz))) ∙
                   cong (_++ fromList bz) (λ i → [ x ] ++ h bx by i)
                    ≡
                  cong ([ x ] ++_) ((h _ bz ∙ cong (_++ _) (h bx by)))
                     ∙ sym (++-assoc _ _ _) 
          zz0' =
            cong ((λ i → [ x ] ++ h (bx B.++ by) bz i) ∙_)
              (homotopyNatural (λ a i → ++-assoc [ x ] a (fromList bz) (~ i))
                (λ i → h bx by i))
             ∙ assoc _ _ _ ∙
              cong (_∙ (sym (++-assoc _ _ _)))
                (sym (cong-∙ ([ x ] ++_) _ _)) 

          zz0 : (((λ i → [ x ] ++ h (bx B.++ by) bz i) ∙
                  (λ i → ++-assoc [ x ] (fromList (bx B.++ by)) (fromList bz) (~ i)))
                 ∙
                 cong (_++ fromList bz)
                 ((λ i → [ x ] ++ h bx by i) ∙
                  (λ i → ++-assoc [ x ] (fromList bx) (fromList by) (~ i))))
                  ≡ cong ([ x ] ++_) 
                               ((h _ bz ∙ cong (_++ _) (h bx by)))
                      ∙∙
                       (cong ([ x ] ++_) (++-assoc _ _ _)
                         ∙' sym (++-assoc [ x ] (fromList bx) (fromList by ++ fromList bz)))
                       ∙∙ sym (++-assoc ([ x ] ++ fromList bx) (fromList by) (fromList bz))
          zz0 =
             cong₂ _∙_ refl (cong-∙ ((_++ fromList bz)) _ _)
              ∙ assoc _ _ _ ∙
               cong (_∙ cong (_++ fromList bz)
                  (λ i → ++-assoc [ x ] (fromList bx) (fromList by) (~ i)))
                   (sym (assoc _ _ _) ∙ zz0')
                ∙ sym (assoc _ _ _) ∙
                 cong ((λ i → cong ([ x ] ++_)
                    (h (bx B.++ by) bz ∙ cong (_++ fromList bz) (h bx by)) i) ∙_)
                     {!!}
                ∙ sym (doubleCompPath-elim'
                     (cong ([ x ] ++_) 
                               ((h _ bz ∙ cong (_++ _) (h bx by))))
                     ((cong ([ x ] ++_) (++-assoc _ _ _)
                         ∙' sym (++-assoc [ x ] (fromList bx) (fromList by ++ fromList bz))))
                     (sym (++-assoc ([ x ] ++ fromList bx) (fromList by) (fromList bz))))
         

          zz1 : (((λ i → [ x ] ++ h bx (by B.++ bz) i) ∙
                  (λ i → ++-assoc [ x ] (fromList bx) (fromList (by B.++ bz)) (~ i)))
                 ∙ cong (_++_ (x ∷ fromList bx)) (h by bz))
                  ≡ (cong ([ x ] ++_) ( h bx _ ∙ cong (_ ++_) (h by bz)) 
                      ∙' sym (++-assoc [ x ] (fromList bx) (fromList by ++ fromList bz)))
          zz1 =
            sym (assoc _ _ _)
            ∙ cong ((λ i → [ x ] ++ h bx (by B.++ bz) i) ∙_)
              (homotopyNatural (sym ∘ ++-assoc [ x ] (fromList bx)) (h by bz))
            ∙
            assoc _ _ _
            ∙
            λ i j → leftright (sym (cong-∙ ([ x ] ++_)
                     (h bx _) (cong (_ ++_) (h by bz))) i)
              (sym (++-assoc [ x ] (fromList bx) (fromList by ++ fromList bz))) i j



          zz : Square
                (((λ i → [ x ] ++ h (bx B.++ by) bz i) ∙
                  (λ i → ++-assoc [ x ] (fromList (bx B.++ by)) (fromList bz) (~ i)))
                 ∙
                 cong (_++ fromList bz)
                 ((λ i → [ x ] ++ h bx by i) ∙
                  (λ i → ++-assoc [ x ] (fromList bx) (fromList by) (~ i))))
                  
                (((λ i → [ x ] ++ h bx (by B.++ bz) i) ∙
                  (λ i → ++-assoc [ x ] (fromList bx) (fromList (by B.++ bz)) (~ i)))
                 ∙ cong (_++_ (x ∷ fromList bx)) (h by bz))
                 
                (cong fromList (λ i → x B.∷ BP.++-assoc bx by bz i))
                (++-assoc (x ∷ fromList bx) (fromList by) (fromList bz))
          zz =
            zz0 ◁
              (λ i →
               cong ([ x ] ++_) (zzPrev i)
                 ∙∙ doubleCompPath-filler
                        (cong ([ x ] ++_) (++-assoc _ _ _))
                        (sym (++-assoc [ x ] (fromList bx) (fromList by ++ fromList bz)))
                        refl (~ i)
                 ∙∙ λ j → (++-assoc (x ∷ fromList bx) (fromList by) (fromList bz)) (i ∨ ~ j))
            ▷ sym zz1


     h3 : {xs ys zs : List A} (bx : fromList (toList xs) ≡ xs)
      (by : fromList (toList ys) ≡ ys) (bz : fromList (toList zs) ≡ zs) →
      _
      -- Square
      --   (h (toList (xs ++ ys)) (toList zs)
      --     ∙ cong₂ _++_ (h (toList xs) (toList ys) ∙ cong₂ _++_ bx by) bz)
      --   (h (toList xs) (toList (ys ++ zs))
      --     ∙ cong₂ _++_ bx (h (toList ys) (toList zs) ∙ cong₂ _++_ by bz))
      --   (cong (fromList) (BP.++-assoc (toList xs) (toList ys) (toList zs)))
      --   (++-assoc xs ys zs)
     h3 bx by bz =
       (cong ((h (toList (bx i1 ++ by i1)) (toList (bz i1))) ∙_)
          (cong₂-∙-fst _++_ _ (cong₂ _++_ bx by) bz))
           ∙ assoc _ _ _ ◁
          (λ i →
            (h3' (toList (bx i1)) (toList (by i1)) (toList (bz i1)) i)
            ∙ λ j → ++-assoc (bx j) (by j) (bz j) i)
       ▷ (sym (assoc _ _ _)
         ∙ cong ((h (toList (bx i1)) (toList (by i1 ++ bz i1))) ∙_)
           (sym (cong₂-∙'' _++_ _ _ _)))
       

  -- isoList : Iso (List A) (B.List A)
  -- fun isoList = toList
  -- inv isoList = fromList
  -- rightInv isoList = toList-fromList
  -- leftInv isoList = fromList-toList


  -- fromList-toList : ∀ l → fromList (toList l) ≡ l
  -- fromList-toList =
  --    ElimSet.f (λ _ → trunc _ _)
  --      refl
  --      (++-unit-r ∘ [_])
  --      (λ {xs} {ys} x y →
  --        h _ _ ∙ cong₂ _++_ x y)
  --      h1
  --      (λ b i j → hcomp
  --        (λ k →
  --          λ { (i = i1) → b (j ∧ k)
  --            ; (j = i0) → fromList (toList (b i1))
  --            ; (j = i1) → ++-unit-l (b k) i
  --             })
  --        (++-unit-l (b i0) (i ∨  ~ j)))
  --      h3
  
  --  where

  --    h : ∀ (xs ys : B.List A) →
  --         fromList (xs B.++ ys) ≡ fromList xs ++ fromList ys 
  --    h = B.elimL (sym ∘ ++-unit-l ∘ fromList)
  --            ((_∙ (sym (++-assoc _ _ _)) ∘ cong (_ ∷_ )) ∘_)

  --    h1'' : (xs : B.List A) → 
  --            Square
  --              (h xs B.[])
  --              (refl {x = fromList xs})
  --              (cong fromList (BP.++-unit-r xs))
  --              (++-unit-r (fromList xs))
  --    h1'' B.[] i j = lem-pqr' {p = refl} {q = sym (++-unit-l [])} {sym (++-unit-r [])}
  --         (cong sym (sym ++-unit-lr[])) (~ i) j
        
  --    h1'' xs'@(x B.∷ xs) i j = 
  --      hcomp
  --        (λ k →
  --          λ { (i = i1) → fromList xs'
  --            ; (j = i0) → cong fromList (BP.++-unit-r xs') i
  --            ; (j = i1) → lawCool-r [ x ] (fromList xs) i (~ k)
  --             })
  --        ([ x ] ++ h1'' xs i j)

     
  --    h1 : {xs : List A} (b : fromList (toList xs) ≡ xs) → _
  --    h1 b i j =
  --      hcomp
  --        (λ k →
  --          λ { (i = i1) → b (j ∧ k)
  --            ; (j = i0) → fromList (BP.++-unit-r (toList (b i1)) i)
  --            ; (j = i1) → ++-unit-r (b k) i
  --             })
  --        (h1'' (toList (b i1)) i j)

  --    -- h2 : {xs : List A} (b : fromList (toList xs) ≡ xs) → _
  --    -- h2 {xs} b i j =
  --    --    hcomp
  --    --     (λ k →
  --    --       λ { (i = i1) → b (j ∧ k)
  --    --         ; (j = i0) → fromList (toList (b i1))
  --    --         ; (j = i1) → ++-unit-l (b k) i
  --    --          })
  --    --     (++-unit-l (b i0) (i ∨  ~ j))



  --    h3' : (xs ys zs : B.List A) →
  --     Square
  --       (h (xs B.++ ys) zs ∙ cong (_++ _) (h xs ys))
  --       (h xs (ys B.++ zs) ∙ cong (_ ++_) (h ys zs))
  --       (cong (fromList) (BP.++-assoc xs ys zs))
  --       (++-assoc _ _ _)
  --    h3' B.[] by bz = {!by!}
  --    h3' (x B.∷ bx) by bz = zz


  --       where

  --         zzPrev : Square
  --                    (h (bx B.++ by) bz ∙ cong (_++ fromList bz) (h bx by))
  --                    (h bx (by B.++ bz) ∙ cong (_++_ (fromList bx)) (h by bz))
  --                    (cong fromList (BP.++-assoc bx by bz))
  --                    (++-assoc (fromList bx) (fromList by) (fromList bz))
  --         zzPrev =
  --           h3' bx by bz
          


  --         zzPentU : PathP
  --                     (λ i →
  --                        sym (++-assoc ([ x ] ++ fromList bx) (fromList by) (fromList bz)) i
  --                        ≡ ++-assoc [ x ] (fromList bx) (fromList by ++ fromList bz) i)
  --                     refl
  --                     (++-pentagon-diag [ x ] (fromList bx) (fromList by) (fromList bz))
  --         zzPentU =
  --           ++-pentagon-△
  --             [ x ]
  --             (fromList bx)
  --             (fromList by)
  --             (fromList bz)

  --         zz0' : ((λ i → [ x ] ++ h (bx B.++ by) bz i))
  --                 ∙ (sym (++-assoc [ x ] (fromList (bx B.++ by)) (fromList bz))) ∙
  --                  cong (_++ fromList bz) (λ i → [ x ] ++ h bx by i)
  --                   ≡
  --                 cong ([ x ] ++_) ((h _ bz ∙ cong (_++ _) (h bx by)))
  --                    ∙ sym (++-assoc _ _ _) 
  --         zz0' =
  --           cong ((λ i → [ x ] ++ h (bx B.++ by) bz i) ∙_)
  --             (homotopyNatural (λ a i → ++-assoc [ x ] a (fromList bz) (~ i))
  --               (λ i → h bx by i))
  --            ∙ assoc _ _ _ ∙
  --             cong (_∙ (sym (++-assoc _ _ _)))
  --               (sym (cong-∙ ([ x ] ++_) _ _)) 

  --         zz0 : (((λ i → [ x ] ++ h (bx B.++ by) bz i) ∙
  --                 (λ i → ++-assoc [ x ] (fromList (bx B.++ by)) (fromList bz) (~ i)))
  --                ∙
  --                cong (_++ fromList bz)
  --                ((λ i → [ x ] ++ h bx by i) ∙
  --                 (λ i → ++-assoc [ x ] (fromList bx) (fromList by) (~ i))))
  --                 ≡ cong ([ x ] ++_) 
  --                              ((h _ bz ∙ cong (_++ _) (h bx by)))
  --                     ∙∙
  --                      (cong ([ x ] ++_) (++-assoc _ _ _)
  --                        ∙' sym (++-assoc [ x ] (fromList bx) (fromList by ++ fromList bz)))
  --                      ∙∙ sym (++-assoc ([ x ] ++ fromList bx) (fromList by) (fromList bz))
  --         zz0 =
  --            cong₂ _∙_ refl (cong-∙ ((_++ fromList bz)) _ _)
  --             ∙ assoc _ _ _ ∙
  --              cong (_∙ cong (_++ fromList bz)
  --                 (λ i → ++-assoc [ x ] (fromList bx) (fromList by) (~ i)))
  --                  (sym (assoc _ _ _) ∙ zz0')
  --               ∙ sym (assoc _ _ _) ∙
  --                cong ((λ i → cong ([ x ] ++_)
  --                   (h (bx B.++ by) bz ∙ cong (_++ fromList bz) (h bx by)) i) ∙_)
  --                    {!!}
  --               ∙ sym (doubleCompPath-elim'
  --                    (cong ([ x ] ++_) 
  --                              ((h _ bz ∙ cong (_++ _) (h bx by))))
  --                    ((cong ([ x ] ++_) (++-assoc _ _ _)
  --                        ∙' sym (++-assoc [ x ] (fromList bx) (fromList by ++ fromList bz))))
  --                    (sym (++-assoc ([ x ] ++ fromList bx) (fromList by) (fromList bz))))
         

  --         zz1 : (((λ i → [ x ] ++ h bx (by B.++ bz) i) ∙
  --                 (λ i → ++-assoc [ x ] (fromList bx) (fromList (by B.++ bz)) (~ i)))
  --                ∙ cong (_++_ (x ∷ fromList bx)) (h by bz))
  --                 ≡ (cong ([ x ] ++_) ( h bx _ ∙ cong (_ ++_) (h by bz)) 
  --                     ∙' sym (++-assoc [ x ] (fromList bx) (fromList by ++ fromList bz)))
  --         zz1 =
  --           {!!}
  --           ∙
  --           {!!}
  --           ∙
  --           {!!}
  --           -- cong (λ z → (cong ([ x ] ++_) ( h bx _ ∙ cong (_ ++_) (h by bz)) 
  --           --           ∙' (λ i → sym (++-assoc [ x ] (fromList bx) {!z!}) i)))
  --           --           (h by bz )


  --         zz : Square
  --               (((λ i → [ x ] ++ h (bx B.++ by) bz i) ∙
  --                 (λ i → ++-assoc [ x ] (fromList (bx B.++ by)) (fromList bz) (~ i)))
  --                ∙
  --                cong (_++ fromList bz)
  --                ((λ i → [ x ] ++ h bx by i) ∙
  --                 (λ i → ++-assoc [ x ] (fromList bx) (fromList by) (~ i))))
                  
  --               (((λ i → [ x ] ++ h bx (by B.++ bz) i) ∙
  --                 (λ i → ++-assoc [ x ] (fromList bx) (fromList (by B.++ bz)) (~ i)))
  --                ∙ cong (_++_ (x ∷ fromList bx)) (h by bz))
  --               (cong fromList (λ i → x B.∷ BP.++-assoc bx by bz i))
  --               (++-assoc (x ∷ fromList bx) (fromList by) (fromList bz))
  --         zz =
  --           zz0 ◁
  --             (λ i →
  --              cong ([ x ] ++_) (zzPrev i)
  --                ∙∙ doubleCompPath-filler
  --                       (cong ([ x ] ++_) (++-assoc _ _ _))
  --                       (sym (++-assoc [ x ] (fromList bx) (fromList by ++ fromList bz)))
  --                       refl (~ i)
  --                ∙∙ λ j → (++-assoc (x ∷ fromList bx) (fromList by) (fromList bz)) (i ∨ ~ j))
  --           ▷ sym zz1


  --    h3 : {xs ys zs : List A} (bx : fromList (toList xs) ≡ xs)
  --     (by : fromList (toList ys) ≡ ys) (bz : fromList (toList zs) ≡ zs) →
  --     _
  --     -- Square
  --     --   (h (toList (xs ++ ys)) (toList zs)
  --     --     ∙ cong₂ _++_ (h (toList xs) (toList ys) ∙ cong₂ _++_ bx by) bz)
  --     --   (h (toList xs) (toList (ys ++ zs))
  --     --     ∙ cong₂ _++_ bx (h (toList ys) (toList zs) ∙ cong₂ _++_ by bz))
  --     --   (cong (fromList) (BP.++-assoc (toList xs) (toList ys) (toList zs)))
  --     --   (++-assoc xs ys zs)
  --    h3 bx by bz =
  --      (cong ((h (toList (bx i1 ++ by i1)) (toList (bz i1))) ∙_)
  --         (cong₂-∙-fst _++_ _ (cong₂ _++_ bx by) bz))
  --          ∙ assoc _ _ _ ◁
  --         (λ i →
  --           (λ j → h3' (toList (bx i1)) (toList (by i1)) (toList (bz i1)) i j)
  --           ∙ λ j → ++-assoc (bx j) (by j) (bz j) i)
  --      ▷ (sym (assoc _ _ _)
  --        ∙ cong ((h (toList (bx i1)) (toList (by i1 ++ bz i1))) ∙_)
  --          (sym (cong₂-∙'' _++_ _ _ _)))
       

  -- -- isoList : Iso (List A) (B.List A)
  -- -- fun isoList = toList
  -- -- inv isoList = fromList
  -- -- rightInv isoList = toList-fromList
  -- -- leftInv isoList = fromList-toList
