{-# OPTIONS --safe #-}

module Cubical.Functions.Involution where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Data.Sigma


isInvolution : ∀{ℓ} {A : Type ℓ} → (A → A) → Type _
isInvolution f = ∀ x → f (f x) ≡ x

module _ {ℓ} {A : Type ℓ} {f : A → A} (invol : isInvolution f) where
  open Iso


  isInvolution∘invol : ∀ {ℓ'} {B : Type ℓ'}
     → isInvolution {A = A → B} (_∘ f) 
  isInvolution∘invol x = funExt (cong x ∘ invol)

  isInvolutionInvol∘ : ∀ {ℓ'} {B : Type ℓ'}
     → isInvolution {A = B → A} (f ∘_) 
  isInvolutionInvol∘ x = funExt (invol ∘ x)
  

  involIso : Iso A A
  involIso .fun = f
  involIso .inv = f
  involIso .rightInv = invol
  involIso .leftInv = invol

  involIsEquiv : isEquiv f
  involIsEquiv = isoToIsEquiv involIso

  involEquiv : A ≃ A
  involEquiv = f , involIsEquiv

  involPath : A ≡ A
  involPath = ua involEquiv


  involEquivComp : compEquiv involEquiv involEquiv ≡ idEquiv A
  involEquivComp
    = equivEq (λ i x → invol x i)

  involPathComp : involPath ∙ involPath ≡ refl
  involPathComp
    = sym (uaCompEquiv involEquiv involEquiv) ∙∙ cong ua involEquivComp ∙∙ uaIdEquiv

  involPath² : Square involPath refl refl involPath
  involPath²
    = subst (λ s → Square involPath s refl involPath)
        involPathComp (compPath-filler involPath involPath)


  involEqPa : PathP (λ i → (A ≃ involPath i)) involEquiv (idEquiv A)
  involEqPa = ΣPathPProp
                              {A = λ i → A → involPath i}
                                  {B = λ _ → isEquiv}
                               {u = involEquiv}
                               {v = idEquiv _}
                             isPropIsEquiv
                             (funExt λ x → ua-gluePath _
                               (invol x))
                               
  involEqPa' : PathP (λ i → (A ≃ involPath i))
                 (idEquiv A) involEquiv      
  involEqPa' = ΣPathPProp {A = λ i → A → involPath i}
                                  {B = λ _ → isEquiv}
                                {u = idEquiv _}
                                {v = involEquiv}
                                isPropIsEquiv 
                                 ((funExt λ x →
                                      ua-gluePath _
                                    refl))

  involEqPa⁻ : PathP (λ i → (involPath i ≃ A)) involEquiv (idEquiv A)
  involEqPa⁻ = ΣPathPProp {A = λ i → involPath i → A}
                                  {B = λ _ → isEquiv}
                                   
                                   isPropIsEquiv
                                   (ua-ungluePathExt involEquiv)


  involPath²' : Square involPath refl refl involPath
  involPath²' j i =
    Glue (involPath j)
      λ { (i = i0) → A , involEqPa j
        ; (i = i1) → involPath j , idEquiv _
        ; (j = i1) → A , idEquiv A
        }

  involPathSym-Sides : ∀ i j → Partial (j ∨ ~ j)
     (Σ-syntax (Type ℓ) (λ T → T ≃ ua involEquiv i))
  involPathSym-Sides i j = 
      λ { (j = i0) → A , involEqPa i
        ; (j = i1) → A , involEqPa' i }
  involPathSym : involPath ≡ sym (involPath) 
  involPathSym i j =
     Glue (ua (involEquiv) i) (involPathSym-Sides i j)
         -- λ { (j = i0) → A , involEqPa i
         --   ; (j = i1) → A , involEqPa' i }

  -- glueInvolPathSymSi :
  --    (∀ a → cong f (invol a) ≡ (invol (f a)))
  --     → SquareP (λ i j → A → ua (involEquiv) i)
  --          refl
  --          (refl)
  --          (λ i → fst (involEqPa i) ∘ f)
  --          (λ i → fst (involEqPa' i) ∘ funExt invol (i))
  -- glueInvolPathSymSi involCoh i j a =
  --   glue (λ { (i = i0) → f (f a)
  --           ; (i = i1) → f a
  --           } ) (involCoh a (~ j) i)

  -- glueInvolPathSym : (∀ a → ?)
  --    → SquareP (λ i j → A → involPathSym i j)
  --            (λ j → ua-gluePathExt involEquiv j ∘ f)
  --            (symP (ua-gluePathExt involEquiv))
  --            refl
  --            (funExt invol)
  -- glueInvolPathSym involCoh i j a = ?
  --   -- glue (λ { (j = i0) → f a 
  --   --         ; (j = i1) → invol a i
  --   --         })
  --   --         (glueInvolPathSymSi involCoh i j a)

  -- glueInvolPathSymSi' :
  --    (∀ a → cong f (invol a) ≡ (invol (f a)))
  --     → SquareP (λ i j → A → ua (involEquiv) i)
  --          refl
  --          (refl)
  --          (λ i → fst (involEqPa i) ∘ f)
  --          (λ i → fst (involEqPa' i) ∘ funExt invol (i))
  -- glueInvolPathSymSi' involCoh i j a =
  --   glue (λ { (i = i0) → {!!}
  --           ; (i = i1) → {!!}
  --           } ) {!!}


  -- ua-gluePathExtInvo : PathP (λ i → involPath i → A) (idfun _) f
  -- ua-gluePathExtInvo i x = {!!}
    -- glue (λ { (i = i0) → x ; (i = i1) → f x }) (f x)


  -- glueInvolPathSym : (pp : {!!}) → 
  --     SquareP (λ i j → involPath i → involPathSym i j)
  --            (ua-gluePathExt involEquiv)
  --            (symP (ua-gluePathExt involEquiv))
  --            pp
  --            (ua-ungluePathExt involEquiv)
  -- glueInvolPathSym pp i j a = {!!}
  --   -- glue (λ { (j = i0) → f a 
  --   --         ; (j = i1) → f (f a)
  --   --         })
  --   --          (glue (λ { (i = i0) → f (f a) 
  --   --                   ; (i = i1) → f (invol a (~ j))
  --   --                   }) (involCoh a i j))



  -- glueInvolPathSym' : (∀ a →
  --         Square
  --            refl
  --            (λ j → f (invol a (~ j)))
  --            (λ i → invol (f a) i)
  --            refl)
  --    → SquareP (λ i j → A → involPathSym i j)
  --            (λ j → ua-gluePathExt involEquiv j)
  --            ({!symP (ua-gluePathExt involEquiv)!})
  --            refl
  --            refl
  -- glueInvolPathSym' involCoh i j a = {!!}
  --   glue (λ { (j = i0) → f a 
  --           ; (j = i1) → f (f a)
  --           })
  --            (glue (λ { (i = i0) → f (f a) 
  --                     ; (i = i1) → f (invol a (~ j))
  --                     }) (involCoh a i j))


  -- sqI : Square {A = A → A}
  --           (λ i x → invol (invol x i) (~ i))
  --           (λ i x → x)
  --           (λ i x → invol x i)
  --           λ i x → invol x i
  -- sqI i j x = invol (invol x (i ∨ j)) (i ∨ ~ j)

  -- involEqPa : PathP (λ i → Σ (A → involPath (~ i)) isEquiv) (idEquiv A) involEquiv
  -- involEqPa = ΣPathPProp {A = λ i → A → involPath (~ i)}
  --                                 {B = λ _ → isEquiv}
  --                               {u = idEquiv _}
  --                               {v = involEquiv}
  --                               isPropIsEquiv 
  --                                (funExt (λ x i → ua-gluePath involEquiv (invol x) (~ i) ))

  -- involEqPa' : PathP (λ i → Σ (A → involPath (~ i)) isEquiv) involEquiv (idEquiv A)
  -- involEqPa' = ΣPathPProp {A = λ i → A → involPath (~ i)}
  --                                 {B = λ _ → isEquiv}
                                
  --                               {u = involEquiv}
  --                               {v = idEquiv _}
  --                               isPropIsEquiv 
  --                                (funExt λ x i → ua-gluePath involEquiv (λ _ → f x) (~ i))


  -- involPathSym : involPath ≡ sym (involPath) 
  -- involPathSym i j =
  --    Glue (ua (involEquiv) (~ i))
  --        λ { (j = i0) → A , involEqPa' i
  --          ; (j = i1) → A , involEqPa i }


  -- invoPSGsq : SquareP (λ i j → ua involEquiv i → involPathSym i j)
  --                (λ j x → {!!})
  --                (λ j x → {!!})
  --                (λ i x → {!!} )
  --                {!!}
  -- invoPSGsq = {!!}

  InvolSymTy : PathP (λ i → involPath i → A) (λ x → x) (λ x → f x) → Type ℓ
  InvolSymTy p = SquareP (λ i j → involPath i → involPathSym i j)
          (λ j x → glue (λ { (j = i0) → x ; (j = i1) → f x }) (f x))
          ((λ j x → glue (λ { (j = i0) → f x ; (j = i1) → x }) (f x)))
          -- (subst (λ v → PathP (λ i → v i → A) (λ x → x) (λ x → f x))
          --    (sym (involPathSym)) (λ i x → ua-unglue involEquiv (~ i) x))
          -- (ua→ λ x → sym (invol x))
          p
          -- (sym (funExt invol) ◁ ((λ i x → f (ua-unglue involEquiv (i) x))))
         -- ({!!} ◁ ((λ i x → f (ua-unglue involEquiv (i) x))))
         (λ i → ua-unglue involEquiv i)

  involSymSide : PathP (λ i → involPath i → A) (λ x → x) (λ x → f x)
  involSymSide = sym (funExt invol) ◁ ((λ i x → f (ua-unglue involEquiv (i) x)))




  -- ua-involPreComp : ∀ {ℓ'} (B : Type ℓ') → ∀ ∘f-isEq → (λ i → involPath i → B) ≡ ua ((_∘ f) , ∘f-isEq) 
  -- ua-involPreComp B ∘f-isEq j i = 
  --   Glue (involPath i → B)
  --        λ { (j = i0) → _ , idEquiv _ 
  --           ; (j = i1) → ua ((_∘ f) , ∘f-isEq) i ,
  --                (λ x x₁ → ua-ungluePathExt ((_∘ f) , ∘f-isEq) i x (ua-ungluePathExt involEquiv i x₁)  ) ,
  --                 isProp→PathP
  --                   (λ i → isPropIsEquiv {A = ua ((_∘ f) , ∘f-isEq) i}
  --                                 {B = involPath i → B} 
  --                     (λ x x₁ → ua-ungluePathExt ((_∘ f) , ∘f-isEq) i x (ua-ungluePathExt involEquiv i x₁)  ))
  --                   ((isEquivPreComp (involEquiv ∙ₑ involEquiv))) (idIsEquiv _) i
  --           ; (i = i0) → (A → B) , (λ x x₁ → x (invol x₁ (~ j))) ,
  --                 isProp→PathP (λ j →  isPropIsEquiv (λ x x₁ → x (invol x₁ (~ j))))
  --                   (idIsEquiv _) (isEquivPreComp (involEquiv ∙ₑ involEquiv)) j
  --           ; (i = i1) → (A → B) , (idEquiv _)
  --           }


  -- ua-involPreComp' : ∀ {ℓ'} (B : Type ℓ') → ∀ ∘f-isEq → (λ i → involPath i → B) ≡ ua ((_∘ f) , ∘f-isEq) 
  -- ua-involPreComp' B ∘f-isEq j i = 
  --     Glue (A → B)
  --          λ { (j = i0) → {!!} , {!!} 
  --             ; (j = i1) → {!!}
  --             ; (i = i0) → {!!}
  --             ; (i = i1) → {!!} , {!!}
  --             }


  module InvolSym (p : PathP (λ i → involPath i → A) (λ x → x) (λ x → f x)) where

    pathStrict : ∀ i → involPath i → A
    pathStrict i x = f (ua-unglue involEquiv i x)

    Ty = InvolSymTy p
   



  -- involPathSym-glue : --∀ i j → involPath i → involPathSym i j
  --    SquareP (λ i j → involPath i → involPathSym i j)
  --     (λ j x → glue (λ { (j = i0) → x ; (j = i1) → f x }) (f x))
  --     ((λ j x → glue (λ { (j = i0) → f x ; (j = i1) → x }) (f x)))
  --     -- (subst (λ v → PathP (λ i → v i → A) (λ x → x) (λ x → f x))
  --     --    (sym (involPathSym)) (λ i x → ua-unglue involEquiv (~ i) x))
  --     -- (ua→ λ x → sym (invol x))
  --     (sym (funExt invol) ◁ ((λ i x → f (ua-unglue involEquiv (i) x))))
  --    -- ({!!} ◁ ((λ i x → f (ua-unglue involEquiv (i) x))))
  --    (λ i x → ua-unglue involEquiv (i) x)
     
  -- involPathSym-glue i j x = 
  --   glue
  --    (λ { (j = i0) → {!!} 
  --       ; (j = i1) → {!!} --ua-unglue involEquiv i x --ua-unglue involEquiv i x
  --       })
  --        {!!}

module preCompInvol {ℓ ℓ'} {A : Type ℓ} {f : A → A}
               (B : Type ℓ') (invol : isInvolution f)
               (cohInvo : ((y : A) → Square
                    (λ j → f (invol (f y) j))
                    (λ j → invol y (~ j))
                    (λ i → invol (invol y i) i)
                    λ i → f (f y))) where


  ∘invol : isInvolution {A = A → B} (_∘ f)
  ∘invol = λ x i b → x (invol b i)

  e = involEquiv {f = f} invol             
  p = involPath {f = f} invol

  pS = involPathSym {f = f} invol

  -- gipS = glueInvolPathSym {f = f} invol cohInvo

  e' = involEquiv {A = A → B} {f = (_∘ f)} ∘invol
  p' = involPath {A = A → B} {f = (_∘ f)} ∘invol
  pS' = involPathSym {A = A → B} {f = (_∘ f)} ∘invol
  -- gipS' = glueInvolPathSym {A = A → B} {f = (_∘ f)} ∘invol
  --           λ a i j x → a (cohInvo x (~ j) (~ i))

  -- eq : Path ((A → B) ≡ (A → B) )
  --            ((λ i → p i → B)) p'

  -- eq j i = 
  --   Glue (p i → B)
  --        λ { (j = i0) → _ , idEquiv _ 
  --           ; (j = i1) → p' i ,
  --             (λ x y → ua-ungluePathExt e' i x (ua-ungluePathExt e i y)) ,
  --             isProp→PathP (λ i → isPropIsEquiv {A = p' i} {B = p i → B}
  --     (λ x y → ua-ungluePathExt e' i x (ua-ungluePathExt e i y)))
  --              (snd (e' ∙ₑ e')) (idIsEquiv _) i
  --           ; (i = i0) → (A → B) ,
  --                 equivEq {e = idEquiv _} {f = e' ∙ₑ e'} (λ i x b → x (invol b (~ i))) j
  --           ; (i = i1) → (A → B) , (idEquiv _)
  --           }

  eq≃ : PathP (λ i → (p i → B) → p' i)
             (idfun _)
             (idfun _)
  eq≃ i x =
    glue (λ { (i = i0) → x ; (i = i1) → x })
     λ x₁ → x (glue (( λ { (i = i0) → f x₁ ; (i = i1) → x₁ })) (invol x₁ i))

  unsguleEqSym : SquareP (λ i j → pS i j → p i)
             (λ j → unglue (j ∨ ~ j))
             (λ j → unglue (j ∨ ~ j))
             (λ i → fst (involEqPa {f = f} invol i))
             (λ i → fst (involEqPa' {f = f}  invol i))
  unsguleEqSym i j x = unglue (j ∨ ~ j)  x 

  glueEqSym : SquareP (λ i j → pS i j → p i)
             (λ j → unglue (j ∨ ~ j))
             (λ j → unglue (j ∨ ~ j))
             (λ i → fst (involEqPa {f = f} invol i))
             (λ i → fst (involEqPa' {f = f}  invol i))
  glueEqSym i j x = unglue (j ∨ ~ j)  x 


  eq≃Sym : SquareP (λ i j → (pS i j → B) → pS' i j)
             eq≃
             (symP (eq≃))
             refl
             refl
  eq≃Sym i j x = 
    glue (λ { (j = i0) → x ; (j = i1) → x })
        (glue (λ { (i = i0) →
          λ y → x (glue (λ { (j = i0) → f y ; (j = i1) → y})
                   (invol (y) j))
            ; (i = i1) → λ y → x ((glue (λ { (j = i0) → y ; (j = i1) → f y})
                   (invol y (~ j)))) })
          λ y →
            x (glue (λ { (j = i0) → invol y i ; (j = i1) → f y })
               (glue (λ { (i = i0) → (invol (f y) j) ;
                          (i = i1) → invol y (~ j) })
                            (cohInvo y i j))))   
                           
-- module preCompInvol2 {ℓ ℓ'} {A : Type ℓ} {f : A → A}
--                (B : Type ℓ') (invol : isInvolution f)
--                (cohInvo : ((y : A) → Square
--                     (λ j → f (invol (f y) j))
--                     (λ j → invol y (~ j))
--                     (λ i → invol (invol y i) i)
--                     λ i → f (f y))) where


--   ∘invol : isInvolution {A = A → B} (_∘ f)
--   ∘invol = λ x i b → x (invol b i)

--   e = involEquiv {f = f} invol             
--   p = involPath {f = f} invol

--   pS = involPathSym {f = f} invol

--   -- gipS = glueInvolPathSym {f = f} invol cohInvo

--   e' = involEquiv {A = A → B} {f = (_∘ f)} ∘invol
--   p' = involPath {A = A → B} {f = (_∘ f)} ∘invol
--   pS' = involPathSym {A = A → B} {f = (_∘ f)} ∘invol
--   -- gipS' = glueInvolPathSym {A = A → B} {f = (_∘ f)} ∘invol
--   --           λ a i j x → a (cohInvo x (~ j) (~ i))

--   eq : Path ((A → B) ≡ (A → B) )
--              ((λ i → p i → B)) p'

--   eq j i = 
--     Glue (A → B)
--          λ { (j = i0) → (p i → B) ,
--                (λ x y → x
--                 (glue (
--                  λ { (i = i0) → f y
--                    ; (i = i1) → y
--                    })
--                   (invol y i))) , {!!}
--             ; (i = i0) → (A → B) , e'                 
--             ; (i = i1) → (A → B) , idEquiv _
--             }

--   eq≃ : PathP (λ i → (p i → B) → p' i)
--              (idfun _)
--              (idfun _)
--   eq≃ i x =
--     glue (λ { (i = i0) → x ; (i = i1) → x })
--      λ x₁ → x (glue (( λ { (i = i0) → f x₁ ; (i = i1) → x₁ })) (invol x₁ i))

--   unsguleEqSym : SquareP (λ i j → pS i j → p i)
--              (λ j → unglue (j ∨ ~ j))
--              (λ j → unglue (j ∨ ~ j))
--              (λ i → fst (involEqPa {f = f} invol i))
--              (λ i → fst (involEqPa' {f = f}  invol i))
--   unsguleEqSym i j x = unglue (j ∨ ~ j)  x 

--   glueEqSym : SquareP (λ i j → pS i j → p i)
--              (λ j → unglue (j ∨ ~ j))
--              (λ j → unglue (j ∨ ~ j))
--              (λ i → fst (involEqPa {f = f} invol i))
--              (λ i → fst (involEqPa' {f = f}  invol i))
--   glueEqSym i j x = unglue (j ∨ ~ j)  x 


-- --   eq≃Sym : SquareP (λ i j → (pS i j → B) → pS' i j)
-- --              eq≃
-- --              (symP (eq≃))
-- --              refl
-- --              refl
-- --   eq≃Sym i j x = 
-- --     glue (λ { (j = i0) → x ; (j = i1) → x })
-- --         (glue (λ { (i = i0) →
-- --           λ y → x (glue (λ { (j = i0) → f y ; (j = i1) → y})
-- --                    (invol (y) j))
-- --             ; (i = i1) → λ y → x ((glue (λ { (j = i0) → y ; (j = i1) → f y})
-- --                    (invol y (~ j)))) })
-- --           λ y →
-- --             x (glue (λ { (j = i0) → invol y i ; (j = i1) → f y })
-- --                (glue (λ { (i = i0) → (invol (f y) j) ;
-- --                           (i = i1) → invol y (~ j) })
-- --                             (cohInvo y i j))))   


module preCompInvol* {ℓ ℓ'} {A : Type ℓ} {f : A → A}
               (B : Type ℓ') (invol : isInvolution f)
               (cohInvo : ((y : A) → Square
                    (λ j → f (f (f y)))
                    (λ j → f y)
                    (λ i → f (invol y i))
                    λ i → invol (f y) i)) where


  ∘invol : isInvolution {A = A → B} (_∘ f)
  ∘invol = λ x i b → x (invol b i)

  e = involEquiv {f = f} invol             
  p = involPath {f = f} invol

  pS = involPathSym {f = f} invol

  -- gipS = glueInvolPathSym {f = f} invol cohInvo

  e' = involEquiv {A = A → B} {f = (_∘ f)} ∘invol
  p' = involPath {A = A → B} {f = (_∘ f)} ∘invol
  pS' = involPathSym {A = A → B} {f = (_∘ f)} ∘invol
  -- gipS' = glueInvolPathSym {A = A → B} {f = (_∘ f)} ∘invol
  --           λ a i j x → a (cohInvo x (~ j) (~ i))

  -- eqj1 : PathP (λ i → p' i → p (~ i) → B)
  --           (_∘ f)
  --           (_∘ f)
  -- eqj1 i x y = unglue (i ∨ ~ i) x (unglue (i ∨ ~ i) y) 
  

  eq≃ : PathP (λ i → (p (i) → B) → p' (~ i))
             (idfun _)
             (idfun _)
  eq≃ i x =
    glue (λ { (i = i0) → x ; (i = i1) → x })
     λ y → x (glue (( λ { (i = i0) → y ; (i = i1) → f y })) (f y))
     

  -- unsguleEqSym : SquareP (λ i j → pS i j → p i)
  --            (λ j → unglue (j ∨ ~ j))
  --            (λ j → unglue (j ∨ ~ j))
  --            (λ i → fst (involEqPa {f = f} invol i))
  --            (λ i → fst (involEqPa' {f = f}  invol i))
  -- unsguleEqSym i j x = unglue (j ∨ ~ j)  x 

  -- glueEqSym : SquareP (λ i j → pS i j → p i)
  --            (λ j → unglue (j ∨ ~ j))
  --            (λ j → unglue (j ∨ ~ j))
  --            (λ i → fst (involEqPa {f = f} invol i))
  --            (λ i → fst (involEqPa' {f = f}  invol i))
  -- glueEqSym i j x = unglue (j ∨ ~ j)  x 


  eq≃Sym : SquareP (λ i j → (pS i j → B) → pS' i (~ j))
             eq≃
             (symP (eq≃))
             refl
             refl
  eq≃Sym i j x = 
    glue (λ { (j = i0) → x ; (j = i1) → x })
        (glue (λ { (i = i0) →
          λ y → x (glue (λ { (j = i0) → y ; (j = i1) → f y})
                   (f y))
            ; (i = i1) → λ y → x ((glue (λ { (j = i0) → f  y ; (j = i1) → y})
                   (f y))) })
          λ y →
            x (glue (λ { (j = i0) → f y ; (j = i1) → invol y i })
               (glue (λ { (i = i0) → f (f y) ;
                          (i = i1) → f y })
                 (cohInvo  y i (~ j)))))   

  eq≃Sym' : (cohInvo' : (y : A) → Square
                    refl refl
                    (λ i → invol (invol y (~ i)) i)
                    refl)
                  → SquareP (λ i j → (pS i j → B) → pS' (~ i) j)
             eq≃
             (symP (eq≃))
             refl
             refl
  eq≃Sym' cohInvo' i j x = 
    glue (λ { (j = i0) → x ; (j = i1) → x })
        (glue (λ { (i = i0) →
         λ y → x (glue (λ { (j = i0) → y ; (j = i1) → f y}) (f y))
     ; (i = i1) → λ y → x ((glue (λ { (j = i0) → f  y ; (j = i1) → y})
                   (f y))) })
          λ y → x
               (glue (λ { (j = i0) → invol y (~ i) ; (j = i1) → f y })
               (glue (λ { (i = i0) → f y ; (i = i1) → f (f y) })
                (cohInvo' y i j))))   
