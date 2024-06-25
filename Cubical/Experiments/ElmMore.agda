{-# OPTIONS --safe #-}

module Cubical.Experiments.ElmMore where

open import Cubical.Foundations.Everything

open import Cubical.Data.Nat
open import Cubical.Data.Int renaming (ℤ to Int)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥ renaming (elim to ⊥-elim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe
open import Cubical.Data.Maybe as ℙ renaming (Maybe to ℙ ; nothing to ₋₋ ; just to ⌞_) 
open import Cubical.Data.Sigma
open import Cubical.Data.List

open import Cubical.Relation.Nullary
import Cubical.Functions.Logic as L
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Poset

open import Agda.Builtin.String

open import Cubical.Algebra.Lattice
open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.CommMonoid
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.CommMonoid.CommMonoidProd
open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Ring

open import Cubical.HITs.PropositionalTruncation as T₁

open import Cubical.Experiments.Elm

open import Cubical.Functions.Embedding

instance
 HasPat× : ∀ {A B} → {{HasPat A}} → {{HasPat B}} → HasPat (A × B)
 HasPat× {A} {B} {{hpA}} {{hpB}} = w
  where
  module HPA = HasPat hpA
  module HPB = HasPat hpB




  open HasPat

  P× = _

  module DP× = DecPoset {P = P×} (DecPoset×
      _ _ (DecPosetℙ _ _ (HPA.patDecPoset))
           
      _ _ (DecPosetℙ _ _ (HPB.patDecPoset))
            )

  open DP× 

  ℙA = _ 
  ℙB = _ 

  module DℙA = DecPoset {P = ℙA} (DecPosetℙ _ _ (HPA.patDecPoset))
  module DℙB = DecPoset {P = ℙB} (DecPosetℙ _ _ (HPB.patDecPoset))


  w : HasPat (A × B)
  Pat w = ℙ (HPA.Pat) × ℙ (HPB.Pat)
  patData w (a , b) = patData' a × patData' b 
  patOrd w = _
  patDecPoset w = _

  pat─ w = ×─
   where
   ×─ : DecPoset.─Ty (patDecPoset w)
   ×─ (x , x') (y , y') =
       x─-++-y─ , isFull'⇒isFull _ x─-++-y─ isF'-x─-++-y─
    where
     -- TODO : fix the meess with x/y prim/unprimed, it is used randomly below!
     x─Ty : _
     x─Ty = _
     
     x─ : Σ x─Ty _
     x─ = (─ℙ _ _ (HPA.patDecPoset) HPA.pat─ HPA.patSAC) x y

     xxH : _
     xxH x y x₁ = x₁ ∘ T₁.map
       λ x₃ → fst (fst x₃) , (fst (fst (snd x₃))) , (fst (snd (snd x₃)))

     x─' : StrAntiChain _
     x─' = SAC-poset-map (λ x₂ → x₂ , x')
              (λ x₂ → λ x₃ → ((fst x₃) , PosetStr.is-refl (Posetℙ _ HPB.patOrd _) x'  ) ,
               snd x₃ ∘ T₁.map λ a → (fst (fst a)) , ((fst (fst (snd a))) ,
                                       fst (snd (snd a))))
              xxH
              (fst x─)
              
     x<>y→xx'<>yy' : ∀ x y x' y' → ⟨ x DℙA.≮≯ₚ y ⟩  → ⟨ (x , x') ≮≯ₚ (y , y') ⟩ 
     x<>y→xx'<>yy' _ _ _ _ X =
       X ∘ T₁.map λ x₁ → (fst (fst x₁)) , (fst (fst (snd x₁))) , fst (snd (snd x₁)) 

     y─' : Σ (StrAntiChain _) λ yy → (Σ ⟨ _⊈⊉_ _ x─' yy ⟩
                   λ x⊈⊉y →  ⟨ isFull' _ (_++AC_ _ x─' yy x⊈⊉y) ⟩  )
     y─' =  ⊎.rec (uncurry ∩xy) (λ q → [] , (tt , uncurry (full-case-x<>y q))) ⊎xy 
      where
      ⊎xy = DℙA._⊓?_ x y

      full-case-x<>y : _ → _
      full-case-x<>y  x<>y pa pb ((pa<x , pb<x') , xx) =
        let F'x* = DℙA.isFull⇒isFull'  _ (fst x─) (snd x─) pa
                       (pa<x , DℙA.≤-≮≯  x y pa x<>y pa<x )
        in T₁.map (λ (pa* , q) →
                 (pa* , pb) , sc∃-SAC-poset-map 
                         (λ x₂ → x₂ , x')
              (λ x₂ → λ x₃ → ((fst x₃) , PosetStr.is-refl (Posetℙ _ HPB.patOrd _) x'  ) ,
               snd x₃ ∘ T₁.map λ a → (fst (fst a)) , ((fst (fst (snd a))) ,
                                       fst (snd (snd a))))
              _ _ 
              xxH
              (λ v (pa*<v , pa*<pa)
                   (v<x , v<y) x₄ →
                    (pa*<v , pb<x') ,
                     pa*<pa , PosetStr.is-refl (snd ℙB) pb)
              (fst x─) q) F'x*

      ∩xy : _
      ∩xy x* q* =
        fst-y─' , (x⊈⊉y (fst x─) (fst y─₀) , uncurry F'xy)
       where
        P' = _
        Q' = _

        y─Ty : _
        y─Ty = _

        y─₀ : Σ y─Ty _
        y─₀ = (─ℙ _ _ (HPB.patDecPoset) HPB.pat─ HPB.patSAC) x' y'

        yyH : _
        yyH x y x₁ = x₁ ∘ T₁.map
           λ x₃ → (snd (fst x₃)) , ((snd (fst (snd x₃))) , snd (snd (snd x₃)))

        ∀<>xy : (xx : x─Ty) (y* : ℙ HPB.Pat)
                 → ⟨ P' y* ⟩
                 →
                ⟨ fst ( ∀≮≯ _
                 (SAC-poset-map {Q = Q'} (λ x₂ → x₂ , x')
              (λ x₂ → λ x₃ → ((fst x₃) , PosetStr.is-refl (Posetℙ _ HPB.patOrd _) x'  ) ,
               snd x₃ ∘ T₁.map λ a → (fst (fst a)) , ((fst (fst (snd a))) ,
                                       fst (snd (snd a))))
              xxH
              (xx))
              (x* , y*) ) ⟩ 
        ∀<>xy DecPoset.[] y* x = tt
        ∀<>xy (xx DecPoset.∷ p [ x₁ , x₂ ]s) y* x =
          ∀<>xy xx y* x ,
           let p<>x* : ⟨ p DℙA.≮≯ₚ x* ⟩
               p<>x* = DℙA.≮≯-≤ p y x* (snd x₁) (snd (fst q*))
           in x<>y→xx'<>yy' p x* x' y* p<>x*


        x⊈⊉y : (xx : x─Ty) (yy : y─Ty) →
                ⟨ _⊈⊉_ _
                 (SAC-poset-map  {Q = Q'} (λ x₂ → x₂ , x')
              (λ x₂ → λ x₃ → ((fst x₃) , PosetStr.is-refl (Posetℙ _ HPB.patOrd _) x'  ) ,
               snd x₃ ∘ T₁.map λ a → (fst (fst a)) , ((fst (fst (snd a))) ,
                                       fst (snd (snd a))))
              xxH
              (xx))
              (SAC-poset-map {P = P'} 
                 (λ x₂ → x* , x₂)
                 (λ x₁ x₂ → (fst (fst q*) , (fst x₂)) ,
                   snd x₂ ∘ T₁.map λ x₃ → snd (fst x₃) , (snd (fst (snd x₃))) ,
                     snd (snd (snd x₃)))
                 yyH
                 yy) ⟩ 
        x⊈⊉y xx [] = tt
        x⊈⊉y xx (yy ∷ p [ x , x₁ ]s) =
         let zz = x⊈⊉y xx yy
         in zz , ∀<>xy xx p x

        fst-y─' = SAC-poset-map {Q = Q'}
          (λ x₂ → x* , x₂)
          (λ x₁ x₂ → (fst (fst q*) , (fst x₂)) ,
            snd x₂ ∘ T₁.map λ x₃ → snd (fst x₃) , (snd (fst (snd x₃))) ,
              snd (snd (snd x₃)))
          yyH
          (fst y─₀)

        F'xy : (pa : ℙ _) → (pb : ℙ _) → _ → _
        F'xy pa pb ((pa<x , pb<x') , xx) with pa DℙA.⊓? y 
        ... | inl (x'** , q**) =
           let pb<>y' = xx ∘ T₁.map
                 λ x₁ →
                    (x'** , fst x₁) ,
                     (((fst (fst q**)) , (fst (snd x₁))) , ((snd (fst q**)) , (snd (snd x₁))))
               F'x* = DℙB.isFull⇒isFull'  _ (fst y─₀) (snd y─₀) pb
                       (pb<x' , pb<>y')
           in T₁.map (λ (pb* , q) →
                 (x'** , pb*) , sc∃++ _ _ x─' fst-y─'  (x⊈⊉y (fst x─) (fst y─₀))
                   ∣ inr
                       (sc∃-SAC-poset-map 
                         (λ x₂ → x* , x₂)
                 (λ x₁ x₂ → (fst (fst q*) , (fst x₂)) ,
                   snd x₂ ∘ T₁.map λ x₃ → snd (fst x₃) , (snd (fst (snd x₃))) ,
                     snd (snd (snd x₃)))
              _ _ 
              yyH
              (λ v (pa*<v , pa*<pa)
                   (v<x , v<y) x₄ →
                    (((snd q* x'**
                       (PosetStr.is-trans (snd ℙA)
                          x'** pa x (fst (fst q**)) pa<x ,
                        (snd (fst q**))))) , pa*<v) ,
                        fst (fst q**) , pa*<pa )
              (fst y─₀) q) ∣₁) F'x*
        ... | inr pa<>y =
           let F'x* = DℙA.isFull⇒isFull'  _ (fst x─) (snd x─) pa
                       (pa<x , pa<>y)
           in T₁.map (λ (pa* , q) →
                 (pa* , pb) , sc∃++ _ _ x─' fst-y─'  (x⊈⊉y (fst x─) (fst y─₀))
                   ∣ inl
                       (sc∃-SAC-poset-map 
                         (λ x₂ → x₂ , x')
              (λ x₂ → λ x₃ → ((fst x₃) , PosetStr.is-refl (Posetℙ _ HPB.patOrd _) x'  ) ,
               snd x₃ ∘ T₁.map λ a → (fst (fst a)) , ((fst (fst (snd a))) ,
                                       fst (snd (snd a))))
              _ _ 
              xxH
              (λ v (pa*<v , pa*<pa)
                   (v<x , v<y) x₄ →
                    (pa*<v , pb<x') ,
                     pa*<pa , PosetStr.is-refl (snd ℙB) pb)
              (fst x─) q) ∣₁) F'x*
        
         
     x─-++-y─ = (_ ++AC x─') (fst y─') (fst (snd y─'))

     -- isF'-A = DℙA.isFull'⇒isFull _ _ {!snd y─'!}
     -- isF'-B = {!!}

     isF'-x─-++-y─ : ⟨ isFull' _ (x─-++-y─) ⟩
     isF'-x─-++-y─ = snd (snd y─')
     
  fst (patSAC w) = [] ∷ (₋₋ , ₋₋) [ _ , _ ]s 
  snd (patSAC w) = w'
   where
   w' : _
   w' x x₁ = snd (snd x₁) ∣ x , _ , PosetStr.is-refl (snd P×) x ∣₁

  toPat w = map-× (⌞_ ∘ HPA.toPat ) (⌞_ ∘ HPB.toPat)
  toPatMin w a (⌞_ x , ⌞_ x₁) = map-× (HPA.toPatMin (fst a) x) (HPB.toPatMin (snd a) x₁)
  
  patDataEquiv w (pa , pb) =
   Σ-transpose-≃ ∙ₑ ≃-× (patData'Equiv pa) (patData'Equiv pb)
   
  -- patDataEquiv w (₋₋ , _) =
  --    Σ-cong-equiv-snd (λ _ → invEquiv ΣPathP≃PathPΣ ∙ₑ
  --     ≃-× (uninhabEquiv ℙ.¬just≡nothing (idfun _)) (idEquiv _)
  --     ∙ₑ ΣEmpty _ )
  --     ∙ₑ ×⊥ _ ∙ₑ invEquiv (ΣEmpty _)
  -- patDataEquiv w (⌞_ x , ₋₋) =
  --     Σ-cong-equiv-snd (λ _ → invEquiv ΣPathP≃PathPΣ ∙ₑ
  --     ≃-× (idEquiv _) (uninhabEquiv ℙ.¬just≡nothing (idfun _)) 
  --     ∙ₑ ×⊥ _ )
  --     ∙ₑ ×⊥ _ ∙ₑ invEquiv (×⊥ _ )
  -- patDataEquiv w (⌞_ pa , ⌞_ pb) =
  --   Σ-cong-equiv-snd (λ _ → invEquiv ΣPathP≃PathPΣ ∙ₑ
  --       ≃-× (invEquiv (_ , ℙ.isEmbedding-just _ _))
  --           (invEquiv (_ , ℙ.isEmbedding-just _ _)))
  --    ∙ₑ Σ-transpose-≃
  --    ∙ₑ ≃-× (HPA.patDataEquiv pa)
  --            (HPB.patDataEquiv pb)

module Poset⊎ (Pat : Type)
        (PAV : PosetStr ℓ-zero Pat)
        (PADV :  DecPoset (_ , PAV))
        (Pat' : Type)
        (PBV : PosetStr ℓ-zero Pat')
        (PBDV :  DecPoset (_ , PBV)) where

  module PA = PosetStr PAV
  module PB = PosetStr PBV

  module PAD = DecPoset PADV
  module PBD = DecPoset PBDV


  open PosetStr

  PS⊎ : PosetStr ℓ-zero (Pat ⊎ Pat')
  (PS⊎ PosetStr.≤ inl x) (inl x₁) = x PA.≤ x₁
  (PS⊎ PosetStr.≤ inr x) (inr x₁) = x PB.≤ x₁
  (PS⊎ PosetStr.≤ _) (_) = ⊥

  IsPoset.is-set (isPoset PS⊎) = isSet⊎ PA.is-set PB.is-set
  IsPoset.is-prop-valued (isPoset PS⊎) (inl x₁) (inl x₂) = PA.is-prop-valued x₁ x₂
  IsPoset.is-prop-valued (isPoset PS⊎) (inr x₁) (inr x₂) = PB.is-prop-valued x₁ x₂
  IsPoset.is-refl (isPoset PS⊎) (inl x) = PA.is-refl x
  IsPoset.is-refl (isPoset PS⊎) (inr x) = PB.is-refl x
  IsPoset.is-trans (isPoset PS⊎) (inl x₂) (inl x₃) (inl x₄) =
     PA.is-trans x₂ x₃ x₄
  IsPoset.is-trans (isPoset PS⊎) (inr x₂) (inr x₃) (inr x₄) =
     PB.is-trans x₂ x₃ x₄ 
  IsPoset.is-antisym (isPoset PS⊎) (inl x₂) (inl x₃) x y =
     cong inl (PA.is-antisym x₂ x₃ x y) 
  IsPoset.is-antisym (isPoset PS⊎) (inr x₂) (inr x₃) x y =
     cong inr (PB.is-antisym x₂ x₃ x y)

  DP⊎ : DecPoset ((Pat ⊎ Pat') , PS⊎)
  DecPoset.patOrdDec (DP⊎) = ww
   where
   ww : ∀ x y → _
   ww (inl x) (inl x₁) = PAD.patOrdDec x x₁
   ww (inl x) (inr x₁) = no (idfun _)
   ww (inr x) (inl x₁) = no (idfun _)
   ww (inr x) (inr x₁) = PBD.patOrdDec x x₁
  DecPoset._⊓?_ (DP⊎) = ww
   where
   ww : ∀ x y → _
   ww (inl x) (inl x₁) =
     ⊎.map www 
       (_∘ T₁.map wwww )
     (x PAD.⊓? x₁)
    where
    www : ∀ xx → Σ _ _
    fst (www xx) = inl (fst xx)
    snd (www xx) = (fst (snd xx)) , wwww
      where
      wwww : ∀ yy → _
      wwww (inl x) = snd (snd xx) x

    wwww : _ → _
    wwww (inl x , snd₁) = x , snd₁
    
   ww (inr x) (inr x₁) = ⊎.map www 
       (_∘ T₁.map wwww )
     (x PBD.⊓? x₁)
    where
    www : ∀ xx → Σ _ _
    fst (www xx) = inr (fst xx)
    snd (www xx) = (fst (snd xx)) , wwww
      where
      wwww : ∀ yy → _
      wwww (inr x) = snd (snd xx) x

    wwww : _ → _
    wwww (inr x , snd₁) = x , snd₁
    
   ww (inl x) (inr x₁) = inr (T₁.rec isProp⊥ (uncurry www))
    where
     www : _
     www (inl x) = snd
     www (inr x) = fst
   ww (inr x) (inl x₁) = inr (T₁.rec isProp⊥ (uncurry www))
    where
     www : _
     www (inl x) = fst
     www (inr x) = snd

  open DecPoset DP⊎

  inl<>inr : ∀ x y → ⟨ ((inl x) ≮≯ₚ (inr y)) ⟩ 
  inl<>inr x y = T₁.rec isProp⊥ w
    where
    w : _
    w (inl x , y) = snd y
    w (inr x , y) = fst y

  module _ (─A : PAD.─Ty) (─B : PBD.─Ty) where 
   _─_ : ─Ty
   _─_ = ww
    where

    ww : DecPoset.─Ty (DP⊎)
    ww (inl x) (inl y) =
      let (xs , v) = ─A x y
          P = _
          Q = _
          f = inl
          g = (λ p → map-snd (_∘ T₁.map
             (uncurry λ { (inl z) y₁ → z , y₁ ; (inr z) () })))
          pres<> = (λ _ _ →
             _∘ T₁.map (uncurry λ { (inl z) → λ y₁ → z , y₁ ; (inr z) () }))
      in  SAC-poset-map {P = P} {Q = Q} f g pres<> xs
        ,
        λ { (inl z) → v z ∘ λ a → (fst (fst a) , snd (fst a) ∘ T₁.map (λ x₁ → inl (fst x₁) , snd x₁)) ,
                          SAC-poset-map∀≮≯⁻ {P = P} {Q = Q}
                            f g pres<> (λ _ _ → _∘ T₁.map λ a → inl (fst a) , snd a) xs z (snd a) 
            ; (inr z) → fst ∘ fst
                 }
    ww (inl x) (inr x₁) = ([] ∷ (inl x) [ (PA.is-refl x , inl<>inr x x₁ ) , tt ]s) , qq
     where
     qq : _
     qq (inl x') (p , q) = snd q ∣ (inl x') , fst p , PA.is-refl x' ∣₁
    ww (inr x) (inl x₁) = ([] ∷ inr x [ (PB.is-refl x , ≮≯-sym _ _ (inl<>inr x₁ x) ) , tt ]s) , qq
     where
     qq : _
     qq (inr x') (p , q) = snd q ∣ (inr x') , fst p , PB.is-refl x' ∣₁

    ww (inr x) (inr y) =
      let (xs , v) = ─B x y
          P = _
          Q = _
          f = inr
          g = (λ p → map-snd (_∘ T₁.map
             (uncurry λ { (inr z) y₁ → z , y₁ ; (inl z) () })))
          pres<> = (λ _ _ →
             _∘ T₁.map (uncurry λ { (inr z) → λ y₁ → z , y₁ ; (inl z) () }))
      in  SAC-poset-map {P = P} {Q = Q} f g pres<> xs
        ,
        λ { (inr z) → v z ∘ λ a → (fst (fst a) , snd (fst a) ∘ T₁.map (λ x₁ → inr (fst x₁) , snd x₁)) ,
                          SAC-poset-map∀≮≯⁻ {P = P} {Q = Q}
                            f g pres<> (λ _ _ → _∘ T₁.map λ a → inr (fst a) , snd a) xs z (snd a) 
            ; (inl z) → fst ∘ fst
                 }

instance
 HasPat⊎ : ∀ {A B} → {{HasPat A}} → {{HasPat B}} → HasPat (A ⊎ B)
 HasPat⊎ {A} {B} {{hpA}} {{hpB}} = w
  where
  module HPA = HasPat hpA
  module HPB = HasPat hpB

  module PA =  PosetStr ((HPA.patOrd))
  module PB =  PosetStr ((HPB.patOrd))

  module PAD =  DecPoset ((HPA.patDecPoset))
  module PBD =  DecPoset ((HPB.patDecPoset))

  ℙA = _ 
  ℙB = _ 

  module DℙA = DecPoset {P = ℙA} (DecPosetℙ _ _ (HPA.patDecPoset))
  module DℙB = DecPoset {P = ℙB} (DecPosetℙ _ _ (HPB.patDecPoset))

  

  open PosetStr

  open Poset⊎ _ _ (DecPosetℙ _ _ HPA.patDecPoset)
              _ _ (DecPosetℙ _ _ HPB.patDecPoset)

  open DecPoset DP⊎


  w : HasPat (A ⊎ B)
  HasPat.Pat w = ℙ HPA.Pat ⊎ ℙ HPB.Pat
  HasPat.patData w = ⊎.rec patData' patData' 
  HasPat.patOrd w = PS⊎
  HasPat.patDecPoset w = DP⊎

  
  HasPat.pat─ w =
   (─ℙ _ _ _ HPA.pat─ HPA.patSAC)
    ─
   (─ℙ _ _ _ HPB.pat─ HPB.patSAC)

  HasPat.patSAC w = ([] ∷ inl ₋₋ [ tt , tt ]s ∷ inr ₋₋ [ tt , tt ]s) , ww
   where
   ww : _
   ww (inl x) =
     (λ b → b (∣ inl x , _ , PosetStr.is-refl PS⊎ (inl x) ∣₁)) ∘ snd ∘ fst ∘ snd

   ww (inr x) =
      (λ b → b (∣ inr x , _ , PosetStr.is-refl PS⊎ (inr x) ∣₁)) ∘ snd ∘ snd
  HasPat.toPat w =
    ⊎.map (⌞_ ∘ HPA.toPat) (⌞_ ∘ HPB.toPat)
  HasPat.toPatMin w (inl x) (inl (⌞_ x₂)) x₁ = HPA.toPatMin x x₂ x₁
  HasPat.toPatMin w (inr x) (inr (⌞_ x₂)) x₁ = HPB.toPatMin x x₂ x₁
  HasPat.patDataEquiv w (inl x) =
    isoToEquiv ww ∙ₑ patData'Equiv x
   where
   ww : Iso _ _
   Iso.fun ww (inl x , y) = x , y
   Iso.inv ww (x' , y) = inl x' , y
   Iso.rightInv ww _ = refl
   Iso.leftInv ww (inl x , y) = refl
  HasPat.patDataEquiv w (inr x) =
    isoToEquiv ww ∙ₑ patData'Equiv x
   where
   ww : Iso _ _
   Iso.fun ww (inr x , y) = x , y
   Iso.inv ww (x' , y) = inr x' , y
   Iso.rightInv ww _ = refl
   Iso.leftInv ww (inr x , y) = refl
   
