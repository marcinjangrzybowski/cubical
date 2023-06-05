{-# OPTIONS --safe --experimental-lossy-unification  #-} --experimental-lossy-unification  
module Cubical.HITs.ListedFiniteSet.Base3CTabMore where

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
open import Cubical.HITs.ListedFiniteSet.Base3CTab

open import Cubical.HITs.Permutation.Group
open import Cubical.HITs.Permutation.Base hiding (ℙrm)

open import Cubical.Data.Nat.Order.Permutation

open import Cubical.Algebra.Group.Morphisms

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B : Type ℓ

𝕃Fin-rec : ∀ xs → A → (𝕃Fin xs → A)
                → 𝕃Fin (tt ∷2 xs) → A

𝕃Fin-rec _ _ f ((false , snd₂) , snd₁) = f (snd₂ , snd₁)
𝕃Fin-rec _ a _ ((true , snd₂) , snd₁) = a



whisk-cong : {ℓ ℓ' : Level} {A : I → Type ℓ} {B : (i : I) → Type ℓ'}
      (f : (i : I) → (A i) → B i) {x x' : A i0} {y y' : A i1}
      → (p : x' ≡ x)
      → (q : PathP (λ i → A i) x y)
      → (r : y ≡ y')
      → congP f (p ◁ q ▷ r)
         ≡
        (cong (f i0) p ◁ congP f q ▷ cong (f i1) r) 
whisk-cong {A = A} {B} f {x} {y} p q r i j =
    hcomp 
      (λ k → λ  { (j = i0) → f j (p (~ k))
                ; (j = i1) → f j (r k)
                ; (i = i0) → f j (doubleWhiskFiller p q r k j)
                }) (f j (q j))

congP-iso : {ℓ ℓ' : Level} {A : I → Type ℓ} {B : (i : I) → Type ℓ'}
      (e : (i : I) → (A i) ≃ B i) {x : A i0} {y : A i1}
      → Iso (PathP A x y) (PathP B (fst (e i0) x ) (fst (e i1) y)) 
congP-iso {A = A} {B} e {x} {y} = w
 where
  w : Iso (PathP A x y) (PathP B (fst (e i0) x) (fst (e i1) y))
  Iso.fun w = congP (λ i → fst (e i))
  Iso.inv w p =  sym (retEq (e i0) x) ◁ congP (λ i → invEq (e i)) p ▷ retEq (e i1) y 
  Iso.rightInv w b = 
    whisk-cong (λ i → fst (e i)) (sym (retEq (e i0) x)) _ _
      ∙ cong₂ {B = λ z → _ ≡ fst (e i1) y}
              (_◁ congP (λ i → fst (e i) ∘ invEq (e i)) b ▷_) 
         (sym (cong sym (commPathIsEq (snd (e i0)) x)))
         
         ((sym ((commPathIsEq (snd (e i1)) y)))) ∙
         (λ j → ((λ i → secEq (e i0) (fst (e i0) x) (~ i ∨ j)) ◁
       (λ i → secEq (e i) (( (b i))) j) ▷ (λ i → secEq (e i1) (fst (e i1) y) (i ∨ j))))
         ∙
         sym (doubleWhiskFiller refl b refl)

  Iso.leftInv w a =
     _ 
     ≡⟨ (λ j → ((λ i → retEq (e i0) x (~ i ∨ j)) ◁
       (λ i → retEq (e i) ((a i)) j) ▷ (λ i → retEq (e i1) y (i ∨ j)))) ⟩
       (refl ◁ a ▷ refl)
       
     ≡⟨ sym (doubleWhiskFiller refl a refl) ⟩
      _ ∎

preCompDep : (e : A ≃ B) → {C : A → Type ℓ'} →
       (∀ (b : B) → C (invEq e b)) → (∀ a → C a)
preCompDep e {C = C} f a = subst C (retEq e a ) (f (fst e a))



𝕃Fin-comm-snd : ∀ 𝕝 {a' a''} →
   (x
       : Bool ×
         Bool × 𝕃Bool 𝕝) →
      fst (𝕃FinSnd (a' ∷2 a'' ∷2 𝕝) x) →
      fst (𝕃FinSnd (a'' ∷2 a' ∷2 𝕝) (equivFun Σ-swap-01-≃ x))
𝕃Fin-comm-snd 𝕝 {tt} {tt} = uncurry (uncurry ∘ curry w)
  where
  w : (x : Bool × Bool) → _ 
  w (false , false) y x₁ = x₁
  w (false , true) y x₁ = x₁
  w (true , false) y x₁ = x₁

𝕃Fin-comm-snd⁻ : ∀ 𝕝 {a' a''} →
   (x
       : Bool ×
         Bool × 𝕃Bool 𝕝) →
      fst (𝕃FinSnd (a'' ∷2 a' ∷2 𝕝) (equivFun Σ-swap-01-≃ x)) → 
      fst (𝕃FinSnd (a' ∷2 a'' ∷2 𝕝) x)

𝕃Fin-comm-snd⁻ 𝕝 {tt} {tt} = uncurry (uncurry ∘ curry w)
  where
  w : (x : Bool × Bool) → _ 
  w (false , false) y x₁ = x₁
  w (false , true) y x₁ = x₁
  w (true , false) y x₁ = x₁


𝕃Fin-comm-unglue-equiv0 : ∀ 𝕝 {a' a''} → 𝕃Fin (a' ∷2 a'' ∷2 𝕝) ≃ 𝕃Fin (a'' ∷2 a' ∷2 𝕝)
𝕃Fin-comm-unglue-equiv0 𝕝 {a'} {a''}  = Σ-cong-equiv-prop
  Σ-swap-01-≃
  (snd ∘ 𝕃FinSnd (a' ∷2 a'' ∷2 𝕝))
  (snd ∘ 𝕃FinSnd (a'' ∷2 a' ∷2 𝕝))
  (𝕃Fin-comm-snd 𝕝 {a'} {a''})
  (𝕃Fin-comm-snd⁻ 𝕝 {a'} {a''})




-- RElimSet.f w
--  where
--  w : RElimSet
--        (λ z →
--           (y : 𝕃Fin (tt ∷2 tt ∷2 z) → _) →
--           Path (FMSet2C Unit) (<$tt (𝕃tab (tt ∷2 tt ∷2 z) y))
--           (<$tt
--            (𝕃tab (tt ∷2 tt ∷2 z) (y ∘ invEq (𝕃Fin-comm-unglue-equiv0 z)))))
--  RElimSet.[]* w y = refl
--  (w RElimSet.∷* x) {xs} x₁ y = cong (tt ∷2_) (x₁ {!y ∘ ? !})
--  RElimSet.comm* w = {!!}
--  RElimSet.trunc* w = {!!}

𝕃Fin-comm-unglue-equiv : ∀ 𝕝 {a' a''} →
             PathP (λ i → 𝕃Fin (comm a' a'' 𝕝 i) ≃ (𝕃Fin (a'' ∷2 a' ∷2 𝕝)))
               (𝕃Fin-comm-unglue-equiv0 𝕝 {a'} {a''})
                -- (𝕃Fin-swap01 𝕝 {a'} {a''} ,
                --  {!snd (Σ-cong-equiv-prop ? ? ? ? ?)!})
               (idEquiv _)
               -- (𝕃Fin-suc (a' ∷2 𝕝) {a''} (𝕃Fin-suc 𝕝 {a'} x))
               -- (𝕃Fin-suc (a'' ∷2 𝕝) {a'} (𝕃Fin-suc 𝕝 {a''} x))
𝕃Fin-comm-unglue-equiv 𝕝 {tt} {tt} = equivPathP
     (w)
       (snd (𝕃Fin-comm-unglue-equiv0 𝕝 {tt} {tt})) (idIsEquiv _)
 where
 


 w : PathP (λ i → 𝕃Fin (comm tt tt 𝕝 i) → 𝕃Fin (tt ∷2 tt ∷2 𝕝))
       (fst (𝕃Fin-comm-unglue-equiv0 𝕝)) (idfun (𝕃Fin (comm tt tt 𝕝 i1)))
 fst (w i (x , y)) = ua-unglue Σ-swap-01-≃ i x
 snd (w i (x , y)) = isProp→PathP
     (λ i → isPropΠ λ (x : 𝕃Fin (comm tt tt 𝕝 i)) → snd (𝕃FinSnd (tt ∷2 tt ∷2 𝕝)
         (ua-unglue Σ-swap-01-≃ i (fst x))))
           (snd ∘ fst (𝕃Fin-comm-unglue-equiv0 𝕝) ) snd i (x , y)

𝕃Fin-comm-unglue-equiv-lem : (xs : FMSet2C Unit) (x : 𝕃Fin xs) →
  SquareP (λ i j → 𝕃Bool (comm tt tt xs i))
    (λ j → false , false , fst x) refl
     (λ i → ((funExt (𝕃Fin-comm xs) i x .fst)))
     λ i → (invEq (𝕃Fin-comm-unglue-equiv xs i)
         (𝕃Fin-suc (tt ∷2 xs) (𝕃Fin-suc xs x)) .fst)
  -- ∀ i →  
  --  Path (𝕃Bool (comm tt tt xs i)) ((funExt (𝕃Fin-comm xs) i x .fst))
  --        (invEq (𝕃Fin-comm-unglue-equiv xs i)
  --        (𝕃Fin-suc (tt ∷2 xs) (𝕃Fin-suc xs x)) .fst)
𝕃Fin-comm-unglue-equiv-lem xs x =
  isSet→SquareP (λ i j → (isSet𝕃₂ _ (isSetBool) (comm tt tt xs i))) _ _ _ _

module 𝕃ook' (isGroupoidA : isGroupoid A) where
 fOO = fromOnlyOneₚ
         (isGroupoidΣ isGroupoidA (λ _ → isSet→isGroupoid isSetBool))

 𝕃look : (𝕝 : FMSet2 A) → (𝕃Fin (<$tt 𝕝) → A)
 𝕃look 𝕝 b = 
   let (x , y) = 𝕃addIndex 𝕝 b
   in fst (fst (fOO x y))


--  -- 𝕃look-comm : ∀ x y xs → 
--  --      Square {A = 𝕃Fin (<$tt xs) → A}
--  --       (λ i x' → 𝕃look (comm x y xs i) (𝕃Fin-comm (<$tt xs) x' i))
--  --       (λ _ → 𝕃look xs)
--  --       (λ _ → 𝕃look xs)
--  --       (λ _ → 𝕃look xs)
--  -- 𝕃look-comm x y xs = 
--  --   congSq (λ q b →
--  --        fst (fst (fOO ((fst (𝕃addIndex xs b))) (q b))))
--  --        (isProp→SquareP (λ _ _ → isPropΠ λ b →
--  --            snd (onlyOneₚ (fst (𝕃addIndex xs b))))
--  --            _ _ _ _)


--  -- look-tab : section (uncurry 𝕃tab) (λ 𝕝 → <$tt 𝕝 , 𝕃look 𝕝)
--  -- look-tab = RElimSet.f w
--  --  where
--  --  w : RElimSet (λ z → 𝕃tab (<$tt z) (𝕃look z) ≡ z)
--  --  RElimSet.[]* w _ = []
--  --  (w RElimSet.∷* x) = cong (x ∷2_)
--  --  RElimSet.comm* w x y {xs} b =
--  --    congSqP (λ i j v → comm x y v i)       
--  --      (flipSquare ( wqw ◁ λ j i → b j ))

--  --   where
--  --    wqw : (cong (uncurry 𝕃tab)
--  --                                  (ΣPathP ((λ _ → <$tt xs) ,
--  --                                    λ i x' →
--  --                 𝕃look (comm x y xs i)
--  --                 (𝕃Fin-comm
--  --                  (<$tt xs)
--  --                  x' i)))) ≡ (λ _ → (𝕃tab (<$tt xs) (𝕃look xs)))
--  --    wqw = congSq
--  --          {a₀₋ = ΣPathP
--  --                   (refl ,
--  --                    (λ i x' →
--  --                       𝕃look (comm x y xs i) (𝕃Fin-comm (<$tt xs) x' i)))}
--  --          {a₁₋ = refl}
--  --          {refl}
--  --          {refl}
--  --          (uncurry 𝕃tab)
--  --              (ΣSquareP ((λ _ _ → <$tt xs) ,
--  --                  (𝕃look-comm x y xs)))
 
--  --  RElimSet.trunc* w xs = trunc _ _

--  -- tab-look-∷ : ∀ (xs : FM2⊤) (x₁ : (y₁ : 𝕃Fin (xs) → A) →
--  --      Path (Σ FM2⊤ λ 𝕝 → 𝕃Fin 𝕝 → A) {!(<$tt (𝕃tab xs y₁) , 𝕃look (uncurry 𝕃tab (xs , y₁)))!}
--  --       {!!}) y →
--  --       Path (Σ {!!} {!!})
--  --      {!!}
--  --     {!!}


--  --     --  Path ? (<$tt (uncurry 𝕃tab (xs , y₁)) , 𝕃look (uncurry 𝕃tab (xs , y₁)))
--  --     --   (xs , y₁)) y →
--  --     --   Path ?
--  --     --  (<$tt (uncurry 𝕃tab (tt ∷2 xs , y)) ,
--  --     --  𝕃look (uncurry 𝕃tab (tt ∷2 xs , y)))
--  --     -- (tt ∷2 xs , y)
--  -- tab-look-∷ xs x₁ y = {!!}
--    --       ΣPathP ((λ i → tt ∷2 fst (z i)) , ww)
--    -- where
--    --  z = x₁ (y ∘ 𝕃Fin-suc xs)

--    --  ww : PathP (λ i → 𝕃Fin (tt ∷2 fst (z i)) → A)
--    --         (𝕃look (uncurry 𝕃tab (tt ∷2 xs , y))) y
--    --  ww = ?
--    --  -- ww i ((false , snd₂) , snd₁) = snd (z i) (snd₂ , snd₁)
--    --  -- ww i ((true , snd₂) , snd₁) =
--    --  --  let zwz = (coei→1 (λ i → Σ _ (λ v → ⟨ 𝕃allFalse (fst (z i)) v ⟩)) i (snd₂ , snd₁))
--    --  --  in y ((true ,
--    --  --       allFalse→≡repeat-false-𝔽 xs zwz (~ i)
--    --  --       ) , isProp→PathP
--    --  --             (λ i →
--    --  --                 snd
--    --  --                  (𝕃FinSnd (tt ∷2 xs)
--    --  --                   (true ,
--    --  --                    allFalse→≡repeat-false-𝔽 xs zwz (~ i) )))
--    --  --             (repeat𝕃allFalse xs) (snd zwz) i)




 module _ (xs  : FMSet2C Unit)
       (x-f : ((y : 𝕃Fin xs → A) →
       (Path (FM2⊤) (<$tt (𝕃tab xs y))) (xs)))
       
         (y : 𝕃Fin (tt ∷2 xs) → A) where

  tab-look-∷-fst :  (<$tt (𝕃tab (tt ∷2 xs) y)) ≡ (tt ∷2 xs ) 
  tab-look-∷-fst = cong (tt ∷2_) (x-f (y ∘' 𝕃Fin-suc xs))


  module _ (x-s : (y : 𝕃Fin xs → A) →
       (PathP (λ i → 𝕃Fin (x-f y i) → A )
           (𝕃look (uncurry 𝕃tab (xs , y)))
           (y))) where
           
   tab-look-∷-snd' : (b : Bool) →
      PathP (λ i → (bs : (𝕃Bool (x-f (y ∘' 𝕃Fin-suc xs) i))) → 
                    (⟨ 𝕃FinSnd (tt ∷2 (x-f (y ∘' 𝕃Fin-suc xs) i))
                                (b , bs) ⟩ ) → A)
        (λ bs cs → 𝕃look (𝕃tab (tt ∷2 xs) y) ((b , bs) , cs) )
        (λ bs cs → y ((b , bs) , cs))
   tab-look-∷-snd' false i bs cs = x-s (y ∘' 𝕃Fin-suc xs) i (bs , cs)
   tab-look-∷-snd' true =
    congP (λ i → curry ∘' ((y ∘' invEq Σ-assoc-≃ ∘' (true ,_)) ∘'_))
       (funExtDep λ {_} {x₁} _ →  
          isContr→isProp (isContrΣ𝕃allFalse xs) _ x₁)



   tab-look-∷-snd : PathP (λ i → 𝕃Fin (tab-look-∷-fst i) → A)
               (𝕃look (uncurry 𝕃tab (tt ∷2 xs , y)))
               y
   tab-look-∷-snd  =
     congP (λ _ → uncurry ∘ uncurry)
       (funExt (tab-look-∷-snd'))



 module _ (xs  : FMSet2C Unit)
       (x-f : ((y : 𝕃Fin xs → A) →
       (Path (FM2⊤) (<$tt (𝕃tab xs y))) (xs)))
       (x-s : (y : 𝕃Fin xs → A) →
       (PathP (λ i → 𝕃Fin (x-f y i) → A )
           (𝕃look (uncurry 𝕃tab (xs , y)))
           (y)))
          where

  𝕃Fin-comm-unglue-equiv0-lem :
    (y : 𝕃Fin (tt ∷2 tt ∷2 xs) → A) →
      Path (FMSet2C Unit) (<$tt (𝕃tab (tt ∷2 tt ∷2 xs) y))
      (<$tt (𝕃tab (tt ∷2 tt ∷2 xs) (y ∘ invEq (𝕃Fin-comm-unglue-equiv0 xs))))
  𝕃Fin-comm-unglue-equiv0-lem y =
      
      tab-look-∷-fst (tt ∷2 xs) (tab-look-∷-fst xs x-f ) y
       ∙∙ comm tt tt xs ∙∙ 
       sym (tab-look-∷-fst (tt ∷2 xs) (tab-look-∷-fst xs x-f )
         (y ∘ invEq (𝕃Fin-comm-unglue-equiv0 xs)))


  pp : (y : 𝕃Fin (tt ∷2 tt ∷2 xs) → A) →
      <$tt (uncurry 𝕃tab (tt ∷2 tt ∷2 xs , y)) ≡ tt ∷2 tt ∷2 xs
  pp = tab-look-∷-fst (tt ∷2 xs)
             (tab-look-∷-fst xs x-f)  

  tab-look-comm-fst :  PathP
      (λ i →
         (y : 𝕃Fin (comm tt tt xs i) → A) →
         (<$tt (uncurry 𝕃tab (comm tt tt xs i , y)))
         ≡ (comm tt tt xs i))
      pp pp

  tab-look-comm-fst i y j =
       comm tt tt (x-f (y ∘ funExt (𝕃Fin-comm xs) i) j ) i

  pP' : (y : 𝕃Fin (tt ∷2 tt ∷2 xs) → A) →
      PathP
        (λ i →
           𝕃Fin
           (tab-look-∷-fst (tt ∷2 xs) (tab-look-∷-fst xs x-f)
             y i) →
           A)
        (𝕃look (uncurry 𝕃tab (tt ∷2 tt ∷2 xs , y))) y
  pP' y = tab-look-∷-snd (tt ∷2 xs)
             (tab-look-∷-fst xs x-f)
                 y λ y' → (tab-look-∷-snd xs x-f y' x-s) 


  tab-look-comm-snd-ω : (i : I) (y :  𝕃Fin (comm tt tt xs i) → A)
    (j : I) →
     𝕃Fin
      (tab-look-comm-fst i y j) → A

  tab-look-comm-snd-ω i y j =
    let ff : (𝕃Fin (comm tt tt (x-f (y ∘ funExt (𝕃Fin-comm xs) i) j ) i))
               → 𝕃Fin (comm tt tt xs i)
        ff = {!!}
    in y ∘ ff


  tab-look-comm-snd' : PathP (λ i →
    (y : 𝕃Fin (comm tt tt xs i) → A)
     → PathP (λ j → 𝕃Fin (tab-look-comm-fst i y j) → A)
       {!!} {!!})
        {!!}
        {!!}
    

  tab-look-comm-snd' i y j =
    pP' (y ∘ invEq (𝕃Fin-comm-unglue-equiv xs {tt} {tt} i)) j ∘'
      isSet→SquareP
        {A = λ i j → ∀ y → 𝕃Fin (tab-look-comm-fst i y j) →
             𝕃Fin
             (tab-look-∷-fst (tt ∷2 xs) (tab-look-∷-fst xs x-f)
              (λ x → y (invEq (𝕃Fin-comm-unglue-equiv xs i) x)) j)}
             (λ i j → isSetΠ2 λ y _ →
                isSet𝕃Fin ((tab-look-∷-fst (tt ∷2 xs) (tab-look-∷-fst xs x-f)
                (y ∘ (invEq (𝕃Fin-comm-unglue-equiv xs i))) j)))
         {λ y₂ →
              transport (cong′ (𝕃Fin)
                {x = <$tt (𝕃tab (tt ∷2 tt ∷2 xs) y₂)}
                {y = <$tt (𝕃tab (tt ∷2 tt ∷2 xs)
                  (λ x → y₂ (invEq (𝕃Fin-comm-unglue-equiv0 xs) x)))}
                   (𝕃Fin-comm-unglue-equiv0-lem y₂) 
               )
               -- ∘' {!fst (𝕃Fin-comm-unglue-equiv0 (<$tt xs) {tt} {tt})!}
            }

           {λ y₂ → fst (𝕃Fin-comm-unglue-equiv xs i0)}
            (funExt (λ y* →
               congP (λ _ → uncurry ∘ uncurry ∘ (uncurry ∘_) ∘ curry)
                 (funExt (congP (λ _ → curry) ∘ zzz y*))))
         {λ y₂ y'' → y''} {λ y₂ y'' → y''} (λ i y y'' → y'')
         {!!}
         -- (λ i y → {!!})
         (λ i y → fst (𝕃Fin-comm-unglue-equiv xs i))
         i j y
    where
     zzz : (y*  : 𝕃Fin (tt ∷2 tt ∷2 xs) → A) →
            (b : Bool × Bool) → _
     zzz y* (false , false)  =
      -- toPathP (funExt λ x →
      --   ΣPathPProp (λ x → snd (𝕃FinSnd (tt ∷2 tt ∷2 xs) x))
      --     (ΣPathP (refl , ΣPathP (refl , {!refl!}))))
       funExtDep
       λ {x₀} {x₁} p →  ΣPathPProp (λ x → snd (𝕃FinSnd (tt ∷2 tt ∷2 xs) x))
              {!!}
               -- (toPathP refl ▷
               --  ( transport
               --      (λ z →
               --         𝕃Bool
               --         (tab-look-∷-fst (tt ∷2 xs) (tab-look-∷-fst xs x-f)
               --          (λ x → y* (invEq (𝕃Fin-comm-unglue-equiv xs i0) x)) z))
               --      (
               --       (transp (λ i₁ → 𝕃Bool (𝕃Fin-comm-unglue-equiv0-lem y* i₁)) i0
               --        ((false , false , fst x₀))))
               --   ≡⟨ {!!} ⟩
               --   (false , false , fst x₁) ∎))


         -- toPathP (Σ≡Prop (λ x → snd (𝕃FinSnd (tt ∷2 tt ∷2 xs) x))
         --  (cong₂ _,_ refl
         --   (cong₂ _,_ refl
         --    {!!})))
      
       -- let xx = subst
       --           {x = (x-f (λ x → y* (𝕃Fin-suc (tt ∷2 xs) (𝕃Fin-suc xs x))) i)}
       --             {y = (tab-look-∷-fst (tt ∷2 xs) (tab-look-∷-fst xs x-f)
       --                (λ x → y* (invEq (𝕃Fin-comm-unglue-equiv0 xs) x)) i)}
       --            𝕃Fin {!!} (q , y)
       -- in {!!} --(false , false , fst xx) , (snd xx)
     zzz y* (false , true) = {!!}
     zzz y* (true , snd₁) = {!!}
     
  tab-look-comm-snd : PathP (λ i →
    (y : 𝕃Fin (comm tt tt xs i) → A)
     → PathP (λ j → 𝕃Fin (tab-look-comm-fst i y j) → A)
       ((𝕃look (uncurry 𝕃tab (comm tt tt xs i , y)))) y)
        pP'
        pP'
    

  tab-look-comm-snd = {!!}

-- funExtDep ww
--    where
--     ww : {x₀ x₁ : 𝕃Fin (tt ∷2 tt ∷2 xs) → A}
--       (p : PathP (λ z → 𝕃Fin (comm tt tt xs z) → A) x₀ x₁) →
--       PathP
--       (λ i →
--          PathP (λ j → 𝕃Fin (tab-look-comm-fst i (p i) j) → A)
--          (𝕃look (uncurry 𝕃tab (comm tt tt xs i , p i))) (p i))
--       (pP' x₀) (pP' x₁)
--     ww {x₀} {x₁} p =
--        Iso.inv (congP-iso (λ i →
--           isoToEquiv (congP-iso
--             λ i' → preCompEquiv
--               (invEquiv (𝕃Fin-comm-unglue-equiv
--                (x-f (λ x → p i (funExt (𝕃Fin-comm xs) i x)) i')
--                 {tt} {tt} i)))))
--                 (congSqP (λ _ _ → uncurry ∘ uncurry ∘ (uncurry ∘_) ∘ curry)
--                  (funExtSq _ _ _ _
--                    (congSqP (λ _ _ → curry) ∘ uncurry ww')))
--      where
--      ww' : (b b' : Bool) →
--        SquareP (λ i j →
--           Σ (𝕃Bool (x-f (λ x → p i (funExt (𝕃Fin-comm xs) i x)) j))
--              (λ v → ⟨
--                𝕃FinSnd
--                 {!tt ∷2 tt ∷2 ?!}
--                 {!b , b' , v!} ⟩) → A)
--          {!!}
--          {!!}
--          {!!}
--          {!!}
--      ww' = {!!}
--      -- ww' false false = {!!}
     
--      -- ww' false true = whiskSq.sq'
--      --     (λ i j → Σ (𝕃Bool ?) {!!} → A)
--      --     {!!}
--      --     {!!}
--      --     {!!}
--      --     {!!}
--      --     {!!}  
--      --  -- congSqP {A = λ i _ → 𝕃Fin (comm tt tt xs i)}
--      --  --    (λ i j a _ → pP' (p i ∘ {!!}) j {!a!})
--      --  --     (isSet→SquareP (λ i _ → isSet𝕃Fin (comm tt tt xs i)) _ _ _ _)
--      -- ww' true false = {!!}
--      -- ww' true true = {!!}
 
--  tab-look : retract (uncurry 𝕃tab) (λ 𝕝 → <$tt 𝕝 , 𝕃look 𝕝)
--  tab-look = uncurry (RElimSet.f w)
--   where
--   w : RElimSet _
--   fst (RElimSet.[]* w y i) = []
--   snd (RElimSet.[]* w y i) ()
--   fst ((w RElimSet.∷* tt) {xs} x y i) =
--    tab-look-∷-fst xs (cong fst ∘ x) y i
--   snd ((w RElimSet.∷* tt) {xs} x y i) =
--    tab-look-∷-snd xs (cong fst ∘ x) y (cong snd ∘ x) i
   

--   RElimSet.comm* w tt tt {xs} b i y =
--     ΣPathP ((tab-look-comm-fst xs (cong fst ∘ b) (cong snd ∘ b) i y) ,
--             (tab-look-comm-snd xs (cong fst ∘ b) (cong snd ∘ b) i y))
   
--   RElimSet.trunc* w xs = isSetΠ λ _ →
--     isGroupoidΣ trunc (λ _ → isGroupoidΠ λ _ → isGroupoidA) _ _




-- -- -- -- -- -- -- -- -- --  module _ (isGroupoidA : isGroupoid A) where

-- -- -- -- -- -- -- -- -- --   𝕃look : (𝕝 : FMSet2 A) → (𝕃Fin (<$tt 𝕝) → A)
-- -- -- -- -- -- -- -- -- --   𝕃look = RElim.ff
-- -- -- -- -- -- -- -- -- --      w λ _ _ → isGroupoidΠ λ _ → isGroupoidA
-- -- -- -- -- -- -- -- -- --    where

-- -- -- -- -- -- -- -- -- --    open RElim

-- -- -- -- -- -- -- -- -- --    w∷ : (x : A) (xs : FMSet2C A) → 
-- -- -- -- -- -- -- -- -- --          (𝕃Fin (<$tt xs) → A) →
-- -- -- -- -- -- -- -- -- --           𝕃Fin (<$tt (x ∷2 xs)) → A
-- -- -- -- -- -- -- -- -- --    w∷ _ _ f ((false , bs) , p) = f (bs , p)
-- -- -- -- -- -- -- -- -- --    w∷ a _ _ ((true , _) , _) = a

-- -- -- -- -- -- -- -- -- --    w-comm : (a a' : A) (xs : FMSet2C A) → 
-- -- -- -- -- -- -- -- -- --          (f : 𝕃Fin (<$tt xs) → A) →
-- -- -- -- -- -- -- -- -- --           Path (𝕃Fin (<$tt (a ∷2 a' ∷2 xs)) → A) (w∷ a (a' ∷2 xs) (w∷ a' xs f))
-- -- -- -- -- -- -- -- -- --           (λ x →
-- -- -- -- -- -- -- -- -- --             w∷ a' (a ∷2 xs) (w∷ a xs f)
-- -- -- -- -- -- -- -- -- --             (𝕃Fin-swap01 (<$tt xs) x))
-- -- -- -- -- -- -- -- -- --    w-comm a a' xs f i ((false , false , bs) , snd₁) = f (bs , snd₁)
-- -- -- -- -- -- -- -- -- --    w-comm a a' xs f i ((false , true , bs) , snd₁) = a'
-- -- -- -- -- -- -- -- -- --    w-comm a a' xs f i ((true , false , bs) , snd₁) = a

-- -- -- -- -- -- -- -- -- --    w-comm-inv : (a a' : A) (𝕝 : FMSet2C A) → 
-- -- -- -- -- -- -- -- -- --          (b : 𝕃Fin (<$tt 𝕝) → A) →
-- -- -- -- -- -- -- -- -- --            Square {A = (𝕃Fin (<$tt (a ∷2 a' ∷2 𝕝)) → A)}
-- -- -- -- -- -- -- -- -- --              (w-comm a a' 𝕝 b)
-- -- -- -- -- -- -- -- -- --              (cong (_∘ (𝕃Fin-swap01 (<$tt 𝕝))) (sym (w-comm a' a 𝕝 b)))
-- -- -- -- -- -- -- -- -- --              (cong {x = idfun _}
-- -- -- -- -- -- -- -- -- --                {y = 𝕃Fin-swap01 (<$tt 𝕝) ∘ 𝕃Fin-swap01 (<$tt 𝕝)}
-- -- -- -- -- -- -- -- -- --                 (w∷ a (a' ∷2 𝕝) (w∷ a' 𝕝 b) ∘'_)
-- -- -- -- -- -- -- -- -- --                 (funExt (𝕃Fin-swap01-invol (<$tt 𝕝))))
-- -- -- -- -- -- -- -- -- --              refl
-- -- -- -- -- -- -- -- -- --    -- w-comm-inv = {!!}
-- -- -- -- -- -- -- -- -- --    w-comm-inv a a' xs f i j ((false , false , bs) , snd₁) =
-- -- -- -- -- -- -- -- -- --      f {!!}
-- -- -- -- -- -- -- -- -- --    w-comm-inv a a' xs f i j ((false , true , bs) , snd₁) = a'
-- -- -- -- -- -- -- -- -- --    w-comm-inv a a' xs f i j ((true , false , bs) , snd₁) = a

-- -- -- -- -- -- -- -- -- --    w : RElim (λ z → 𝕃Fin (<$tt z) → A)
-- -- -- -- -- -- -- -- -- --    []* w ()
-- -- -- -- -- -- -- -- -- --    (w ∷* x) {xs} = w∷ x xs
-- -- -- -- -- -- -- -- -- --    comm* w a a' {𝕝} b =
-- -- -- -- -- -- -- -- -- --       w-comm a a' 𝕝 b
-- -- -- -- -- -- -- -- -- --        ◁ (λ i → w∷ a' (a ∷2 𝕝) (w∷ a 𝕝 b)
-- -- -- -- -- -- -- -- -- --             ∘ (𝕃Fin-comm-unglue (<$tt 𝕝) i)) 

-- -- -- -- -- -- -- -- -- --    comm-inv* w a a' {𝕝} b =
-- -- -- -- -- -- -- -- -- --        {!!}
-- -- -- -- -- -- -- -- -- --    commm* w = {!!}
-- -- -- -- -- -- -- -- -- --    commp* w = {!!}
-- -- -- -- -- -- -- -- -- --    hex* w = {!!}
 
-- -- -- -- -- -- -- -- -- -- --   -- look-tab : section (uncurry 𝕃tab)
-- -- -- -- -- -- -- -- -- -- --   --     (λ 𝕝 → <$tt 𝕝 , 𝕃look 𝕝)
-- -- -- -- -- -- -- -- -- -- --   -- look-tab = RElimSet.f w
-- -- -- -- -- -- -- -- -- -- --   --  where
-- -- -- -- -- -- -- -- -- -- --   --  w : RElimSet
-- -- -- -- -- -- -- -- -- -- --   --        (λ z →
-- -- -- -- -- -- -- -- -- -- --   --           uncurry 𝕃tab (<$tt z , 𝕃look z) ≡ z)
-- -- -- -- -- -- -- -- -- -- --   --  RElimSet.[]* w = refl
-- -- -- -- -- -- -- -- -- -- --   --  (w RElimSet.∷* a) x₁ = cong (a ∷2_) x₁
-- -- -- -- -- -- -- -- -- -- --   --  RElimSet.comm* w a a' {xs} b =
-- -- -- -- -- -- -- -- -- -- --   --    flipSquareP (
-- -- -- -- -- -- -- -- -- -- --   --      ({!!})
-- -- -- -- -- -- -- -- -- -- --   --      ◁ λ i j → comm-inv a a' (b i) (~ i) j)
-- -- -- -- -- -- -- -- -- -- --   --  RElimSet.trunc* w _ = trunc _ _

-- -- -- -- -- -- -- -- -- -- --   tab-look-fst : (x : FM2⊤) → (y : 𝕃Fin x → A) →
-- -- -- -- -- -- -- -- -- -- --      mapFM2 (idfun Unit) (λ _ → tt) (uncurry 𝕃tab (x , y)) ≡ x

-- -- -- -- -- -- -- -- -- -- --   tab-look-fst = RElimSet.f w
-- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- --    w : RElimSet
-- -- -- -- -- -- -- -- -- -- --          (λ z →
-- -- -- -- -- -- -- -- -- -- --             (y : 𝕃Fin z → A) →
-- -- -- -- -- -- -- -- -- -- --             <$tt (uncurry 𝕃tab (z , y)) ≡ z)
-- -- -- -- -- -- -- -- -- -- --    RElimSet.[]* w _ = refl
-- -- -- -- -- -- -- -- -- -- --    (w RElimSet.∷* x ) {xs} x₁ y = cong (x ∷2_) (x₁ (y ∘ 𝕃Fin-suc xs)) 
-- -- -- -- -- -- -- -- -- -- --    RElimSet.comm* w tt tt {xs} b i y j =
-- -- -- -- -- -- -- -- -- -- --       comm tt tt (b (λ x → y (𝕃Fin-comm xs x i)) j) i 
-- -- -- -- -- -- -- -- -- -- --    RElimSet.trunc* w xs =
-- -- -- -- -- -- -- -- -- -- --      isSetΠ λ y → trunc _ _


-- -- -- -- -- -- -- -- -- -- --   repF-tab-lem : ∀ xs (y : 𝕃Fin xs → A) →
-- -- -- -- -- -- -- -- -- -- --                let qq = tab-look-fst xs y i0
-- -- -- -- -- -- -- -- -- -- --             in ∀ (snd₁ : 𝕃Bool qq) → ⟨ 𝕃allFalse qq snd₁ ⟩ →  (repeatF xs) ≡
-- -- -- -- -- -- -- -- -- -- --         transport
-- -- -- -- -- -- -- -- -- -- --         (λ i → 𝕃Bool (tab-look-fst xs y i))
-- -- -- -- -- -- -- -- -- -- --         (snd₁)
-- -- -- -- -- -- -- -- -- -- --   repF-tab-lem = RElimProp.f w
-- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- --    w : RElimProp
-- -- -- -- -- -- -- -- -- -- --          (λ z →
-- -- -- -- -- -- -- -- -- -- --             (y : 𝕃Fin z → A) (snd₁ : 𝕃Bool (tab-look-fst z y i0)) →
-- -- -- -- -- -- -- -- -- -- --              ⟨ 𝕃allFalse (tab-look-fst z y i0) snd₁ ⟩ → 
-- -- -- -- -- -- -- -- -- -- --             repeatF z ≡ transport (λ i → 𝕃Bool (tab-look-fst z y i)) snd₁)
-- -- -- -- -- -- -- -- -- -- --    RElimProp.[]* w _ _ _ _ = tt* 
-- -- -- -- -- -- -- -- -- -- --    (w RElimProp.∷* tt) x₁ y (false , snd₁) qq =
-- -- -- -- -- -- -- -- -- -- --      cong₂ _,_ refl (x₁ _ snd₁ qq)
-- -- -- -- -- -- -- -- -- -- --    RElimProp.trunc* w xs =
-- -- -- -- -- -- -- -- -- -- --      isPropΠ3 λ _ _ _ → isSet𝕃₂ _ (isSetBool) xs _ _

-- -- -- -- -- -- -- -- -- -- --   𝕃Fin0-tab-lem : ∀ xs y (snd₁ : _) →
-- -- -- -- -- -- -- -- -- -- --      (⟨ 𝕃FinSnd (tt ∷2 tab-look-fst xs y i0) (true , snd₁) ⟩ ) →  (true , repeatF xs) ≡
-- -- -- -- -- -- -- -- -- -- --         transport
-- -- -- -- -- -- -- -- -- -- --         (λ i → 𝕃Bool (tt ∷2 tab-look-fst xs y i))
-- -- -- -- -- -- -- -- -- -- --         (true , snd₁)
-- -- -- -- -- -- -- -- -- -- --   𝕃Fin0-tab-lem xs y snd₁ qq = cong₂ _,_ refl (repF-tab-lem xs y snd₁ qq)
  
-- -- -- -- -- -- -- -- -- -- --   tab-look-snd : (x : FM2⊤) → (y : 𝕃Fin x → A) →
-- -- -- -- -- -- -- -- -- -- --      PathP (λ i → 𝕃Fin (tab-look-fst x y i) → A)
-- -- -- -- -- -- -- -- -- -- --        (𝕃look (uncurry 𝕃tab (x , y))) y     

-- -- -- -- -- -- -- -- -- -- --   tab-look-snd x y =  --toPathP ∘ ? ∘  (RElimSet.f w x)
-- -- -- -- -- -- -- -- -- -- --     let z = RElimSet.f w x y
-- -- -- -- -- -- -- -- -- -- --         z' = sym (funExt (uncurry z))
-- -- -- -- -- -- -- -- -- -- --     in symP (toPathP {!   z'!})
-- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- --     -- w : RElimSet (λ x →
-- -- -- -- -- -- -- -- -- -- --     --       (y : 𝕃Fin x → A) →
-- -- -- -- -- -- -- -- -- -- --     --       ( -- transport (λ i → 𝕃Fin (tab-look-fst x y i) → A)
-- -- -- -- -- -- -- -- -- -- --     --         Path (𝕃Fin x → A) (𝕃look (𝕃tab x y) ∘ (
-- -- -- -- -- -- -- -- -- -- --     --             (transport (λ i → 𝕃Fin (tab-look-fst x y (~ i)))
-- -- -- -- -- -- -- -- -- -- --     --               ))) (y)))
-- -- -- -- -- -- -- -- -- -- --     -- RElimSet.[]* w y i ()
-- -- -- -- -- -- -- -- -- -- --     -- (w RElimSet.∷* x) x₁ y i ((false , xs) , ys) = ?
-- -- -- -- -- -- -- -- -- -- --     -- (w RElimSet.∷* x) x₁ y i ((true , xs) , ys) = ?
-- -- -- -- -- -- -- -- -- -- --     -- RElimSet.comm* w = {!!}
-- -- -- -- -- -- -- -- -- -- --     -- RElimSet.trunc* w = {!!}
-- -- -- -- -- -- -- -- -- -- --     w : RElimSet (λ x →
-- -- -- -- -- -- -- -- -- -- --              (y : 𝕃Fin x → A) →
-- -- -- -- -- -- -- -- -- -- --              ( -- transport (λ i → 𝕃Fin (tab-look-fst x y i) → A)
-- -- -- -- -- -- -- -- -- -- --                ∀ v v' → (𝕃look (𝕃tab x y) (v , v')) ≡ y (
-- -- -- -- -- -- -- -- -- -- --                    (transport (λ i → 𝕃Fin (tab-look-fst x y i))
-- -- -- -- -- -- -- -- -- -- --                      ((v , v'))))))
-- -- -- -- -- -- -- -- -- -- --     RElimSet.[]* w y v ()
-- -- -- -- -- -- -- -- -- -- --     (w RElimSet.∷* x) x₁ y (false , snd₁) v' =
-- -- -- -- -- -- -- -- -- -- --        x₁ _ snd₁ v'
-- -- -- -- -- -- -- -- -- -- --     (w RElimSet.∷* tt) {xs} x₁ y (true , snd₁) v' =
-- -- -- -- -- -- -- -- -- -- --       cong′ y 
-- -- -- -- -- -- -- -- -- -- --         (Σ≡Prop (snd ∘ (𝕃FinSnd (tt ∷2 xs)))
-- -- -- -- -- -- -- -- -- -- --           (𝕃Fin0-tab-lem xs (λ x₂ → y (𝕃Fin-suc xs x₂)) snd₁ v') )
-- -- -- -- -- -- -- -- -- -- --     -- RElimSet.comm* w tt tt {xs} b i y v v' j =
-- -- -- -- -- -- -- -- -- -- --     --   let qq = (𝕃Fin-comm-unglue
-- -- -- -- -- -- -- -- -- -- --     --                 ((<$tt (𝕃tab (xs)
-- -- -- -- -- -- -- -- -- -- --     --                      (y ∘' λ x → 𝕃Fin-comm xs x i))))
-- -- -- -- -- -- -- -- -- -- --     --                 i (v , v'))
-- -- -- -- -- -- -- -- -- -- --     --       q = b (y ∘' λ x → 𝕃Fin-comm xs x i)
-- -- -- -- -- -- -- -- -- -- --     --            (snd (snd (fst qq)))
-- -- -- -- -- -- -- -- -- -- --     --   in {!!}
-- -- -- -- -- -- -- -- -- -- --     RElimSet.comm* w tt tt {xs} b =
-- -- -- -- -- -- -- -- -- -- --       -- let q : PathP (λ i → (y : (𝕃Fin (comm tt tt xs i)) → A) →
-- -- -- -- -- -- -- -- -- -- --       --                ∀ v v' → _ ≡ _)
-- -- -- -- -- -- -- -- -- -- --       --            (λ y → b (λ x₁ → y ((false , false , fst x₁) , snd x₁)))
-- -- -- -- -- -- -- -- -- -- --       --             (λ y → b (λ x₁ → y ((false , false , fst x₁) , snd x₁)))
-- -- -- -- -- -- -- -- -- -- --       --     q = λ i y → b (y ∘' λ x → 𝕃Fin-comm xs x i)
-- -- -- -- -- -- -- -- -- -- --       -- in
-- -- -- -- -- -- -- -- -- -- --          congP (λ _ → curry ∘ curry)
-- -- -- -- -- -- -- -- -- -- --            (funTypePathP _ _ _ _ (funExt ww''))
           
-- -- -- -- -- -- -- -- -- -- --      where
-- -- -- -- -- -- -- -- -- -- --       ww'' : (x : Σ (Σ _ _) _) → _ ≡ _ 
-- -- -- -- -- -- -- -- -- -- --       ww'' ((fst₁ , false , false , bb'') , snd₁) =
-- -- -- -- -- -- -- -- -- -- --         {!!}
-- -- -- -- -- -- -- -- -- -- --       ww'' ((f , false , true , bb'') , snd₁) i j = {!!}
-- -- -- -- -- -- -- -- -- -- --        --  ((
-- -- -- -- -- -- -- -- -- -- --        --   (((λ i → transp (λ _ → A) (~ i) (f (p₀ i) )) ∙
-- -- -- -- -- -- -- -- -- -- --        --           cong (transport refl ∘ f) p₁)
-- -- -- -- -- -- -- -- -- -- --        --        ∙∙P (cong (transport refl ∘ f) p₂) ∙∙P
-- -- -- -- -- -- -- -- -- -- --        --        (λ i → transp (λ _ → A) i (f (p₃ i))))
-- -- -- -- -- -- -- -- -- -- --        --   ≡⟨ (λ j →
-- -- -- -- -- -- -- -- -- -- --        --      fixComp (((λ i → transp (λ _ → A) ((~ i) ∨ j) (f (p₀ i))))
-- -- -- -- -- -- -- -- -- -- --        --           ∙ ( (cong (transp (λ _ → A) (j) ∘ f) p₁)))
-- -- -- -- -- -- -- -- -- -- --        --         ((cong (transp (λ _ → A) (j) ∘ f) p₂))
-- -- -- -- -- -- -- -- -- -- --        --         ((λ i → transp (λ _ → A) (i ∨ j) (f (p₃ i)))) (~ j))
-- -- -- -- -- -- -- -- -- -- --        --      ∙∙ 
-- -- -- -- -- -- -- -- -- -- --        --          (λ j → (cong-∙ f p₀ p₁ (~ j)  ) ∙∙ (cong f p₂) ∙∙ (cong f p₃))
-- -- -- -- -- -- -- -- -- -- --        --          ∙∙ (sym (cong-∙∙ f (p₀ ∙ p₁) p₂ p₃))
-- -- -- -- -- -- -- -- -- -- --        --          ⟩

-- -- -- -- -- -- -- -- -- -- --        --    (cong f ((p₀ ∙ p₁) ∙∙ p₂ ∙∙ p₃)) ∎ ))

-- -- -- -- -- -- -- -- -- -- --        --    ◁ congSq f
-- -- -- -- -- -- -- -- -- -- --        --       (isSet→isSet' (isSet𝕃Fin (tt ∷2 tt ∷2 xs))
-- -- -- -- -- -- -- -- -- -- --        --         ((p₀ ∙ p₁) ∙∙ p₂ ∙∙ p₃) _ _ _)
-- -- -- -- -- -- -- -- -- -- --        -- where
-- -- -- -- -- -- -- -- -- -- --        --  p₀ : Path (𝕃Fin (tt ∷2 tt ∷2 xs))
-- -- -- -- -- -- -- -- -- -- --        --        (𝕃Fin-suc (tt ∷2 xs) (𝕃Fin0 xs))
-- -- -- -- -- -- -- -- -- -- --        --        (transp (λ j → 𝕃Fin (comm tt tt xs (i0 ∨ ~ (i0 ∨ ~ j)))) i0
-- -- -- -- -- -- -- -- -- -- --        --          (fst (𝕃Fin-01 xs i0)))
-- -- -- -- -- -- -- -- -- -- --        --  p₀ = ?

-- -- -- -- -- -- -- -- -- -- --        --  p₁ : Path (𝕃Fin (tt ∷2 tt ∷2 xs)) _ _
-- -- -- -- -- -- -- -- -- -- --        --  p₁ = _

-- -- -- -- -- -- -- -- -- -- --        --  p₂ : Path (𝕃Fin (tt ∷2 tt ∷2 xs)) _ _
-- -- -- -- -- -- -- -- -- -- --        --  p₂ = _

-- -- -- -- -- -- -- -- -- -- --        --  p₃ : Path (𝕃Fin (tt ∷2 tt ∷2 xs)) _ _
-- -- -- -- -- -- -- -- -- -- --        --  p₃ = _

-- -- -- -- -- -- -- -- -- -- --       ww'' ((fst₁ , true , false , bb'') , snd₁)  = {!!}
          
-- -- -- -- -- -- -- -- -- -- --         --  -- -- (λ i j → hcomp
-- -- -- -- -- -- -- -- -- -- --         --  -- --      (λ k → λ {
-- -- -- -- -- -- -- -- -- -- --         --  -- --           (i = i1) → fst₁ {!!}
-- -- -- -- -- -- -- -- -- -- --         --  -- --          ;(j = i0) → fst₁ {!!}
-- -- -- -- -- -- -- -- -- -- --         --  -- --          ;(j = i1) → fst₁ {!!}
-- -- -- -- -- -- -- -- -- -- --         --  -- --          })
-- -- -- -- -- -- -- -- -- -- --         --  -- --      (fst₁ {!!}))
-- -- -- -- -- -- -- -- -- -- --         --  -- (λ i j → fst₁
-- -- -- -- -- -- -- -- -- -- --         --  --  (fill (λ _ → 𝕃Fin (tt ∷2 tt ∷2 xs))
-- -- -- -- -- -- -- -- -- -- --         --  --      (λ k → 
-- -- -- -- -- -- -- -- -- -- --         --  --        (λ { (j = i0) →
-- -- -- -- -- -- -- -- -- -- --         --  --            (true , repeatF (tt ∷2 xs)) , repeat𝕃allFalse (tt ∷2 xs)
-- -- -- -- -- -- -- -- -- -- --         --  --           ; (j = i1) →
-- -- -- -- -- -- -- -- -- -- --         --  --           {!transport
-- -- -- -- -- -- -- -- -- -- --         --  --             (λ i₁ → 𝕃Fin (tab-look-fst (tt ∷2 tt ∷2 xs) fst₁ i₁)) 
-- -- -- -- -- -- -- -- -- -- --         --  --               ((true , false , bb'') , snd₁)!}
-- -- -- -- -- -- -- -- -- -- --         --  --           }))
-- -- -- -- -- -- -- -- -- -- --         --  --    (inS {!!}) (~ i)))
-- -- -- -- -- -- -- -- -- -- --         --     ({!!} ) ◁ congSq fst₁
-- -- -- -- -- -- -- -- -- -- --         --      (isSet→isSet' (isSet𝕃Fin (tt ∷2 tt ∷2 xs)) _ _ _ _)
-- -- -- -- -- -- -- -- -- -- --         -- -- congSq fst₁ {!!}
        
           
-- -- -- -- -- -- -- -- -- -- --     RElimSet.trunc* w xs =
-- -- -- -- -- -- -- -- -- -- --       isSetΠ3 λ _ _ _ → isGroupoidA _ _

   
-- -- -- -- -- -- -- -- -- -- -- --   Iso-look-tab : Iso (Σ FM2⊤ λ 𝕝 → (𝕃Fin 𝕝 → A)) (FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- --   Iso.fun Iso-look-tab = uncurry 𝕃tab
-- -- -- -- -- -- -- -- -- -- -- --   Iso.inv Iso-look-tab =
-- -- -- -- -- -- -- -- -- -- -- --     λ 𝕝 → (mapFM2 (idfun _) (λ _ → _) 𝕝) , 𝕃look 𝕝
-- -- -- -- -- -- -- -- -- -- -- --   Iso.rightInv Iso-look-tab = look-tab
-- -- -- -- -- -- -- -- -- -- -- --   fst (Iso.leftInv Iso-look-tab (x , y) i) = tab-look-fst x y i
-- -- -- -- -- -- -- -- -- -- -- --   snd (Iso.leftInv Iso-look-tab (x , y) i) = tab-look-snd x y i


-- -- -- -- -- -- -- -- -- -- -- --   -- Iso-×^ : Iso (Σ (Σ ℕ ℙrm) λ (n , p) → fst (𝕍₂ Bool isSetBool n p))
-- -- -- -- -- -- -- -- -- -- -- --   --              (Σ _ (𝕃Bool))
-- -- -- -- -- -- -- -- -- -- -- --   -- Iso-×^ = Σ-cong-iso (invIso Iso-FM2⊤-Σℙrm) (uncurry λ n → R𝕡elimSet'.f (w n))
-- -- -- -- -- -- -- -- -- -- -- --   --  where

-- -- -- -- -- -- -- -- -- -- -- --   --  wIso : ∀ n → Iso (fst (𝕍₂ Bool isSetBool n 𝕡base))
-- -- -- -- -- -- -- -- -- -- -- --   --                   (𝕃Bool (toFM2⊤ (n , 𝕡base)))
-- -- -- -- -- -- -- -- -- -- -- --   --  wIso zero = idIso
-- -- -- -- -- -- -- -- -- -- -- --   --  wIso (suc n) = prodIso idIso (wIso n)

-- -- -- -- -- -- -- -- -- -- -- --   --  w : ∀ n → R𝕡elimSet'
-- -- -- -- -- -- -- -- -- -- -- --   --              (λ z →
-- -- -- -- -- -- -- -- -- -- -- --   --                 Iso (fst (𝕍₂ Bool isSetBool n z))
-- -- -- -- -- -- -- -- -- -- -- --   --                 (𝕃Bool (Iso.fun (invIso Iso-FM2⊤-Σℙrm) (n , z))))
-- -- -- -- -- -- -- -- -- -- -- --   --  R𝕡elimSet'.isSetA (w n) x =
-- -- -- -- -- -- -- -- -- -- -- --   --   isSet-SetsIso
-- -- -- -- -- -- -- -- -- -- -- --   --    (snd (𝕍₂ Bool isSetBool n x))
-- -- -- -- -- -- -- -- -- -- -- --   --    (isSet𝕃₂ Bool isSetBool (toFM2⊤ (n , x)))
-- -- -- -- -- -- -- -- -- -- -- --   --  R𝕡elimSet'.abase (w n) = wIso n
-- -- -- -- -- -- -- -- -- -- -- --   --  R𝕡elimSet'.aloop (w (suc n)) (suc k , k<) =
-- -- -- -- -- -- -- -- -- -- -- --   --   congP (λ _ z → prodIso idIso z)
-- -- -- -- -- -- -- -- -- -- -- --   --     (R𝕡elimSet'.aloop (w n) (k , k<))
-- -- -- -- -- -- -- -- -- -- -- --   --  Iso.fun (R𝕡elimSet'.aloop (w (suc (suc n))) (zero , k<) i) =
-- -- -- -- -- -- -- -- -- -- -- --   --    ua-gluePathExt Σ-swap-01-≃ i
-- -- -- -- -- -- -- -- -- -- -- --   --     ∘' (map-snd (map-snd (Iso.fun (wIso n))))
-- -- -- -- -- -- -- -- -- -- -- --   --     ∘' (swap-01 ∘' (ua-ungluePathExt Σ-swap-01-≃ i))
-- -- -- -- -- -- -- -- -- -- -- --   --  Iso.inv (R𝕡elimSet'.aloop (w (suc (suc n))) (zero , k<) i) =
-- -- -- -- -- -- -- -- -- -- -- --   --   ua-gluePathExt Σ-swap-01-≃ i
-- -- -- -- -- -- -- -- -- -- -- --   --     ∘' (map-snd (map-snd (Iso.inv (wIso n))))
-- -- -- -- -- -- -- -- -- -- -- --   --     ∘' (swap-01 ∘' (ua-ungluePathExt Σ-swap-01-≃ i))
-- -- -- -- -- -- -- -- -- -- -- --   --  Iso.rightInv (R𝕡elimSet'.aloop (w (suc (suc n))) (zero , k<) i) =
-- -- -- -- -- -- -- -- -- -- -- --   --    {!!}
-- -- -- -- -- -- -- -- -- -- -- --   --  Iso.leftInv (R𝕡elimSet'.aloop (w (suc (suc n))) (zero , k<) i) = {!!}


-- -- -- -- -- -- -- -- -- -- -- --   Iso-Fin×→ : Iso (Σ (Σ ℕ ℙrm) λ (n , p) → 𝔽in n p → A)
-- -- -- -- -- -- -- -- -- -- -- --                (Σ _ (λ 𝕝 → 𝕃Fin 𝕝 → A))
-- -- -- -- -- -- -- -- -- -- -- --   Iso-Fin×→ = Σ-cong-iso (invIso Iso-FM2⊤-Σℙrm)
-- -- -- -- -- -- -- -- -- -- -- --       (λ (n , 𝕡) → domIso (Σ-cong-iso (R𝕡elimSet'.f (w n) 𝕡) {!!}))
-- -- -- -- -- -- -- -- -- -- -- --    where

-- -- -- -- -- -- -- -- -- -- -- --     wIso : ∀ n → Iso (fst (𝕍₂ Bool isSetBool n 𝕡base))
-- -- -- -- -- -- -- -- -- -- -- --                      (𝕃Bool (toFM2⊤ (n , 𝕡base)))
-- -- -- -- -- -- -- -- -- -- -- --     wIso zero = idIso
-- -- -- -- -- -- -- -- -- -- -- --     wIso (suc n) = prodIso idIso (wIso n)

-- -- -- -- -- -- -- -- -- -- -- --     w : ∀ n → R𝕡elimSet'
-- -- -- -- -- -- -- -- -- -- -- --                 (λ z →
-- -- -- -- -- -- -- -- -- -- -- --                    Iso (fst (𝕍₂ Bool isSetBool n z))
-- -- -- -- -- -- -- -- -- -- -- --                    (𝕃Bool (Iso.fun (invIso Iso-FM2⊤-Σℙrm) (n , z))))
-- -- -- -- -- -- -- -- -- -- -- --     R𝕡elimSet'.isSetA (w n) x =
-- -- -- -- -- -- -- -- -- -- -- --      isSet-SetsIso
-- -- -- -- -- -- -- -- -- -- -- --       (snd (𝕍₂ Bool isSetBool n x))
-- -- -- -- -- -- -- -- -- -- -- --       (isSet𝕃₂ Bool isSetBool (toFM2⊤ (n , x)))
-- -- -- -- -- -- -- -- -- -- -- --     R𝕡elimSet'.abase (w n) = wIso n
-- -- -- -- -- -- -- -- -- -- -- --     R𝕡elimSet'.aloop (w (suc n)) (suc k , k<) =
-- -- -- -- -- -- -- -- -- -- -- --      congP (λ _ z → prodIso idIso z)
-- -- -- -- -- -- -- -- -- -- -- --        (R𝕡elimSet'.aloop (w n) (k , k<))
-- -- -- -- -- -- -- -- -- -- -- --     Iso.fun (R𝕡elimSet'.aloop (w (suc (suc n))) (zero , k<) i) =
-- -- -- -- -- -- -- -- -- -- -- --       ua-gluePathExt Σ-swap-01-≃ i
-- -- -- -- -- -- -- -- -- -- -- --        ∘' (map-snd (map-snd (Iso.fun (wIso n))))
-- -- -- -- -- -- -- -- -- -- -- --        ∘' (swap-01 ∘' (ua-ungluePathExt Σ-swap-01-≃ i))
-- -- -- -- -- -- -- -- -- -- -- --     Iso.inv (R𝕡elimSet'.aloop (w (suc (suc n))) (zero , k<) i) =
-- -- -- -- -- -- -- -- -- -- -- --      ua-gluePathExt Σ-swap-01-≃ i
-- -- -- -- -- -- -- -- -- -- -- --        ∘' (map-snd (map-snd (Iso.inv (wIso n))))
-- -- -- -- -- -- -- -- -- -- -- --        ∘' (swap-01 ∘' (ua-ungluePathExt Σ-swap-01-≃ i))
-- -- -- -- -- -- -- -- -- -- -- --     Iso.rightInv (R𝕡elimSet'.aloop (w (suc (suc n))) (zero , k<) i) =
-- -- -- -- -- -- -- -- -- -- -- --       {!!}
-- -- -- -- -- -- -- -- -- -- -- --     Iso.leftInv (R𝕡elimSet'.aloop (w (suc (suc n))) (zero , k<) i) = {!!}


-- -- -- -- -- -- -- -- -- -- -- --    -- w : ∀ n → R𝕡elimSet'
-- -- -- -- -- -- -- -- -- -- -- --    --             (λ z → {!!})
-- -- -- -- -- -- -- -- -- -- -- --    -- w = {!!}


-- -- -- -- -- -- -- -- -- -- -- --   look-tab-≃ = isoToEquiv Iso-look-tab
 

-- -- -- -- -- -- -- -- -- -- -- --   lookup× : (l : List A) → Fin× (length l) → A
-- -- -- -- -- -- -- -- -- -- -- --   lookup× (a ∷ l) = Fin×cases a (lookup× l)

-- -- -- -- -- -- -- -- -- -- -- --   tab×L : ∀ n → (Fin× n → A) → List A
-- -- -- -- -- -- -- -- -- -- -- --   tab×L zero _ = []
-- -- -- -- -- -- -- -- -- -- -- --   tab×L (suc n) x = x Fin×0 ∷ tab×L n (x ∘ sucFin×)

-- -- -- -- -- -- -- -- -- -- -- --   -- lookup×-iso : Iso (List A) (Σ _ (λ n → Fin× n → A))
-- -- -- -- -- -- -- -- -- -- -- --   -- lookup×-iso = w
-- -- -- -- -- -- -- -- -- -- -- --   --  where

-- -- -- -- -- -- -- -- -- -- -- --   --   ri : ∀ n f → _ ≡ _
-- -- -- -- -- -- -- -- -- -- -- --   --   fst (ri zero f i) = zero
-- -- -- -- -- -- -- -- -- -- -- --   --   snd (ri zero f i) ()
-- -- -- -- -- -- -- -- -- -- -- --   --   ri (suc n) f = {!!}

-- -- -- -- -- -- -- -- -- -- -- --   --   w : Iso (List A) (Σ ℕ (λ n → Fin× n → A))
-- -- -- -- -- -- -- -- -- -- -- --   --   Iso.fun w l = _ , lookup× l
-- -- -- -- -- -- -- -- -- -- -- --   --   Iso.inv w = uncurry tab×L
-- -- -- -- -- -- -- -- -- -- -- --   --   Iso.rightInv w = uncurry ri
-- -- -- -- -- -- -- -- -- -- -- --   --   Iso.leftInv w = {!!}

-- -- -- -- -- -- -- -- -- -- -- --   lookup×-lem : (x : List A) →  lookup (List-perm.List→×^ x) ≡
-- -- -- -- -- -- -- -- -- -- -- --       equivFun (preCompEquiv (isoToEquiv (IsoFinFin× (length x))))
-- -- -- -- -- -- -- -- -- -- -- --       (lookup× x)
-- -- -- -- -- -- -- -- -- -- -- --   lookup×-lem [] i ()
-- -- -- -- -- -- -- -- -- -- -- --   lookup×-lem (x ∷ l) = funExt (uncurry w)
-- -- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- -- --     w : (x₁ : ℕ) (y : x₁ < length (x ∷ l)) →
-- -- -- -- -- -- -- -- -- -- -- --           lookup (List-perm.List→×^ (x ∷ l)) (x₁ , y) ≡
-- -- -- -- -- -- -- -- -- -- -- --           equivFun (preCompEquiv (isoToEquiv (IsoFinFin× (length (x ∷ l)))))
-- -- -- -- -- -- -- -- -- -- -- --           (lookup× (x ∷ l)) (x₁ , y)
-- -- -- -- -- -- -- -- -- -- -- --     w zero y = refl
-- -- -- -- -- -- -- -- -- -- -- --     w (suc x₁) y =
-- -- -- -- -- -- -- -- -- -- -- --       funExt⁻ (lookup×-lem l) (x₁ , y)
  
-- -- -- -- -- -- -- -- -- -- -- --   tab-fromList-fst : (l : List A) →
     
-- -- -- -- -- -- -- -- -- -- -- --        (fst (equivFun (invEquiv look-tab-≃ ∙ₑ isoToEquiv (invIso Iso-Fin×→))
-- -- -- -- -- -- -- -- -- -- -- --         (fromList l))) ≡
-- -- -- -- -- -- -- -- -- -- -- --      (length l , 𝕡base)
-- -- -- -- -- -- -- -- -- -- -- --   fst (tab-fromList-fst [] i) = zero
-- -- -- -- -- -- -- -- -- -- -- --   fst (tab-fromList-fst (x ∷ l) i) = suc (fst (tab-fromList-fst l i))
-- -- -- -- -- -- -- -- -- -- -- --   snd (tab-fromList-fst [] i) = 𝕡base
-- -- -- -- -- -- -- -- -- -- -- --   snd (tab-fromList-fst (x ∷ l) i) =
-- -- -- -- -- -- -- -- -- -- -- --     sucℙrm _ (snd (tab-fromList-fst l i))

-- -- -- -- -- -- -- -- -- -- -- --   tab-fromList-snd' : ∀ l f → ((snd
-- -- -- -- -- -- -- -- -- -- -- --       (equivFun (invEquiv look-tab-≃ ∙ₑ isoToEquiv (invIso Iso-Fin×→))
-- -- -- -- -- -- -- -- -- -- -- --        (fromList l))
-- -- -- -- -- -- -- -- -- -- -- --       ∘
-- -- -- -- -- -- -- -- -- -- -- --       subst
-- -- -- -- -- -- -- -- -- -- -- --       (λ (x , y) →
-- -- -- -- -- -- -- -- -- -- -- --          𝔽in x y)
-- -- -- -- -- -- -- -- -- -- -- --       (sym (tab-fromList-fst l))) f)
-- -- -- -- -- -- -- -- -- -- -- --       ≡ lookup× l f
-- -- -- -- -- -- -- -- -- -- -- --   tab-fromList-snd' [] ()
-- -- -- -- -- -- -- -- -- -- -- --   tab-fromList-snd' (x ∷ l) ((false , bs) , z) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --   tab-fromList-snd' (x ∷ l) ((true , bs) , _) = {!!}

-- -- -- -- -- -- -- -- -- -- -- --   tab-fromList-snd : (l : List A) →
-- -- -- -- -- -- -- -- -- -- -- --     PathP (λ i → 𝔽in (fst (tab-fromList-fst l i))
-- -- -- -- -- -- -- -- -- -- -- --                      (snd (tab-fromList-fst l i)) → A)
-- -- -- -- -- -- -- -- -- -- -- --       (snd ((equivFun (invEquiv look-tab-≃ ∙ₑ isoToEquiv (invIso Iso-Fin×→))
-- -- -- -- -- -- -- -- -- -- -- --         (fromList l))))
-- -- -- -- -- -- -- -- -- -- -- --       (lookup× l)
-- -- -- -- -- -- -- -- -- -- -- --   tab-fromList-snd l =
-- -- -- -- -- -- -- -- -- -- -- --     funTypeTransp' (λ (x , y) → 𝔽in x y) A (tab-fromList-fst l) _
-- -- -- -- -- -- -- -- -- -- -- --      ▷ funExt (tab-fromList-snd' l)

-- -- -- -- -- -- -- -- -- -- -- --   tab-fromList : (l : List A) →
     
-- -- -- -- -- -- -- -- -- -- -- --        (equivFun (invEquiv look-tab-≃ ∙ₑ isoToEquiv (invIso Iso-Fin×→))
-- -- -- -- -- -- -- -- -- -- -- --         (fromList l)) ≡
-- -- -- -- -- -- -- -- -- -- -- --      ((length l , 𝕡base) , lookup× l)
-- -- -- -- -- -- -- -- -- -- -- --   tab-fromList l = ΣPathP ( tab-fromList-fst l , tab-fromList-snd l)

-- -- -- -- -- -- -- -- -- -- -- --   ≃nm-help : (A : (n m : ℕ) → n ≡ m → Type ℓ)
-- -- -- -- -- -- -- -- -- -- -- --      → ∀ n m →
-- -- -- -- -- -- -- -- -- -- -- --         Iso (Σ (n ≡ m) (A n m)) ((n ≡ m) × A n n refl)
-- -- -- -- -- -- -- -- -- -- -- --      -- → (∀ n → A n n ≃ B n n)
-- -- -- -- -- -- -- -- -- -- -- --      -- → ∀ n m → (A n m) ≃ (B n m)
-- -- -- -- -- -- -- -- -- -- -- --   ≃nm-help = {!!}

-- -- -- -- -- -- -- -- -- -- -- --   Σ-Iso-look-tabΩ-fst : ∀ n m →
-- -- -- -- -- -- -- -- -- -- -- --        Iso (Path (Σ ℕ ℙrm) (n , 𝕡base) (m , 𝕡base))
-- -- -- -- -- -- -- -- -- -- -- --            ((Path (ℙrm n) 𝕡base 𝕡base) × (n ≡ m))
-- -- -- -- -- -- -- -- -- -- -- --   Σ-Iso-look-tabΩ-fst n m = w
-- -- -- -- -- -- -- -- -- -- -- --     -- ≃nm-help _ _ {!!}
-- -- -- -- -- -- -- -- -- -- -- --     --  λ n → invEquiv ΣPath≃PathΣ ∙ₑ
-- -- -- -- -- -- -- -- -- -- -- --     --         Σ-cong-equiv {!!} {!!}
-- -- -- -- -- -- -- -- -- -- -- --     --          ∙ₑ Σ-swap-≃
-- -- -- -- -- -- -- -- -- -- -- --    where

-- -- -- -- -- -- -- -- -- -- -- --    w→ : Path (Σ ℕ ℙrm) (n , 𝕡base) (m , 𝕡base) →
-- -- -- -- -- -- -- -- -- -- -- --           Path (ℙrm n) 𝕡base 𝕡base × (n ≡ m)
-- -- -- -- -- -- -- -- -- -- -- --    fst (w→ x) i = coei→0 (λ i → ℙrm (fst (x i))) i (snd (x i))
-- -- -- -- -- -- -- -- -- -- -- --    snd (w→ x) = cong fst x

-- -- -- -- -- -- -- -- -- -- -- --    w← : Path (ℙrm n) 𝕡base 𝕡base × (n ≡ m) →
-- -- -- -- -- -- -- -- -- -- -- --           Path (Σ ℕ ℙrm) (n , 𝕡base) (m , 𝕡base)
-- -- -- -- -- -- -- -- -- -- -- --    fst (w← x i) = snd x i 
-- -- -- -- -- -- -- -- -- -- -- --    snd (w← x i) = coe0→i (λ i → ℙrm (snd x i)) i (fst x i)

-- -- -- -- -- -- -- -- -- -- -- --    w : Iso (Path (Σ ℕ ℙrm) (n , 𝕡base) (m , 𝕡base))
-- -- -- -- -- -- -- -- -- -- -- --          (Path (ℙrm n) 𝕡base 𝕡base × (n ≡ m))
-- -- -- -- -- -- -- -- -- -- -- --    Iso.fun w = w→
-- -- -- -- -- -- -- -- -- -- -- --    Iso.inv w = w←
-- -- -- -- -- -- -- -- -- -- -- --    fst (Iso.rightInv w b j) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --    snd (Iso.rightInv w b j) = snd b
-- -- -- -- -- -- -- -- -- -- -- --    fst (Iso.leftInv w a j i) = fst (a i)
-- -- -- -- -- -- -- -- -- -- -- --    snd (Iso.leftInv w a j i) = {!!}
   
-- -- -- -- -- -- -- -- -- -- -- --     -- invEquiv ΣPath≃PathΣ ∙ₑ {!isoTo!}


-- -- -- -- -- -- -- -- -- -- -- --   -- Iso-look-tabΩ :
-- -- -- -- -- -- -- -- -- -- -- --   --      (n : ℕ)
-- -- -- -- -- -- -- -- -- -- -- --   --     (x y : List A) → (length x ≡ n) → (length y ≡ n) → 
-- -- -- -- -- -- -- -- -- -- -- --   --   (fromList x ≡ fromList y) ≃
-- -- -- -- -- -- -- -- -- -- -- --   --     Σ (Perm (length x))
-- -- -- -- -- -- -- -- -- -- -- --   --      λ p →
-- -- -- -- -- -- -- -- -- -- -- --   --        List-perm.permuteList x p ≡ y
-- -- -- -- -- -- -- -- -- -- -- --   -- Iso-look-tabΩ n x y lx ly =
-- -- -- -- -- -- -- -- -- -- -- --   --    (fromList x ≡ fromList y)
-- -- -- -- -- -- -- -- -- -- -- --   --     ≃⟨ congEquiv {x = fromList x} {fromList y}
-- -- -- -- -- -- -- -- -- -- -- --   --     (invEquiv look-tab-≃ ∙ₑ isoToEquiv (invIso Iso-Fin×→)) ⟩
-- -- -- -- -- -- -- -- -- -- -- --   --        _
-- -- -- -- -- -- -- -- -- -- -- --   --     ≃⟨   compPathrEquiv {!!}
-- -- -- -- -- -- -- -- -- -- -- --   --       ∙ₑ compPathlEquiv (sym (tab-fromList x ∙
-- -- -- -- -- -- -- -- -- -- -- --   --              {!!}))
-- -- -- -- -- -- -- -- -- -- -- --   --       --   compPathrEquiv (tab-fromList y ∙
-- -- -- -- -- -- -- -- -- -- -- --   --       --    ΣPathP ((ΣPathP ((sym ((sym ly))) , (toPathP refl))) ,
-- -- -- -- -- -- -- -- -- -- -- --   --       --       toPathP {!!}))
-- -- -- -- -- -- -- -- -- -- -- --   --       -- ∙ₑ compPathlEquiv (sym (tab-fromList x) ∙ ?)
-- -- -- -- -- -- -- -- -- -- -- --   --       ⟩
-- -- -- -- -- -- -- -- -- -- -- --   --       Path (Σ (Σ ℕ ℙrm)
-- -- -- -- -- -- -- -- -- -- -- --   --              (λ (p , q) →
-- -- -- -- -- -- -- -- -- -- -- --   --                 𝔽in p q → A))
-- -- -- -- -- -- -- -- -- -- -- --   --         ((n , 𝕡base) , lookup× x ∘ subst Fin× (sym lx))
-- -- -- -- -- -- -- -- -- -- -- --   --         ((n , 𝕡base) , lookup× y ∘ subst Fin× (sym ly))
       
-- -- -- -- -- -- -- -- -- -- -- --   --    ≃⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- --   --      Path (Σ (ℙrm n) λ q → 𝔽in n q → A)
-- -- -- -- -- -- -- -- -- -- -- --   --         (𝕡base , lookup× x ∘ subst Fin× (sym lx))
-- -- -- -- -- -- -- -- -- -- -- --   --         (𝕡base , lookup× y ∘ subst Fin× (sym ly))
-- -- -- -- -- -- -- -- -- -- -- --   --    ≃⟨ invEquiv ΣPath≃PathΣ  ⟩
-- -- -- -- -- -- -- -- -- -- -- --   --      Σ (Path (ℙrm n) 𝕡base 𝕡base)
-- -- -- -- -- -- -- -- -- -- -- --   --          (λ q → PathP (λ i → 𝔽in n (q i) → A)
-- -- -- -- -- -- -- -- -- -- -- --   --                   (λ x₁ → lookup× x (subst Fin× (λ i → lx (~ i)) x₁))
-- -- -- -- -- -- -- -- -- -- -- --   --                   (λ x₁ → lookup× y (subst Fin× (λ i → ly (~ i)) x₁)))
-- -- -- -- -- -- -- -- -- -- -- --   --    ≃⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- --   --      _
-- -- -- -- -- -- -- -- -- -- -- --   --    ≃⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- --   --    _ ■
     
-- -- -- -- -- -- -- -- -- -- -- --   -- permuteList-lemma : (x y : List A) → (l= : length x ≡ length y) →
-- -- -- -- -- -- -- -- -- -- -- --   --     (p : Perm (length x)) →
-- -- -- -- -- -- -- -- -- -- -- --   --    PathP (λ i → isoToPath {!!} i)
-- -- -- -- -- -- -- -- -- -- -- --   --       {!!} {!!} ≃
-- -- -- -- -- -- -- -- -- -- -- --   --   (List-perm.permuteList x p ≡ y)
   


-- -- -- -- -- -- -- -- -- -- -- --   -- permuteList-lemma = {!!}



-- -- -- -- -- -- -- -- -- -- -- -- -- transport
-- -- -- -- -- -- -- -- -- -- -- -- --       (λ i →
-- -- -- -- -- -- -- -- -- -- -- -- --          𝔽in
-- -- -- -- -- -- -- -- -- -- -- -- --          (fst
-- -- -- -- -- -- -- -- -- -- -- --           -- (ΣPathP
-- -- -- -- -- -- -- -- -- -- -- --           --  ((λ i₁ → p (~ i₁)) ,
-- -- -- -- -- -- -- -- -- -- -- --           --   toPathP (λ _ → transport (λ i₁ → ℙrm (p (~ i₁))) 𝕡base))
-- -- -- -- -- -- -- -- -- -- -- --           --  i))
-- -- -- -- -- -- -- -- -- -- -- -- --          (snd
-- -- -- -- -- -- -- -- -- -- -- -- --           (ΣPathP
-- -- -- -- -- -- -- -- -- -- -- -- --            ((λ i₁ → p (~ i₁)) ,
-- -- -- -- -- -- -- -- -- -- -- -- --             toPathP (λ _ → transport (λ i₁ → ℙrm (p (~ i₁))) 𝕡base))
-- -- -- -- -- -- -- -- -- -- -- -- --            i)) →
-- -- -- -- -- -- -- -- -- -- -- -- --          A)
-- -- -- -- -- -- -- -- -- -- -- -- --       (lookup× y)
-- -- -- -- -- -- -- -- -- -- -- -- --       ≡ transport (λ i → 𝔽in (p (~ i)) 𝕡base → A) (lookup× y)

-- -- -- -- -- -- -- -- -- -- -- --   -- lemΣrefl : ∀ {ℓ} n → (A : ℕ → Type ℓ) → (a₀ a₁ : A n)
-- -- -- -- -- -- -- -- -- -- -- --   --              →     (Path (Σ ℕ A) (n , a₀) (n , a₁))
-- -- -- -- -- -- -- -- -- -- -- --   --                    ≃ (Path (A n) a₀ a₁)
-- -- -- -- -- -- -- -- -- -- -- --   -- lemΣrefl n A a₀ a₁ = invEquiv ΣPath≃PathΣ ∙ₑ
-- -- -- -- -- -- -- -- -- -- -- --   --     {!!}

-- -- -- -- -- -- -- -- -- -- -- --   lemΣrefl : ∀ {ℓ} n → (A : ℕ → Type ℓ) → (a₀ a₁ : A n)
-- -- -- -- -- -- -- -- -- -- -- --                → Iso (Path (Σ ℕ A) (n , a₀) (n , a₁))
-- -- -- -- -- -- -- -- -- -- -- --                      (Path (A n) a₀ a₁)
-- -- -- -- -- -- -- -- -- -- -- --   lemΣrefl n A a₀ a₁ = compIso (invIso ΣPathIsoPathΣ)
-- -- -- -- -- -- -- -- -- -- -- --      (Σ-contractFstIso (refl , (isSetℕ n n refl)))


-- -- -- -- -- -- -- -- -- -- -- --   -- hhh : ∀ (x y : List A) (p : length x ≡ length y) →
-- -- -- -- -- -- -- -- -- -- -- --   --       equivFun (isoToEquiv (invIso (Iso-×^-F→ (length x))))
-- -- -- -- -- -- -- -- -- -- -- --   --     (equivFun (preCompEquiv (isoToEquiv (IsoFinFin× (length x))))
-- -- -- -- -- -- -- -- -- -- -- --   --      (λ x₂ → lookup× y (subst Fin× p x₂)))
-- -- -- -- -- -- -- -- -- -- -- --   --     ≡
-- -- -- -- -- -- -- -- -- -- -- --   --     equivFun (isoToEquiv (invIso (Iso-×^-F→ (length x))))
-- -- -- -- -- -- -- -- -- -- -- --   --     (equivFun
-- -- -- -- -- -- -- -- -- -- -- --   --      (isoToEquiv
-- -- -- -- -- -- -- -- -- -- -- --   --       (compIso (List-perm.IsoListOfLen×^ (length x))
-- -- -- -- -- -- -- -- -- -- -- --   --        (Iso-×^-F→ (length x))))
-- -- -- -- -- -- -- -- -- -- -- --   --      (y , (λ i → p (~ i))))
-- -- -- -- -- -- -- -- -- -- -- --   -- hhh [] [] p = refl
-- -- -- -- -- -- -- -- -- -- -- --   -- hhh [] (x ∷ y) p = ⊥.rec (Nat.znots p)
-- -- -- -- -- -- -- -- -- -- -- --   -- hhh (x ∷ x₁) [] p = ⊥.rec (Nat.snotz p)
-- -- -- -- -- -- -- -- -- -- -- --   -- hhh (x ∷ []) (x₂ ∷ []) p = {!!}
-- -- -- -- -- -- -- -- -- -- -- --   -- hhh (x ∷ []) (x₂ ∷ x₁ ∷ y) p = {!!}
-- -- -- -- -- -- -- -- -- -- -- --   -- hhh (x ∷ x₁ ∷ x₃) (x₂ ∷ []) p = {!!}
-- -- -- -- -- -- -- -- -- -- -- --   -- hhh (x ∷ x₁ ∷ x₃) (x₂ ∷ x₄ ∷ y) p = {!!}
-- -- -- -- -- -- -- -- -- -- -- --   --    -- ΣPathP ({!!}
-- -- -- -- -- -- -- -- -- -- -- --   --    --        ,
-- -- -- -- -- -- -- -- -- -- -- --   --    --         ( cong tabulate
-- -- -- -- -- -- -- -- -- -- -- --   --    --            ((cong₂ _∘_
-- -- -- -- -- -- -- -- -- -- -- --   --    --               {!Fin×elimFunExt ? ?!} {!!})
-- -- -- -- -- -- -- -- -- -- -- --   --    --              ∙ {!!})
-- -- -- -- -- -- -- -- -- -- -- --   --    --          -- ({!Fin×elimFunExt ? ?!}
-- -- -- -- -- -- -- -- -- -- -- --   --    --          --   ∙ {!!})
-- -- -- -- -- -- -- -- -- -- -- --   --    --           ∙ hhh x₁ y (cong predℕ p) ))
   
-- -- -- -- -- -- -- -- -- -- -- -- -- Goal: (λ x₃ →
-- -- -- -- -- -- -- -- -- -- -- -- --          Fin×cases x₂ (lookup× y)
-- -- -- -- -- -- -- -- -- -- -- -- --          (transp (λ i → Σ (Bool ×^ p i) (λ x₄ → fst (Fin×Snd (p i) x₄))) i0
-- -- -- -- -- -- -- -- -- -- -- -- --           ((false , ℕ→Fin× (length x₁) (fst x₃)) ,
-- -- -- -- -- -- -- -- -- -- -- -- --            ℕ→Fin×-snd (length x₁) (fst x₃) (snd x₃))))
-- -- -- -- -- -- -- -- -- -- -- -- --       ≡
-- -- -- -- -- -- -- -- -- -- -- -- --       (λ x₃ →
-- -- -- -- -- -- -- -- -- -- -- -- --          lookup× y
-- -- -- -- -- -- -- -- -- -- -- -- --          (transp
-- -- -- -- -- -- -- -- -- -- -- -- --           (λ i →
-- -- -- -- -- -- -- -- -- -- -- -- --              Σ (Bool ×^ predℕ (p i)) (λ x₄ → fst (Fin×Snd (predℕ (p i)) x₄)))
-- -- -- -- -- -- -- -- -- -- -- -- --           i0
-- -- -- -- -- -- -- -- -- -- -- -- --           (ℕ→Fin× (length x₁) (fst x₃) ,
-- -- -- -- -- -- -- -- -- -- -- -- --            ℕ→Fin×-snd (length x₁) (fst x₃) (snd x₃))))


-- -- -- -- -- -- -- -- -- -- -- --   -- hhhXXX' : ∀ x₂ (y : List A) →
-- -- -- -- -- -- -- -- -- -- -- --   --      lookup× y ≡
-- -- -- -- -- -- -- -- -- -- -- --   --     (λ x₃ →
-- -- -- -- -- -- -- -- -- -- -- --   --        lookup
-- -- -- -- -- -- -- -- -- -- -- --   --        (Iso.fun (List-perm.IsoListOfLen×^ (suc (length y)))
-- -- -- -- -- -- -- -- -- -- -- --   --         (x₂ ∷ y , (λ _ → suc (length y))))
-- -- -- -- -- -- -- -- -- -- -- --   --        (Fin×→ℕ (suc (length y)) (fst x₃) ,
-- -- -- -- -- -- -- -- -- -- -- --   --         Fin×→ℕ-snd (suc (length y)) (fst x₃) (snd x₃)))
-- -- -- -- -- -- -- -- -- -- -- --   --     ∘' sucFin×
-- -- -- -- -- -- -- -- -- -- -- --   -- hhhXXX' x₂ y = funExt (uncurry (w y))
-- -- -- -- -- -- -- -- -- -- -- --   --  where
-- -- -- -- -- -- -- -- -- -- -- --   --  w : ∀ y → (x : Bool ×^ length y) (y₁ : fst (Fin×Snd (length y) x)) →
-- -- -- -- -- -- -- -- -- -- -- --   --        lookup× y (x , y₁) ≡
-- -- -- -- -- -- -- -- -- -- -- --   --        ((λ x₃ →
-- -- -- -- -- -- -- -- -- -- -- --   --            lookup
-- -- -- -- -- -- -- -- -- -- -- --   --            (Iso.fun (List-perm.IsoListOfLen×^ (suc (length y)))
-- -- -- -- -- -- -- -- -- -- -- --   --             (x₂ ∷ y , (λ _ → suc (length y))))
-- -- -- -- -- -- -- -- -- -- -- --   --            (Fin×→ℕ (suc (length y)) (fst x₃) ,
-- -- -- -- -- -- -- -- -- -- -- --   --             Fin×→ℕ-snd (suc (length y)) (fst x₃) (snd x₃)))
-- -- -- -- -- -- -- -- -- -- -- --   --         ∘' sucFin×)
-- -- -- -- -- -- -- -- -- -- -- --   --        (x , y₁)
-- -- -- -- -- -- -- -- -- -- -- --   --  w (x₁ ∷ y) (false , snd₁) y₁ = w y snd₁ y₁
-- -- -- -- -- -- -- -- -- -- -- --   --  w (x₁ ∷ y) (true , snd₁) y₁ = refl

-- -- -- -- -- -- -- -- -- -- -- --   hhhXXX : ∀ (x y : List A) (p : length x ≡ length y) → ∀ z z' → 
-- -- -- -- -- -- -- -- -- -- -- --                ((equivFun (preCompEquiv (isoToEquiv (IsoFinFin× (length x))))
-- -- -- -- -- -- -- -- -- -- -- --                (λ x₁ → lookup× y (subst Fin× p x₁))) (z , z'))
-- -- -- -- -- -- -- -- -- -- -- --                ≡
-- -- -- -- -- -- -- -- -- -- -- --                ((equivFun
-- -- -- -- -- -- -- -- -- -- -- --                (isoToEquiv
-- -- -- -- -- -- -- -- -- -- -- --                 (compIso (List-perm.IsoListOfLen×^ (length x))
-- -- -- -- -- -- -- -- -- -- -- --                  (Iso-×^-F→ (length x))))
-- -- -- -- -- -- -- -- -- -- -- --                (y , (λ i → p (~ i)))) (z , z'))
-- -- -- -- -- -- -- -- -- -- -- --   hhhXXX (x ∷ x₁) [] p z z' = ⊥.rec (Nat.snotz p)
-- -- -- -- -- -- -- -- -- -- -- --   hhhXXX (x ∷ x₁) (x₂ ∷ y) p zero z' = 
-- -- -- -- -- -- -- -- -- -- -- --         cong {x = (transp (λ i → Σ (Bool ×^ p i) (λ x₃ → fst (Fin×Snd (p i) x₃))) i0
-- -- -- -- -- -- -- -- -- -- -- --        ((true , repeat (length x₁) false) ,
-- -- -- -- -- -- -- -- -- -- -- --         allFalse-repeat-false (length x₁)))}
-- -- -- -- -- -- -- -- -- -- -- --              {y = (true , _) ,
-- -- -- -- -- -- -- -- -- -- -- --                    allFalseSubst {m =  (length y)} (cong predℕ p)
-- -- -- -- -- -- -- -- -- -- -- --                      (repeat (length x₁) false) (allFalse-repeat-false
-- -- -- -- -- -- -- -- -- -- -- --                       (length x₁))}
-- -- -- -- -- -- -- -- -- -- -- --              (Fin×cases x₂ (lookup× y))
-- -- -- -- -- -- -- -- -- -- -- --            (Σ≡Prop (snd ∘ (Fin×Snd (p i1))) (subst×^Suc p _ ))
-- -- -- -- -- -- -- -- -- -- -- --   hhhXXX (x ∷ x₁) (x₂ ∷ y) p (suc z) z' =
-- -- -- -- -- -- -- -- -- -- -- --     (cong (Fin×cases x₂ (lookup× y))
-- -- -- -- -- -- -- -- -- -- -- --          ((Σ≡Prop (snd ∘ (Fin×Snd (p i1))) 
-- -- -- -- -- -- -- -- -- -- -- --             (subst×^Suc p _ )))
-- -- -- -- -- -- -- -- -- -- -- --       )
-- -- -- -- -- -- -- -- -- -- -- --     ∙ hhhXXX x₁ y (cong predℕ p) z z'


-- -- -- -- -- -- -- -- -- -- -- --   hhhXX : ∀ x →
-- -- -- -- -- -- -- -- -- -- -- --        Path (Fin (length x) → A)
-- -- -- -- -- -- -- -- -- -- -- --        (equivFun
-- -- -- -- -- -- -- -- -- -- -- --       (isoToEquiv
-- -- -- -- -- -- -- -- -- -- -- --        (compIso (List-perm.IsoListOfLen×^ (length x))
-- -- -- -- -- -- -- -- -- -- -- --         (Iso-×^-F→ (length x))))
-- -- -- -- -- -- -- -- -- -- -- --       (x , (λ _ → length x)))
      
-- -- -- -- -- -- -- -- -- -- -- --       (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- --          lookup× x
-- -- -- -- -- -- -- -- -- -- -- --          (ℕ→Fin× (length x) (fst x₁) ,
-- -- -- -- -- -- -- -- -- -- -- --           ℕ→Fin×-snd (length x) (fst x₁) (snd x₁)))
-- -- -- -- -- -- -- -- -- -- -- --   hhhXX x = invEq (congEquiv (isoToEquiv (invIso (Iso-×^-F→ (length x)))))
-- -- -- -- -- -- -- -- -- -- -- --             (h x)
-- -- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- -- --     h : ∀ x → equivFun (isoToEquiv (invIso (Iso-×^-F→ (length x))))
-- -- -- -- -- -- -- -- -- -- -- --       (equivFun
-- -- -- -- -- -- -- -- -- -- -- --        (isoToEquiv
-- -- -- -- -- -- -- -- -- -- -- --         (compIso (List-perm.IsoListOfLen×^ (length x))
-- -- -- -- -- -- -- -- -- -- -- --          (Iso-×^-F→ (length x))))
-- -- -- -- -- -- -- -- -- -- -- --        (x , (λ _ → length x)))
-- -- -- -- -- -- -- -- -- -- -- --       ≡
-- -- -- -- -- -- -- -- -- -- -- --       equivFun (isoToEquiv (invIso (Iso-×^-F→ (length x))))
-- -- -- -- -- -- -- -- -- -- -- --       (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- --          lookup× x
-- -- -- -- -- -- -- -- -- -- -- --          (ℕ→Fin× (length x) (fst x₁) ,
-- -- -- -- -- -- -- -- -- -- -- --           ℕ→Fin×-snd (length x) (fst x₁) (snd x₁)))
-- -- -- -- -- -- -- -- -- -- -- --     h [] = refl
-- -- -- -- -- -- -- -- -- -- -- --     h (x ∷ x₁) = ΣPathP (refl , h x₁)
    
-- -- -- -- -- -- -- -- -- -- -- --   hhhX : ∀ x → (p' : Path (ℙrm (length x)) 𝕡base 𝕡base)
-- -- -- -- -- -- -- -- -- -- -- --       →
-- -- -- -- -- -- -- -- -- -- -- --       Path (Fin (length x) → A)
-- -- -- -- -- -- -- -- -- -- -- --         (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- --          equivFun
-- -- -- -- -- -- -- -- -- -- -- --          (isoToEquiv
-- -- -- -- -- -- -- -- -- -- -- --           (compIso (List-perm.IsoListOfLen×^ (length x))
-- -- -- -- -- -- -- -- -- -- -- --            (Iso-×^-F→ (length x))))
-- -- -- -- -- -- -- -- -- -- -- --          (x , (λ _ → length x))
-- -- -- -- -- -- -- -- -- -- -- --          (permuteF' (length x) (equivFun (invEquiv
-- -- -- -- -- -- -- -- -- -- -- --            (isoToEquiv ((fst (GIso-𝕡Ω₂-PermG (length x)))) )) p') x₁))
      
-- -- -- -- -- -- -- -- -- -- -- --       (equivFun (preCompEquiv (isoToEquiv (IsoFinFin× (length x))))
-- -- -- -- -- -- -- -- -- -- -- --       (transport (λ i → 𝔽in (length x) (p' i) → A) (lookup× x)))
-- -- -- -- -- -- -- -- -- -- -- --   hhhX x p' =
-- -- -- -- -- -- -- -- -- -- -- --      ( cong′ (_∘' (permuteF' (length x) 
-- -- -- -- -- -- -- -- -- -- -- --           (equivFun (invEquiv (isoToEquiv (fst (GIso-𝕡Ω₂-PermG (length x)))))
-- -- -- -- -- -- -- -- -- -- -- --            p')))
-- -- -- -- -- -- -- -- -- -- -- --           {x = equivFun
-- -- -- -- -- -- -- -- -- -- -- --          (isoToEquiv
-- -- -- -- -- -- -- -- -- -- -- --           (compIso (List-perm.IsoListOfLen×^ (length x))
-- -- -- -- -- -- -- -- -- -- -- --            (Iso-×^-F→ (length x))))
-- -- -- -- -- -- -- -- -- -- -- --          (x , (λ _ → length x))}
-- -- -- -- -- -- -- -- -- -- -- --           {y = lookup× x ∘ Iso.fun (IsoFinFin× (length x))}
-- -- -- -- -- -- -- -- -- -- -- --           (hhhXX x) ∙
-- -- -- -- -- -- -- -- -- -- -- --        cong (((lookup× x ∘
-- -- -- -- -- -- -- -- -- -- -- --          (Iso.fun (IsoFinFin× (length x)) ∘
-- -- -- -- -- -- -- -- -- -- -- --           (permuteF' (length x)
-- -- -- -- -- -- -- -- -- -- -- --             (equivFun
-- -- -- -- -- -- -- -- -- -- -- --               (invEquiv (isoToEquiv (fst (GIso-𝕡Ω₂-PermG (length x))))) p')))))
-- -- -- -- -- -- -- -- -- -- -- --           ∘_ ) (sym (funExt (Iso.leftInv (IsoFinFin× (length x))))))
     
-- -- -- -- -- -- -- -- -- -- -- --      ∙
-- -- -- -- -- -- -- -- -- -- -- --      cong
-- -- -- -- -- -- -- -- -- -- -- --        {x = lookup× x ∘ 
-- -- -- -- -- -- -- -- -- -- -- --              Iso.fun (IsoFinFin× (length x))
-- -- -- -- -- -- -- -- -- -- -- --             ∘ 
-- -- -- -- -- -- -- -- -- -- -- --             permuteF' (length x) (equivFun (invEquiv
-- -- -- -- -- -- -- -- -- -- -- --            (isoToEquiv ((fst (GIso-𝕡Ω₂-PermG (length x)))) )) p')
-- -- -- -- -- -- -- -- -- -- -- --             ∘ Iso.inv (IsoFinFin× (length x))}
-- -- -- -- -- -- -- -- -- -- -- --        {y = transport (λ i → 𝔽in (length x) (p' i) → A) (lookup× x)}
-- -- -- -- -- -- -- -- -- -- -- --        (equivFun (preCompEquiv (isoToEquiv (IsoFinFin× (length x)))))
-- -- -- -- -- -- -- -- -- -- -- --        ((cong (lookup× x ∘_) (hhhPF' (length x) ((equivFun (invEquiv
-- -- -- -- -- -- -- -- -- -- -- --            (isoToEquiv ((fst (GIso-𝕡Ω₂-PermG (length x)))) )) p'))
-- -- -- -- -- -- -- -- -- -- -- --             ∙ cong ((subst (𝔽in (length x)) ∘ sym))
-- -- -- -- -- -- -- -- -- -- -- --              (Iso.rightInv ((((fst (GIso-𝕡Ω₂-PermG (length x)))) )) p')))
-- -- -- -- -- -- -- -- -- -- -- --          ∙ sym (fromPathP {A = λ i → 𝔽in (length x) (p' i) → A}
-- -- -- -- -- -- -- -- -- -- -- --          (funTypeTransp' (𝔽in (length x)) A p' ((lookup× x)))))


-- -- -- -- -- -- -- -- -- -- -- --   Iso-look-tabΩ : (x y : List A) → (length x ≡ length y) → 
-- -- -- -- -- -- -- -- -- -- -- --     (fromList x ≡ fromList y) ≃
-- -- -- -- -- -- -- -- -- -- -- --       Σ (Perm (length x))
-- -- -- -- -- -- -- -- -- -- -- --        λ p →
-- -- -- -- -- -- -- -- -- -- -- --          List-perm.permuteList x p ≡ y
-- -- -- -- -- -- -- -- -- -- -- --   Iso-look-tabΩ x y p =
-- -- -- -- -- -- -- -- -- -- -- --        (fromList x ≡ fromList y)
-- -- -- -- -- -- -- -- -- -- -- --       ≃⟨ congEquiv {x = fromList x} {fromList y}
-- -- -- -- -- -- -- -- -- -- -- --       (invEquiv look-tab-≃ ∙ₑ isoToEquiv (invIso Iso-Fin×→)) ⟩
-- -- -- -- -- -- -- -- -- -- -- --        _
-- -- -- -- -- -- -- -- -- -- -- --       ≃⟨ compPathrEquiv (tab-fromList y ∙
-- -- -- -- -- -- -- -- -- -- -- --            ΣPathP ((ΣPathP ((sym p) , (toPathP refl))) ,
-- -- -- -- -- -- -- -- -- -- -- --               toPathP                
-- -- -- -- -- -- -- -- -- -- -- --                 (funExt⁻
-- -- -- -- -- -- -- -- -- -- -- --                 (cong transport
-- -- -- -- -- -- -- -- -- -- -- --                    (cong {A = Path (Σ ℕ ℙrm)
-- -- -- -- -- -- -- -- -- -- -- --                           (length y , 𝕡base) (length x , 𝕡base)} {x =
-- -- -- -- -- -- -- -- -- -- -- --                     λ i → (p (~ i)) ,
-- -- -- -- -- -- -- -- -- -- -- --                           toPathP {A = λ i → ℙrm (p (~ i))}
-- -- -- -- -- -- -- -- -- -- -- --                              {x = 𝕡base}
-- -- -- -- -- -- -- -- -- -- -- --                              (λ _ → transport (λ i₁ → ℙrm (p (~ i₁)))
-- -- -- -- -- -- -- -- -- -- -- --                             𝕡base) i}
-- -- -- -- -- -- -- -- -- -- -- --                          {y = λ i → (p (~ i)) , 𝕡base {n = p (~ i)}}
-- -- -- -- -- -- -- -- -- -- -- --                       (cong (λ X → uncurry 𝔽in X → A))
-- -- -- -- -- -- -- -- -- -- -- --                      zzz))
-- -- -- -- -- -- -- -- -- -- -- --                 (lookup× y))
-- -- -- -- -- -- -- -- -- -- -- --                 ))
-- -- -- -- -- -- -- -- -- -- -- --         ∙ₑ compPathlEquiv (sym (tab-fromList x)) ⟩
-- -- -- -- -- -- -- -- -- -- -- --         Path (Σ (Σ ℕ ℙrm)
-- -- -- -- -- -- -- -- -- -- -- --                (λ (p , q) →
-- -- -- -- -- -- -- -- -- -- -- --                   𝔽in p q → A))
-- -- -- -- -- -- -- -- -- -- -- --           ((length x , 𝕡base) , lookup× x)
-- -- -- -- -- -- -- -- -- -- -- --           ((length x , 𝕡base) , transport
-- -- -- -- -- -- -- -- -- -- -- --                                   (λ i →
-- -- -- -- -- -- -- -- -- -- -- --                                      𝔽in
-- -- -- -- -- -- -- -- -- -- -- --                                      (p (~ i))
-- -- -- -- -- -- -- -- -- -- -- --                                      𝕡base  →
-- -- -- -- -- -- -- -- -- -- -- --                                      A)
-- -- -- -- -- -- -- -- -- -- -- --                                   (lookup× y))
-- -- -- -- -- -- -- -- -- -- -- --       ≃⟨ congEquiv Σ-assoc-≃ ∙ₑ
-- -- -- -- -- -- -- -- -- -- -- --           (isoToEquiv
-- -- -- -- -- -- -- -- -- -- -- --             (lemΣrefl (length x) _ _ _))⟩
-- -- -- -- -- -- -- -- -- -- -- --       Path (Σ (ℙrm (length x)) λ q → 𝔽in (length x) q → A)
-- -- -- -- -- -- -- -- -- -- -- --          (𝕡base , lookup× x)
-- -- -- -- -- -- -- -- -- -- -- --          (𝕡base , transport (λ i → 𝔽in (p (~ i)) 𝕡base → A) (lookup× y))
-- -- -- -- -- -- -- -- -- -- -- --       ≃⟨ invEquiv ΣPath≃PathΣ ⟩
-- -- -- -- -- -- -- -- -- -- -- --         Σ (𝕡base ≡ 𝕡base)
-- -- -- -- -- -- -- -- -- -- -- --           (λ p₁ →
-- -- -- -- -- -- -- -- -- -- -- --              PathP (λ i → 𝔽in (length x) (p₁ i) → A)
-- -- -- -- -- -- -- -- -- -- -- --                    (lookup× x)
-- -- -- -- -- -- -- -- -- -- -- --                    (transport (λ i → 𝔽in (p (~ i)) 𝕡base → A) (lookup× y)))
-- -- -- -- -- -- -- -- -- -- -- --       ≃⟨ Σ-cong-equiv-snd (λ _ →
           
-- -- -- -- -- -- -- -- -- -- -- --             PathP≃Path _ _ _
-- -- -- -- -- -- -- -- -- -- -- --         ∙ₑ congEquiv (preCompEquiv (isoToEquiv (IsoFinFin× (length x))))
-- -- -- -- -- -- -- -- -- -- -- --         ) ⟩
-- -- -- -- -- -- -- -- -- -- -- --          _
-- -- -- -- -- -- -- -- -- -- -- --       ≃⟨ Σ-cong-equiv-snd (λ p' →
-- -- -- -- -- -- -- -- -- -- -- --            compPathrEquiv

-- -- -- -- -- -- -- -- -- -- -- --              (cong {x = (transport (λ i → Fin× (p (~ i)) → A) (lookup× y))}
-- -- -- -- -- -- -- -- -- -- -- --                    {y = lookup× y ∘' subst Fin× p}
-- -- -- -- -- -- -- -- -- -- -- --                (equivFun (preCompEquiv (isoToEquiv (IsoFinFin× (length x)))))
-- -- -- -- -- -- -- -- -- -- -- --                  (fromPathP {x = lookup× y} (funTypeTransp' Fin× A (sym p) _))
-- -- -- -- -- -- -- -- -- -- -- --               ∙ hhh* x y p  )
-- -- -- -- -- -- -- -- -- -- -- --         ∙ₑ compPathlEquiv (hhhX x p')) ⟩ 
-- -- -- -- -- -- -- -- -- -- -- --         _
-- -- -- -- -- -- -- -- -- -- -- --       ≃⟨ Σ-cong-equiv-fst (invEquiv pp) ∙ₑ
-- -- -- -- -- -- -- -- -- -- -- --          Σ-cong-equiv-snd (List-perm.permuteList-lemma x y p) ⟩
-- -- -- -- -- -- -- -- -- -- -- --       _ ■

-- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- --       pp :  (Perm (length x)) ≃ (_≡_ {A = ℙrm (length x)} 𝕡base 𝕡base)        
-- -- -- -- -- -- -- -- -- -- -- --       pp = isoToEquiv ((fst (GIso-𝕡Ω₂-PermG (length x)))) 

-- -- -- -- -- -- -- -- -- -- -- --       zzz : _ ≡ _
-- -- -- -- -- -- -- -- -- -- -- --       fst (zzz i x) = p (~ x)
-- -- -- -- -- -- -- -- -- -- -- --       snd (zzz i x) = (rUnit (λ _ → 𝕡base)) (~ i) x

-- -- -- -- -- -- -- -- -- -- -- --       hhh* : ∀ (x y : List A) (p : length x ≡ length y) →
-- -- -- -- -- -- -- -- -- -- -- --             equivFun (preCompEquiv (isoToEquiv (IsoFinFin× (length x))))
-- -- -- -- -- -- -- -- -- -- -- --             (λ x₁ → lookup× y (subst Fin× p x₁))
-- -- -- -- -- -- -- -- -- -- -- --             ≡
-- -- -- -- -- -- -- -- -- -- -- --             equivFun
-- -- -- -- -- -- -- -- -- -- -- --             (isoToEquiv
-- -- -- -- -- -- -- -- -- -- -- --              (compIso (List-perm.IsoListOfLen×^ (length x))
-- -- -- -- -- -- -- -- -- -- -- --               (Iso-×^-F→ (length x))))
-- -- -- -- -- -- -- -- -- -- -- --             (y , (λ i → p (~ i)))
-- -- -- -- -- -- -- -- -- -- -- --       hhh* x y p = funExt (uncurry (hhhXXX x y  p))

