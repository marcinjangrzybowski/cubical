module Cubical.HITs.CauchyReals.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)

open import Cubical.Data.Rationals.Fast as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Fast.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡ ;  [_/_]₊)
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence

open import Cubical.Tactics.CommRingSolverFast.RationalsReflection
open import Cubical.Tactics.CommRingSolverFast.FastRationalsReflection
open import Cubical.Tactics.CommRingSolverFast.IntReflection
open import Cubical.HITs.CauchyReals.LiftingExpr
open import Cubical.Tactics.CommRingSolverFast.RealsReflection



IsUContinuous : (ℝ → ℝ) → Type
IsUContinuous f =
  ∀ (ε : ℚ₊) → Σ[ δ ∈ ℚ₊ ]
     (∀ u v → u ∼[ δ ] v → f u ∼[ ε ] f v)

IsUContinuous→IsContinuous : ∀ f → IsUContinuous f → IsContinuous f
IsUContinuous→IsContinuous f fc u ε =
  ∣ map-snd (_$ u) (fc ε) ∣₁

restrIsUContinuousℙ : ∀ P f → IsUContinuous f → IsUContinuousℙ P λ x _ → f x
restrIsUContinuousℙ _ _ =
  map-snd (((const ∘ const) ∘_) ∘_) ∘_


IsUContinuous∘ : ∀ {f g} → IsUContinuous f → IsUContinuous g →
  IsUContinuous (f ∘ g)
IsUContinuous∘ cF cG ε =
  let (η , X) = cF ε ; (δ , Y) = cG η
  in _ , λ _ _ → X _ _ ∘ Y _ _


interpℝ : ℝ → ℝ → ℝ → ℝ
interpℝ a b t = a +ᵣ t ·ᵣ (b -ᵣ a)



IsUContinuous+ᵣL : ∀ x → IsUContinuous (x +ᵣ_)
IsUContinuous+ᵣL x ε = ε , λ u v u∼v →
  subst2 (_∼[ ε ]_) (+ᵣComm _ _) (+ᵣComm _ _) $ +ᵣ-∼ u v x ε u∼v


·ᵣ-∼ : ∀ u v r r' ε
    → absᵣ r ≤ᵣ rat (fst r')
    → u ∼[ ε ℚ₊· invℚ₊ r' ] v
    → (u ·ᵣ r) ∼[ ε ] (v ·ᵣ r)
·ᵣ-∼ u v r r' ε abs-r≤ᵣr' u∼v =
 invEq (∼≃abs<ε _ _ _)
   (isTrans≤<ᵣ _ _ _
     (isTrans≡≤ᵣ _ _ _
       (cong absᵣ (sym (𝐑'.·DistL- _ _ _) ∙ ·ᵣComm _ _)
        ∙ ·absᵣ _ _)
       (≤ᵣ-·ᵣo _ _ (absᵣ (u +ᵣ -ᵣ v)) (0≤absᵣ _) abs-r≤ᵣr'))
     (isTrans<≡ᵣ _ _ _
    (<ᵣ-o·ᵣ _ _ (ℚ₊→ℝ₊ r')  (fst (∼≃abs<ε _ _ _) u∼v))
    (sym (rat·ᵣrat _ _) ∙ cong rat (cong ((fst r') ℚ.·_) (ℚ.·Comm (fst ε) _)
     ∙ ℚ.y·[x/y] r' (fst ε) ))))



IsUContinuous·ᵣR : ∀ x → ∥ IsUContinuous (_·ᵣ x) ∥₁
IsUContinuous·ᵣR x =
  PT.map
    (λ (x' , (absᵣx<x' , _)) ε →
      ε ℚ₊· invℚ₊ (x' , ℚ.<→0< x'
       (<ᵣ→<ℚ 0 x' (isTrans≤<ᵣ 0 (absᵣ x) _ (0≤absᵣ _) absᵣx<x'))) ,
       λ _ _ → ·ᵣ-∼ _ _ _ _ ε (<ᵣWeaken≤ᵣ _ _ absᵣx<x') )
    (denseℚinℝ (absᵣ x) ((absᵣ x) +ᵣ 1)
       (isTrans≡<ᵣ _ _ _
         (sym (+IdR _)) (<ᵣ-o+ 0 1 (absᵣ x) decℚ<ᵣ?)))

IsUContinuous∘ℙ : ∀ P {f g} → IsUContinuous f → IsUContinuousℙ P g  →
  IsUContinuousℙ P (λ x x∈ → f (g x x∈))
IsUContinuous∘ℙ P cF cG ε =
  let (η , X) = cF ε ; (δ , Y) = cG η
  in _ , λ _ _ _ _ → X _ _ ∘ Y _ _ _ _

IsUContinuousℙ∘ℙ : ∀ P P' {f g} → (g∈ : ∀ x x∈ → g x x∈ ∈ P')
  → IsUContinuousℙ P' f → IsUContinuousℙ P g

  → IsUContinuousℙ P (λ x x∈ → f (g x x∈) (g∈ x x∈))
IsUContinuousℙ∘ℙ P P' g∈ cF cG  ε =
  let (η , X) = cF ε ; (δ , Y) = cG η
     in _ , λ _ _ _ _ → X _ _ _ _ ∘ Y _ _ _ _


IsUContinuous-εᵣ : ∀ f → IsUContinuous f →
   ∀ (ε : ℝ₊) → ∃[ δ ∈ ℚ₊ ]
     (∀ u v → u ∼[ δ ] v → absᵣ (f u -ᵣ f v) <ᵣ fst ε)
IsUContinuous-εᵣ f fuc εᵣ =
 PT.map
   (λ (ε , 0<ε , ε<εᵣ) →
     map-snd
      (λ {δ} X →
        λ u v u∼v → isTrans<ᵣ _ _ _ (fst (∼≃abs<ε _ _ _) (X u v u∼v)) ε<εᵣ)
      (fuc (ε , ℚ.<→0< _ (<ᵣ→<ℚ 0 ε 0<ε))))
   (denseℚinℝ 0 (fst εᵣ) (snd εᵣ))



IsUContinuousℚ : (ℚ → ℝ) → Type
IsUContinuousℚ f =
  ∀ (ε : ℚ₊) → Σ[ δ ∈ ℚ₊ ]
     (∀ u v → ℚ.abs (u ℚ.- v) ℚ.< fst ε  → f u ∼[ ε ] f v)


Lipschitiz→IsUContinuous : ∀ L f →
     Lipschitz-ℝ→ℝ L f → IsUContinuous f
Lipschitiz→IsUContinuous L f X ε =
   (invℚ₊ L) ℚ₊· ε ,
    ( λ u v → subst∼ (ℚ.y·[x/y] (fst L , L .snd) _)
      ∘ X u v ((invℚ₊ L) ℚ₊· ε))

-- IsUContinuousℙ : (P : ℙ ℝ) → (∀ x → x ∈ P → ℝ) → Type
-- IsUContinuousℙ P f =
--   ∀ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
--      (∀ u u∈ v v∈ → u ∼[ δ ] v → f u u∈ ∼[ ε ] f v v∈)





-- fromUContinuous : Σ _ (λ f → (IsUContinuousℚ f)) →
--   Σ _ (λ f' → IsUContinuous f')
-- fromUContinuous (f , uC) = f' , Iso.inv Σ-Π-Iso (cMod , rl)
--  where

--  cMod : (a : ℚ₊) → ℚ₊
--  cMod = fst ∘ uC

--  cMod' : (a : ℚ₊) → ℚ₊
--  cMod' = fst ∘ uC

--  isCMode : {!!}
--  isCMode = {!!}

--  cMod≤ : ∀ δ ε → fst (cMod' (cMod δ ℚ₊+ cMod ε)) ℚ.≤ fst (δ ℚ₊+ ε)
--  cMod≤ = {!!}

--  cMod≤' : ∀ ε → fst (cMod' (cMod ε)) ℚ.≤ fst (ε)
--  cMod≤' = {!!}
--  w : Elimℝ (λ _ → ℝ) λ u v ε z → u ∼[ cMod' ε  ] v


--  w .Elimℝ.ratA = f
--  w .Elimℝ.limA x p a v = lim (a ∘ cMod)
--    λ δ ε →
--     let v' = v ((cMod δ)) ((cMod ε))
--     in ∼-monotone≤ (cMod≤ δ ε) v'
--  w .Elimℝ.eqA p a a' x y =
--    eqℝ a a' λ ε →
--      ∼-monotone≤  (cMod≤' ε) (y (cMod ε))


--  w .Elimℝ.rat-rat-B q r ε x x₁ = {!snd (uC ε) q r !}
--  w .Elimℝ.rat-lim-B = {!!}
--  w .Elimℝ.lim-rat-B x r ε δ p v₁ u v' u' x₁ =
--   {!!}
--  w .Elimℝ.lim-lim-B x y ε δ η p p' v₁ r v' u' v'' u'' x₁ =
--   let z = {!!}
--   in ?
--     -- lim-lim _ _ _ (cMod' δ) (cMod' η)  _ _
--     --      {!!} {!!}
--  w .Elimℝ.isPropB _ _ _ _ = isProp∼ _ _ _

--  f' : ℝ → ℝ
--  f' = Elimℝ.go w

--  rl : (ε : ℚ₊) (u v : ℝ) → u ∼[ cMod ε ] v → f' u ∼[ ε ] f' v
--  rl ε u v u∼v = ∼-monotone≤  (cMod≤' ε) (Elimℝ.go∼ w u∼v)



at_limitOf_is_ : (x : ℝ) → (∀ r → x ＃ r → ℝ)  → ℝ → Type
at x limitOf f is L =
  ∀ (ε : ℝ₊) → ∃[ δ ∈ ℝ₊ ]
   (∀ r x＃r → absᵣ (x -ᵣ r) <ᵣ fst δ → absᵣ (L -ᵣ f r x＃r) <ᵣ fst ε)

at_limitOfℙ_,_is_ : (x : ℝ) → (P : ℙ ℝ) →  (∀ r → r ∈ P → x ＃ r → ℝ)  → ℝ → Type
at x limitOfℙ P , f is L =
  ∀ (ε : ℝ₊) → ∃[ δ ∈ ℝ₊ ]
   (∀ r r∈ x＃r → absᵣ (x -ᵣ r) <ᵣ fst δ → absᵣ (L -ᵣ f r r∈ x＃r) <ᵣ fst ε)

at_limitOfℙ_,_is'_ : (x : ℝ) → (P : ℙ ℝ) →  (∀ r → r ∈ P → x ＃ r → ℝ)  → ℝ → Type
at x limitOfℙ P , f is' L =
  ∀ (ε : ℚ₊) → Σ[ δ ∈ ℚ₊ ]
   (∀ r r∈ x＃r → absᵣ (x -ᵣ r) <ᵣ rat (fst δ) → absᵣ (L -ᵣ f r r∈ x＃r) <ᵣ rat (fst ε))

at_limitOf_is'_ : (x : ℝ) → (∀ r → x ＃ r → ℝ)  → ℝ → Type
at x limitOf f is' L =
  ∀ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
   (∀ r x＃r → absᵣ (x -ᵣ r) <ᵣ rat (fst δ) → absᵣ (L -ᵣ f r x＃r) <ᵣ rat (fst ε))

at_inclLimitOf_is_ : (x : ℝ) → (∀ r → ℝ)  → ℝ → Type
at x inclLimitOf f is L =
  ∀ (ε : ℝ₊) → ∃[ δ ∈ ℝ₊ ]
   (∀ r → absᵣ (x -ᵣ r) <ᵣ fst δ → absᵣ (L -ᵣ f r) <ᵣ fst ε)

inclLimit→Limit : ∀ f x L → at x inclLimitOf f is L
                          → at x limitOf (λ r _ → f r)  is L
inclLimit→Limit f x L = PT.map (map-snd (const ∘_)) ∘_

substLim : ∀ {x f f' L}
  → (∀ r x＃r → f r x＃r ≡ f' r x＃r)
  → at x limitOf f is L → at x limitOf f' is L
substLim {x} {L = L} p =  subst (at x limitOf_is L) (funExt₂ p)

IsContinuousInclLim : ∀ f x → IsContinuous f →
                    at x inclLimitOf f is (f x)
IsContinuousInclLim f x cx = uncurry
  λ ε → (PT.rec squash₁
   λ (q , 0<q , q<ε) →
     PT.map (λ (δ , X) →
       (ℚ₊→ℝ₊ δ) ,
         λ r x₁ → isTrans<ᵣ _ _ _
           (fst (∼≃abs<ε _ _ _) (X r (invEq (∼≃abs<ε _ _ _) x₁)))
            q<ε  )
       (cx x (q , ℚ.<→0< q (<ᵣ→<ℚ 0 q 0<q)))) ∘ denseℚinℝ 0 ε

IsContinuousLim : ∀ f x → IsContinuous f →
                    at x limitOf (λ r _ → f r) is (f x)
IsContinuousLim f x cx = inclLimit→Limit _ _ _ (IsContinuousInclLim f x cx)

IsContinuousLimℙ : ∀ P f x x∈ → IsContinuousWithPred P f →
                    at x limitOfℙ P , (λ r r∈ _ → f r r∈) is (f x x∈)
IsContinuousLimℙ P f x x∈ cx = uncurry
  λ ε → (PT.rec squash₁
   λ (q , 0<q , q<ε) →
     PT.map (λ (δ , X) →
       (ℚ₊→ℝ₊ δ) ,
         λ r x₁ xx yy → isTrans<ᵣ _ _ _
           (fst (∼≃abs<ε _ _ _) ((X r x₁ (invEq (∼≃abs<ε _ _ _) yy))))
            q<ε)
       (cx x (q , ℚ.<→0< q (<ᵣ→<ℚ 0 q 0<q)) x∈)) ∘ denseℚinℝ 0 ε



IsContinuousInclLim→IsContinuous : ∀ f  →
                    (∀ x → at x inclLimitOf f is (f x))
                    → IsContinuous f
IsContinuousInclLim→IsContinuous f xc x (ε , 0<ε) =
  PT.rec squash₁ w z

 where
  z = xc x (rat ε , <ℚ→<ᵣ 0 ε (ℚ.0<→< _ 0<ε) )
  w : Σ ℝ₊
        (λ δ →
           (r : ℝ) →
           absᵣ (x -ᵣ r) <ᵣ fst δ → absᵣ (f x -ᵣ f r) <ᵣ rat ε) →
        ∃-syntax ℚ₊ (λ δ → (v₁ : ℝ) → x ∼[ δ ] v₁ → f x ∼[ ε , 0<ε ] f v₁)
  w ((δ , 0<δ) , X) =
      PT.map (λ (q , 0<q , q<δ) →
        ((q , ℚ.<→0< q (<ᵣ→<ℚ 0 q 0<q))) ,
          λ r x∼r → invEq (∼≃abs<ε _ _ _) (X r
            (isTrans<ᵣ _ _ _ (fst (∼≃abs<ε _ _ _) x∼r) q<δ)))
       (denseℚinℝ 0 δ 0<δ)

IsContinuousInclLim≃IsContinuous : ∀ f  →
                    (∀ x → at x inclLimitOf f is (f x))
                    ≃ (IsContinuous f)
IsContinuousInclLim≃IsContinuous f =
  propBiimpl→Equiv (isPropΠ2 λ _ _ → squash₁) (isPropIsContinuous f)
    (IsContinuousInclLim→IsContinuous f)
     λ fc x → IsContinuousInclLim f x fc

IsContinuousLimΔ : ∀ f x → IsContinuous f →
                    at 0 limitOf (λ Δx _ → f (x +ᵣ Δx)) is (f x)
IsContinuousLimΔ f x cx =
  subst (at rat [ pos 0 / 1+ 0 ] limitOf (λ Δx _ → f (x +ᵣ Δx)) is_)
   (cong f (+IdR x))
  (IsContinuousLim (λ Δx → f (x +ᵣ Δx)) 0
    (IsContinuous∘ _ _ cx (IsContinuous+ᵣL x)))



const-lim : ∀ C x → at x limitOf (λ _ _ → C) is C
const-lim C x ε = ∣ (1 , decℚ<ᵣ?) ,
  (λ r x＃r x₁ → subst (_<ᵣ fst ε) (sym (absᵣ-rat 0) ∙ cong absᵣ (sym (+-ᵣ C))) (snd ε)) ∣₁

const-limℙ : ∀ P C x → at x limitOfℙ P ,  (λ _ _ _ → C) is C
const-limℙ _ C x ε = ∣ (1 , decℚ<ᵣ?) ,
  (λ r x＃r _ x₁ → subst (_<ᵣ fst ε) (sym (absᵣ-rat 0) ∙ cong absᵣ (sym (+-ᵣ C))) (snd ε) ) ∣₁



id-lim : ∀ x → at x limitOf (λ r _ → r) is x
id-lim x ε = ∣ ε , (λ r x＃r p → p )  ∣₁

_$[_]$_ : (ℝ → ℝ)
        → (ℝ → ℝ → ℝ)
        → (ℝ → ℝ)
        → (ℝ → ℝ)
f $[ _op_ ]$ g = λ r → (f r) op (g r)

_#[_]$_ : {x : ℝ}
        → (∀ r → x ＃ r → ℝ)
        → (ℝ → ℝ → ℝ)
        → (∀ r → x ＃ r → ℝ)
        → (∀ r → x ＃ r → ℝ)
f #[ _op_ ]$ g = λ r x → (f r x) op (g r x)

+-lim : ∀ x f g F G
        → at x limitOf f is F
        → at x limitOf g is G
        → at x limitOf (f #[ _+ᵣ_ ]$ g) is (F +ᵣ G)
+-lim x f g F G fL gL ε =
  PT.map2 (λ (δ , p) (δ' , p') →
       (minᵣ₊ δ δ') ,
        λ r x＃r x₁ →
         let u = p r x＃r (isTrans<≤ᵣ _ _ _ x₁ (min≤ᵣ _ _))
             u' = p' r x＃r (isTrans<≤ᵣ _ _ _ x₁ (min≤ᵣ' _ _))
         in subst2 _<ᵣ_
                (cong absᵣ ℝ!)
                (x·rat[α]+x·rat[β]=x (fst ε))
               (isTrans≤<ᵣ _ _ _
                 (absᵣ-triangle _ _)
                 (<ᵣMonotone+ᵣ _ _ _ _ u u')))
    (fL (ε ₊·ᵣ (rat [ 1 / 2 ] , decℚ<ᵣ?)))
     (gL (ε ₊·ᵣ (rat [ 1 / 2 ] , decℚ<ᵣ?)))


·-lim : ∀ x f g F G
        → at x limitOf f is F
        → at x limitOf g is G
        → at x limitOf (f #[ _·ᵣ_ ]$ g) is (F ·ᵣ G)
·-lim x f g F G fL gL ε = PT.map3 w (fL (ε'f)) (gL (ε'g)) (gL 1)

 where

  ε'f : ℝ₊
  ε'f = (ε ₊／ᵣ₊ 2) ₊／ᵣ₊ (1 +ᵣ absᵣ G ,
           isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat _ _))
            (<≤ᵣMonotone+ᵣ 0 1 0 (absᵣ G) decℚ<ᵣ? (0≤absᵣ G)))

  ε'g : ℝ₊
  ε'g = (ε ₊／ᵣ₊ 2) ₊／ᵣ₊ (1 +ᵣ absᵣ F ,
            isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat _ _))
            (<≤ᵣMonotone+ᵣ 0 1 0 (absᵣ F) decℚ<ᵣ? (0≤absᵣ F)))

  w : _
  w (δ , p) (δ' , p') (δ'' , p'') = δ* , ww

   where

    δ* : ℝ₊
    δ* = minᵣ₊ (minᵣ₊ δ δ') δ''

    ww : (r : ℝ) (x＃r : x ＃ r) →
           absᵣ (x -ᵣ r) <ᵣ fst δ* →
           absᵣ (F ·ᵣ G -ᵣ (f #[ _·ᵣ_ ]$ g) r x＃r) <ᵣ fst ε
    ww r x＃r x₁ = subst2 _<ᵣ_
         (cong absᵣ ℝ!)
         yy
         (isTrans≤<ᵣ _ _ _
           ((absᵣ-triangle _ _) )
           (<ᵣMonotone+ᵣ _ _ _ _
             (isTrans≡<ᵣ _ _ _
               (·absᵣ _ _)
               (<ᵣ₊Monotone·ᵣ _ _ _ _
               (0≤absᵣ _) (0≤absᵣ _) gx< u))
               (isTrans≡<ᵣ _ _ _ (·absᵣ _ _)
                 (<ᵣ₊Monotone·ᵣ _ _ _ _
               ((0≤absᵣ F)) (0≤absᵣ _)
                (subst (_<ᵣ (1 +ᵣ (absᵣ F)))
                 (+IdL _)
                  (<ᵣ-+o (rat 0) (rat 1) (absᵣ F) decℚ<ᵣ?)) u'))))


      where
       x₁' = isTrans<≤ᵣ _ _ _ x₁
                  (isTrans≤ᵣ _ _ _ (min≤ᵣ _ _) (min≤ᵣ _ _))
       x₁'' = isTrans<≤ᵣ _ _ _ x₁
                  (isTrans≤ᵣ _ _ _ (min≤ᵣ _ _) (min≤ᵣ' _ _))
       x₁''' = isTrans<≤ᵣ _ _ _ x₁ (min≤ᵣ' _ _)
       u = p r x＃r x₁'
       u' = p' r x＃r x₁''
       u'' = p'' r x＃r x₁'''
       gx< : absᵣ (g r x＃r) <ᵣ 1 +ᵣ absᵣ G
       gx< =
          subst (_<ᵣ (1 +ᵣ absᵣ G))
             (cong absᵣ ℝ!)

            (isTrans≤<ᵣ _ _ _
              (absᵣ-triangle ((g r x＃r) -ᵣ G) G)
               (<ᵣ-+o _ 1 (absᵣ G)
                 (subst (_<ᵣ 1) (minusComm-absᵣ _ _) u'')))
       0<1+g = isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat _ _)) (<≤ᵣMonotone+ᵣ 0 1 0 (absᵣ G) decℚ<ᵣ? (0≤absᵣ G))
       0<1+f = isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat _ _)) $ <≤ᵣMonotone+ᵣ 0 1 0 (absᵣ F) decℚ<ᵣ? (0≤absᵣ F)

       yy : _ ≡ _
       yy = (cong₂ _+ᵣ_
           (cong ((1 +ᵣ absᵣ G) ·ᵣ_)
             (cong ((fst (ε ₊／ᵣ₊ 2)) ·ᵣ_)
               (invℝ≡ _ _ _)
              ∙ ·ᵣComm  (fst (ε ₊／ᵣ₊ 2))
             (invℝ (1 +ᵣ absᵣ G)
                 (inl 0<1+g))) ∙
             ·ᵣAssoc _ _ _)
           (cong ((1 +ᵣ absᵣ F) ·ᵣ_)
             (cong ((fst (ε ₊／ᵣ₊ 2)) ·ᵣ_)
              (invℝ≡ _ _ _)
              ∙ ·ᵣComm  (fst (ε ₊／ᵣ₊ 2))
             (invℝ (1 +ᵣ absᵣ F)
                 (inl 0<1+f))) ∙
              ·ᵣAssoc _ _ _) ∙
           sym (·DistR+ _ _ (fst (ε ₊／ᵣ₊ 2)))
            ∙∙ cong {y = 2} (_·ᵣ (fst (ε ₊／ᵣ₊ 2)))
                            (cong₂ _+ᵣ_
                                (x·invℝ[x] (1 +ᵣ absᵣ G)
                                  (inl 0<1+g))
                                (x·invℝ[x] (1 +ᵣ absᵣ F)
                                  (inl 0<1+f))
                               ∙ +ᵣ-rat _ _)
                       ∙∙ ·ᵣComm 2 (fst (ε ₊／ᵣ₊ 2))  ∙
                         [x/y]·yᵣ (fst ε) _ (inl _))

At_limitOf_ : (x : ℝ) → (∀ r → x ＃ r → ℝ) → Type
At x limitOf f = Σ _ (at x limitOf f is_)


differenceAt : (ℝ → ℝ) → ℝ → ∀ h → 0 ＃ h → ℝ
differenceAt f x h 0＃h = (f (x +ᵣ h) -ᵣ f x) ／ᵣ[ h , 0＃h ]

differenceAt0-swap : ∀ f h 0＃h → differenceAt f 0 h 0＃h ≡ differenceAt f h (-ᵣ h)
  (subst (_＃ (-ᵣ h)) (-ᵣ-rat 0) (-＃ _ _ 0＃h)) --
differenceAt0-swap f h 0＃h =
     sym (-ᵣ·-ᵣ _ _)
  ∙ cong₂ _·ᵣ_
    (cong -ᵣ_ (cong₂ _-ᵣ_
         (cong f (+IdL _))
         (cong f (sym (+-ᵣ _))))
      ∙ -[x-y]≡y-x _ _)
    (-invℝ h 0＃h)



differenceAtℙ : ∀ P → (∀ r → r ∈ P → ℝ) → ∀ x → ∀ h → 0 ＃ h → x ∈ P → x +ᵣ h ∈ P   → ℝ
differenceAtℙ P f x h 0＃h x∈ x+h∈ = (f (x +ᵣ h) x+h∈ -ᵣ f x x∈) ／ᵣ[ h , 0＃h ]

incr→0<differenceAtℙ : ∀ P f x h 0＃h x∈ x+h∈ →
          (∀ x x∈ y y∈ → x <ᵣ y → f x x∈ <ᵣ f y y∈) →
            0 <ᵣ differenceAtℙ P f x h 0＃h x∈ x+h∈
incr→0<differenceAtℙ P f x h (inl 0<h) x∈ x+h∈ incr =
 snd ((_ , x<y→0<y-x _ _ (incr _ _ _ _
  (isTrans≡<ᵣ _ _ _ (sym (+IdR _)) $ <ᵣ-o+ 0 h x 0<h)))
   ₊·ᵣ (_ , invℝ-pos _ 0<h))
incr→0<differenceAtℙ P f x h (inr h<0) x∈ x+h∈ incr =
 let z = -ᵣ<ᵣ _ _ $ x<y→x-y<0 _ _ (incr _ x+h∈ _ x∈ (isTrans<≡ᵣ _ _ _ (<ᵣ-o+ h 0 x h<0) (+IdR x)))
 in subst (0 <ᵣ_) ℝ!
        ((fst (0<x≃0<y₊·x _ (_ , (isTrans≡<ᵣ 0 _ _ ℝ! $ -ᵣ<ᵣ _ _ (invℝ-neg h h<0)))) (isTrans≡<ᵣ _ _ _ ℝ! z)))
  
＃ℙ : ℝ → ℙ ℝ
＃ℙ r x = r ＃ x , isProp＃ r x

diff-≃ : (P : ℙ ℝ) → (f f' : ∀ r → r ∈ P → ℝ)
                   → ∀ (ε δ : ℚ₊)
                  → ∀ x x∈ h h∈ 0＃h
                  → (absᵣ (f' x x∈ -ᵣ differenceAtℙ P f x h 0＃h x∈ h∈)
                    <ᵣ rat (fst ε)) ≃
                     (absᵣ ((f' x x∈ ·ᵣ h) -ᵣ
                       (f (x +ᵣ h) h∈ -ᵣ f x x∈))
                    <ᵣ rat (fst ε) ·ᵣ absᵣ h)
diff-≃ P f f' ε δ x x∈ h h∈ 0＃h =
        substEquiv (_<ᵣ _) (
             cong absᵣ (
                cong₂ _-ᵣ_ (sym ([x·y]/yᵣ _ _ _)) refl
               ∙ sym (𝐑'.·DistL- _ _ _))
            ∙∙ ·absᵣ _ _ ∙∙
            cong₂ _·ᵣ_ refl (absᵣ-invℝ _ _))
      ∙ₑ z/y<x₊≃z<y₊·x (rat (fst ε)) (absᵣ ((f' x x∈ ·ᵣ  h) -ᵣ
                       (f (x +ᵣ h) h∈ -ᵣ f x x∈)))
          (absᵣ h , 0＃→0<abs h 0＃h)
      ∙ₑ substEquiv (_ <ᵣ_) (·ᵣComm _ _)


uDerivativeOfℙ_,_is_ : (P : ℙ ℝ) → (∀ r → r ∈ P → ℝ)
                                    → (∀ r → r ∈ P → ℝ) → Type
uDerivativeOfℙ P , f is f' =
  ∀ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
   (∀ x x∈ h h∈ 0＃h → absᵣ h <ᵣ rat (fst δ)
    → absᵣ (f' x x∈ -ᵣ differenceAtℙ P f x h 0＃h x∈ h∈) <ᵣ rat (fst ε))

isProp-uDerivativeOfℙ : ∀ P f f' → isProp (uDerivativeOfℙ P , f is f')
isProp-uDerivativeOfℙ P f f' = isPropΠ λ _ → squash₁

uDerivativeOfℙ-restr : ∀ (P P' : ℙ ℝ) f f' → (P'⊆P : P' ⊆ P)
 → uDerivativeOfℙ P , f is f'
 → uDerivativeOfℙ P' , (λ x x∈ → f x (P'⊆P x x∈)) is λ x x∈ → f' x (P'⊆P x x∈)
uDerivativeOfℙ-restr P P' f f' P'⊆P X =
  PT.map (map-snd (λ X _ _ _ _ → X _ _ _ _)) ∘ X

IsUContinuousℙ-restr : ∀ (P P' : ℙ ℝ) f → (P'⊆P : P' ⊆ P)
 → IsUContinuousℙ P f
 → IsUContinuousℙ P' (λ x x∈ → f x (P'⊆P x x∈))
IsUContinuousℙ-restr P P' f  P'⊆P X =
  map-snd (λ X u v u∈ v∈  → X _ _ _ _) ∘ X

IsContinuousWithPred-differenceAt : ∀ x f → IsContinuous f
   → IsContinuousWithPred (＃ℙ 0) (differenceAt f x)
IsContinuousWithPred-differenceAt x f cf =
  cont₂·ᵣWP (＃ℙ 0) _ _
    (AsContinuousWithPred (＃ℙ 0) _
      (cont₂+ᵣ _ _ (IsContinuous∘ _ _ cf (IsContinuous+ᵣL _)) (IsContinuousConst _)))
    IsContinuousWithPredInvℝ

derivativeAt : (ℝ → ℝ) → ℝ → Type
derivativeAt f x = At 0 limitOf (differenceAt f x)


derivativeOfℙ_,_at_is_ : (P : ℙ ℝ) → (∀ r → r ∈ P → ℝ) → Σ _ (_∈ P) → ℝ → Type
derivativeOfℙ P , f at (x , x∈) is d =
 at 0 limitOfℙ P ∘S (x +ᵣ_) , (λ h h∈ 0＃h → differenceAtℙ P f x h 0＃h x∈ h∈) is d

derivativeOf_at_is_ : (ℝ → ℝ) → ℝ → ℝ → Type
derivativeOf f at x is d = at 0 limitOf (differenceAt f x) is d

as-derivativeOfℙ : ∀ P f x x∈P x'
    → derivativeOf f at x is x'
    → derivativeOfℙ P , (λ r _ → f r) at x , x∈P  is x'
as-derivativeOfℙ P f x x∈P x' X ε =
  PT.map (map-snd λ y r _ y＃r x₂ → y r  y＃r x₂) (X ε)


derivativeOf_at_is'_ : (ℝ → ℝ) → ℝ → ℝ → Type
derivativeOf f at x is' d = at 0 limitOf (differenceAt f x) is' d

constDerivative : ∀ C x → derivativeOf (λ _ → C) at x is 0
constDerivative C x =
 subst (at 0 limitOf_is 0)
   (funExt₂ λ _ _ → ℝ!)
   (const-lim 0 0)

idDerivative : ∀ x → derivativeOf (idfun ℝ) at x is 1
idDerivative x =  subst (at 0 limitOf_is 1)
   (funExt₂ λ r 0＃r → sym (x·invℝ[x] r 0＃r) ∙
    cong (_·ᵣ (invℝ r 0＃r)) ℝ!)
   (const-lim 1 0)

+Derivative : ∀ x f f'x g g'x
        → derivativeOf f at x is f'x
        → derivativeOf g at x is g'x
        → derivativeOf (f $[ _+ᵣ_ ]$ g) at x is (f'x +ᵣ g'x)
+Derivative x f f'x g g'x F G =
 subst {x = (differenceAt f x) #[ _+ᵣ_ ]$ (differenceAt g x)}
            {y = (differenceAt (f $[ _+ᵣ_ ]$ g) x)}
      (at 0 limitOf_is (f'x +ᵣ g'x))
       (funExt₂ λ _ _ → ℝ!) (+-lim _ _ _ _ _ F G)

+uDerivativeℙ : ∀ P  f f' g g'
        → uDerivativeOfℙ P , f is f'
        → uDerivativeOfℙ P , g is g'
        → uDerivativeOfℙ P , (λ x x∈ → f x x∈ +ᵣ g x x∈)
          is (λ x x∈ → f' x x∈ +ᵣ g' x x∈)
+uDerivativeℙ P f f' g g' F G ε =
  PT.map2
    (λ (δ , X) (δ' , X') →
       let δ⊔δ' = ℚ.min₊ δ δ'
       in δ⊔δ' ,
           λ x x∈ h h∈ 0＃h x₁ →
              (subst2 _<ᵣ_
                (cong absᵣ ℝ!)
                (+ᵣ-rat _ _ ∙ cong rat (ℚ.ε/2+ε/2≡ε (fst ε)))
               (isTrans≤<ᵣ _ _ _ (absᵣ-triangle _ _)
                (<ᵣMonotone+ᵣ _ _ _ _
                 (X x x∈ h h∈ 0＃h (isTrans<≤ᵣ _ _ _ x₁
                  (≤ℚ→≤ᵣ _ _ (ℚ.min≤ (fst δ) (fst δ') ))))
                 (X' x x∈ h h∈ 0＃h (isTrans<≤ᵣ _ _ _ x₁
                  (≤ℚ→≤ᵣ _ _ (ℚ.min≤' (fst δ) (fst δ')))))))))
    (F (/2₊ ε))
    (G (/2₊ ε))

C·Derivative : ∀ C x f f'x
        → derivativeOf f at x is f'x
        → derivativeOf ((C ·ᵣ_) ∘S f) at x is (C ·ᵣ f'x)
C·Derivative C x f f'x F =
   subst {x = λ h 0＃h → C ·ᵣ differenceAt f x h 0＃h}
            {y = (differenceAt ((C ·ᵣ_) ∘S f) x)}
      (at 0 limitOf_is (C ·ᵣ f'x))
       (funExt₂ λ h 0＃h → ℝ!)
       (·-lim _ _ _ _ _ (const-lim C 0) F)

substDer : ∀ {x f' f g} → (∀ r → f r ≡ g r)
     → derivativeOf f at x is f'
     → derivativeOf g at x is f'
substDer = subst (derivativeOf_at _ is _) ∘ funExt

substDer₂ : ∀ {x f' g' f g} →
        (∀ r → f r ≡ g r) → f' ≡ g'
     → derivativeOf f at x is f'
     → derivativeOf g at x is g'
substDer₂ p q = subst2 (derivativeOf_at _ is_) (funExt p) q


Derivative-ᵣ : ∀ x f f'x
        → derivativeOf f at x is f'x
        → derivativeOf (-ᵣ_ ∘ f) at x is (-ᵣ f'x)
Derivative-ᵣ x f f'x dF =
  (substDer₂ {f = _·ᵣ_ (rat -1) ∘S f} {g = -ᵣ_ ∘ f} (λ _ → ℝ!) ℝ!
      (C·Derivative (rat -1) x f f'x dF))


-Derivative : ∀ x f f'x g g'x
        → derivativeOf f at x is f'x
        → derivativeOf g at x is g'x
        → derivativeOf (f $[ _-ᵣ_ ]$ g) at x is (f'x -ᵣ g'x)
-Derivative x f f'x g g'x dF dG =
  +Derivative x f _ (λ z → -ᵣ g z) _ dF
    (substDer₂ {f = _·ᵣ_ (rat -1) ∘S g} {g = λ z → -ᵣ g z} (λ _ → ℝ!) ℝ!
      (C·Derivative (rat -1) x g g'x dG))


uDerivativeℙ-id : ∀ P
 → uDerivativeOfℙ P , (λ x _ → x) is (λ _ _ → 1)
uDerivativeℙ-id P ε =
 ∣ ε , (λ _ _ h _ 0＃h _ →
   isTrans≡<ᵣ _ _ _
     (cong absᵣ ((𝐑'.+InvR' _ _ (sym (x·invℝ[x] h 0＃h) ∙
    cong (_·ᵣ (invℝ h 0＃h)) ℝ!)))
    ∙ absᵣ0)
    (snd (ℚ₊→ℝ₊ ε))) ∣₁

uDerivativeℙ-const : ∀ P C →
 uDerivativeOfℙ P , (λ _ _ → C) is (λ _ _ → 0)

uDerivativeℙ-const P C ε =
 ∣ 1 , (λ _ _ h _ 0＃h _ →
   isTrans≡<ᵣ _ _ _
    (minusComm-absᵣ _ _ ∙
      cong absᵣ (𝐑'.+IdR' _ _ (-ᵣ-rat 0)
        ∙ cong (_·ᵣ (invℝ h 0＃h)) (+-ᵣ _)
     ∙ (𝐑'.0LeftAnnihilates (invℝ h 0＃h)))
     ∙ absᵣ0
     )
    (snd (ℚ₊→ℝ₊ ε))) ∣₁


uDerivativeℙ-cancelConst : ∀ P C f f'
        → uDerivativeOfℙ P , (λ x x∈ → f x x∈ +ᵣ C) is f'
        → uDerivativeOfℙ P , f is f'
uDerivativeℙ-cancelConst P C f f' df =
   subst2
     (uDerivativeOfℙ P ,_is_)
     (funExt₂ λ _ _ → 𝐑'.plusMinus _ _)
     (funExt₂ λ _ _ → +IdR _)
     (+uDerivativeℙ P _ _ _ _ df (uDerivativeℙ-const P (-ᵣ C)) )


C·uDerivativeℙ : ∀ P C f f'
        → uDerivativeOfℙ P , f is f'
        → uDerivativeOfℙ P , (λ x x∈ → C ·ᵣ f x x∈) is (λ x x∈ → C ·ᵣ f' x x∈)
C·uDerivativeℙ P C f f' udp ε =
  PT.rec squash₁
    (λ (η , 0<η , η<1/[C+1]) →
      PT.map (map-snd
        (λ X _ x∈ _ h∈ 0＃h h<a →
          isTrans≡<ᵣ _ _ _
             (cong absᵣ ℝ!
               ∙ ·absᵣ _ _)
             (isTrans≤<ᵣ _ _ _
               (≤ᵣ-·ᵣo (absᵣ C) _ _ (0≤absᵣ _)
                 (isTrans≡≤ᵣ _ _ _
                    (sym (+IdR _))
                    (≤ᵣ-o+ 0 1 (absᵣ C) decℚ≤ᵣ?)))
               (fst (z<x/y₊≃y₊·z<x _ _ _)
             (isTrans<ᵣ _ _ _
            (X _ x∈ _ h∈ 0＃h h<a)
            η<1/[C+1])))))
        (udp (η , ℚ.<→0< _ (<ᵣ→<ℚ _ _ 0<η))))
    (denseℚinℝ 0 _ (snd (ℚ₊→ℝ₊ ε ₊·ᵣ invℝ₊ (absᵣ C +ᵣ 1 ,
      isTrans≡<ᵣ _ _ _
        (sym (+ᵣ-rat _ _)) (≤<ᵣMonotone+ᵣ _ _ _ _
          (0≤absᵣ C) (decℚ<ᵣ? {0} {1}))))))

uDerivativeOfℙ-ᵣ : ∀ P f f'
        → uDerivativeOfℙ P , f is f'
        → uDerivativeOfℙ P , (λ x x∈ → -ᵣ (f x x∈)) is (λ x x∈ → -ᵣ (f' x x∈))
uDerivativeOfℙ-ᵣ P f f' df =
     subst2
     (uDerivativeOfℙ P ,_is_)
     (funExt₂ λ _ _ → sym (-ᵣ≡[-1·ᵣ] _))
     (funExt₂ λ _ _ → sym (-ᵣ≡[-1·ᵣ] _))
     (C·uDerivativeℙ P -1 f f' df)


·CuDerivativeℙ : ∀ P C f f'
        → uDerivativeOfℙ P , f is f'
        → uDerivativeOfℙ P , (λ x x∈ → f x x∈ ·ᵣ C) is (λ x x∈ → f' x x∈ ·ᵣ C)
·CuDerivativeℙ P C f f' df =
     subst2
     (uDerivativeOfℙ P ,_is_)
     (funExt₂ λ _ _ → ·ᵣComm _ _)
     (funExt₂ λ _ _ → ·ᵣComm _ _)
     (C·uDerivativeℙ P C f f' df)


-uDerivativeℙ : ∀ P  f f' g g'
        → uDerivativeOfℙ P , f is f'
        → uDerivativeOfℙ P , g is g'
        → uDerivativeOfℙ P , (λ x x∈ → f x x∈ -ᵣ g x x∈)
          is (λ x x∈ → f' x x∈ -ᵣ g' x x∈)
-uDerivativeℙ P f f' g g' F G =
 +uDerivativeℙ P _ _ _ _ F (uDerivativeOfℙ-ᵣ P _ _ G)

C·Derivative' : ∀ C x f f'x
        → derivativeOf f at x is f'x
        → derivativeOf ((_·ᵣ C) ∘S f) at x is (f'x ·ᵣ C)
C·Derivative' C x f f'x F =
  substDer₂ {f = _·ᵣ_ C ∘S f } {g = (_·ᵣ C) ∘S f} (λ _ → ℝ!) (·ᵣComm _ _)
    (C·Derivative C x f f'x F)

-- -- ·Derivative : ∀ x f f'x g g'x
-- --         → derivativeOf f at x is f'x
-- --         → derivativeOf g at x is g'x
-- --         → derivativeOf (f $[ _·ᵣ_ ]$ g) at x is
-- --            (f'x ·ᵣ (g x) +ᵣ (f x) ·ᵣ g'x)
-- -- ·Derivative x f f'x g g'x F G ε =
-- --   PT.map2
-- --     (λ (δ , X) (δ' , X') →
-- --       let ∣f'g'∣+1 = _ ,
-- --                 isTrans≡<ᵣ _ _ _
-- --                   (sym (+ᵣ-rat 0 0))
--                   (≤<ᵣMonotone+ᵣ 0 (absᵣ (f'x ·ᵣ g'x)) 0 1
--                     (0≤absᵣ _) decℚ<ᵣ?)
--           δ'' = (ε ₊·ᵣ ℚ₊→ℝ₊ ([ 1 / 2 ] , _)) ₊·ᵣ invℝ₊ ∣f'g'∣+1
--           ⊔δ = minᵣ₊ (minᵣ₊ δ δ') δ''
--           X'' : absᵣ ((f'x ·ᵣ g'x) ·ᵣ fst ⊔δ ) <ᵣ ε .fst ·ᵣ rat [ 1 / 2 ]
--           X'' = isTrans≡<ᵣ _ _ _
--                (·absᵣ _ _)
--                 (isTrans≤<ᵣ _ _ _
--                   (≤ᵣ-o·ᵣ _ _ _ (0≤absᵣ _)
--                     (isTrans≡≤ᵣ _ _ _
--                       (absᵣPos _ (snd ⊔δ))
--                       (min≤ᵣ' _ _)))
--                   {!!})
--       in ⊔δ , λ h 0＃h ∣h∣< →
--             isTrans≤<ᵣ _ _ _
--               {!!}
--               (isTrans<≡ᵣ _ _ _
--                 (<ᵣMonotone+ᵣ _ _ _ _
--                   (<ᵣMonotone+ᵣ _ _ _ _
--                     (X {!!} {!!} {!!})
--                     (X' {!!} {!!} {!!}))
--                   X'')
--                 (cong₂ _+ᵣ_ (sym (·DistL+ _ _ _)) refl
--                  ∙ sym (·DistL+ _ _ _)
--                   ∙ cong₂ _·ᵣ_ refl
--                     (cong₂ _+ᵣ_ (+ᵣ-rat [ 1 / 4 ] [ 1 / 4 ]
--                     ∙ decℚ≡ᵣ?) refl
--                       ∙ +ᵣ-rat [ 1 / 2 ] [ 1 / 2 ]
--                     ∙ decℚ≡ᵣ?) ∙ ·IdR _)))
--     (F (ε ₊·ᵣ ℚ₊→ℝ₊ ([ 1 / 4 ] , _)))
--     (G (ε ₊·ᵣ ℚ₊→ℝ₊ ([ 1 / 4 ] , _)))


·Derivative : ∀ x f f'x g g'x
        → IsContinuous g
        → derivativeOf f at x is f'x
        → derivativeOf g at x is g'x
        → derivativeOf (f $[ _·ᵣ_ ]$ g) at x is
           (f'x ·ᵣ (g x) +ᵣ (f x) ·ᵣ g'x)
·Derivative x f f'x g g'x gC F G =
  substLim (λ _ _ → ℝ!)
    (+-lim _ _ _ _ _
      (·-lim _ _ _ _ _
        F (IsContinuousLimΔ g x gC)) (·-lim _ _ _ _ _ (const-lim _ _) G))

Derivative² : ∀ x g g'x
        → IsContinuous g
        → derivativeOf g at x is g'x
        → derivativeOf (g $[ _·ᵣ_ ]$ g) at x is
           (2 ·ᵣ (g'x ·ᵣ g x))
Derivative² x g g'x gC gD =
  subst (derivativeOf (g $[ _·ᵣ_ ]$ g) at x is_)
    (cong₂ _+ᵣ_ refl (·ᵣComm _ _)
     ∙ x+x≡2x _ ) (·Derivative x g g'x g g'x gC gD gD)

-- -- LimEverywhere→LimIncl : ∀ f → (∀ x → at x limitOf (λ x _ → f x) is (f x))
-- --                            → (∀ x → at x inclLimitOf f is (f x))
-- -- LimEverywhere→LimIncl = {!!}


-- hasDer→isCont : ∀ f (f' : ℝ → ℝ) →
--   (∀ x → derivativeOf f at x is f' x )
--   → IsContinuous f
-- hasDer→isCont f f' df ε = {!df!}

derivative-^ⁿ : ∀ n x →
   derivativeOf (_^ⁿ (suc n)) at x
            is (fromNat (suc n) ·ᵣ (x ^ⁿ n))
derivative-^ⁿ zero x =
 substDer₂ {f = idfun ℝ} {g = λ z → 1 ·ᵣ idfun ℝ z}
   (λ _ → sym (·IdL _))
   (sym (·IdL _))
   (idDerivative x)
derivative-^ⁿ (suc n) x =
  substDer₂ {f = (_^ⁿ suc n) $[ _·ᵣ_ ]$ (λ z → z)} {g = λ z → ((_^ⁿ suc n) $[ _·ᵣ_ ]$ (λ z₁ → z₁)) z} (λ _ → refl)
    (+ᵣComm _ _ ∙ cong₂ _+ᵣ_
       (·ᵣComm _ _) (sym (·ᵣAssoc _ _ _)) ∙
       sym (·DistR+ _ _ _) ∙
        cong (_·ᵣ ((x ^ⁿ n) ·ᵣ idfun ℝ x))
         (+ᵣ-rat _ _ ∙ cong rat (ℚ.ℕ+→ℚ+ 1 (suc n))))
    (·Derivative _ (_^ⁿ suc n) _ _ _ IsContinuousId
       (derivative-^ⁿ n x) (idDerivative x))

derivative-∘· : ∀ f f' x k
   → derivativeOf f at x is f'
   → derivativeOf (f ∘ (fst k ·ᵣ_)) at x ／ᵣ₊ k is (fst k ·ᵣ f')
derivative-∘· f f' x k X ε =
 PT.map
  (λ (δ , Y) →
    (δ ₊·ᵣ invℝ₊ k) , λ h 0＃h v →
         let 0＃k·h : (0 <ᵣ fst k ·ᵣ h) ⊎ (fst k ·ᵣ h <ᵣ 0)
             0＃k·h = ⊎.map
                (λ 0<h → snd (k ₊·ᵣ (h , 0<h)))
                (λ h<0 → isTrans<≡ᵣ _ _ _
                           (<ᵣ-o·ᵣ _ _ k h<0) (𝐑'.0RightAnnihilates _)) 0＃h
             u = fst (z<x/y₊≃y₊·z<x _ _ _) (Y (fst k ·ᵣ h)
                   0＃k·h (isTrans≡<ᵣ _ _ _
                    (cong absᵣ (+IdL _ ∙ sym (·-ᵣ _ _)) ∙ ·absᵣ _ _  ∙
                      cong₂ _·ᵣ_
                       ((absᵣPos _ (snd k)))
                       (cong absᵣ (sym (+IdL _))))
                    (fst (z<x/y₊≃y₊·z<x _ _ _) v)))
         in  isTrans≡<ᵣ _ _ _
              (cong absᵣ
                  (   cong (_-ᵣ_ (fst k ·ᵣ f'))
                    ((cong₂ _·ᵣ_
                       (cong₂ _-ᵣ_
                         (cong f (·DistL+ _ _ _ ∙
                           cong (_+ᵣ fst k ·ᵣ h)
                             (·ᵣComm _ _ ∙ [x/₊y]·yᵣ x k) ))
                         (cong f (·ᵣComm _ _ ∙ [x/₊y]·yᵣ x k)))
                       ((sym ([x/y]·yᵣ _ _ _))
                        ∙ cong (_·ᵣ (fst k))
                         (·ᵣComm _ _ ∙ sym (invℝ· (fst k) h (inl (snd k)) _ 0＃k·h)) )
                     ∙  (·ᵣAssoc _ _ _))
                      ∙ ·ᵣComm _ _)
                    ∙ sym (·DistL- _ _ _))
               ∙∙ ·absᵣ _ _
               ∙∙ cong (_·ᵣ absᵣ (f' -ᵣ differenceAt f x (fst k ·ᵣ h) 0＃k·h))
                   (absᵣPos _ (snd k))) u)
   (X (ε ₊·ᵣ invℝ₊ k))

-- -- -- easy to prove, but with narrow assumptin



chainRuleIncr : ∀ x f f'gx g g'x
        → isIncrasing g
        → IsContinuous g
        → derivativeOf g at x is g'x
         → derivativeOf f at (g x) is f'gx
        → derivativeOf (f ∘ g) at x is (f'gx ·ᵣ g'x)
chainRuleIncr x f f'gx g g'x incrG cg dg df =
  let z = ·-lim _ _ _ _ _ w dg
  in substLim (λ h 0#h → sym (x/y=x/z·z/y _ _ _ _ _)) z

 where
 0#g : ∀ h → (0＃h : 0 ＃ h) → 0 ＃ (g (x +ᵣ h) -ᵣ g x)
 0#g h = ⊎.map ((x<y→0<y-x _ _ ∘S incrG _ _)
           ∘S subst (_<ᵣ (x +ᵣ h)) (+IdR x) ∘S <ᵣ-o+ _ _ x)
            (((x<y→x-y<0 _ _ ∘S incrG _ _)
           ∘S subst ((x +ᵣ h) <ᵣ_) (+IdR x) ∘S <ᵣ-o+ _ _ x))

 w' :   ∀ (ε : ℝ₊) → ∃[ δ ∈ ℝ₊ ]
        (∀ h 0＃h →
           absᵣ (0 -ᵣ h) <ᵣ fst δ →
             absᵣ (f'gx -ᵣ ((f (g (x)  +ᵣ h) -ᵣ f (g x))
           ／ᵣ[ (h) , 0＃h ])) <ᵣ fst ε)

 w' = df

 w : at 0 limitOf
        (λ h 0＃h → (f (g (x +ᵣ h)) -ᵣ f (g x))
           ／ᵣ[ (g (x +ᵣ h) -ᵣ g x) , 0#g h 0＃h ]) is f'gx
 w ε =
   PT.rec squash₁
     (λ (δ , X) →
       PT.map
        (map-snd (λ X* →
          (λ h 0＃h ∣h∣<δ' →
           let Δg<δ = isTrans≡<ᵣ _ _ _
                     (cong absᵣ (+IdL _ ∙ -[x-y]≡y-x _ _))
                    (X* h 0＃h ∣h∣<δ')
               z = X (g (x +ᵣ h) -ᵣ g x) (0#g h 0＃h) Δg<δ
           in isTrans≡<ᵣ _ _ _
             (cong (absᵣ ∘ (λ x → f'gx -ᵣ x)
               ∘ _／ᵣ[ (g (x +ᵣ h) -ᵣ g x) , 0#g h 0＃h ] ∘
                  (_-ᵣ f (g x)) ∘ f)
               ℝ! ) z )))
                (IsContinuousLimΔ _ x cg δ))
     (w' ε)

-- -- -- chainRule : ∀ x f f'gx g g'x
-- -- --         → derivativeOf g at x is g'x
-- -- --          → derivativeOf f at (g x) is f'gx
-- -- --         → derivativeOf (f ∘ g) at x is (f'gx ·ᵣ g'x)
-- -- -- chainRule = {!!}


-- IsContinuousLimExcl : ∀ x f → IsContinuousWithPred (＃ℙ x) f →
--                     at x limitOf f is (f x)
-- IsContinuousLimExcl f x cx = ?
--  -- inclLimit→Limit _ _ _ (IsContinuousInclLim f x cx)


limitUniq : ∀ x f y y'
 → at x limitOf f is y
 → at x limitOf f is y'
 → y ≡ y'
limitUniq x f y y' X X' = eqℝ _ _
  λ ε →
    PT.rec2 (isProp∼ _ _ _)
      (λ (δ , D) (δ' , D') →
        let [δ⊔δ]/2 = (minᵣ₊ δ δ') ₊·ᵣ (ℚ₊→ℝ₊ ([ 1 / 2 ]₊))
            x＃ : x ＃ (x +ᵣ -ᵣ (minᵣ₊ δ δ' ₊·ᵣ ℚ₊→ℝ₊ ([ 1 / 2 ]₊)) .fst)
            x＃ = (inr (isTrans<≡ᵣ _ _ _
                        (<ᵣ-o+ _ _ _ (-ᵣ<ᵣ _ _ (snd [δ⊔δ]/2))) ℝ!))
        in subst∼ (ℚ.ε/2+ε/2≡ε (fst ε))
                  (triangle∼  {ε = /2₊ ε} {/2₊ ε}
                    (invEq (∼≃abs<ε _ _ _) (D (x -ᵣ fst [δ⊔δ]/2)
                     x＃
                     ((isTrans≡<ᵣ _ _ _
                       (cong 
                         absᵣ ℝ! ∙ absᵣPos _ (snd [δ⊔δ]/2))
                       (isTrans≤<ᵣ _ _ _
                         (≤ᵣ-·o _ _ _ (ℚ.0≤pos _ _) (min≤ᵣ _ _)) (isTrans<≡ᵣ _ _ _
                           (<ᵣ-o·ᵣ _ _ δ decℚ<ᵣ?) (·IdR _)))))))
                      (sym∼ _ _ _
                       ((invEq (∼≃abs<ε _ _ _) (D' (x -ᵣ fst [δ⊔δ]/2)
                     x＃
                     (isTrans≡<ᵣ _ _ _
                       (cong absᵣ ℝ! ∙ absᵣPos _ (snd [δ⊔δ]/2))
                       (isTrans≤<ᵣ _ _ _
                         (≤ᵣ-·o _ _ _ (ℚ.0≤pos _ _) (min≤ᵣ' _ _)) (isTrans<≡ᵣ _ _ _
                           (<ᵣ-o·ᵣ _ _ δ' decℚ<ᵣ?) (·IdR _)))))))))
        )
      (X (ℚ₊→ℝ₊ (/2₊ ε))) (X' (ℚ₊→ℝ₊ (/2₊ ε)))


uDer-lem : ∀ (ε : ℚ₊) x y h 0＃h →
   (absᵣ (x -ᵣ (y ／ᵣ[ h , 0＃h ])) <ᵣ rat (fst ε))
    ≃ ((absᵣ (x ·ᵣ h -ᵣ y) <ᵣ absᵣ h ·ᵣ rat (fst ε)))
uDer-lem ε x y h 0＃h =
  substEquiv (_<ᵣ rat (fst ε))
    (   cong absᵣ
          (  cong₂ _-ᵣ_ (sym ([x·y]/yᵣ _ _ 0＃h)) refl
           ∙ sym (𝐑'.·DistL- _ _ _))
     ∙∙ ·absᵣ _ _
     ∙∙ cong₂ _·ᵣ_
       refl
       (absᵣ-invℝ _ _)) ∙ₑ
    z/y<x₊≃z<y₊·x _ _ (_ , 0＃→0<abs h 0＃h)

Bounded : (P : ℙ ℝ) → (f : ∀ x → x ∈ P → ℝ)
                    → Type
Bounded P f = Σ[ b ∈ ℚ₊ ] (∀ x x∈ → absᵣ (f x x∈) ≤ᵣ rat (fst b))


uDerivativeOfℙ· : ∀ a b → a <ᵣ b
  → (f g f' g' : ∀ x → x ∈ intervalℙ a b → ℝ)
  → Bounded (intervalℙ a b) f
  → Bounded (intervalℙ a b) g
  → IsUContinuousℙ (intervalℙ a b) f
  → Bounded (intervalℙ a b) g'
  → uDerivativeOfℙ intervalℙ a b , f is f'
  → uDerivativeOfℙ intervalℙ a b , g is g'
  → uDerivativeOfℙ intervalℙ a b , (λ x x∈ → f x x∈ ·ᵣ g x x∈)
    is λ x x∈ → f' x x∈ ·ᵣ g x x∈ +ᵣ g' x x∈ ·ᵣ f x x∈
uDerivativeOfℙ· a b a<b f g f' g'
  (bf , <bf)  (bg , <bg) ucf (bg' , <bg') dF dG ε = do
    let M = ℚ.max₊ (ℚ.max₊ bf bg) bg'
    -- (M' , M<M') ← ∃ℚ₊LargerThanℝ₊ M
    let ε' = (/3₊ ε) ℚ₊· invℚ₊ M
    (δf' , Df) ← dF ε'
    (δg' , Dg) ← dG ε'
    let (δf , Cf) = ucf ε'
    let δ = ℚ.min₊ (ℚ.min₊ δf' δg') δf
    return (δ ,
      λ x x∈ h h∈ 0＃h ∣h∣<δ →
       let Df* = isTrans≡<ᵣ _ _ _
               (·absᵣ _ _)
               (isTrans≤<ᵣ _ _ _
               (≤ᵣ-·ᵣo _ _ _
                 (0≤absᵣ _)
                 (isTrans≤ᵣ _ _ _
                    (<bg _ x∈)
                    (≤ℚ→≤ᵣ _ _
                      (ℚ.isTrans≤ _ _ _
                        (ℚ.≤max' (bf .fst) _) (ℚ.≤max _ (bg' .fst))))))
              (fst (z<x/y₊≃y₊·z<x  _ _ (ℚ₊→ℝ₊ M)) $ isTrans<≡ᵣ _ _ _
               (fst (uDer-lem ε' _ _ _ 0＃h) $
                   Df x x∈ h h∈ 0＃h
                     (isTrans<≤ᵣ _ _ _
                       ∣h∣<δ
                       (≤ℚ→≤ᵣ _ _
                        (ℚ.isTrans≤ _ _ _
                          (ℚ.min≤ _ _)
                          (ℚ.min≤ _ _)))))
                   (cong₂ _·ᵣ_ refl (rat·ᵣrat (fst ε ℚ.· [ 1 / 3 ]) _ )
                    ∙∙ ·ᵣAssoc _ _ _
                    ∙∙ cong₂ _·ᵣ_ refl
                       (sym (invℝ₊-rat M)))))
           Dg* = isTrans≡<ᵣ _ _ _
               (·absᵣ _ _)
               (isTrans≤<ᵣ _ _ _
               (≤ᵣ-·ᵣo _ _ _
                 (0≤absᵣ _)
                 ((isTrans≤ᵣ _ _ _
                    (<bf _ h∈)
                    (≤ℚ→≤ᵣ _ _
                      (ℚ.isTrans≤ _ _ _
                        (ℚ.≤max _ (bg .fst)) (ℚ.≤max _ (bg' .fst)))))))
              (fst (z<x/y₊≃y₊·z<x  _ _ (ℚ₊→ℝ₊ M)) $ isTrans<≡ᵣ _
               _ _
               (fst (uDer-lem ε' _ _ _ 0＃h) $
                   Dg x x∈ h h∈ 0＃h
                     (isTrans<≤ᵣ _ _ _
                       ∣h∣<δ
                       (≤ℚ→≤ᵣ _ _
                        (ℚ.isTrans≤ _ _ _
                          (ℚ.min≤ _ (ucf ε' .fst .fst))
                          (ℚ.min≤' (δf' .fst) _)))))
                   (cong₂ _·ᵣ_ refl (rat·ᵣrat (fst ε ℚ.· [ 1 / 3 ]) _ )
                    ∙∙ ·ᵣAssoc _ _ _
                    ∙∙ cong₂ _·ᵣ_ refl
                       (sym (invℝ₊-rat _)))))
           Cf* = isTrans≡<ᵣ _ _ _
                (·absᵣ _ _)
                (<ᵣ-o·ᵣ _ _ (_ , 0＃→0<abs h 0＃h)
               (isTrans≡<ᵣ _ _ _
               (·absᵣ _ _)
                (isTrans≤<ᵣ _ _ _
               (≤ᵣ-·ᵣo _ _ _
                 (0≤absᵣ _)
                  (isTrans≤ᵣ _ _ _
                    (<bg' _ x∈)
                    (≤ℚ→≤ᵣ _ _
                      (ℚ.≤max' (ℚ.max (bf .fst) (bg .fst)) _ )))) (fst (z<x/y₊≃y₊·z<x  _ _ (ℚ₊→ℝ₊ M)) $
                   isTrans<≡ᵣ _ _ _ (fst (∼≃abs<ε _ _ _) $ Cf _ _ x∈ h∈
                  (invEq (∼≃abs<ε _ _ _)
                    (isTrans≡<ᵣ _ _ _
                       (cong absᵣ ℝ!
                         ∙ sym (-absᵣ _))
                       (isTrans<≤ᵣ _ _ _ ∣h∣<δ
                         (≤ℚ→≤ᵣ _ _ (ℚ.min≤' (ℚ.min (δf' .fst) (δg' .fst)) _))))))
                     (rat·ᵣrat (fst ε ℚ.· [ 1 / 3 ]) _
                      ∙ cong₂ _·ᵣ_ refl (sym (invℝ₊-rat _)))))))
       in
          invEq (uDer-lem ε _ _ _ 0＃h)
            (isTrans≡<ᵣ _ _ _
              (cong absᵣ ℝ!)
              (isTrans<≡ᵣ _ _ _
                (isTrans<≡ᵣ _ _ _ (isTrans≤<ᵣ _ _ _
                    (absᵣ-triangle _ _)
                    (<ᵣMonotone+ᵣ _ _ _ _
                  (isTrans≤<ᵣ _ _ _
                    (absᵣ-triangle _ _)
                    (isTrans<≡ᵣ _ _ _
                      (<ᵣMonotone+ᵣ _ _ _ _ Df* Dg*)
                      (sym (·DistL+ _ _ _))))
                  Cf*))
                  (sym (·DistL+ _ _ _)))
                (cong₂ _·ᵣ_ refl
                   (cong₂ _+ᵣ_ (+ᵣ-rat _ _) refl
                     ∙ +ᵣ-rat _ _ ∙
                     cong rat (sym (ℚ.+Assoc (fst ε ℚ.· [ 1 / 3 ]) (fst ε ℚ.· [ 1 / 3 ]) (fst ε ℚ.· [ 1 / 3 ]))
                      ∙ ℚ.ε/3+ε/3+ε/3≡ε (fst ε)))))))

uDerivativeOfℙ² : ∀ a b → a <ᵣ b
  → (f f' : ∀ x → x ∈ intervalℙ a b → ℝ)
  → Bounded (intervalℙ a b) f
  → IsUContinuousℙ (intervalℙ a b) f
  → Bounded (intervalℙ a b) f'
  → uDerivativeOfℙ intervalℙ a b , f is f'
  → uDerivativeOfℙ intervalℙ a b , (λ x x∈ → f x x∈ ·ᵣ f x x∈)
    is λ x x∈ → 2 ·ᵣ (f' x x∈ ·ᵣ f x x∈)
uDerivativeOfℙ² a b x f f' x₁ x₂ x₃ x₄ =
   subst (uDerivativeOfℙ intervalℙ a b , (λ x x∈ → f x x∈ ·ᵣ f x x∈)
    is_) (funExt₂ λ _ _ → x+x≡2x _)
     (uDerivativeOfℙ· a b x f f f' f' x₁ x₁ x₂ x₃ x₄ x₄ )

uDerivativeOfℙ-transl : ∀ P f f' Δ
    → uDerivativeOfℙ P , f is f'
    → uDerivativeOfℙ P ∘ (_+ᵣ Δ) , (λ x x∈ → f (x +ᵣ Δ) x∈) is
         (λ x x∈ → f' (x +ᵣ Δ) x∈)
uDerivativeOfℙ-transl P f f' Δ =
  PT.map (map-snd (λ X x x∈ h h∈ 0＃h h< →
    isTrans≡<ᵣ _ _ _ (cong (λ d → absᵣ
      (f' (x +ᵣ Δ) x∈ -ᵣ d))
        (cong₂ _·ᵣ_ (cong₂ _-ᵣ_ (cong (uncurry f)
         (Σ≡Prop (∈-isProp P) ℝ!)) refl )
          refl)
        ) (X (x +ᵣ Δ) x∈ h (subst-∈ P ℝ! h∈) 0＃h h<))) ∘_

-- mapLimit : ∀ x f y (g : ℝ → ℝ)
--   → IsContinuousWithPred (＃ℙ x) f
--   → IsContinuous g
--   → at x limitOf f is y
--   → at x limitOf (λ r r#x → g (f r r#x)) is g y
-- mapLimit x f y g fC gC X (ε , 0<ε) =
--   PT.rec squash₁
--     (λ (q , 0<q , q<e) →
--      let q₊ = (q , {!!})
--      in PT.rec squash₁
--          (λ (δ , D) →
--             PT.rec squash₁
--               (λ (δ' , D') →
--                 ∣ minᵣ₊ (ℚ₊→ℝ₊ δ') δ ,
--                     (λ r x＃r x-r<δ →
--                        {!D r x＃r ?!}) ∣₁)
--               (gfC (x +ᵣ fst δ) (/2₊ q₊)
--                   {!!})

--                 )

--          (X (ℚ₊→ℝ₊ (/2₊ q₊)) ))
--    (denseℚinℝ _ _ 0<ε)

--  where
--   gfC : _
--   gfC = IsContinuousWP∘' _ _ _ gC fC


-- mapLimit' : ∀ x z f y (v : ∀ r r#x → z ＃ f r r#x) → ∀ ＃y → (g : ∀ r → z ＃ r → ℝ)
--   → IsContinuousWithPred (＃ℙ x) f
--   → IsContinuousWithPred (＃ℙ z) g
--   → at x limitOf f is y
--   → at x limitOf (λ r r#x → g (f r r#x) (v _ _)) is (g y ＃y)
-- mapLimit' x z f y v ＃y g fC gC L = {!!}


-- preMapLimit : ∀ x x' f g y → (u : ∀ r ＃r →  x' ＃ g r ＃r)
--   → at x  limitOf g is x'
--   → at x' limitOf f is y
--   → at x  limitOf (λ r ＃r → f (g r ＃r) (u _ _)) is y
-- preMapLimit = {!!}


-- invDerivative : ∀ f x (f' : ℝ) → ∀ 0＃f'  → (isEquivF : isEquiv f)
--   → IsContinuous f
--   → IsContinuous (invEq (f , isEquivF))
--   → derivativeOf f at x is f'
--   → derivativeOf (invEq (f , isEquivF)) at (f x) is (invℝ f' 0＃f')
-- invDerivative f x f' 0＃f' isEquivF fC gC d =
--  let g = invEq (f , isEquivF)
--      h' = λ h 0＃h →
--              g (f x +ᵣ h) -ᵣ x
--      d' = preMapLimit 0 0 _ h' f'
--            (λ r ＃r →
--              invEq (＃Δ _ _) {!!})
--             (subst (at 0 limitOf h' is_)
--               (cong (_-ᵣ x) (retEq (f , isEquivF) x) ∙ +-ᵣ x)
--               (+-lim _ _ _ _ _ (IsContinuousLimΔ g (f x) gC)
--                (const-lim (-ᵣ x) _)))
--             d
--      d'' = mapLimit' 0 0 _ f' {!!} 0＃f'
--           invℝ
--           (IsContinuousWP∘ _ _ _ _ _
--             (IsContinuousWithPred-differenceAt _ _ fC)
--              {!!})
--           IsContinuousWithPredInvℝ
--           d'

--  in substLim (λ r x＃r →
--       invℝ· _ _ (invEq (＃Δ _ _) {!!}) _ _ ∙∙ ·ᵣComm _ _ ∙∙
--         cong₂ _·ᵣ_
--           (invℝInvol _ _ ∙
--             cong (λ z → (invEq (f , isEquivF) (f x +ᵣ r)) -ᵣ z)
--               (sym (retEq (f , isEquivF) x)))
--           (cong₂ invℝ
--              (cong (_-ᵣ f x) (fst (equivAdjointEquiv (f , isEquivF))
--                  (cong (x +ᵣ_) (cong (_-ᵣ x) (cong (invEq (f , isEquivF)) (+ᵣComm _ _)) )
--                   ∙ +ᵣComm _ _ ∙ 𝐑'.minusPlus _ _))
--                ∙ 𝐑'.plusMinus _ _)
--              (toPathP (isProp＃  _ _ _ _)))
--       ) d''


-- fromCauchySequence'-limit : ∀ s ics →
--     {!fromCauchySequence' s ics!}
-- fromCauchySequence'-limit = {!!}
