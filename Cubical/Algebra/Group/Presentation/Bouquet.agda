{-# OPTIONS --safe --lossy-unification #-} 
module Cubical.Algebra.Group.Presentation.Bouquet where

open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Powerset
-- open import Cubical.Foundations.Function
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Empty as ⊥
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Bool using (false ; true) renaming (Bool to 𝟚) 



open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup

open import Cubical.HITs.EilenbergMacLane1


open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.GroupoidTruncation as GT
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base
open import Cubical.HITs.FreeGroup as FG renaming (assoc to ·assoc)

open import Cubical.HITs.Bouquet
open import Cubical.Data.List as List
open import Cubical.Functions.Logic as L
open import Cubical.Relation.Nullary

open import Cubical.Data.Int hiding (_·_)

open import Cubical.Foundations.Pointed

open import Cubical.Homotopy.Loopspace

open import Cubical.Algebra.Group.Instances.SetsAutomorphism


module _ {ℓ} (A∙ : Pointed ℓ) where
 
 IT→ : ∥ ⟨ Ω A∙ ⟩ ∥₂ → ⟨ Ω (∥ ⟨ A∙ ⟩ ∥₃ , ∣ pt A∙ ∣₃) ⟩
 IT→ = ST.rec (squash₃ _ _) (cong ∣_∣₃)

 IT←'T : ∀ (x : ∥ ⟨ A∙ ⟩ ∥₃)  → hSet ℓ
 IT←'T = GT.rec (isGroupoidHSet)
          λ x → (∥ snd A∙ ≡ x ∥₂) , (isSetSetTrunc)
 
 IT←' : ∀ x → ∣ snd A∙ ∣₃ ≡ x → ⟨ IT←'T x ⟩
 IT←' x = J (λ x _ → ⟨ IT←'T x ⟩) ∣ refl ∣₂


 IT← : ⟨ Ω (∥ ⟨ A∙ ⟩ ∥₃ , ∣ pt A∙ ∣₃) ⟩ → ∥ ⟨ Ω A∙ ⟩ ∥₂ 
 IT← = IT←' _


 IsoΩTrunc₂ : Iso ∥ ⟨ Ω A∙ ⟩ ∥₂ ⟨ Ω (∥ ⟨ A∙ ⟩ ∥₃ , ∣ pt A∙ ∣₃) ⟩
 Iso.fun IsoΩTrunc₂ = IT→
 Iso.inv IsoΩTrunc₂ = IT←
 Iso.rightInv IsoΩTrunc₂ =
    J (λ x y →
      ⟨ GT.elim (λ x → isGroupoidΠ λ (y : ∣ snd A∙ ∣₃ ≡ x )
         → isSet→isGroupoid isSetHProp ) 
         (λ x y → (ST.rec (squash₃ _ _) (cong ∣_∣₃) (IT←' ∣ x ∣₃ y) ≡ y) ,
            squash₃ _ _ _ _ ) x y ⟩)
              (cong (cong ∣_∣₃) (transportRefl _)) {∣ pt A∙ ∣₃}
 Iso.leftInv IsoΩTrunc₂ =
   ST.elim (λ _ → isProp→isSet (squash₂ _ _))
    λ a → cong ∣_∣₂ (substInPathsL _ _ ∙ sym (lUnit _))


-- -- record Sq' {ℓ} (A : Type ℓ) : Type ℓ where
-- --  constructor sq
-- --  field
-- --   fc₀₋ fc₁₋ fc₋₀ fc₋₁ : A  


private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    A∙ : Pointed ℓ


η* : 𝟚 × A → FreeGroup A
η* (b , a) = (𝟚.if b then idfun _ else inv) (η a)

fromList' : FreeGroup A → List (𝟚 × A) → FreeGroup A
fromList' = foldr (_·_ ∘ η*) 

fromList : List (𝟚 × A) → FreeGroup A
fromList = fromList' ε

fromList· : ∀ xs ys → fromList {A = A} (xs ++ ys) ≡
                          fromList xs · fromList ys
fromList· [] ys = idl _
fromList· (x ∷ xs) ys =
 cong (_ ·_) (fromList· xs ys) ∙
  FG.assoc _ _ _


module _ {ℓ} {A : Type ℓ} (_≟_ : Discrete A) where

 isSetA = Discrete→isSet _≟_

 IsRedex : 𝟚 × A → 𝟚 × A → hProp _
 IsRedex (b , x) (b' , x') =
   ((b ≡ 𝟚.not b') , 𝟚.isSetBool _ _)
     L.⊓ ((x ≡ x') , isSetA x x')

 WillReduce : 𝟚 → A → (xs : List (𝟚 × A)) → hProp ℓ
 WillReduce _ _ [] = ⊥* , isProp⊥*
 WillReduce b x (h ∷ _) = IsRedex (b , x) h

 Normalised : List (𝟚 × A) → hProp ℓ
 Normalised [] = L.⊤
 Normalised ((b , x) ∷ xs) = L.¬ WillReduce b x xs  L.⊓ Normalised xs


 isSet[𝟚×A] : isSet _
 isSet[𝟚×A] = isOfHLevelList 0 (isSet× 𝟚.isSetBool isSetA)

 NFSnd : FreeGroup A → List (𝟚 × A) →  hProp _
 NFSnd g l = ((fromList l ≡ g) , trunc _ _ ) ⊓ Normalised l 

 NF : (g : FreeGroup A) → Type _
 NF g = Σ _  λ l → ⟨ NFSnd g l ⟩

 open GroupTheory (freeGroupGroup A)

 redex-ε-η* : ∀ x x' → ⟨ IsRedex x x' ⟩ → η* x · η* x' ≡ ε
 redex-ε-η* (false , _) (false , _) (p , _) = ⊥.rec (𝟚.false≢true p)
 redex-ε-η* (false , x) (true , _) (_ , q) = 
   cong (inv (η x) ·_) (cong (η) (sym q)) ∙ invl (η x) 
 redex-ε-η* (true , x) (false , _) (_ , q) =
   cong (η x ·_) (cong (inv ∘ η) (sym q)) ∙ invr (η x)
 redex-ε-η* (true , _) (true , _) (p , _) = ⊥.rec (𝟚.true≢false p)


 redex-ε : ∀ x x' → ⟨ IsRedex x x' ⟩ → fromList [ x ] · fromList [ x' ] ≡ ε
 redex-ε x x' q = cong₂ _·_ (sym (idr _)) (sym (idr _)) ∙ redex-ε-η* x x' q


 NFSnd∷ : ∀ g x l → ⟨ NFSnd g (x ∷ l) ⟩ →
    ⟨ NFSnd (fromList' g [ 𝟚.not (fst x) , snd x ]) l ⟩  
 NFSnd∷ g x l p =
   ·CancelL (η* x) (fst p ∙∙ idl g ∙
     cong (_· g) (sym (redex-ε-η* _ _ (sym (𝟚.notnot _) , refl)))
      ∙∙ sym (FG.assoc _ _ _))
   , snd (snd p)

 IsRedex? : ∀ x x' → Dec ⟨ IsRedex x x' ⟩
 IsRedex? (b , x) (b' , x') =
   subst Dec (sym ΣPathP≡PathPΣ)
     (discreteΣ 𝟚._≟_ (λ _ → _≟_) (b , x) (𝟚.not b' , x'))
 
 WillReduce? : ∀ x xs → Dec ⟨ WillReduce (fst x) (snd x) xs ⟩  
 WillReduce? _ [] = no λ ()
 WillReduce? _ (_ ∷ xs) = IsRedex? _ _



 -- NFSndε : ∀ l → ⟨ NFSnd ε l ⟩ → l ≡ []
 -- NFSndε [] _ = refl
 -- NFSndε (x ∷ x₁ ∷ l) (p , (nwf , _ , q)) =
 --  let z = NFSndε l ({!p!} , q)
 --  in {!!}
 -- NFSndε ((false , _) ∷ []) (p , q) = ⊥.rec (0≢1-ℤ (sym (cong (toℤ ∘ inv) p)))

 NFε : NF ε
 NFε = [] , refl , _


 normalised∷' : (b : 𝟚) → (a : A)  →
               ∀ xs → ⟨ Normalised xs ⟩
                → Dec ⟨ WillReduce b a xs ⟩
                →  (Σ _ (fst ∘ Normalised))
 normalised∷' b a [] _ _ = [ b , a ] , (λ ()) , tt*
 normalised∷' b a (x₂ ∷ xs) y (yes p) = xs , snd y
 normalised∷' b a xs@(_ ∷ _) y (no ¬p) = (b , a) ∷ xs , ¬p , y

 normalised∷ : 𝟚 → A  →
               ∀ xs → ⟨ Normalised xs ⟩ → (Σ _ (fst ∘ Normalised))
 normalised∷ b a xs y = normalised∷' b a xs y (WillReduce? (b , a) xs)

 normalised∷¬WR' : ∀ b a xs y → ⟨ L.¬ (WillReduce b a xs) ⟩
     → ∀ q →  fst (normalised∷' b a xs y q) ≡ (b , a) ∷ xs
 normalised∷¬WR' b a xs y x (yes p) = ⊥.rec (x p)
 normalised∷¬WR' b a [] y x (no ¬p) = refl
 normalised∷¬WR' b a (x₁ ∷ xs) y x (no ¬p) = refl


 normalised∷¬WR : ∀ b a xs y → ⟨ L.¬ (WillReduce b a xs) ⟩
     → fst (normalised∷ b a xs y) ≡ (b , a) ∷ xs
 normalised∷¬WR b a xs y ¬p = normalised∷¬WR' b a xs y ¬p _ 

 normalised∷-sec : ∀ b a xs y p p' →
    fst (uncurry (normalised∷' (𝟚.not b) a)
      (normalised∷' b a xs y p) p')
      ≡ xs
 normalised∷-sec b x [] y (no ¬p) (yes p) = refl
 normalised∷-sec b x [] y (no ¬p) (no ¬p₁) = ⊥.rec (¬p₁ (refl , refl)) 
 normalised∷-sec b x (x₁ ∷ xs) y (no ¬p) (yes p) = refl
 normalised∷-sec b x (x₁ ∷ xs) y (no ¬p) (no ¬p₁) = ⊥.rec (¬p₁ (refl , refl))
 normalised∷-sec b x (x₁ ∷ []) y (yes p) (no ¬p) =
   cong [_] (cong₂ _,_ (cong 𝟚.not (fst p) ∙ 𝟚.notnot _) (snd p)) 
 normalised∷-sec b x (x₁ ∷ x₂ ∷ xs) y (yes p) (no ¬p) =
   cong (_∷ _) (cong₂ _,_ (cong 𝟚.not (fst p) ∙ 𝟚.notnot _) (snd p))
 normalised∷-sec b x ((b' , x') ∷ (b'' , x'') ∷ xs) y (yes p) (yes p₁) =
   ⊥.rec ( fst y (((sym (𝟚.notnot b') ∙ sym (cong 𝟚.not (fst p))) ∙ fst p₁) ,
      sym (snd p) ∙ snd p₁))


 NF∷Iso : 𝟚 → A  →
             Iso (Σ _ (fst ∘ Normalised)) (Σ _ (fst ∘ Normalised)) 
 NF∷Iso b x = w b
  where
  w : 𝟚 → Iso _ _
  Iso.fun (w b) = uncurry (normalised∷ b x) 
  Iso.inv (w b) = uncurry (normalised∷ (𝟚.not b) x)
  Iso.rightInv (w false) (xs , p) =
    Σ≡Prop (snd ∘ Normalised) (normalised∷-sec _ _ _ _ _ _)
  Iso.rightInv (w true) (xs , p) =
    Σ≡Prop (snd ∘ Normalised) (normalised∷-sec _ _ _ _ _ _)
       
  Iso.leftInv (w _) a = Σ≡Prop (snd ∘ Normalised) (normalised∷-sec _ _ _ _ _ _)
  
 NFSet = isSetΣ (isOfHLevelList 0 (isSet× 𝟚.isSetBool isSetA))
          (isProp→isSet ∘ snd ∘ Normalised)

 NFAutG = (SetAut (Σ _ (fst ∘ Normalised)) (NFSet))
 
 NFhom : GroupHom (freeGroupGroup A) NFAutG 
 NFhom = FG.rec {Group = NFAutG} (NF∷Iso false)

 NFhomLem : ∀ xs y → (Iso.inv (fst NFhom (fromList xs)) ([] , _)) ≡ (xs , y) 
 NFhomLem [] y = refl
 NFhomLem (x@(false , a) ∷ xs) y =
  let z = cong (fst ∘ uncurry (uncurry (normalised∷) x)  ) (NFhomLem xs (snd y))
  in Σ≡Prop (snd ∘ Normalised) (z ∙ (normalised∷¬WR _ _ _ _ (fst y)))
 NFhomLem (x@(true , a) ∷ xs) y = 
  let z = cong (fst ∘ uncurry (uncurry (normalised∷) x)  ) (NFhomLem xs (snd y))
  in Σ≡Prop (snd ∘ Normalised) (z ∙ (normalised∷¬WR _ _ _ _ (fst y)))


 isPropNF : ∀ g → isProp (NF g)
 isPropNF g (x , p , q) (x' , p' , q') =
   Σ≡Prop (snd ∘ NFSnd g)
     (cong fst (sym (NFhomLem x q))
      ∙∙ cong (λ g → fst (Iso.inv (fst NFhom g) ([] , tt*)))
           (p ∙ sym p') ∙∙
      cong fst (NFhomLem x' q'))
 
 norm'-fromList : ∀ x xs q v →
  fromList (fst (normalised∷' (fst x) (snd x) xs q v))
   ≡ (fromList [ x ] · fromList xs)
 norm'-fromList x [] q v = idr _
 norm'-fromList x (x₁ ∷ xs) q (yes p) =
   (idl _ ∙ cong (_· fromList xs) (sym (redex-ε x x₁ p)))
    ∙∙ sym (FG.assoc _ _ _)
     ∙∙ cong (fromList [ x ] ·_) (sym (fromList· [ x₁ ] xs))
 norm'-fromList x (x₁ ∷ xs) q (no ¬p) = fromList· _ _
 
 NF∷ : ∀ {g} → ∀ x → NF g → NF (fromList [ x ] · g)  
 NF∷ x (xs , (p , q)) =
  let (xs' , q') = normalised∷ (fst x) (snd x) xs q 
  in xs' , norm'-fromList _ _ _ _ ∙ cong (fromList [ x ] ·_) p , q'
  
 NF++ : ∀ {g h} → NF g → NF h → NF (g · h)
 NF++ {g} {h} nfg y@(ys , (p' , q')) =  
   uncurry (NF++' g) nfg
    where
    NF++' : ∀ (g : _) x (y : (fromList x ≡ g) × fst (Normalised x)) →
              NF (g · h)
    NF++' _ [] (p , q) =
       ys , p' ∙ idl _ ∙ cong (_· _) p  , q'
    NF++' g (x ∷ xs) (p , q) =
     let p' = (idl _ ∙ cong (_· fromList xs)
              (sym (redex-ε-η* _ _ (refl , refl))))
             ∙∙ sym (FG.assoc _ _ _)
             ∙∙ cong (flip fromList' [  (𝟚.not (fst x) , snd x) ]) p
         (xs* , p* , q*) = NF∷ x (NF++' (fromList' g [ (𝟚.not (fst x) , snd x) ]) xs
               (p' , snd q)) 
      in xs*
        , p* ∙∙ FG.assoc _ _ _ ∙∙ cong (_· h)
             (FG.assoc _ _ _ ∙∙ cong (_· g)
               (cong (_· η* (𝟚.not (fst x) , snd x)) (sym (idr _))
                ∙ redex-ε-η* _ _ (sym (𝟚.notnot _) , refl)) ∙∙ sym (idl g))
        , q*


 substNF : ∀ {g g'} → g ≡ g' → NF g → NF g'
 substNF p = map-snd (map-fst (_∙ p))

 NFinv : ∀ {g} → NF g → NF (inv g) 
 NFinv {g} = uncurry (NFinv' g) 
  where
  NFinv' : ∀ g xs → (fromList xs ≡ g) × _ → NF (inv g)
  NFinv' g [] (p , q) = [] , sym inv1g ∙ cong inv p  , _
  NFinv' g (x@(b , a) ∷ xs) (p , q) = 
   let z' = NFinv' _ xs (NFSnd∷ g x xs (p , q))
       z = NF++ z' ([ (𝟚.not b , a) ] , refl , (λ ()) , _)  
   in substNF
         (injInv (
         invDistr _ _ ∙∙
          cong₂ (_·_) (cong inv (sym (idr _))) (invInv _) ∙
            FG.assoc _ _ _ ∙
              cong (_· g) (invl _) ∙ sym (idl _) 
          ∙∙ sym (invInv _)))
          z



 nf : ∀ g → NF g
 nf = ElimProp.f w
  where
  open ElimProp
  w : ElimProp (λ z → NF z)
  isPropB w = isPropNF
  εB w = NFε
  ηB w a = [ true , a ] , sym (idr _) , (λ ()) , _
  invB w _ = NFinv
  ·B w _ _ = NF++

 FG≃ΣNormalised : (Σ _ (fst ∘ Normalised)) ≃ FreeGroup A
 fst FG≃ΣNormalised = fromList ∘ fst
 equiv-proof (snd FG≃ΣNormalised) g =
  let (xs , p , q) = nf g
  in ((xs , q) , p) ,
       λ ((xs' , q') , p') i →
         let (xs'' , p'' , q'') = isPropNF g (xs , p , q) (xs' , p' , q') i
         in (xs'' , q'') , p''


 discreteFreeGroup : Discrete (FreeGroup A)
 discreteFreeGroup x y =
   mapDec (invEq (congEquiv (invEquiv FG≃ΣNormalised)) ∘
     Σ≡Prop (snd ∘ Normalised)) (_∘ cong (fst ∘ nf))
    (discreteList (discreteΣ 𝟚._≟_ (λ _ → _≟_)) (fst (nf x)) (fst (nf y)))


 BCode : Bouquet A → Type ℓ
 BCode base = Σ _ (fst ∘ Normalised)
 BCode (loop x i) = ua (isoToEquiv (NF∷Iso true x)) i


 bcode : ∀ x → base ≡ x → BCode x
 bcode x p = subst BCode p ([] , _) 
  -- J (λ v _ → BCode v) ([] , _)

 bb : ∀ a → fst (bcode base (loop a)) ≡ [ true , a ]
 bb a = transportRefl _


 ΩFG : Type ℓ → Pointed ℓ
 ΩFG A = Ω (Bouquet∙ A)

 loop* : 𝟚 × A → ⟨ ΩFG A ⟩
 loop* (b , a) = (𝟚.if b then idfun _ else sym) (loop a)

 fromList'Ω : ⟨ ΩFG A ⟩ → List (𝟚 × A) → ⟨ ΩFG A ⟩
 fromList'Ω = foldr (flip _∙_ ∘ loop*) 

 fromListΩ : List (𝟚 × A) → ⟨ ΩFG A ⟩
 fromListΩ = fromList'Ω refl
 
 bdecodeLoop'' :  ∀ a (x : List (𝟚 × A))
                   (y : ((λ r → fst r) ∘ Normalised) x) {z} → 
               fromListΩ
                 (fst (normalised∷' false a x y z))
                    ≡ fromListΩ x ∙ loop a ⁻¹
 bdecodeLoop'' a [] y {z} = refl
 bdecodeLoop'' a (x ∷ x₁) y {no ¬p} = refl
 bdecodeLoop'' a ((false , a') ∷ x₁) y {yes p} =
   ⊥.rec (𝟚.false≢true (fst p))
 bdecodeLoop'' a ((true , a') ∷ x₁) y {yes p} = 
     rUnit _ ∙∙ cong (fromListΩ x₁ ∙_) (sym (rCancel _)) ∙∙
          λ i → assoc (fromListΩ x₁) (loop a') (loop (snd p (~ i)) ⁻¹) i
 
 bdecodeLoop' : ∀ a → (x : List (𝟚 × A)) (y : ((λ r → fst r) ∘ Normalised) x) →
      transport
      (λ i → ua (isoToEquiv (NF∷Iso true a)) i → base ≡ loop a i)
      (fromListΩ ∘ (fst)) (x , y)
      ≡ (fromListΩ) x
 bdecodeLoop' a x y =
   substInPathsL _ _ ∙∙
     cong (_∙ loop a) (cong (fromListΩ ∘ fst)
       (~uaβ (isoToEquiv (NF∷Iso true a)) (x , y)))
       ∙∙ (cong (_∙ loop a) (bdecodeLoop'' a x y) ∙ (sym (assoc _ _ _)
         ∙∙ cong (fromListΩ x ∙_) (lCancel (loop a))
          ∙∙ sym (rUnit (fromListΩ x))))
 
 bdecodeLoop : ∀ a →
   PathP (λ i → ua (isoToEquiv (NF∷Iso true a)) i → base ≡ loop a i)
     (fromListΩ ∘ fst)
     (fromListΩ ∘ fst)
 bdecodeLoop a =
   toPathP (funExt (uncurry (bdecodeLoop' a)))
 
 bdecode : ∀ x → BCode x → base ≡ x
 bdecode base = fromListΩ ∘ fst
 bdecode (loop a i) = bdecodeLoop a i

 bdecodeencode : ∀ x p → (bdecode x) (bcode x p) ≡ p 
 bdecodeencode x = J (λ x p → (bdecode x) (bcode x p) ≡ p)
   refl

 BCodeLoop* : ∀ x xs y → subst BCode (loop* x) (xs , snd y) ≡ (x ∷ xs , y)
 BCodeLoop* (false , a) xs y =
   ~uaβ (isoToEquiv (NF∷Iso true a)) _ ∙
    Σ≡Prop (snd ∘ Normalised) (normalised∷¬WR _ _ _ _ (fst y))
 BCodeLoop* (true , a) xs y =
  uaβ (isoToEquiv (NF∷Iso true a)) _ ∙
   Σ≡Prop (snd ∘ Normalised) (normalised∷¬WR _ _ _ _ (fst y))

 bencodedecode : ∀ xs y → (bcode base) (bdecode base (xs , y)) ≡ (xs , y) 
 bencodedecode [] y = Σ≡Prop (snd ∘ Normalised ) refl
 bencodedecode (x ∷ xs) y =
   let z = bencodedecode xs (snd y)
   in substComposite BCode _ (loop* x) ([] , _) ∙∙
        cong (subst BCode (loop* x)) z ∙∙ BCodeLoop* x xs y


 BCodeIso : Iso ⟨ ΩFG A ⟩ (Σ _ (fst ∘ Normalised))
 Iso.fun BCodeIso = bcode base
 Iso.inv BCodeIso = bdecode base
 Iso.rightInv BCodeIso = uncurry bencodedecode
 Iso.leftInv BCodeIso = bdecodeencode base
 





data 𝟜 : Type where
 ₀₋ ₁₋ ₋₀ ₋₁ : 𝟜


□Ω : ∀ {ℓ} (A : Pointed ℓ) → Type ℓ
□Ω A = 𝟜 → ⟨ Ω A ⟩




-- -- -- mapSq : ∀ {A : Pointed ℓ} {B : Pointed ℓ'} → (A →∙ B) → Sq A → Sq B
-- -- -- Sq.fc₀₋ (mapSq f x₁) = {!fst f!}
-- -- -- Sq.fc₁₋ (mapSq f x₁) = {!!}
-- -- -- Sq.fc₋₀ (mapSq f x₁) = {!!}
-- -- -- Sq.fc₋₁ (mapSq f x₁) = {!!}

module _ (A : Pointed ℓ) {B : Type ℓ'} (rels : B → □Ω A) where



 data _≡/₃_ : Type (ℓ-max ℓ ℓ') 


 [_]' : ⟨ A ⟩ → _≡/₃_

 _≡/₃∙_ : Pointed (ℓ-max ℓ ℓ') 
 _≡/₃∙_ = _≡/₃_ , [ pt A ]'


 data _≡/₃_ where

  [_]≡/₃ : ⟨ A ⟩ → _≡/₃_
  □_ : (b : B) → Square {A = _≡/₃_}
                (cong [_]' (rels b ₀₋))
                (cong [_]' (rels b ₁₋))
                (cong [_]' (rels b ₋₀))
                (cong [_]' (rels b ₋₁))
  -- trunc : isGroupoid _≡/₃_

 [_]' = [_]≡/₃


 record Rec≡/₃ (X : Pointed ℓ'') : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
  field
   -- isGroupoidX : isGroupoid ⟨ X ⟩ 
   a→x : A →∙ X 
   sq : (b : B) → Square {A = ⟨ X ⟩}
                (λ i → fst a→x (rels b ₀₋ i))
                (λ i → fst a→x (rels b ₁₋ i))
                (λ i → fst a→x (rels b ₋₀ i))
                (λ i → fst a→x (rels b ₋₁ i))
   

  f : _≡/₃_ → ⟨ X ⟩
  f [ x ]≡/₃ = fst a→x x
  f ((□ b) i i₁) = sq b i i₁
  -- f (trunc x y p q r s i i₁ i₂) =
  --   isGroupoidX _ _ _ _
  --     (λ i j → f (r i j)) (λ i j → f (s i j))
  --     i i₁ i₂ 
   

  f∙ : _≡/₃∙_ →∙ X
  f∙ = f , snd a→x

 record Elim≡/₃ (X : typ _≡/₃∙_ → Type ℓ'') : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
  field
   -- isGroupoidX : ∀ x → isGroupoid ⟨ ∙X x ⟩ 
   a→x : ∀ a  → X [ a ]≡/₃
   sq : (b : B) → SquareP (λ i j → X ((□ b) i j))
                (λ i → a→x (rels b ₀₋ i))
                (λ i → a→x (rels b ₁₋ i))
                (λ i → a→x (rels b ₋₀ i))
                (λ i → a→x (rels b ₋₁ i))
   
  f : ∀ a → (X a)
  f [ x ]≡/₃ = a→x x
  f ((□ b) i j) = sq b i j 
  -- f (trunc x y p q r s i i₁ i₂) =
  --    isOfHLevel→isOfHLevelDep 3 isGroupoidX
  --      (f x) (f y) (cong f p) (cong f q)
  --        (λ i j → f (r i j)) (λ i j → f (s i j))
  --       (trunc x y p q r s)
  --       i i₁ i₂ 

  -- f∙ : ⟨ Πᵖ∙ _≡/₃∙_ ∙X ⟩
  -- fst f∙ = f
  -- snd f∙ = snd a→x


IsoTrunc⊥ : Iso ⟨ A∙ ⟩ (A∙ ≡/₃ ⊥.rec)
Iso.fun IsoTrunc⊥ = [_]≡/₃ 
Iso.inv IsoTrunc⊥ [ x ]≡/₃ = x
Iso.rightInv IsoTrunc⊥ [ x ]≡/₃ = refl 
Iso.leftInv IsoTrunc⊥ _ = refl
-- GT.elim (λ _ → {!!}) λ _ → refl

module X (A : Type ℓ) {B : Type ℓ'} (rels : B → □Ω (Bouquet∙ A)) where
 ⟨_∣_⟩ : Type (ℓ-max ℓ ℓ') 
 ⟨_∣_⟩ = Bouquet∙ A ≡/₃ rels

 ⟨_∣_⟩∙ : Pointed (ℓ-max ℓ ℓ') 
 ⟨_∣_⟩∙ = Bouquet∙ A ≡/₃∙ rels


 record RecSet {ℓ''} (∙X : Pointed ℓ'') 
                   : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
  field
   loopX : A → ⟨ Ω ∙X ⟩

  bq : Bouquet∙ A →∙ ∙X
  fst bq base = _
  fst bq (loop x i) = loopX x i
  snd bq = refl

  record RecGpd : Type (ℓ-max ℓ' ℓ'') where
   field
    sqX : (b : B) → _
    
   R : Rec≡/₃ (Bouquet∙ A) rels ∙X
   Rec≡/₃.a→x R = bq
   Rec≡/₃.sq R = sqX

   f = Rec≡/₃.f R

 record ElimSet {ℓ''} (∙X : typ ⟨_∣_⟩∙ → Pointed ℓ') 
                   : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
  field
   loopX : ∀ a → PathP (λ i → typ (∙X [ loop a i ]≡/₃))
                  (pt (∙X [ base ]≡/₃))
                  (pt (∙X [ base ]≡/₃))


  bq : ⟨ Πᵖ∙ (Bouquet∙ A) (∙X ∘ [_]≡/₃) ⟩
  fst bq base = _
  fst bq (loop x i) = loopX x i
  snd bq = refl

  record ElimGpd : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
   field
    sqX : (b : B) → SquareP _ _ _ _ _
    
   R : Elim≡/₃ (Bouquet∙ A) rels (fst ∘ ∙X)
   Elim≡/₃.a→x R = fst bq
   Elim≡/₃.sq R = sqX

   f = Elim≡/₃.f R

   -- f∙ = Elim≡/₃.f∙ R


   -- sqX : ∀ b → SquareP (λ i j → typ (∙X ((□ b) i j)))
   --               {!!}
   --               {!!}
   --               {!λ i → fst f [ rels b ₋₀ i ]!}
   --               {!!}

-- Goal: typ (∙X ((□ b) i i₁))
-- ———— Boundary (wanted) —————————————————————————————————————
-- i₁ = i0 ⊢ fst f [ rels b ₋₀ i ]
-- i₁ = i1 ⊢ fst f [ rels b ₋₁ i ]
-- i = i0 ⊢ fst f [ rels b ₀₋ i₁ ]
-- i = i1 ⊢ fst f [ rels b ₁₋ i₁ ]


--   bq : Bouquet∙ A →∙ ∙X
--   fst bq base = _
--   fst bq (loop x i) = loopX x i
--   snd bq = refl


module _ (IxG : Type ℓ) where

 data Fc : Type ℓ where
  fc : 𝟚 → IxG → Fc
  cns : Fc

 Fc∙ : Pointed ℓ
 Fc∙ = Fc , cns

 mkFc≡ : (IxG → ⟨ Ω A∙ ⟩) → Fc∙ →∙ Ω A∙ 
 fst (mkFc≡ f) (fc b x) = 𝟚.if b then f x else sym (f x)
 fst (mkFc≡ _) cns = _
 snd (mkFc≡ _) = refl


module Pres (A : Type ℓ) {B : Type ℓ} (rels : B → 𝟜 → Fc A) where
 open X A (λ b → fst (mkFc≡ _ loop) ∘ rels b) public

 module F𝔹 = X A ⊥.rec

 F = freeGroupGroup A

 fc→fg : Fc A → FreeGroup A
 fc→fg (fc x a) = 𝟚.if x then η a else inv (η a)
 fc→fg cns = ε

 rels' : B → 𝟜 → FreeGroup A
 rels' = λ b → fc→fg ∘' rels b 
 


 relatorsF : B → FreeGroup A 
 relatorsF b =
  let r = rels' b
  in inv (r ₁₋ · r ₋₀) · (r ₋₁ · r ₀₋)

 FN = freeGroupGroup (FreeGroup A × B)

 FN→F : GroupHom FN F
 FN→F = fst A→Group≃GroupHom λ (g , b) → inv g · (relatorsF b · g) 

 h→ : ⟨ F ⟩ → GroupHom FN FN
 h→ a = fst A→Group≃GroupHom λ (g , b) → η (g · a , b) 



 _∼ₚ_ :  (FreeGroup A) → (FreeGroup A) → Type ℓ 
 g ∼ₚ g' = Σ B λ b →
                   let r = rels' b
                   in (r ₋₁ · (r ₀₋ · g)) ≡ (r ₁₋ · (r ₋₀ · g'))


 open GroupTheory F

 module FGS = GroupStr (snd F)
 

 lemGen : ∀ a y → FN→F .fst (fst (h→ (inv a)) y) ≡
      (a · (fst FN→F y · inv a) )
 lemGen a = ElimProp.f w
  where
  w : ElimProp
        (λ z → FN→F .fst (fst (h→ (inv a)) z) ≡ (a · (fst FN→F z · inv a)))
  ElimProp.isPropB w _ = trunc _ _
  ElimProp.εB w = sym (invr a) ∙ cong (a ·_) (idl (inv a))
  ElimProp.ηB w (g , b) =
   cong₂ _·_ (invDistr g (inv a) ∙ cong (_· (inv g)) (invInv a))
     (FGS.·Assoc _ _ _)
    ∙∙ sym (FGS.·Assoc _ _ _)
    ∙∙ cong (a ·_) (FGS.·Assoc _ _ _)
  ElimProp.invB w x p = cong inv p ∙
     invDistr _ _ ∙
       cong (_· inv a) (invDistr _ _) ∙
        λ i → ·assoc (invInv a i) (IsGroupHom.presinv (snd FN→F) x i) (inv a)
             (~ i)
         
  ElimProp.·B w x y X Y =
     cong₂ _·_ X Y ∙∙
        (λ i → ·assoc a (fst FN→F x · inv a) (·assoc a (fst FN→F y) (inv a) i) (~ i))
          ∙∙ cong (a ·_) (·assoc _ _ _ ∙ cong (_· inv a)
            (·assoc _ _ _ ∙∙ cong (_· _)
               (sym (·assoc _ _ _) ∙∙ cong ((fst FN→F x) ·_) (invl a)
                ∙∙ sym (idr _))
                ∙∙ sym (IsGroupHom.pres· (snd FN→F) _ _)))


 isNormalN : isNormal (imSubgroup FN→F)
 isNormalN x h = PT.map
   λ (g , p) → _ , lemGen x g ∙ λ i → (x · (p i · inv x))
   
 P : Group ℓ 
 P = F / (imSubgroup FN→F , isNormalN)


--  𝔹P = {!!}

--  -- ℙ = ? / ?

-- --  3→2T : ∥ Bouquet A ∥₃ → hSet ℓ
-- --  3→2T = GT.rec isGroupoidHSet λ x → ∥ base ≡ x ∥₂ , squash₂ 
-- --    -- λ {base → ∥ Path (Bouquet A) base base ∥₂ , squash₂
-- --    --   ; (loop a i) → ∥ Path (Bouquet A) base (loop a i) ∥₂ , {!!} }

-- --  3→2 : ∀ x → (Path (∥ Bouquet A ∥₃) ∣ base ∣₃ x) → 
-- --              ⟨ 3→2T x ⟩
-- --  3→2 x = J (λ x → λ v → ⟨ 3→2T x ⟩) ∣ refl ∣₂

-- --  -- 2→3 : ∀ x → Path (Bouquet A) base x 
-- --  --           → (Path (∥ Bouquet A ∥₃) ∣ base ∣₃ ∣ x ∣₃)
-- --  -- 2→3 x = cong ∣_∣₃
-- --  --  -- J (λ x _ → (Path (∥ Bouquet A ∥₃) ∣ base ∣₃ ∣ x ∣₃)) refl


-- --  2→3' : ∀ x → ⟨ 3→2T x ⟩ 
-- --            → (Path (∥ Bouquet A ∥₃) ∣ base ∣₃ x) 
-- --  2→3' = GT.elim (λ _ → isGroupoidΠ λ _ → isSet→isGroupoid (squash₃ _ _))
-- --             λ x → ST.rec (squash₃ _ _) (cong ∣_∣₃)
 

-- --  sec2' : ∀ x → (p : Path (Bouquet A) base x) →
-- --                (3→2 (∣ x ∣₃) (2→3' ∣ x ∣₃ ∣ p ∣₂)) ≡ ∣ p ∣₂ 
-- --  sec2' x = J (λ x (p : Path (Bouquet A) base x) →
-- --                (3→2 (∣ x ∣₃) (2→3' ∣ x ∣₃ ∣ p ∣₂)) ≡ ∣ p ∣₂)
-- --                   (cong ∣_∣₂ (transportRefl _))
-- --                   -- (cong ∣_∣₂ (transportRefl _ ∙∙ transportRefl _ ∙∙ transportRefl _)
-- --                   -- )

-- --  sec3 : ∀ x → (p : Path (∥ Bouquet A ∥₃) ∣ base ∣₃ x)  →
-- --                (2→3' (x) ((3→2 x p))) ≡ p 
-- --  sec3 x = J (λ x → λ (p : Path (∥ Bouquet A ∥₃) ∣ base ∣₃ x)  →
-- --                (2→3' (x) ((3→2 x p))) ≡ p)
-- --                  λ j i → ∣ doubleCompPath-filler refl (λ _ → base) refl (~ j) i ∣₃
                   

-- --  Iso₂₃ : Iso (Path (∥ Bouquet A ∥₃) ∣ base ∣₃ ∣ base ∣₃)
-- --              ∥ Path (Bouquet A) base base ∥₂
-- --  Iso.fun Iso₂₃ = 3→2 ∣ base ∣₃
-- --  Iso.inv Iso₂₃ = (2→3' ∣ base ∣₃)
-- --  Iso.rightInv Iso₂₃ = ST.elim (λ _ → isProp→isSet (squash₂ _ _)) (sec2' base)  
-- --  Iso.leftInv Iso₂₃ = sec3 ∣ base ∣₃


-- --  -- FF : F𝔹.⟨_∣_⟩∙ →∙ (Bouquet∙ A)
-- --  -- fst FF [ x ] = x
-- --  -- snd FF = {!!}
-- --  -- -- fst FF = F𝔹.RecSet.RecGpd.f  w
-- --  -- --  where
-- --  -- --  w' : F𝔹.RecSet (∥ Bouquet A ∥₃ , ∣ base ∣₃)
-- --  -- --  X.RecSet.loopX w' a = cong ∣_∣₃ (loop a)
  
-- --  --  w : F𝔹.RecSet.RecGpd w'
-- --  --  X.RecSet.RecGpd.isGroupoidX w _ _ = squash₃ _ _
-- --  -- snd FF = refl

-- --  -- GHF𝔹 : GroupIso {!F𝔹!} F
-- --  -- fst GHF𝔹 = {!compIso TruncatedFamiliesIso {A = ?} base !}
-- --  -- snd GHF𝔹 = {!!}
 

-- -- --  P𝔹 = πGr 1 (Bouquet∙ A ) / (imSubgroup {!!} , {!!})

-- -- --   -- X = ⟨ ∙X ⟩
-- -- -- --   field
-- -- -- --    isGroupoidX : isGroupoid X
-- -- -- --    bq : Bouquet A → X

-- -- -- --    □X : ∀ b → Square
-- -- -- --                (cong bq (Sq'.fc₀₋ (rels b)))
-- -- -- --                (cong bq (Sq'.fc₁₋ (rels b)))
-- -- -- --                (cong bq (Sq'.fc₋₀ (rels b)))
-- -- -- --                (cong bq (Sq'.fc₋₁ (rels b)))

-- -- -- --   f : ⟨_∣_⟩ → X
-- -- -- --   f [ x ] = bq x
-- -- -- --   f ((□ b) i i₁) =  □X b i i₁
-- -- -- --   f (trunc x₁ x₂ x₃ y x₄ y₁ i i₁ x₅) = {!!}




-- -- -- --  Sq = Sq' Fc

-- -- -- --  Sq→SqΩ : ∀ {ℓa} {A : Type ℓa} {base : A} → (loop : IxG → base ≡ base)
-- -- -- --               → Sq → SqΩ (A , base)
-- -- -- --  Sq'.fc₀₋ (Sq→SqΩ l x) = mkFc≡ l (Sq'.fc₀₋ x)
-- -- -- --  Sq'.fc₁₋ (Sq→SqΩ l x) = mkFc≡ l (Sq'.fc₁₋ x)
-- -- -- --  Sq'.fc₋₀ (Sq→SqΩ l x) = mkFc≡ l (Sq'.fc₋₀ x)
-- -- -- --  Sq'.fc₋₁ (Sq→SqΩ l x) = mkFc≡ l (Sq'.fc₋₁ x)

-- -- -- -- -- module _ (A : Type ℓ) {B : Type ℓ'} (rels : B → Sq A) where
-- -- -- -- --  open X A (Sq→SqΩ _ loop ∘ rels)
   
  
-- -- -- -- -- private
-- -- -- -- --   variable
-- -- -- -- --     A : Type ℓ
-- -- -- -- --     B : Type ℓ'
-- -- -- -- --     rels : B → SqΩ (Bouquet∙ A)


-- -- -- -- -- -- zz : X.⟨ A ∣ rels ⟩ → A
-- -- -- -- -- -- zz [ base ] = {!!}
-- -- -- -- -- -- zz [ loop x i ] = {!!}
-- -- -- -- -- -- zz ((□ b) i i₁) = {!!}
-- -- -- -- -- -- zz (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) = {!!}
