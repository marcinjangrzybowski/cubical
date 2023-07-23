{-# OPTIONS --safe --lossy-unification #-} 
module Cubical.Algebra.Group.Presentation.Base where

open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything
-- open import Cubical.Foundations.Function
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Bool using (false ; true) renaming (Bool to 𝟚) 

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties

open import Cubical.HITs.EilenbergMacLane1

open import Cubical.HITs.GroupoidTruncation as GT


private
  variable
    ℓ ℓ' : Level

p∙'[p⁻∙'q]≡q : ∀ {ℓ} {A : Type ℓ} → {x y : A} → (p q : x ≡ y) → 
              p ∙' (sym p ∙' q) ≡ q
p∙'[p⁻∙'q]≡q p q i j =
   hcomp ( λ k → 
          λ { (j = i0) → p (~ i ∧ ~ k)
            ; (j = i1) → q i1
            ; (i = i1) → q j
            }) (compPath'-filler (sym p) q (~ i) j)


module hlp∙' {ℓ} {A : Type ℓ} {a b c d e f : A}  {p : a ≡ c} {q : b ≡ d} {r : a ≡ b} {s : c ≡ d} {u : e ≡ f} {v : d ≡ e} {w : d ≡ f} where

 sq : (S : Square r s p q) → (Q : Square v w refl u)
         → Square (p ∙' (s ∙' v))
                  (r ∙' (q ∙' w))
                 (λ _ → a)
                 u
 sq S Q  i = (λ j' → S (j' ∧ ~ i) (j' ∧ i))
           ∙' ((λ j' → S (j' ∨ ~ i) (j' ∨ i)) ∙' Q i)



module Pres (IxG : Type ℓ) where

 data Fc : Type ℓ where
  fc : 𝟚 → IxG → Fc
  cns : Fc

 mkFc≡ : ∀ {ℓa} {A : Type ℓa} {base : A} (loop : IxG → base ≡ base)
        → Fc → base ≡ base 
 mkFc≡ loop (fc x x₁) = 𝟚.if x then loop x₁ else sym (loop x₁)
 mkFc≡ loop cns = refl


 module FcCons {ℓ*} {XS : Type ℓ*} (cons : (𝟚 × IxG) → XS → XS) where
  fcCons : Fc → XS → XS
  fcCons (fc x x₂) x₁ = cons (x , x₂) x₁
  fcCons cns x₁ = x₁

 record Sq : Type ℓ where
  constructor fc
  field
   fc₀₋ fc₁₋ fc₋₀ fc₋₁ : Fc

  module Faces' {A : Type (ℓ-max ℓ ℓ')} {base : A} (loop : IxG → base ≡ base) where
   pa : Fc → base ≡ base
   pa (fc x x₁) = 𝟚.if x then loop x₁ else sym (loop x₁)
   pa cns = refl

   pa₀₋ pa₁₋ pa₋₀ pa₋₁ : base ≡ base
   pa₀₋ = pa fc₀₋
   pa₁₋ = pa fc₁₋
   pa₋₀ = pa fc₋₀
   pa₋₁ = pa fc₋₁

   SqTy : Type (ℓ-max ℓ ℓ')
   SqTy = Square pa₀₋ pa₁₋ pa₋₀ pa₋₁
   
  module Faces {ℓa} {A : Type ℓa} {base : A} (pa : Fc → base ≡ base) where


   pa₀₋ pa₁₋ pa₋₀ pa₋₁ : base ≡ base
   pa₀₋ = pa fc₀₋
   pa₁₋ = pa fc₁₋
   pa₋₀ = pa fc₋₀
   pa₋₁ = pa fc₋₁

   SqTy : Type (ℓa)
   SqTy = Square pa₀₋ pa₁₋ pa₋₀ pa₋₁


 open Sq


   
 module _ {IxR : Type ℓ'} (rels : IxR → Sq) where

  

  data T : Type (ℓ-max ℓ ℓ') 

  infixr 5 _∷_ _fc∷_ 

  _fc∷_ : Fc → T → T
 
  data T where
   ε : T
   _∷_ : (𝟚 × IxG) → T → T
   inv∷ : ∀ b ixG xs → ((𝟚.not b) , ixG) ∷ (b , ixG) ∷ xs ≡ xs
   rel : (ixR : IxR) → ∀ x →
          fc₋₁ (rels ixR) fc∷ fc₀₋ (rels ixR) fc∷ x ≡
          fc₁₋ (rels ixR) fc∷ fc₋₀ (rels ixR) fc∷ x
   trunc : isSet T   

  _fc∷_ = FcCons.fcCons _∷_


  ∷iso : IxG → Iso T T
  Iso.fun (∷iso x) = (true , x) ∷_
  Iso.inv (∷iso x) = (false , x) ∷_
  Iso.rightInv (∷iso x) = inv∷ false x 
  Iso.leftInv (∷iso x) = inv∷ true x
  
  η : IxG → T
  η = (_∷ ε) ∘ (true ,_)

  η⁻ : IxG → T
  η⁻ = (_∷ ε) ∘ (false ,_)


  ∷≃ : IxG → T ≃ T
  ∷≃ = isoToEquiv ∘ ∷iso

  ∷fcIso' : Fc → Iso T T
  ∷fcIso' (fc x x₁) = 𝟚.if x then ∷iso x₁ else (invIso (∷iso x₁)) 
  ∷fcIso' cns = idIso

  notFC : Fc → Fc
  notFC (fc x x₁) = fc (𝟚.not x) x₁
  notFC cns = cns

  invFC∷ : ∀ fc xs → (notFC fc fc∷ fc fc∷ xs) ≡ xs 
  invFC∷ (fc x x₁) xs = inv∷ _ _ _
  invFC∷ cns xs = refl

  invFC∷' : ∀ fc xs → (fc fc∷ (notFC fc) fc∷ xs) ≡ xs 
  invFC∷' (fc false x₁) xs = inv∷ _ _ _
  invFC∷' (fc true x₁) xs = inv∷ _ _ _
  invFC∷' cns xs = refl
  
  relInv : (ixR : IxR) → 
         notFC (fc₀₋ (rels ixR)) fc∷ notFC (fc₋₁ (rels ixR)) fc∷ ε ≡
         notFC (fc₋₀ (rels ixR)) fc∷ notFC (fc₁₋ (rels ixR)) fc∷ ε
  relInv ixR = 
      sym (invFC∷ (fc₋₀ (rels ixR)) _) ∙∙
       cong (notFC (fc₋₀ (rels ixR)) fc∷_)
         (sym (invFC∷ (fc₁₋ (rels ixR)) _))
       ∙∙ cong ((notFC (fc₋₀ (rels ixR)) fc∷_) ∘'
          (notFC (fc₁₋ (rels ixR)) fc∷_)) (sym (rel ixR
            (notFC (fc₀₋ (rels ixR)) fc∷ (notFC (fc₋₁ (rels ixR)) fc∷ ε)))) ∙∙
       cong ((notFC (fc₋₀ (rels ixR)) fc∷_)
            ∘' ((notFC (fc₁₋ (rels ixR)) fc∷_)
              ∘' ((fc₋₁ (rels ixR)) fc∷_)))
              (invFC∷' (fc₀₋ (rels ixR)) _) ∙∙
         cong ((notFC (fc₋₀ (rels ixR)) fc∷_)
            ∘' ((notFC (fc₁₋ (rels ixR)) fc∷_)))
             (invFC∷' (fc₋₁ (rels ixR)) _)
  
  ∷fcIso : Fc → Iso T T
  Iso.fun (∷fcIso x) = x fc∷_
  Iso.inv (∷fcIso x) = notFC x fc∷_
  Iso.rightInv (∷fcIso (fc false x₁)) = inv∷ _ _
  Iso.rightInv (∷fcIso (fc true x₁)) = inv∷ _ _
  Iso.rightInv (∷fcIso cns) _ = refl
  Iso.leftInv (∷fcIso (fc x x₁)) = inv∷ _ _
  Iso.leftInv (∷fcIso cns) _ = refl

 
  ∷fc≃ : Fc → T ≃ T
  ∷fc≃ = isoToEquiv ∘ ∷fcIso

  ∷inv≃P : ∀ b → (ixG : IxG) →
            PathP (λ i → T → ua (∷fc≃ (fc (𝟚.not b) ixG)) i)
               (λ x → (b , ixG) ∷ x)
               (λ x → x) 
  ∷inv≃P b ixG = funExt (ua-gluePath _ ∘ (inv∷ b ixG))
 

  rel≃ : ∀ ixR → ∷fc≃ (fc₀₋ (rels ixR)) ∙ₑ ∷fc≃ (fc₋₁ (rels ixR))
               ≡ ∷fc≃ (fc₋₀ (rels ixR)) ∙ₑ ∷fc≃ (fc₁₋ (rels ixR))
  rel≃ ixR  = equivEq (funExt (rel ixR))

  

  module _ (f : Sq) where
   module F≃ = Faces f (ua ∘ ∷fc≃)

  module _ (f : Sq) where
   module F≡ = Faces f (mkFc≡ (ua ∘ ∷≃))

  mkFc≡uaLem : ∀ fc →  mkFc≡ (ua ∘ ∷≃) fc ≡ ua (∷fc≃ fc) 
  mkFc≡uaLem (fc false x₁) = sym (uaInvEquiv _) ∙ cong ua (equivEq refl)
  mkFc≡uaLem (fc true x₁) = cong ua (equivEq refl)
  mkFc≡uaLem cns =  sym uaIdEquiv ∙ cong ua (equivEq refl)

  rel≡Sq : ∀ ixR → F≡.SqTy (rels ixR)
  rel≡Sq ixR = flipSquare (compPath→Square
    (
       ((cong₂ _∙_
         (mkFc≡uaLem (fc₀₋ (rels ixR)))
         (mkFc≡uaLem (fc₋₁ (rels ixR)))
         ∙ sym (uaCompEquiv _ _))
        ◁ cong ua (  (rel≃ ixR)) ▷
         (uaCompEquiv _ _ ∙
           cong₂ _∙_
            (sym (mkFc≡uaLem (fc₋₀ (rels ixR))))
            (sym (mkFc≡uaLem (fc₁₋ (rels ixR))))
                     ))))
    
    -- {!!} ◁  {!!} ▷ {!!} 
    -- Glue (ua (rel≃ ixR i) j)
    -- -- Glue T {i ∨ ~ i ∨ j ∨ ~ j}
    --   λ { (i = i0) → pa₀₋ j , {!!}
    --      ; (i = i1) → pa₁₋ j , {!!}
    --      ; (j = i0) → pa₋₀ i , {!!}
    --      ; (j = i1) → pa₋₁ i , {!!}
    --      }
    where
    open F≡ (rels ixR)

    
  module FcConsDep {ℓ*} {XS : T → Type ℓ*}
            (cons : ∀ {xs} → (x : (𝟚 × IxG)) → XS xs → XS (x ∷ xs)) where
   fcConsDep : ∀ {xs} → (x : Fc) → XS xs → XS (x fc∷ xs)
   fcConsDep (fc x x₂) x₁ = cons (x , x₂) x₁
   fcConsDep cns x₁ = x₁


  record RecT {ℓ*} (A : Type ℓ*) : Type (ℓ-max ℓ* (ℓ-max ℓ ℓ')) where
   no-eta-equality
   field
    isSetA : isSet A
    εA : A
    ∷A : 𝟚 → IxG → A → A
    inv∷A : ∀ b ixG a → ∷A (𝟚.not b) ixG (∷A b ixG a) ≡ a

   infixr 5 _fc∷A_ 

   _fc∷A_ : Fc → A → A
   _fc∷A_ = FcCons.fcCons (uncurry ∷A) 
   field
    relA : ∀ ixR a →
          fc₋₁ (rels ixR) fc∷A fc₀₋ (rels ixR) fc∷A a ≡
          fc₁₋ (rels ixR) fc∷A fc₋₀ (rels ixR) fc∷A a

   

   f : T → A
   f ε = εA
   f (x ∷ x₁) = ∷A (fst x) (snd x) (f x₁)
   f (inv∷ b ixG x i) = inv∷A b ixG (f x) i
   f (rel ixR x i) with fc₋₀ (rels ixR) | fc₋₁ (rels ixR) | fc₀₋ (rels ixR) | fc₁₋ (rels ixR) | relA ixR (f x)
   ... | fc x₁ x₂ | fc x₃ x₄ | fc x₅ x₆ | fc x₇ x₈ | q = q i
   ... | fc x₁ x₂ | fc x₃ x₄ | fc x₅ x₆ | cns | q = q i
   ... | fc x₁ x₂ | fc x₃ x₄ | cns | fc x₅ x₆ | q = q i
   ... | fc x₁ x₂ | fc x₃ x₄ | cns | cns | q = q i
   ... | fc x₁ x₂ | cns | fc x₃ x₄ | fc x₅ x₆ | q = q i 
   ... | fc x₁ x₂ | cns | fc x₃ x₄ | cns | q = q i
   ... | fc x₁ x₂ | cns | cns | fc x₃ x₄ | q = q i
   ... | fc x₁ x₂ | cns | cns | cns | q = q i
   ... | cns | fc x₁ x₂ | fc x₃ x₄ | fc x₅ x₆ | q = q i
   ... | cns | fc x₁ x₂ | fc x₃ x₄ | cns | q = q i
   ... | cns | fc x₁ x₂ | cns | fc x₃ x₄ | q = q i
   ... | cns | fc x₁ x₂ | cns | cns | q = q i
   ... | cns | cns | fc x₁ x₂ | fc x₃ x₄ | q = q i
   ... | cns | cns | fc x₁ x₂ | cns | q = q i
   ... | cns | cns | cns | fc x₁ x₂ | q = q i
   ... | cns | cns | cns | cns | q = q i
   f (trunc _ _ p q i i₁) =
     isSetA _ _ (cong f p) (cong f q) i i₁


  record ElimT {ℓ*} (A : T → Type ℓ*) : Type (ℓ-max ℓ* (ℓ-max ℓ ℓ')) where
   no-eta-equality
   field
    isSetA : ∀ x → isSet (A x)
    εA : A ε
    ∷A : ∀ {xs} → ∀ b x → A xs → A ((b , x) ∷ xs)

    inv∷A : ∀ b ixG → ∀ {xs} a →
      PathP (λ i → A (inv∷ b ixG xs i))
       (∷A (𝟚.not b) ixG (∷A b ixG a)) a

   infixr 5 _fc∷A_ 

   _fc∷A_ = FcConsDep.fcConsDep (λ {xs} → uncurry (∷A {xs}))
   
   field
    relA : ∀ ixR {xs} (a : A xs) →
          PathP (λ i → A (rel ixR xs i ))
          (fc₋₁ (rels ixR) fc∷A fc₀₋ (rels ixR) fc∷A a)
          (fc₁₋ (rels ixR) fc∷A fc₋₀ (rels ixR) fc∷A a)

   

   f : ∀ x → A x
   f ε = εA
   f (x ∷ x₁) = ∷A (fst x) (snd x) (f x₁)
   f (inv∷ b ixG x i) = inv∷A b ixG (f x) i
   f (rel ixR x i) with fc₋₀ (rels ixR) | fc₋₁ (rels ixR) | fc₀₋ (rels ixR) | fc₁₋ (rels ixR) | relA ixR (f x)
   ... | fc x₁ x₂ | fc x₃ x₄ | fc x₅ x₆ | fc x₇ x₈ | q = q i
   ... | fc x₁ x₂ | fc x₃ x₄ | fc x₅ x₆ | cns | q = q i
   ... | fc x₁ x₂ | fc x₃ x₄ | cns | fc x₅ x₆ | q = q i
   ... | fc x₁ x₂ | fc x₃ x₄ | cns | cns | q = q i
   ... | fc x₁ x₂ | cns | fc x₃ x₄ | fc x₅ x₆ | q = q i 
   ... | fc x₁ x₂ | cns | fc x₃ x₄ | cns | q = q i
   ... | fc x₁ x₂ | cns | cns | fc x₃ x₄ | q = q i
   ... | fc x₁ x₂ | cns | cns | cns | q = q i
   ... | cns | fc x₁ x₂ | fc x₃ x₄ | fc x₅ x₆ | q = q i
   ... | cns | fc x₁ x₂ | fc x₃ x₄ | cns | q = q i
   ... | cns | fc x₁ x₂ | cns | fc x₃ x₄ | q = q i
   ... | cns | fc x₁ x₂ | cns | cns | q = q i
   ... | cns | cns | fc x₁ x₂ | fc x₃ x₄ | q = q i
   ... | cns | cns | fc x₁ x₂ | cns | q = q i
   ... | cns | cns | cns | fc x₁ x₂ | q = q i
   ... | cns | cns | cns | cns | q = q i
   f (trunc _ _ p q i i₁) =
     isSet→SquareP (λ i j → isSetA (trunc _ _ p q i j))
       (cong f p) (cong f q) refl refl  i i₁ 
     


  record ElimPropT {ℓ*} (A : T → Type ℓ*) : Type (ℓ-max ℓ* (ℓ-max ℓ ℓ')) where
   no-eta-equality
   field
    isPropA : ∀ x → isProp (A x)
    εA : A ε
    ∷A : ∀ {xs} → ∀ b x → A xs → A ((b , x) ∷ xs)

   r : ElimT A
   ElimT.isSetA r = isProp→isSet ∘ isPropA
   ElimT.εA r = εA
   ElimT.∷A r = ∷A
   ElimT.inv∷A r _ _ _ =
    isProp→PathP (λ i → isPropA _)
     _ _
   ElimT.relA r _ _ =
    isProp→PathP (λ i → isPropA _)
     _ _

   f : ∀ x → A x
   f = ElimT.f r
   
  ·R : T → RecT T
  RecT.isSetA (·R y) = trunc
  RecT.εA (·R y) = y
  RecT.∷A (·R y) = curry _∷_
  RecT.inv∷A (·R y) = inv∷
  RecT.relA (·R y) = rel
  
  _·_ : T → T → T
  x · y = RecT.f (·R y) x


  ·IdR : ∀ x → x · ε ≡ x
  ·IdR = ElimPropT.f w
   where
   w : ElimPropT (λ z → (z · ε) ≡ z)
   ElimPropT.isPropA w _ = trunc _ _
   ElimPropT.εA w = refl
   ElimPropT.∷A w b x = cong ((b , x) ∷_)
   
  ·IdL : ∀ x → ε · x ≡ x
  ·IdL _ = refl

  ·assoc : (x y z : T) → (x · (y · z)) ≡ ((x · y) · z)
  ·assoc = ElimPropT.f w
   where
   w : ElimPropT _
   ElimPropT.isPropA w _ = isPropΠ2 λ _ _ → trunc _ _
   ElimPropT.εA w _ _ = refl
   ElimPropT.∷A w _ _ q = ElimPropT.f w'
    where
    w' : ElimPropT _
    ElimPropT.isPropA w' _ = isPropΠ λ _ → trunc _ _
    ElimPropT.εA w' _ = cong ((_ , _) ∷_) (q _ _)
    ElimPropT.∷A w' b x x₁ x₂ =
      cong ((_ , _) ∷_) (q _ _)

  fc→T : Fc → T
  fc→T (fc x x₁) = (x , x₁) ∷ ε
  fc→T cns = ε
  
  _fc∷'_ : Fc → T → T
  x fc∷' x₁ = fc→T x · x₁

  fc∷≡fc∷' : ∀ fc → Path (T → T) (λ x → fc fc∷ x) (λ x → fc fc∷' x)  
  fc∷≡fc∷' (fc x₁ x₂) i x = (x₁ , x₂) ∷ x
  fc∷≡fc∷' cns i x = x

  invRLem : FcCons.fcCons (uncurry (λ b x xs → xs · ((𝟚.not b , x) ∷ ε)))
             ≡ λ fc t → t · fc→T (notFC fc)
  invRLem i (fc x x₂) x₁ = RecT.f (·R ((𝟚.not x , x₂) ∷ ε)) x₁
  invRLem i cns x₁ = ·IdR x₁ (~ i)

  invRLem' : ∀ x x' → (fc→T x · fc→T x')
      ≡ x fc∷ x' fc∷ ε
  invRLem' (fc x x₁) (fc x₂ x₃) = refl
  invRLem' (fc x x₁) cns = refl
  invRLem' cns (fc x x₁) = refl
  invRLem' cns cns = refl


  

  rel' : ∀ ixR → (fc→T (notFC (fc₀₋ (rels ixR))) ·
        fc→T (notFC (fc₋₁ (rels ixR))))
       ≡ (fc→T (notFC (fc₋₀ (rels ixR))) · fc→T (notFC (fc₁₋ (rels ixR))))
  rel' ixR =
     invRLem' (notFC (fc₀₋ (rels ixR))) (notFC (fc₋₁ (rels ixR)))
      ∙∙  (relInv ixR) ∙∙
      sym (invRLem' ((notFC (fc₋₀ (rels ixR))))
           ((notFC (fc₁₋ (rels ixR)))))


  invR : RecT T
  RecT.isSetA invR = trunc
  RecT.εA invR = ε
  RecT.∷A invR b x xs = xs · ((𝟚.not b , x) ∷ ε)
  RecT.inv∷A invR b ixG a  =
     (λ i → (·assoc a ((𝟚.not b , ixG) ∷ ε)
              ((𝟚.notnot b i , ixG) ∷ ε)) (~ i)) ∙∙
      cong (a ·_)
        (inv∷ b ixG ε)
        ∙∙ ·IdR _
  RecT.relA invR ixR a =
    (λ i →
      invRLem i (fc₋₁ (rels ixR)) (invRLem i (fc₀₋ (rels ixR)) a)) 
     ∙∙ sym (·assoc a _ _) ∙∙
       cong (a ·_) (rel' ixR)
       ∙∙ (·assoc a _ _) ∙∙
    (λ i →
      invRLem (~ i) (fc₁₋ (rels ixR)) (invRLem (~ i) (fc₋₀ (rels ixR)) a))

  inv : T → T
  inv = RecT.f invR

  ·InvR : ∀ x → x · inv x ≡ ε
  ·InvR = ElimPropT.f w
   where
   w : ElimPropT _
   ElimPropT.isPropA w _ = trunc _ _
   ElimPropT.εA w = refl
   ElimPropT.∷A w {xs} b x  p = ·assoc ((b , x) ∷ xs ) (inv xs) _ ∙∙
    (λ i → ((𝟚.notnot b (~ i) , x) ∷ p i) · ((𝟚.not b , x) ∷ ε)) ∙∙
     (inv∷ (𝟚.not b) x ε) 

  ·InvL : ∀ x → inv x · x ≡ ε
  ·InvL = ElimPropT.f w
   where
   w : ElimPropT _
   ElimPropT.isPropA w _ = trunc _ _
   ElimPropT.εA w = refl
   ElimPropT.∷A w {xs} b x p =
      sym (·assoc (inv xs) _ _) ∙∙
       cong ((inv xs) ·_) (inv∷ b x _) ∙∙ p 


  GroupT : Group (ℓ-max ℓ ℓ')
  GroupT = makeGroup
    ε
    _·_
    inv trunc
     ·assoc ·IdR ·IdL ·InvR ·InvL



  data 𝔹T : Type (ℓ-max ℓ ℓ')

  base' : 𝔹T
  loop' : IxG → base' ≡ base'


  module _ (f : Sq) where
   open Faces f (mkFc≡ loop') public
   
  data 𝔹T where
   base : 𝔹T
   loop : IxG → base ≡ base
   relSq : (r : IxR) →
     Square {A = 𝔹T}
       (pa₀₋ (rels r))
       (pa₁₋ (rels r))
       (pa₋₀ (rels r))
       (pa₋₁ (rels r))
   trunc : isGroupoid 𝔹T

  base' = base
  loop' = loop


  record Rec𝔹T' {ℓa} (A : Type ℓa) : Type (ℓ-max ℓa (ℓ-max ℓ ℓ')) where
   no-eta-equality
   field
    baseA : A
    loopA : IxG → baseA ≡ baseA

   fcA : Fc → baseA ≡ baseA
   fcA = mkFc≡ {A = A} {base = baseA} loopA 
   field
    relSqA : (r : IxR) →
      Square {A = A}
        (Faces.pa₀₋ (rels r) {base = baseA} fcA)
        (Faces.pa₁₋ (rels r) {base = baseA} fcA)
        (Faces.pa₋₀ (rels r) {base = baseA} fcA)
        (Faces.pa₋₁ (rels r) {base = baseA} fcA)


  record Rec𝔹T {ℓa} (A : Type ℓa) : Type (ℓ-max ℓa (ℓ-max ℓ ℓ')) where
   no-eta-equality
   field
    isGroupoidA : isGroupoid A 
    baseA : A
    loopA : IxG → baseA ≡ baseA

   fcA : Fc → baseA ≡ baseA
   fcA = mkFc≡ {A = A} {base = baseA} loopA 
   field
    relSqA : (r : IxR) →
      Square {A = A}
        (Faces.pa₀₋ (rels r) {base = baseA} fcA)
        (Faces.pa₁₋ (rels r) {base = baseA} fcA)
        (Faces.pa₋₀ (rels r) {base = baseA} fcA)
        (Faces.pa₋₁ (rels r) {base = baseA} fcA)
                
   f : 𝔹T → A
   f base = baseA
   f (loop x i) = loopA x i
   -- f (loopSym b ixG i i₁) = loopSymA b ixG i i₁
   f (relSq ixR i j) with fc₋₀ (rels ixR) | fc₋₁ (rels ixR) | fc₀₋ (rels ixR) | fc₁₋ (rels ixR) | relSqA ixR
   ... | fc false x₁ | fc false x₃ | fc false x₅ | fc false x₇ | q = q i j
   ... | fc false x₁ | fc false x₃ | fc false x₅ | fc true x₇ | q = q i j
   ... | fc false x₁ | fc false x₃ | fc true x₅ | fc false x₇ | q = q i j
   ... | fc false x₁ | fc false x₃ | fc true x₅ | fc true x₇ | q = q i j
   ... | fc false x₁ | fc true x₃ | fc false x₅ | fc false x₇ | q = q i j
   ... | fc false x₁ | fc true x₃ | fc false x₅ | fc true x₇ | q = q i j
   ... | fc false x₁ | fc true x₃ | fc true x₅ | fc false x₇ | q = q i j
   ... | fc false x₁ | fc true x₃ | fc true x₅ | fc true x₇ | q = q i j
   ... | fc true x₁ | fc false x₃ | fc false x₅ | fc false x₇ | q = q i j
   ... | fc true x₁ | fc false x₃ | fc false x₅ | fc true x₇ | q = q i j
   ... | fc true x₁ | fc false x₃ | fc true x₅ | fc false x₇ | q = q i j
   ... | fc true x₁ | fc false x₃ | fc true x₅ | fc true x₇ | q = q i j
   ... | fc true x₁ | fc true x₃ | fc false x₅ | fc false x₇ | q = q i j
   ... | fc true x₁ | fc true x₃ | fc false x₅ | fc true x₇ | q = q i j
   ... | fc true x₁ | fc true x₃ | fc true x₅ | fc false x₇ | q = q i j
   ... | fc true x₁ | fc true x₃ | fc true x₅ | fc true x₇ | q = q i j
   ... | fc false x₁ | fc false x₃ | fc false x₅ | cns | q = q i j
   ... | fc false x₁ | fc false x₃ | fc true x₅ | cns | q = q i j
   ... | fc false x₁ | fc true x₃ | fc false x₅ | cns | q = q i j
   ... | fc false x₁ | fc true x₃ | fc true x₅ | cns | q = q i j
   ... | fc true x₁ | fc false x₃ | fc false x₅ | cns | q = q i j
   ... | fc true x₁ | fc false x₃ | fc true x₅ | cns | q = q i j
   ... | fc true x₁ | fc true x₃ | fc false x₅ | cns | q = q i j
   ... | fc true x₁ | fc true x₃ | fc true x₅ | cns | q = q i j
   ... | fc false x₁ | fc false x₃ | cns | fc false x₅ | q = q i j
   ... | fc false x₁ | fc false x₃ | cns | fc true x₅ | q = q i j
   ... | fc false x₁ | fc true x₃ | cns | fc false x₅ | q = q i j
   ... | fc false x₁ | fc true x₃ | cns | fc true x₅ | q = q i j
   ... | fc true x₁ | fc false x₃ | cns | fc false x₅ | q = q i j
   ... | fc true x₁ | fc false x₃ | cns | fc true x₅ | q = q i j
   ... | fc true x₁ | fc true x₃ | cns | fc false x₅ | q = q i j
   ... | fc true x₁ | fc true x₃ | cns | fc true x₅ | q = q i j
   ... | fc false x₁ | fc false x₃ | cns | cns | q = q i j
   ... | fc false x₁ | fc true x₃ | cns | cns | q = q i j
   ... | fc true x₁ | fc false x₃ | cns | cns | q = q i j
   ... | fc true x₁ | fc true x₃ | cns | cns | q = q i j
   ... | fc false x₁ | cns | fc false x₃ | fc false x₅ | q = q i j
   ... | fc false x₁ | cns | fc false x₃ | fc true x₅ | q = q i j
   ... | fc false x₁ | cns | fc true x₃ | fc false x₅ | q = q i j
   ... | fc false x₁ | cns | fc true x₃ | fc true x₅ | q = q i j
   ... | fc true x₁ | cns | fc false x₃ | fc false x₅ | q = q i j
   ... | fc true x₁ | cns | fc false x₃ | fc true x₅ | q = q i j
   ... | fc true x₁ | cns | fc true x₃ | fc false x₅ | q = q i j
   ... | fc true x₁ | cns | fc true x₃ | fc true x₅ | q = q i j
   ... | fc false x₁ | cns | fc false x₃ | cns | q = q i j
   ... | fc false x₁ | cns | fc true x₃ | cns | q = q i j
   ... | fc true x₁ | cns | fc false x₃ | cns | q = q i j
   ... | fc true x₁ | cns | fc true x₃ | cns | q = q i j
   ... | fc false x₁ | cns | cns | fc false x₃ | q = q i j
   ... | fc false x₁ | cns | cns | fc true x₃ | q = q i j
   ... | fc true x₁ | cns | cns | fc false x₃ | q = q i j
   ... | fc true x₁ | cns | cns | fc true x₃ | q = q i j
   ... | fc false x₁ | cns | cns | cns | q = q i j
   ... | fc true x₁ | cns | cns | cns | q = q i j
   ... | cns | fc false x₁ | fc false x₃ | fc false x₅ | q = q i j
   ... | cns | fc false x₁ | fc false x₃ | fc true x₅ | q = q i j
   ... | cns | fc false x₁ | fc true x₃ | fc false x₅ | q = q i j
   ... | cns | fc false x₁ | fc true x₃ | fc true x₅ | q = q i j
   ... | cns | fc true x₁ | fc false x₃ | fc false x₅ | q = q i j
   ... | cns | fc true x₁ | fc false x₃ | fc true x₅ | q = q i j
   ... | cns | fc true x₁ | fc true x₃ | fc false x₅ | q = q i j
   ... | cns | fc true x₁ | fc true x₃ | fc true x₅ | q = q i j
   ... | cns | fc false x₁ | fc false x₃ | cns | q = q i j
   ... | cns | fc false x₁ | fc true x₃ | cns | q = q i j
   ... | cns | fc true x₁ | fc false x₃ | cns | q = q i j
   ... | cns | fc true x₁ | fc true x₃ | cns | q = q i j
   ... | cns | fc false x₁ | cns | fc false x₃ | q = q i j
   ... | cns | fc false x₁ | cns | fc true x₃ | q = q i j
   ... | cns | fc true x₁ | cns | fc false x₃ | q = q i j
   ... | cns | fc true x₁ | cns | fc true x₃ | q = q i j
   ... | cns | fc false x₁ | cns | cns | q = q i j
   ... | cns | fc true x₁ | cns | cns | q = q i j
   ... | cns | cns | fc false x₁ | fc false x₃ | q = q i j
   ... | cns | cns | fc false x₁ | fc true x₃ | q = q i j
   ... | cns | cns | fc true x₁ | fc false x₃ | q = q i j
   ... | cns | cns | fc true x₁ | fc true x₃ | q = q i j
   ... | cns | cns | fc false x₁ | cns | q = q i j
   ... | cns | cns | fc true x₁ | cns | q = q i j
   ... | cns | cns | cns | fc false x₁ | q = q i j
   ... | cns | cns | cns | fc true x₁ | q = q i j
   ... | cns | cns | cns | cns | q = q i j

   f (trunc x y p q r s i i₁ i₂) =
     isGroupoidA _ _ _ _
       (λ i j → f (r i j)) (λ i j → f (s i j))
       i i₁ i₂ 

  record Elim𝔹T {ℓa} (A : 𝔹T → Type ℓa) : Type (ℓ-max ℓa (ℓ-max ℓ ℓ')) where
   no-eta-equality
   field
    isGroupoidA : ∀ x → isGroupoid (A x) 
    baseA : A base
    loopA : ∀ ixG → PathP (λ i → A (loop ixG i) ) baseA baseA

   fcA : ∀ fc → PathP (λ i → A (mkFc≡ loop fc i))
               baseA baseA
   fcA = λ { (fc false x₁) →  symP (loopA x₁)
            ; (fc true x₁) → (loopA x₁)
            ; cns → refl }
   
   field
    relSqA : (r : IxR) →
      SquareP (λ i j → A (relSq r i j))
        (fcA (fc₀₋ (rels r)))
        (fcA (fc₁₋ (rels r)))
        (fcA (fc₋₀ (rels r)))
        (fcA (fc₋₁ (rels r)))
        
   f : ∀ x → A x
   f base = baseA
   f (loop x i) = loopA x i
   -- f (loopSym b ixG i i₁) = loopSymA b ixG i i₁
   f (relSq ixR i j) with fc₋₀ (rels ixR) | fc₋₁ (rels ixR) | fc₀₋ (rels ixR) | fc₁₋ (rels ixR) |  relSqA ixR
   ... | fc false x₁ | fc false x₃ | fc false x₅ | fc false x₇ | q = q i j
   ... | fc false x₁ | fc false x₃ | fc false x₅ | fc true x₇ | q = q i j
   ... | fc false x₁ | fc false x₃ | fc true x₅ | fc false x₇ | q = q i j
   ... | fc false x₁ | fc false x₃ | fc true x₅ | fc true x₇ | q = q i j
   ... | fc false x₁ | fc true x₃ | fc false x₅ | fc false x₇ | q = q i j
   ... | fc false x₁ | fc true x₃ | fc false x₅ | fc true x₇ | q = q i j
   ... | fc false x₁ | fc true x₃ | fc true x₅ | fc false x₇ | q = q i j
   ... | fc false x₁ | fc true x₃ | fc true x₅ | fc true x₇ | q = q i j
   ... | fc true x₁ | fc false x₃ | fc false x₅ | fc false x₇ | q = q i j
   ... | fc true x₁ | fc false x₃ | fc false x₅ | fc true x₇ | q = q i j
   ... | fc true x₁ | fc false x₃ | fc true x₅ | fc false x₇ | q = q i j
   ... | fc true x₁ | fc false x₃ | fc true x₅ | fc true x₇ | q = q i j
   ... | fc true x₁ | fc true x₃ | fc false x₅ | fc false x₇ | q = q i j
   ... | fc true x₁ | fc true x₃ | fc false x₅ | fc true x₇ | q = q i j
   ... | fc true x₁ | fc true x₃ | fc true x₅ | fc false x₇ | q = q i j
   ... | fc true x₁ | fc true x₃ | fc true x₅ | fc true x₇ | q = q i j
   ... | fc false x₁ | fc false x₃ | fc false x₅ | cns | q = q i j
   ... | fc false x₁ | fc false x₃ | fc true x₅ | cns | q = q i j
   ... | fc false x₁ | fc true x₃ | fc false x₅ | cns | q = q i j
   ... | fc false x₁ | fc true x₃ | fc true x₅ | cns | q = q i j
   ... | fc true x₁ | fc false x₃ | fc false x₅ | cns | q = q i j
   ... | fc true x₁ | fc false x₃ | fc true x₅ | cns | q = q i j
   ... | fc true x₁ | fc true x₃ | fc false x₅ | cns | q = q i j
   ... | fc true x₁ | fc true x₃ | fc true x₅ | cns | q = q i j
   ... | fc false x₁ | fc false x₃ | cns | fc false x₅ | q = q i j
   ... | fc false x₁ | fc false x₃ | cns | fc true x₅ | q = q i j
   ... | fc false x₁ | fc true x₃ | cns | fc false x₅ | q = q i j
   ... | fc false x₁ | fc true x₃ | cns | fc true x₅ | q = q i j
   ... | fc true x₁ | fc false x₃ | cns | fc false x₅ | q = q i j
   ... | fc true x₁ | fc false x₃ | cns | fc true x₅ | q = q i j
   ... | fc true x₁ | fc true x₃ | cns | fc false x₅ | q = q i j
   ... | fc true x₁ | fc true x₃ | cns | fc true x₅ | q = q i j
   ... | fc false x₁ | fc false x₃ | cns | cns | q = q i j
   ... | fc false x₁ | fc true x₃ | cns | cns | q = q i j
   ... | fc true x₁ | fc false x₃ | cns | cns | q = q i j
   ... | fc true x₁ | fc true x₃ | cns | cns | q = q i j
   ... | fc false x₁ | cns | fc false x₃ | fc false x₅ | q = q i j
   ... | fc false x₁ | cns | fc false x₃ | fc true x₅ | q = q i j
   ... | fc false x₁ | cns | fc true x₃ | fc false x₅ | q = q i j
   ... | fc false x₁ | cns | fc true x₃ | fc true x₅ | q = q i j
   ... | fc true x₁ | cns | fc false x₃ | fc false x₅ | q = q i j
   ... | fc true x₁ | cns | fc false x₃ | fc true x₅ | q = q i j
   ... | fc true x₁ | cns | fc true x₃ | fc false x₅ | q = q i j
   ... | fc true x₁ | cns | fc true x₃ | fc true x₅ | q = q i j
   ... | fc false x₁ | cns | fc false x₃ | cns | q = q i j
   ... | fc false x₁ | cns | fc true x₃ | cns | q = q i j
   ... | fc true x₁ | cns | fc false x₃ | cns | q = q i j
   ... | fc true x₁ | cns | fc true x₃ | cns | q = q i j
   ... | fc false x₁ | cns | cns | fc false x₃ | q = q i j
   ... | fc false x₁ | cns | cns | fc true x₃ | q = q i j
   ... | fc true x₁ | cns | cns | fc false x₃ | q = q i j
   ... | fc true x₁ | cns | cns | fc true x₃ | q = q i j
   ... | fc false x₁ | cns | cns | cns | q = q i j
   ... | fc true x₁ | cns | cns | cns | q = q i j
   ... | cns | fc false x₁ | fc false x₃ | fc false x₅ | q = q i j
   ... | cns | fc false x₁ | fc false x₃ | fc true x₅ | q = q i j
   ... | cns | fc false x₁ | fc true x₃ | fc false x₅ | q = q i j
   ... | cns | fc false x₁ | fc true x₃ | fc true x₅ | q = q i j
   ... | cns | fc true x₁ | fc false x₃ | fc false x₅ | q = q i j
   ... | cns | fc true x₁ | fc false x₃ | fc true x₅ | q = q i j
   ... | cns | fc true x₁ | fc true x₃ | fc false x₅ | q = q i j
   ... | cns | fc true x₁ | fc true x₃ | fc true x₅ | q = q i j
   ... | cns | fc false x₁ | fc false x₃ | cns | q = q i j
   ... | cns | fc false x₁ | fc true x₃ | cns | q = q i j
   ... | cns | fc true x₁ | fc false x₃ | cns | q = q i j
   ... | cns | fc true x₁ | fc true x₃ | cns | q = q i j
   ... | cns | fc false x₁ | cns | fc false x₃ | q = q i j
   ... | cns | fc false x₁ | cns | fc true x₃ | q = q i j
   ... | cns | fc true x₁ | cns | fc false x₃ | q = q i j
   ... | cns | fc true x₁ | cns | fc true x₃ | q = q i j
   ... | cns | fc false x₁ | cns | cns | q = q i j
   ... | cns | fc true x₁ | cns | cns | q = q i j
   ... | cns | cns | fc false x₁ | fc false x₃ | q = q i j
   ... | cns | cns | fc false x₁ | fc true x₃ | q = q i j
   ... | cns | cns | fc true x₁ | fc false x₃ | q = q i j
   ... | cns | cns | fc true x₁ | fc true x₃ | q = q i j
   ... | cns | cns | fc false x₁ | cns | q = q i j
   ... | cns | cns | fc true x₁ | cns | q = q i j
   ... | cns | cns | cns | fc false x₁ | q = q i j
   ... | cns | cns | cns | fc true x₁ | q = q i j
   ... | cns | cns | cns | cns | q = q i j

   f (trunc x y p q r s i i₁ i₂) =
     isOfHLevel→isOfHLevelDep 3 isGroupoidA
       (f x) (f y) (cong f p) (cong f q)
         (λ i j → f (r i j)) (λ i j → f (s i j))
        (trunc x y p q r s)
        i i₁ i₂ 


  record ElimSet𝔹T {ℓa} (A : 𝔹T → Type ℓa) : Type (ℓ-max ℓa (ℓ-max ℓ ℓ')) where
   no-eta-equality
   field
    isSetA : ∀ x → isSet (A x) 
    baseA : A base
    loopA : ∀ ixG → PathP (λ i → A (loop ixG i) ) baseA baseA

   r : Elim𝔹T (λ z → A z)
   Elim𝔹T.isGroupoidA r = isSet→isGroupoid ∘ isSetA
   Elim𝔹T.baseA r = baseA
   Elim𝔹T.loopA r = loopA
   Elim𝔹T.relSqA r ixR =
     isSet→SquareP (λ _ _ → isSetA _)
       _ _ _ _
               
   f : ∀ x → A x
   f = Elim𝔹T.f r


  record ElimProp𝔹T {ℓa} (A : 𝔹T → Type ℓa) : Type (ℓ-max ℓa (ℓ-max ℓ ℓ')) where
   no-eta-equality
   field
    isPropA : ∀ x → isProp (A x) 
    baseA : A base

   r : ElimSet𝔹T (λ z → A z)
   ElimSet𝔹T.isSetA r = isProp→isSet ∘ isPropA
   ElimSet𝔹T.baseA r = baseA
   ElimSet𝔹T.loopA r _ = isProp→PathP (λ _ → isPropA _) _ _
               
   f : ∀ x → A x
   f = ElimSet𝔹T.f r



  module 𝔹T→hSet {ℓ*} (f₃ : 𝔹T → ∥ Type ℓ*  ∥₃) where

   isSet₃ : ∥ Type ℓ*  ∥₃ → hProp ℓ*
   isSet₃ = GT.rec (isSet→isGroupoid isSetHProp)
      (λ x → isSet x , isPropIsSet) 
      
   module _ (isSet₃-base : ⟨ isSet₃ (f₃ base) ⟩) where
   
    p'r : ElimProp𝔹T λ bt → ⟨ isSet₃ (f₃ bt) ⟩  
    ElimProp𝔹T.isPropA p'r = snd ∘ isSet₃ ∘ f₃
    ElimProp𝔹T.baseA p'r = isSet₃-base

    p' : ∀ bt → ⟨ isSet₃ (f₃ bt) ⟩  
    p' = ElimProp𝔹T.f p'r

    hSet₃ : (x : ∥ Type ℓ* ∥₃) → (fst (isSet₃ x)) → hSet ℓ*
    fst (hSet₃ ∣ x ∣₃ x₁) = x
    snd (hSet₃ ∣ x ∣₃ x₁) = x₁
    hSet₃ (squash₃ x y p q r s i i₁ i₂) =
      isOfHLevel→isOfHLevelDep 3 {∥ Type ℓ* ∥₃}
        {λ Ty₃ → ⟨ isSet₃ Ty₃ ⟩ → hSet ℓ*}
         (λ _ → isGroupoidΠ λ _ → isGroupoidHSet)
        _ _
         _ _ (λ i₃ i₄ → hSet₃ (r i₃ i₄)) (λ i₃ i₄ → hSet₃ (s i₃ i₄))
         (squash₃ x y p q r s) i i₁ i₂

    f' : 𝔹T → hSet ℓ*
    f' bt =  hSet₃ (f₃ bt) (p' bt)


  CodeHR : Rec𝔹T (∥ Type (ℓ-max ℓ ℓ') ∥₃)
  Rec𝔹T.isGroupoidA CodeHR = squash₃
  Rec𝔹T.baseA CodeHR = ∣ T ∣₃
  Rec𝔹T.loopA CodeHR = (cong ∣_∣₃) ∘ ua ∘ ∷≃  
  Rec𝔹T.relSqA CodeHR ixR i j with fc₋₀ (rels ixR) | fc₋₁ (rels ixR) | fc₀₋ (rels ixR) | fc₁₋ (rels ixR) | (rel≡Sq ixR)
  ... | fc false x₁ | fc false x₃ | fc false x₅ | fc false x₇ | q = ∣ q i j ∣₃
  ... | fc false x₁ | fc false x₃ | fc false x₅ | fc true x₇ | q = ∣ q i j ∣₃
  ... | fc false x₁ | fc false x₃ | fc true x₅ | fc false x₇ | q = ∣ q i j ∣₃
  ... | fc false x₁ | fc false x₃ | fc true x₅ | fc true x₇ | q = ∣ q i j ∣₃
  ... | fc false x₁ | fc true x₃ | fc false x₅ | fc false x₇ | q = ∣ q i j ∣₃
  ... | fc false x₁ | fc true x₃ | fc false x₅ | fc true x₇ | q = ∣ q i j ∣₃
  ... | fc false x₁ | fc true x₃ | fc true x₅ | fc false x₇ | q = ∣ q i j ∣₃
  ... | fc false x₁ | fc true x₃ | fc true x₅ | fc true x₇ | q = ∣ q i j ∣₃
  ... | fc true x₁ | fc false x₃ | fc false x₅ | fc false x₇ | q = ∣ q i j ∣₃
  ... | fc true x₁ | fc false x₃ | fc false x₅ | fc true x₇ | q = ∣ q i j ∣₃
  ... | fc true x₁ | fc false x₃ | fc true x₅ | fc false x₇ | q = ∣ q i j ∣₃
  ... | fc true x₁ | fc false x₃ | fc true x₅ | fc true x₇ | q = ∣ q i j ∣₃
  ... | fc true x₁ | fc true x₃ | fc false x₅ | fc false x₇ | q = ∣ q i j ∣₃
  ... | fc true x₁ | fc true x₃ | fc false x₅ | fc true x₇ | q = ∣ q i j ∣₃
  ... | fc true x₁ | fc true x₃ | fc true x₅ | fc false x₇ | q = ∣ q i j ∣₃
  ... | fc true x₁ | fc true x₃ | fc true x₅ | fc true x₇ | q = ∣ q i j ∣₃
  ... | fc false x₁ | fc false x₃ | fc false x₅ | cns | q = ∣ q i j ∣₃
  ... | fc false x₁ | fc false x₃ | fc true x₅ | cns | q = ∣ q i j ∣₃
  ... | fc false x₁ | fc true x₃ | fc false x₅ | cns | q = ∣ q i j ∣₃
  ... | fc false x₁ | fc true x₃ | fc true x₅ | cns | q = ∣ q i j ∣₃
  ... | fc true x₁ | fc false x₃ | fc false x₅ | cns | q = ∣ q i j ∣₃
  ... | fc true x₁ | fc false x₃ | fc true x₅ | cns | q = ∣ q i j ∣₃
  ... | fc true x₁ | fc true x₃ | fc false x₅ | cns | q = ∣ q i j ∣₃
  ... | fc true x₁ | fc true x₃ | fc true x₅ | cns | q = ∣ q i j ∣₃
  ... | fc false x₁ | fc false x₃ | cns | fc false x₅ | q = ∣ q i j ∣₃
  ... | fc false x₁ | fc false x₃ | cns | fc true x₅ | q = ∣ q i j ∣₃
  ... | fc false x₁ | fc true x₃ | cns | fc false x₅ | q = ∣ q i j ∣₃
  ... | fc false x₁ | fc true x₃ | cns | fc true x₅ | q = ∣ q i j ∣₃
  ... | fc true x₁ | fc false x₃ | cns | fc false x₅ | q = ∣ q i j ∣₃
  ... | fc true x₁ | fc false x₃ | cns | fc true x₅ | q = ∣ q i j ∣₃
  ... | fc true x₁ | fc true x₃ | cns | fc false x₅ | q = ∣ q i j ∣₃
  ... | fc true x₁ | fc true x₃ | cns | fc true x₅ | q = ∣ q i j ∣₃
  ... | fc false x₁ | fc false x₃ | cns | cns | q = ∣ q i j ∣₃
  ... | fc false x₁ | fc true x₃ | cns | cns | q = ∣ q i j ∣₃
  ... | fc true x₁ | fc false x₃ | cns | cns | q = ∣ q i j ∣₃
  ... | fc true x₁ | fc true x₃ | cns | cns | q = ∣ q i j ∣₃
  ... | fc false x₁ | cns | fc false x₃ | fc false x₅ | q = ∣ q i j ∣₃
  ... | fc false x₁ | cns | fc false x₃ | fc true x₅ | q = ∣ q i j ∣₃
  ... | fc false x₁ | cns | fc true x₃ | fc false x₅ | q = ∣ q i j ∣₃
  ... | fc false x₁ | cns | fc true x₃ | fc true x₅ | q = ∣ q i j ∣₃
  ... | fc true x₁ | cns | fc false x₃ | fc false x₅ | q = ∣ q i j ∣₃
  ... | fc true x₁ | cns | fc false x₃ | fc true x₅ | q = ∣ q i j ∣₃
  ... | fc true x₁ | cns | fc true x₃ | fc false x₅ | q = ∣ q i j ∣₃
  ... | fc true x₁ | cns | fc true x₃ | fc true x₅ | q = ∣ q i j ∣₃
  ... | fc false x₁ | cns | fc false x₃ | cns | q = ∣ q i j ∣₃
  ... | fc false x₁ | cns | fc true x₃ | cns | q = ∣ q i j ∣₃
  ... | fc true x₁ | cns | fc false x₃ | cns | q = ∣ q i j ∣₃
  ... | fc true x₁ | cns | fc true x₃ | cns | q = ∣ q i j ∣₃
  ... | fc false x₁ | cns | cns | fc false x₃ | q = ∣ q i j ∣₃
  ... | fc false x₁ | cns | cns | fc true x₃ | q = ∣ q i j ∣₃
  ... | fc true x₁ | cns | cns | fc false x₃ | q = ∣ q i j ∣₃
  ... | fc true x₁ | cns | cns | fc true x₃ | q = ∣ q i j ∣₃
  ... | fc false x₁ | cns | cns | cns | q = ∣ q i j ∣₃
  ... | fc true x₁ | cns | cns | cns | q = ∣ q i j ∣₃
  ... | cns | fc false x₁ | fc false x₃ | fc false x₅ | q = ∣ q i j ∣₃
  ... | cns | fc false x₁ | fc false x₃ | fc true x₅ | q = ∣ q i j ∣₃
  ... | cns | fc false x₁ | fc true x₃ | fc false x₅ | q = ∣ q i j ∣₃
  ... | cns | fc false x₁ | fc true x₃ | fc true x₅ | q = ∣ q i j ∣₃
  ... | cns | fc true x₁ | fc false x₃ | fc false x₅ | q = ∣ q i j ∣₃
  ... | cns | fc true x₁ | fc false x₃ | fc true x₅ | q = ∣ q i j ∣₃
  ... | cns | fc true x₁ | fc true x₃ | fc false x₅ | q = ∣ q i j ∣₃
  ... | cns | fc true x₁ | fc true x₃ | fc true x₅ | q = ∣ q i j ∣₃
  ... | cns | fc false x₁ | fc false x₃ | cns | q = ∣ q i j ∣₃
  ... | cns | fc false x₁ | fc true x₃ | cns | q = ∣ q i j ∣₃
  ... | cns | fc true x₁ | fc false x₃ | cns | q = ∣ q i j ∣₃
  ... | cns | fc true x₁ | fc true x₃ | cns | q = ∣ q i j ∣₃
  ... | cns | fc false x₁ | cns | fc false x₃ | q = ∣ q i j ∣₃
  ... | cns | fc false x₁ | cns | fc true x₃ | q = ∣ q i j ∣₃
  ... | cns | fc true x₁ | cns | fc false x₃ | q = ∣ q i j ∣₃
  ... | cns | fc true x₁ | cns | fc true x₃ | q = ∣ q i j ∣₃
  ... | cns | fc false x₁ | cns | cns | q = ∣ q i j ∣₃
  ... | cns | fc true x₁ | cns | cns | q = ∣ q i j ∣₃
  ... | cns | cns | fc false x₁ | fc false x₃ | q = ∣ q i j ∣₃
  ... | cns | cns | fc false x₁ | fc true x₃ | q = ∣ q i j ∣₃
  ... | cns | cns | fc true x₁ | fc false x₃ | q = ∣ q i j ∣₃
  ... | cns | cns | fc true x₁ | fc true x₃ | q = ∣ q i j ∣₃
  ... | cns | cns | fc false x₁ | cns | q = ∣ q i j ∣₃
  ... | cns | cns | fc true x₁ | cns | q = ∣ q i j ∣₃
  ... | cns | cns | cns | fc false x₁ | q = ∣ q i j ∣₃
  ... | cns | cns | cns | fc true x₁ | q = ∣ q i j ∣₃
  ... | cns | cns | cns | cns | q = ∣ q i j ∣₃
  


  CodeH₃ : 𝔹T → ∥ Type (ℓ-max ℓ ℓ') ∥₃
  
  CodeH₃ = Rec𝔹T.f CodeHR

  CodeH : 𝔹T → hSet (ℓ-max ℓ ℓ')
  CodeH = 𝔹T→hSet.f' CodeH₃ trunc

  Code : 𝔹T → Type (ℓ-max ℓ ℓ')
  Code = fst ∘ CodeH

  encode : ∀ x → base ≡ x → Code x
  encode _ p = subst Code p ε


  dbr∷ : 𝟚 → IxG → base ≡ base → base ≡ base
  dbr∷ x y = mkFc≡ (sym ∘ loop) (fc x y) ∙'_

  drb-lem : ∀ x x' → (a : (base ≡ base)) →
      FcCons.fcCons (uncurry dbr∷)
      x
      (FcCons.fcCons (uncurry dbr∷) x'
       a) ≡
        (sym (mkFc≡ loop x) ∙' (sym (mkFc≡ loop x') ∙' a ))
  drb-lem (fc false x₁) (fc false x₃) a = refl
  drb-lem (fc false x₁) (fc true x₃) a = refl
  drb-lem (fc true x₁) (fc false x₃) a = refl
  drb-lem (fc true x₁) (fc true x₃) a = refl
  drb-lem (fc false x₁) cns a =
    cong ((loop x₁) ∙'_) (doubleCompPath-filler _ _ _)
  drb-lem (fc true x₁) cns a =
   cong (sym (loop x₁) ∙'_) (doubleCompPath-filler refl a refl)
  drb-lem cns (fc false x₁) a = doubleCompPath-filler _ _ _
  drb-lem cns (fc true x₁) a = doubleCompPath-filler _ _ _
  drb-lem cns cns a =
   doubleCompPath-filler _ _ _ ∙ doubleCompPath-filler _ _ _

  decode-baseR : RecT (base ≡ base)
  RecT.isSetA decode-baseR = trunc _ _
  RecT.εA decode-baseR = refl
  RecT.∷A decode-baseR = dbr∷
  RecT.inv∷A decode-baseR false _ _ =
    p∙'[p⁻∙'q]≡q _ _ 
  RecT.inv∷A decode-baseR true _ _ =
    p∙'[p⁻∙'q]≡q _ _
  RecT.relA decode-baseR ixR a =
     drb-lem (fc₋₁ (rels ixR)) (fc₀₋ (rels ixR)) a
      ∙∙ (hlp∙'.sq ((λ i i₁ → relSq ixR (~ i) (~ i₁))) λ _ → a) ∙∙
      sym (drb-lem (fc₁₋ (rels ixR)) (fc₋₀ (rels ixR)) a)
    
  decodeLoop : ∀ ixG →
      PathP (λ i → (Code (loop ixG i)) → base ≡ loop ixG i)
        (symP ∘ (RecT.f decode-baseR))
        (symP ∘ (RecT.f decode-baseR))
  decodeLoop ixG = ua→ (ElimPropT.f w)
   where
   w : ElimPropT λ z →
            PathP (λ v → base ≡ loop ixG v) ((symP ∘ RecT.f decode-baseR) z)
            ((symP ∘ RecT.f decode-baseR) (isoToEquiv (∷iso ixG) .fst z))
   ElimPropT.isPropA w _ =
     isOfHLevelPathP' 1
      (trunc _ _)
       _ _
   ElimPropT.εA w = doubleCompPath-filler _ _ _       
   ElimPropT.∷A w b x x₁ = doubleCompPath-filler _ _ _
     

  decode : (x : 𝔹T) → Code x → base ≡ x
  decode = ElimSet𝔹T.f w
   where
   w : ElimSet𝔹T (λ z → Code z → base ≡ z)
   ElimSet𝔹T.isSetA w _ = isSet→ (trunc _ _)
   ElimSet𝔹T.baseA w = sym ∘ RecT.f decode-baseR
   ElimSet𝔹T.loopA w = decodeLoop 


  decode∷true : ∀ x xs → decode base ((true , x) ∷ xs)
                     ≡ (decode base xs) ∙ (loop x)
  decode∷true x xs = refl
  

  decodeEncode : section (encode base) (decode base)
  decodeEncode = ElimPropT.f w
   where
   w : ElimPropT (λ z → encode base (decode base z) ≡ z)
   ElimPropT.isPropA w _ = trunc _ _
   ElimPropT.εA w = refl
   ElimPropT.∷A w {xs} false x p =
         substComposite Code (decode base xs) (sym (loop x)) ε
        ∙ cong ((false , x) ∷_) (transportRefl _ ∙ p)


   ElimPropT.∷A w {xs} true x p =
     substComposite Code (decode base xs) (loop x) ε
        ∙ transportRefl _ ∙ cong ((true , x) ∷_) (p)
    
  encodeDecode : ∀ {x} → retract (encode x) (decode x)
  encodeDecode = J (λ (y : 𝔹T) (p : base ≡ y) →
       decode y (encode y p) ≡ p) refl

  encodeDecodeIso : Iso T (base ≡ base)
  Iso.fun encodeDecodeIso = decode base
  Iso.inv encodeDecodeIso = encode base
  Iso.rightInv encodeDecodeIso = encodeDecode {base}
  Iso.leftInv encodeDecodeIso = decodeEncode
