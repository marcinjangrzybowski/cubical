{-# OPTIONS --safe  --experimental-lossy-unification #-} 
module Cubical.Data.FinData.GTrun3 where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws as GL

open import Cubical.Foundations.Path

open import Cubical.HITs.Pushout
open import Cubical.HITs.Sn
open import Cubical.HITs.SetQuotients renaming ([_] to [_]/ ; rec to rec/ ; elimProp to elimProp/ ; elim to elim/)

open import Cubical.HITs.GroupoidQuotients renaming ([_] to [_]//)

import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SetTruncation renaming (map to map₂)



open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.List
import Cubical.Data.Vec as V
open import Cubical.Data.FinData


open import Cubical.Foundations.Function
open import Cubical.Functions.Logic


open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.SymmetricGroup
open import Cubical.Algebra.Group.Generators

-- open import Cubical.HITs.FreeGroup
-- open import Cubical.HITs.FreeGroup.IPresentation

open import Cubical.HITs.EilenbergMacLane1 renaming (elim to elimEM)

open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Univalence

open import Cubical.Relation.Binary

open import Cubical.Functions.FunExtEquiv



module EMΣ {ℓ} {A : Type ℓ}  (isSetA : isSet A)
             -- {ℓ} {G : Group ℓ'} (m' : GroupHom G (Symmetric-Group _ isSetA))             
              where

 -- m = fst m'
 -- mGH = snd m'

 -- open GroupStr (snd G)
 -- module M = IsGroupHom mGH


 sg = Symmetric-Group _ isSetA

 𝔹G = EM₁ sg 

  -- EM₁HFam : EMG → hSet ℓ
  -- EM₁HFam = EMrec.f w
  --   where
  --    w : EMrec lg isGroupoidHSet
  --    EMrec.b w = A , isSetA
  --    EMrec.bloop w = TypeOfHLevel≡ 2
  --    EMrec.bComp w f g =
  --      ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
  --        (compPath-filler _ _)

 -- isGroupoidSinglA : isGroupoid (Σ[ T ∈ Type ℓ ] T ≃ A)
 -- isGroupoidSinglA = 

 rA* : EMrec sg isGroupoidHSet 
 EMrec.b rA* = A , isSetA
 EMrec.bloop rA* g = Σ≡Prop (λ _ → isPropIsSet) (ua g)
 EMrec.bComp rA* g h =
   ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
    (ua-CompFill∙ₑ _ _)

 A*h : EM₁ sg → hSet ℓ  
 A*h = EMrec.f rA*

 A* = fst ∘ A*h

module _ {ℓ ℓb} {A : Type ℓ} (isSetA : isSet A)
                {B : Type ℓb} (isGroupoidB : isGroupoid B)
             where
             
 open EMΣ isSetA

 -- rB* : EMelim sg λ g → Σ[ T ∈ Type (ℓ-max ℓ ℓb) ] T ≃ (fst (A* g) → B) 
 -- EMelim.isGrpB rB* g =
 --   isOfHLevelPlus 3 (EquivContr (fst (A* g) → B))
 -- EMelim.b rB* = _ , idEquiv _
 -- EMelim.bPathP rB* g =
 --   ΣPathP (ua (preCompEquiv g) ,
 --     ΣPathPProp (λ _ → isPropIsEquiv _)
 --       {!!})
 -- EMelim.bSqP rB* = {!!}

 B* : EM₁ sg → Type (ℓ-max ℓ ℓb)
 B* em = A* em → B

 record _↔ₛ_ (x y : A → B) : Type (ℓ-max ℓ ℓb) where
   constructor ↔s
   field
     F≃ : (A ≃ A)
     l≡ : x ∘ invEq F≃  ≡ y  

 isTrans↔ₛ : BinaryRelation.isTrans _↔ₛ_
 isTrans↔ₛ a b c (↔s e p) (↔s f q) = 
   ↔s (e ∙ₑ f) (cong (_∘ (invEq f)) p ∙ q)
   

 A→// : Type (ℓ-max ℓ ℓb)
 A→// = (A → B) // isTrans↔ₛ

-- -- -- [_] : (a : A) → A // Rt
-- -- --   eq// : {a b : A} → (r : R a b) → [ a ] ≡ [ b ]
-- -- --   comp// : {a b c : A} → (r : R a b) → (s : R b c)
-- -- --           → PathP (λ j → [ a ] ≡ eq// s j) (eq// r) (eq// (Rt a b c r s))
-- -- --   squash// : ∀ (x y : A // Rt) (p q : x ≡ y) (r s : p ≡ q) → r ≡ s


 data ZZ : Type (ℓ-max ℓ ℓb) where
  [_]z : (A → B) → ZZ
  loopz : (e : A ≃ A) → ∀ {x y} → (x ∘ invEq e ≡ y) →
    [ x ]z ≡ [ y ]z
  compz : (e f : A ≃ A) → ∀ {x y z} → ∀ p q → Square 
                             (loopz e {x} {y} p)
                             (loopz (e ∙ₑ f) (cong (_∘ invEq f) p ∙ q))
                             refl
                             (loopz f {y} {z} q)
  squashz : isGroupoid ZZ

 rZZfrom// : Rrec {Rt = isTrans↔ₛ} ZZ
 Rrec.Bgpd rZZfrom// = squashz
 Rrec.fb rZZfrom// = [_]z
 Rrec.feq rZZfrom// {a = a} {b = b} (↔s F≃ l≡) =
    loopz F≃ l≡
    -- funExtDep⁻ (loopz F≃)
    --   let z = ((congP (λ i z → l≡ i ∘ z) (ua-ungluePathExt F≃)))
    --   in {!z!}
   -- sym (cong [_]z (cong (a ∘_) (funExt (retEq F≃))))
   --    ∙∙ (λ i → loopz F≃ i (l≡ i ∘ invEq F≃ ∘ ua-ungluePathExt F≃ i))
   --      ∙∙ cong [_]z (cong (b ∘_) (funExt (secEq F≃)) )

 Rrec.fsq rZZfrom// (↔s F≃ l≡) (↔s F≃₁ l≡₁) i j =
   {!!}

-- -- -- --  ZZfrom// : A→// → ZZ
-- -- -- --  ZZfrom// = Rrec.f rZZfrom//

-- -- -- --  ZZto// : ZZ → A→//
-- -- -- --  ZZto// [ x ]z = [ x ]//
-- -- -- --  ZZto// (loopz e i x) =
-- -- -- --       -- hcomp (λ k → λ { (i = i0) → [ x ∘ funExt (retEq e) k ]// 
-- -- -- --       --             ; (i = i1) → [  x ∘ funExt (secEq e) k  ]//
-- -- -- --       --         }) (eq// {a = x ∘ ua-gluePathExt e i ∘ funExt (retEq e) (i)}
-- -- -- --       --                  {b = x ∘ ua-gluePathExt e i ∘ invEq e}
-- -- -- --       --             (↔s e
-- -- -- --       --               λ j → ( x ∘ ua-gluePathExt e i
-- -- -- --       --                   ∘ funExt (retEq e) (~ j ∧ i))) i)

-- -- -- --    hcomp (λ k → λ { (i = i0) → [ x ]// 
-- -- -- --                   ; (i = i1) → [ x ∘ funExt (secEq e) k ]//
-- -- -- --               }) (eq// {a = x ∘ ua-gluePathExt e i}
-- -- -- --                        {b = x ∘ ua-gluePathExt e i ∘ invEq e}
-- -- -- --                   (↔s e
-- -- -- --                     λ j → ( x ∘ ua-gluePathExt e i
-- -- -- --                         ∘ funExt (retEq e) (~ j))) i)
-- -- -- --  ZZto// (compz e f i j x) =
-- -- -- --    hcomp (λ k → λ {
-- -- -- --       (i = i0) → {!!}
-- -- -- --      ;(i = i1) → {!!}
-- -- -- --      ;(j = i0) → {!!}
-- -- -- --      ;(j = i1) → {!!}
-- -- -- --         })
-- -- -- --         {!!}
-- -- -- --   -- let b : A → B
-- -- -- --   --     b = λ a → x (glue {φ = j ∨ ~ j}
-- -- -- --   --                       (λ { (j = i0) → ? 
-- -- -- --   --                          ; (j = i1) → ? })
-- -- -- --   --                          (outS ?)) 
-- -- -- --   -- in hcomp (λ k → λ {
-- -- -- --   --     (i = i0) → {!!}
-- -- -- --   --    ;(i = i1) → {!!}
-- -- -- --   --    ;(j = i0) → [ x ]//
-- -- -- --   --    ;(j = i1) → {!!}
-- -- -- --   --       })
-- -- -- --   --        (comp// (↔s {x = {!!}} e {!!}) (↔s f {!!}) i j)
         
-- -- -- --  ZZto// (squashz x x₁ x₂ y x₃ y₁ i i₁ x₄) = {!!}

-- -- -- --  toZZᵣ : EMelim sg λ em → B* em → ZZ
-- -- -- --  EMelim.isGrpB toZZᵣ em = isGroupoidΠ λ _ → squashz 
-- -- -- --  EMelim.b toZZᵣ = [_]z
-- -- -- --  EMelim.bPathP toZZᵣ g i x = loopz g i x
-- -- -- --  EMelim.bSqP toZZᵣ g h = compz g h 

-- -- -- --  from// : ZZ → Σ _ B*
-- -- -- --  from// [ x ]z = embase , x
-- -- -- --  from// (loopz e i x) = emloop e i , x  
-- -- -- --  from// (compz e f i j x) = emcomp e f i j , x
-- -- -- --  from// (squashz _ _ _ _ r s i j k) =
-- -- -- --    isOfHLevelΣ 3 emsquash
-- -- -- --      (λ _ → isGroupoidΠ λ _ → isGroupoidB) _ _ _ _
-- -- -- --       (λ i j → from// (r i j))
-- -- -- --       (λ i j → from// (s i j)) i j k

-- -- -- -- --  -- A//≡' : (g : A ≃ A) → PathP (λ i → (ua g i → B) → A→//)
-- -- -- -- --  --             [_]// [_]//
-- -- -- -- --  -- A//≡' g = {!!}
-- -- -- -- --  --      ◁ (λ i x → eq// {a = {!x ∘ (ua-gluePathExt g i)!}}
-- -- -- -- --  --                    {b = x ∘ (ua-gluePathExt g i)}
-- -- -- -- --  --                (↔s g
-- -- -- -- --  --         λ j → x ∘ ua-gluePathExt g (i ∧ j) ) i) 
-- -- -- -- --  --         ▷ {!!}
-- -- -- -- --  A//≡ : (g : A ≃ A) →
-- -- -- -- --       PathP (λ i → (ua g i → B) → A→//)
-- -- -- -- --       {!!}
-- -- -- -- --       {!!} --([_]// ∘ (_∘ fst g))
-- -- -- -- --  A//≡ g i x =
-- -- -- -- --   let p : PathP (λ j → ?)
-- -- -- -- --                (x ∘ (ua-gluePathExt g i))
-- -- -- -- --              {!!}
-- -- -- -- --       p = λ j → x ∘ ua-gluePathExt g (i ∧ j)

-- -- -- -- --       pP : PathP (λ i → ua g i → B)
-- -- -- -- --             (λ x₁ → x (ua-gluePathExt g i (fst g x₁)))
-- -- -- -- --             (λ x₁ → x (ua-gluePathExt g i x₁))
-- -- -- -- --       pP = λ j → x ∘ ua-gluePathExt g i ∘ ua-ungluePathExt g j

-- -- -- -- --       p// : [ {!!} ]// ≡ [ {!!} ]//
-- -- -- -- --       p// = eq// (↔s g {!p!})


-- -- -- -- --       -- z : PathP (λ j → ((a : A) → B) // _) {![_]// ∘ ?!} {!!}
-- -- -- -- --       -- z = λ j → 
-- -- -- -- --       --  eq// 
-- -- -- -- --       --    {Rt = {!!}}
-- -- -- -- --       --      {a = x ∘ ua-gluePathExt g i ∘ ua-ungluePathExt g i0}
-- -- -- -- --       --      {b = x ∘ ua-gluePathExt g i ∘ ua-ungluePathExt g i1}
-- -- -- -- --       --     (↔s g λ j → x ∘ ua-gluePathExt g i ∘ ua-ungluePathExt g j) j
-- -- -- -- --   in {!z!}


-- -- -- -- --  data ZZ : Type (ℓ-max ℓ ℓb) where

-- -- -- -- --  to//ᵣ : EMelim sg λ em → B* em → A→//
-- -- -- -- --  EMelim.isGrpB to//ᵣ em = isGroupoidΠ λ _ → squash// 
-- -- -- -- --  EMelim.b to//ᵣ = [_]//
-- -- -- -- --  EMelim.bPathP to//ᵣ g i x =
-- -- -- -- --    ua-unglue {A = (ua g i → B) // {!!}}
-- -- -- -- --     {!!} i {!!}
-- -- -- -- --    -- ua-ungluePath {!!} {!!} i
-- -- -- -- --    -- eq// {a = x ∘ ua-gluePathExt g i }
-- -- -- -- --    --      {b = λ v → {!x ?!}}
-- -- -- -- --    --   (↔s g (λ j →  x ∘ ua-gluePathExt g i ∘ ua-ungluePathExt g j)) i

-- -- -- -- --  EMelim.bSqP to//ᵣ = {!!}

-- -- -- -- --  to// : ∀ em → B* em → A→//
-- -- -- -- --  to// = EMelim.f to//ᵣ

-- -- -- -- --  -- iso-em-// : Iso ? A→//
-- -- -- -- --  -- Iso.fun iso-em-// = uncurry to//
-- -- -- -- --  -- Iso.inv iso-em-// = from//
-- -- -- -- --  -- Iso.rightInv iso-em-// =
-- -- -- -- --  --   elimSet// _ (λ _ → squash// _ _)
-- -- -- -- --  --    (λ _ → refl) λ {a} {b} r → {!!}
-- -- -- -- --  -- Iso.leftInv iso-em-// =
-- -- -- -- --  --    uncurry (elimSet _ (λ _ → isSetΠ λ _ → isGroupoidEmΣ _ _)
-- -- -- -- --  --     (λ _ → refl) {!!})


-- -- -- -- -- -- --   -- record _↔ₛ_ (x y : A → B) : Type (ℓ-max ℓ ℓ') where
-- -- -- -- -- -- --   --   constructor ↔s
-- -- -- -- -- -- --   --   field
-- -- -- -- -- -- --   --     F≃ : (A ≃ A)
-- -- -- -- -- -- --   --     l≡ : PathP (λ i → ua F≃ i → B) x y

-- -- -- -- -- -- --   -- isTrans↔ₛ : BinaryRelation.isTrans _↔ₛ_
-- -- -- -- -- -- --   -- isTrans↔ₛ a b c (↔s e p) (↔s f q) =
-- -- -- -- -- -- --   --   ↔s (e ∙ₑ f) ({!!} ◁ {!!} ▷ {!!})


 




-- -- -- -- -- -- -- module _ {ℓ} (A B : Type ℓ) (AG : isGroupoid A) (BG : isGroupoid B)
-- -- -- -- -- -- --            (f : A → B)
-- -- -- -- -- -- --            (g₂ : ∥ B ∥₂ → ∥ A ∥₂)
-- -- -- -- -- -- --            -- (iso₃ : ∀ x x' → Iso.fun iso₂ ∣ x ∣₂ ≡ ∣ x' ∣₂ → Iso (x ≡ x) (x' ≡ x'))
-- -- -- -- -- -- --               where

-- -- -- -- -- -- --   AtoB : (a : A) → singl {A = B} {!!}
-- -- -- -- -- -- --   AtoB x = {!!}

-- -- -- -- -- -- --   combienHIsos : Iso A B
-- -- -- -- -- -- --   combienHIsos = {!!}

-- -- -- -- -- -- -- funExtDepSq : ∀ {ℓ ℓ'} → {A : I → I → Type ℓ} {B : (i j : I) → A i j → Type ℓ'}
-- -- -- -- -- -- --   {f00 : (x : A i0 i0) → B i0 i0 x}
-- -- -- -- -- -- --   {f01 : (x : A i0 i1) → B i0 i1 x}
-- -- -- -- -- -- --   {f10 : (x : A i1 i0) → B i1 i0 x}
-- -- -- -- -- -- --   {f11 : (x : A i1 i1) → B i1 i1 x}
-- -- -- -- -- -- --   (f0- : PathP (λ i → (a : A i0 i) → B i0 i a) f00 f01)
-- -- -- -- -- -- --   (f1- : PathP (λ i → (a : A i1 i) → B i1 i a) f10 f11)
-- -- -- -- -- -- --   (f-0 : PathP (λ i → (a : A i i0) → B i i0 a) f00 f10)
-- -- -- -- -- -- --   (f-1 : PathP (λ i → (a : A i i1) → B i i1 a) f01 f11)
-- -- -- -- -- -- --    → (∀
-- -- -- -- -- -- --   {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁}
-- -- -- -- -- -- --   {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} {a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁}
-- -- -- -- -- -- --   {a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀} {a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁}
-- -- -- -- -- -- --       → (sqA : SquareP A a₀₋ a₁₋ a₋₀ a₋₁)
-- -- -- -- -- -- --      → SquareP (λ i j → B i j (sqA i j))
-- -- -- -- -- -- --         (λ i → f0- i (a₀₋ i))
-- -- -- -- -- -- --         (λ i → f1- i (a₁₋ i))
-- -- -- -- -- -- --         (λ i → f-0 i (a₋₀ i))
-- -- -- -- -- -- --         (λ i → f-1 i (a₋₁ i)))
-- -- -- -- -- -- --    → SquareP (λ i j → (a : A i j) → B i j a)
-- -- -- -- -- -- --         f0-
-- -- -- -- -- -- --         f1-
-- -- -- -- -- -- --         f-0
-- -- -- -- -- -- --         f-1



-- -- -- -- -- -- -- funExtDepSq = {!!}
-- -- -- -- -- -- -- -- {A = A} {B = B} f0- f1- f-0 f-1 h i j x =
-- -- -- -- -- -- -- --   comp
-- -- -- -- -- -- -- --     (λ k → B i j x)
-- -- -- -- -- -- -- --      (λ k → λ
-- -- -- -- -- -- -- --       { (i = i0) → {!!}
-- -- -- -- -- -- -- --       ; (i = i1) → {!!}
-- -- -- -- -- -- -- --       ; (j = i0) → {!!}
-- -- -- -- -- -- -- --       ; (j = i1) → {!!}
-- -- -- -- -- -- -- --       })
-- -- -- -- -- -- -- --     (h {!!} i j)


-- -- -- -- -- -- doubleCompPathP→ : ∀ {ℓ ℓ' ℓ''} → {A : Type ℓ} → (A' : A → Type ℓ'')
-- -- -- -- -- --                       → ∀ {W X Y Z : A} {B : Type ℓ'}
-- -- -- -- -- --              {W' : A' W → B} {X' : A' X → B} {Y' : A' Y → B} {Z' : A' Z → B}
-- -- -- -- -- --              {p : W ≡ X} {q : X ≡ Y} {r : Y ≡ Z}
-- -- -- -- -- --              (P : PathP (λ i → A' (p i) → B) W' X')
-- -- -- -- -- --              (Q : PathP (λ i → A' (q i) → B) X' Y')
-- -- -- -- -- --              (R : PathP (λ i → A' (r i) → B) Y' Z')
-- -- -- -- -- --           → PathP (λ i → A' ((p ∙∙ q ∙∙ r) i) → B) W' Z'
-- -- -- -- -- -- doubleCompPathP→ A' {B = B} {Y' = Y'} {p = p*} {q = q*} {r = r*}  P Q R i =
-- -- -- -- -- --   let p = cong A' p*
-- -- -- -- -- --       q = cong A' q*
-- -- -- -- -- --       r = cong A' r*
 
-- -- -- -- -- --       p' : PathP (λ k → p i0 → p (~ k)) (transport p) (idfun _)
-- -- -- -- -- --       p' = λ j x → transp (λ j₁ → p (~ j ∧ j₁)) j x

-- -- -- -- -- --       q' : PathP (λ i → A' ((p* ∙∙ q* ∙∙ r*) i) → q i) (transport p) (transport (sym r))
-- -- -- -- -- --       q' i = transport (λ i₁ → A' (doubleCompPath-filler p* q* r* (~ i₁) i ))  
      
-- -- -- -- -- --       r' : PathP (λ k → r i1 → r k) (transport (sym r)) (idfun _)
-- -- -- -- -- --       r' = λ j x → transp (λ j₁ → r (j ∨ ~ j₁)) j x

-- -- -- -- -- --   in hcomp (λ k → λ {(i = i0) → transp (λ i₂ → B) k ∘ (P (~ k) ∘ (p' k))
-- -- -- -- -- --                     ;(i = i1) → transp (λ i₂ → B) k ∘ (R k ∘ (r' k)) })
-- -- -- -- -- --         (transport refl ∘ (Q i ∘ ((q' i))))

-- -- -- -- -- -- doubleCompPathP→-filler : ∀ {ℓ ℓ' ℓ''} → {A : Type ℓ} → (A' : A → Type ℓ'')
-- -- -- -- -- --                       → ∀ {W X Y Z : A} {B : Type ℓ'}
-- -- -- -- -- --              {W' : A' W → B} {X' : A' X → B} {Y' : A' Y → B} {Z' : A' Z → B}
-- -- -- -- -- --              {p : W ≡ X} {q : X ≡ Y} {r : Y ≡ Z}
-- -- -- -- -- --              (P : PathP (λ i → A' (p i) → B) W' X')
-- -- -- -- -- --              (Q : PathP (λ i → A' (q i) → B) X' Y')
-- -- -- -- -- --              (R : PathP (λ i → A' (r i) → B) Y' Z')
-- -- -- -- -- --           → SquareP (λ i j → A' (doubleCompPath-filler p q r i j) → B)
-- -- -- -- -- --                Q
-- -- -- -- -- --                (doubleCompPathP→ A' P Q R)
-- -- -- -- -- --                (symP P)
-- -- -- -- -- --                R
-- -- -- -- -- -- doubleCompPathP→-filler A' {B = B} {Y' = Y'} {p = p*} {q = q*} {r = r*}  P Q R j i =
-- -- -- -- -- --   fill (λ k → A' (doubleCompPath-filler p* q* r* k i) → B) 
-- -- -- -- -- --       ((λ k → λ {(i = i0) → P (~ k)
-- -- -- -- -- --                 ;(i = i1) → R k }))
-- -- -- -- -- --       (inS (Q i)) j






-- -- -- -- -- -- compPathP→ : ∀ {ℓ ℓ' ℓ''} → {A : Type ℓ} → (A' : A → Type ℓ'')
-- -- -- -- -- --                       → ∀ {X Y Z : A} {B : Type ℓ'}
-- -- -- -- -- --              {X' : A' X → B} {Y' : A' Y → B} {Z' : A' Z → B}
-- -- -- -- -- --              {q : X ≡ Y} {r : Y ≡ Z}             
-- -- -- -- -- --              (Q : PathP (λ i → A' (q i) → B) X' Y')
-- -- -- -- -- --              (R : PathP (λ i → A' (r i) → B) Y' Z')
-- -- -- -- -- --           → PathP (λ i → A' ((q ∙ r) i) → B) X' Z'
-- -- -- -- -- -- compPathP→ A {X = X} {X' = X'} =
-- -- -- -- -- --   doubleCompPathP→ A {p = λ _ → X} (λ _ → X')


-- -- -- -- -- -- compPathP→filler : ∀ {ℓ ℓ' ℓ''} → {A : Type ℓ} → (A' : A → Type ℓ'')
-- -- -- -- -- --                       → ∀ {X Y Z : A} {B : Type ℓ'}
-- -- -- -- -- --              {X' : A' X → B} {Y' : A' Y → B} {Z' : A' Z → B}
-- -- -- -- -- --              {q : X ≡ Y} {r : Y ≡ Z}             
-- -- -- -- -- --              (Q : PathP (λ i → A' (q i) → B) X' Y')
-- -- -- -- -- --              (R : PathP (λ i → A' (r i) → B) Y' Z')
-- -- -- -- -- --           → SquareP (λ i j → A' ((compPath-filler q r i) j) → B)
-- -- -- -- -- --                Q
-- -- -- -- -- --                (compPathP→ A' Q R)
-- -- -- -- -- --                refl
-- -- -- -- -- --                R
-- -- -- -- -- -- compPathP→filler A' {X = X} {X' = X'} Q R =
-- -- -- -- -- --   doubleCompPathP→-filler A' refl Q R

-- -- -- -- -- -- _∙∙P_∙∙P_ : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
-- -- -- -- -- --              (p : w ≡ x)
-- -- -- -- -- --              (q : x ≡ y)
-- -- -- -- -- --              (r : y ≡ z)
-- -- -- -- -- --              → w ≡ z
              
-- -- -- -- -- -- _∙∙P_∙∙P_ {A = A} p q r i =
-- -- -- -- -- --   comp (λ _ → A) (doubleComp-faces p r i) (q i)
   

-- -- -- -- -- -- fixComp : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
-- -- -- -- -- --              (p : w ≡ x)
-- -- -- -- -- --              (q : x ≡ y)
-- -- -- -- -- --              (r : y ≡ z)
-- -- -- -- -- --              → (p ∙∙ q ∙∙ r) ≡ p ∙∙P q ∙∙P r 
-- -- -- -- -- -- fixComp {A = A} p q r j i =
-- -- -- -- -- --        hcomp
-- -- -- -- -- --        (doubleComp-faces (λ i₁ → transp (λ _ → A) (~ j ∨ ~ i₁) (p i₁))
-- -- -- -- -- --         (λ i₁ → transp (λ _ → A) (~ j ∨ i₁) (r i₁)) i)
-- -- -- -- -- --        (transp (λ _ → A) (~ j) (q i))


-- -- -- -- -- -- -- module _ {ℓ} {A : Type ℓ} where
-- -- -- -- -- -- --   ΣsinglP≃A : (g : A ≡ A) →
-- -- -- -- -- -- --                  Σ _ (uncurry (PathP λ i → g i))
-- -- -- -- -- -- --                 ≃ A
-- -- -- -- -- -- --   ΣsinglP≃A g = Σ-assoc-≃ ∙ₑ Σ-contractSnd (isContrSinglP λ i → g i )


-- -- -- -- -- -- -- module R' {ℓ} where
 
-- -- -- -- -- -- --   ↔ : {A B : Type ℓ} (a : A) (b : B) → Type (ℓ-suc ℓ)
-- -- -- -- -- -- --   ↔ {A} {B} a b = Σ (A ≡ B) λ p → PathP (λ i → p i) a b 


-- -- -- -- -- -- --   ↔≡ : ∀ {A} {B} (T : Type ℓ) → (p : A ≡ B)
-- -- -- -- -- -- --         → (f : A → T) (g : B → T)
-- -- -- -- -- -- --         → {!!}
-- -- -- -- -- -- --         -- (∀ a b → (r : R a b) → [ a ] ≡ [ b ])
-- -- -- -- -- -- --          → PathP (λ i → p i → T) f g
-- -- -- -- -- -- --   ↔≡ g =  {!!}

-- -- -- -- -- -- --   -- isTrans↔p : BinaryRelation.isTrans _↔p_
-- -- -- -- -- -- --   -- fst (isTrans↔p a b c (p , _) (q , _)) = p ∙ q
-- -- -- -- -- -- --   -- snd (isTrans↔p a b c (p , P) (q , Q)) = compPathP P Q

-- -- -- -- -- -- --   -- A// = A // isTrans↔p

-- -- -- -- -- -- -- module AutR {ℓ} {A : Type ℓ} where
 
-- -- -- -- -- -- --   _↔p_ : (x y : A) → Type (ℓ-suc ℓ)
-- -- -- -- -- -- --   x ↔p y = Σ (A ≡ A) λ p → PathP (λ i → p i) x y 

-- -- -- -- -- -- --   isTrans↔p : BinaryRelation.isTrans _↔p_
-- -- -- -- -- -- --   fst (isTrans↔p a b c (p , _) (q , _)) = p ∙ q
-- -- -- -- -- -- --   snd (isTrans↔p a b c (p , P) (q , Q)) = compPathP P Q

-- -- -- -- -- -- --   A// = A // isTrans↔p

-- -- -- -- -- -- --   -- [_]/↔ : ?
  
-- -- -- -- -- -- --   [_]/↔ = [_]// {Rt = isTrans↔p}
  




-- -- -- -- -- -- -- module EMFam≡ {ℓ ℓ'} {A : Type ℓ} (isSetA : isSet A)
-- -- -- -- -- -- --                 (B : Type ℓ')
-- -- -- -- -- -- --               where

-- -- -- -- -- -- --   open GroupStr (snd (hSetLoop-Group _ isSetA))

-- -- -- -- -- -- --   open AutR {A = A}

-- -- -- -- -- -- --   -- AhSet≡ : A ≃ A → Path (hSet ℓ) (A , isSetA) (A , isSetA)
-- -- -- -- -- -- --   -- AhSet≡ = TypeOfHLevel≡ 2 ∘ ua

-- -- -- -- -- -- --   lg = hSetLoop-Group _ isSetA

-- -- -- -- -- -- --   EMG = EM₁ lg 

-- -- -- -- -- -- --   EM₁HFam : EMG → hSet ℓ
-- -- -- -- -- -- --   EM₁HFam = EMrec.f w
-- -- -- -- -- -- --     where
-- -- -- -- -- -- --      w : EMrec lg isGroupoidHSet
-- -- -- -- -- -- --      EMrec.b w = A , isSetA
-- -- -- -- -- -- --      EMrec.bloop w = TypeOfHLevel≡ 2
-- -- -- -- -- -- --      EMrec.bComp w f g =
-- -- -- -- -- -- --        ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- --          (compPath-filler _ _)

-- -- -- -- -- -- --   -- elimEM lg
-- -- -- -- -- -- --   --  ( λ _ → isGroupoidHSet) (A , isSetA)
-- -- -- -- -- -- --   --       (TypeOfHLevel≡ 2)
-- -- -- -- -- -- --   --       λ g h → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- --   --    (compPath-filler _ _) 

-- -- -- -- -- -- --   EM₁fam = fst ∘ EM₁HFam



-- -- -- -- -- -- --   -- sqH : (g : A ≡ A) →
-- -- -- -- -- -- --   --           ((a : A) → [ a ]/↔ ≡ [ a ]/↔)
-- -- -- -- -- -- --   --           ≡
-- -- -- -- -- -- --   --           PathP (λ i → g i → A//) [_]// [_]//
-- -- -- -- -- -- --   -- sqH g =
-- -- -- -- -- -- --   --    (λ i → (a : A) →
-- -- -- -- -- -- --   --       Path A// [ a ]//
-- -- -- -- -- -- --   --              (eq// {a = a} {b = transport (λ j → g j) a}
-- -- -- -- -- -- --   --                (g , toPathP refl) i ) )
-- -- -- -- -- -- --   --    ∙∙ (λ i → (a : ua isoH i) →
-- -- -- -- -- -- --   --    Path A// [ fst (pFst i a) ]//
-- -- -- -- -- -- --   --             [ snd (pFst i a) ]//)
-- -- -- -- -- -- --   --    ∙∙ ua zz
-- -- -- -- -- -- --   --  where
-- -- -- -- -- -- --   --   isoH : _
-- -- -- -- -- -- --   --   isoH = invEquiv (ΣsinglP≃A g)

-- -- -- -- -- -- --   --   pFst : PathP (λ i → ua isoH i → A × A)
-- -- -- -- -- -- --   --      (λ x → x , transport g x)
-- -- -- -- -- -- --   --      fst
-- -- -- -- -- -- --   --   pFst i z = fst (ua-unglue isoH i z)

-- -- -- -- -- -- --   --   -- qq : {!!}
-- -- -- -- -- -- --   --   --       ≡ ((((a , a') , _) :
-- -- -- -- -- -- --   --   --         Σ (A × A) (λ (a , a') → PathP (λ z → g z) a a')) →
-- -- -- -- -- -- --   --   --            [ a ]// ≡ [ a' ]//)
-- -- -- -- -- -- --   --   -- qq = {!!}

-- -- -- -- -- -- --   --   zz : ((((a , a') , _)
-- -- -- -- -- -- --   --           : Σ (A × A) (λ (a , a') → PathP (λ z → g z) a a')) →
-- -- -- -- -- -- --   --          [ a ]// ≡ [ a' ]//)
-- -- -- -- -- -- --   --          ≃ PathP (λ i → (x : g i) → A//) [_]// [_]//
-- -- -- -- -- -- --   --   zz = curryEquiv'  ∙ₑ funExtDepEquiv {A = λ z → g z}
-- -- -- -- -- -- --   --                       {B = λ _ _ → A//}
-- -- -- -- -- -- --   --                       {[_]//} {[_]//}
-- -- -- -- -- -- --   -- sqH' : (λ x → (a : A) → [ a ]// ≡ [ a ]//) ≡
-- -- -- -- -- -- --   --        (λ x → PathP (λ i → x i → A//) [_]// [_]//)
-- -- -- -- -- -- --   -- sqH' = funExt sqH

-- -- -- -- -- -- --   -- sqHΠ : (A ≡ A → (a : A) → Path A// ([ a ]//) ([ a ]//)) ≡
-- -- -- -- -- -- --   --        ((x : A ≡ A) → PathP (λ i → x i → A//) [_]// [_]//)
-- -- -- -- -- -- --   -- sqHΠ i = (x : A ≡ A) → sqH x i

-- -- -- -- -- -- --   -- A//≡ : (g : A ≡ A) →
-- -- -- -- -- -- --   --     PathP (λ i → g i → A// {A = A})
-- -- -- -- -- -- --   --      (λ x → [ x ]//)
-- -- -- -- -- -- --   --      (λ x → [ x ]//)
-- -- -- -- -- -- --   -- A//≡ g = {!!}

  

  

-- -- -- -- -- -- --   A//≡ : (g : A ≡ A) →
-- -- -- -- -- -- --       PathP (λ i → g i → A//)
-- -- -- -- -- -- --        ([_]/↔)
-- -- -- -- -- -- --        ([_]/↔)
-- -- -- -- -- -- --   A//≡ g = funExt (λ x → eq//
-- -- -- -- -- -- --       (g , (transport-filler g x))) 
-- -- -- -- -- -- --      ◁ congP (λ _ → [_]/↔ ∘_) (transport-fillerExt⁻ g)
  
-- -- -- -- -- -- --   to : Σ _ EM₁fam → A//
-- -- -- -- -- -- --   to = uncurry (EMelim.f w)
-- -- -- -- -- -- --    where
-- -- -- -- -- -- --    --  w : (x : EMG) (y : EM₁fam x) → A//
-- -- -- -- -- -- --    --  w embase y = [ y ]//
-- -- -- -- -- -- --    --  w (emloop x i) y =
-- -- -- -- -- -- --    --    eq// (x , λ i₁ → {!y!}) i
-- -- -- -- -- -- --    --  w (emcomp g h j i) y = {!!}
-- -- -- -- -- -- --    --  w (emsquash x x₁ p q r s i i₁ i₂) y = {!!}
    
-- -- -- -- -- -- --     w : EMelim lg (λ z → (y : EM₁fam z) → A//)
    
-- -- -- -- -- -- --     EMelim.isGrpB w _ = isGroupoidΠ λ _ → squash//
-- -- -- -- -- -- --     EMelim.b w x = [ x ]//
-- -- -- -- -- -- --     EMelim.bPathP w = A//≡

-- -- -- -- -- -- --     EMelim.bSqP w g h =
-- -- -- -- -- -- --      let z : SquareP (λ i j → EM₁fam (emcomp g h i j) → A//)
-- -- -- -- -- -- --                (A//≡ g)
-- -- -- -- -- -- --                (A//≡ (g ∙ h))
-- -- -- -- -- -- --                refl
-- -- -- -- -- -- --                (A//≡ h)
-- -- -- -- -- -- --          z i j = 
-- -- -- -- -- -- --           hcomp
-- -- -- -- -- -- --             (λ k →
-- -- -- -- -- -- --             λ { (i = i0) → {!!}
-- -- -- -- -- -- --               ; (i = i1) → {!!}
-- -- -- -- -- -- --               ; (j = i0) → {!!}
-- -- -- -- -- -- --               ; (j = i1) → {!!}
-- -- -- -- -- -- --               })
-- -- -- -- -- -- --             {!!}

-- -- -- -- -- -- --      in  z
    
-- -- -- -- -- -- --       -- let
-- -- -- -- -- -- --       --     z : Square
-- -- -- -- -- -- --       --           (emloop {Group = lg} g)
-- -- -- -- -- -- --       --           (emloop _)
-- -- -- -- -- -- --       --           (λ i → embase)
-- -- -- -- -- -- --       --           λ i → emloop h i
-- -- -- -- -- -- --       --     z = emcomp g h

-- -- -- -- -- -- --       --     zz : {x y z : A} (P : PathP (λ i → g i) x y)
-- -- -- -- -- -- --       --        → (Q : PathP (λ i → h i) y z) → Square
-- -- -- -- -- -- --       --              (eq// (g , P))
-- -- -- -- -- -- --       --              (eq// (isTrans↔p x y z (g , P) (h , Q)))
-- -- -- -- -- -- --       --              (λ i → [ x ]//)
-- -- -- -- -- -- --       --              λ i → eq// (h , Q) i
-- -- -- -- -- -- --       --     zz P Q = comp// {Rt = isTrans↔p}
-- -- -- -- -- -- --       --            (g , P) (h , Q)

-- -- -- -- -- -- --       --     zz' : SquareP (λ i j → EM₁fam (emcomp g h i j) → A//)
-- -- -- -- -- -- --       --             (funExtDep (λ P → eq// (g , P)))
-- -- -- -- -- -- --       --             (compPathP→ (λ x → x) (funExtDep (λ P → eq// (g , P)))
-- -- -- -- -- -- --       --               (funExtDep (λ P → eq// (h , P))))
-- -- -- -- -- -- --       --             (λ i → [_]//)
-- -- -- -- -- -- --       --             λ i → funExtDep (λ P → eq// (h , P)) i
-- -- -- -- -- -- --       --     zz' = compPathP→filler (λ x → x) {q = g} {r = h}
-- -- -- -- -- -- --       --             (funExtDep (λ P → eq// (g , P)))
-- -- -- -- -- -- --       --             (funExtDep (λ P → eq// (h , P)))

-- -- -- -- -- -- --       --     sss : Square {A = (x : A) → ∀ P Q →  A//}
-- -- -- -- -- -- --       --             (λ j a P Q → eq// (g , P) j)
-- -- -- -- -- -- --       --             (λ j a P Q →
-- -- -- -- -- -- --       --                 eq// ((g ∙ h)
-- -- -- -- -- -- --       --                        , compPathP P Q) j)
-- -- -- -- -- -- --       --             (λ i a P Q → [ a ]//)
-- -- -- -- -- -- --       --             λ i a P Q → eq// (h , Q) i
-- -- -- -- -- -- --       --     sss i j a P Q = zz {a} {a} {a}
-- -- -- -- -- -- --       --       P Q i j


-- -- -- -- -- -- --       --     -- sss' : Square {A = (x : A) →  A//}
-- -- -- -- -- -- --       --     --         {!!}
-- -- -- -- -- -- --       --     --         {!!}
-- -- -- -- -- -- --       --     --         {!!}
-- -- -- -- -- -- --       --     --         {!!}
-- -- -- -- -- -- --       --     -- sss' i j a = zz {a} 
-- -- -- -- -- -- --       --     --   (toPathP refl) (toPathP refl) i j

-- -- -- -- -- -- --       --     zzE : (g : A ≡ A) → Σ
-- -- -- -- -- -- --       --             (({x₀ : g i0} {x₁ : g i1} (p : PathP (λ z₁ → g z₁) x₀ x₁) →
-- -- -- -- -- -- --       --               [ x₀ ]// ≡ [ x₁ ]//) →
-- -- -- -- -- -- --       --              PathP (λ i → (x : g i) → A//) [_]// [_]//)
-- -- -- -- -- -- --       --             isEquiv
-- -- -- -- -- -- --       --     zzE g = ((funExtDepEquiv
-- -- -- -- -- -- --       --              {A = λ z → g z}
-- -- -- -- -- -- --       --                             {B = λ _ _ → A//}) {[_]//} {[_]//})


-- -- -- -- -- -- --       --     zzEsq : ∀ g → (b : PathP (λ i → g i → A//) [_]// [_]//) →
-- -- -- -- -- -- --       --               funExtDep (λ p i → b i (p i)) ≡ b
-- -- -- -- -- -- --       --     zzEsq g = secEq (zzE g)


-- -- -- -- -- -- --       --     zzEsq' : (g : A ≡ A) → ∀ a →
-- -- -- -- -- -- --       --                      (λ p i → (funExtDep a) i (p i)) ≡ a
-- -- -- -- -- -- --       --     zzEsq' g = retEq (zzE g)

-- -- -- -- -- -- --       --     ZZZ : Square
-- -- -- -- -- -- --       --             (λ j → EM₁fam (emloop g j) → A)
-- -- -- -- -- -- --       --             (λ j → EM₁fam (emloop (g ∙ h) j) → A)
-- -- -- -- -- -- --       --             refl
-- -- -- -- -- -- --       --             (λ i → EM₁fam (emloop h i) → A)
-- -- -- -- -- -- --       --     ZZZ i j =
-- -- -- -- -- -- --       --        hcomp (λ k →
-- -- -- -- -- -- --       --           λ { (i = i0) → g j → A
-- -- -- -- -- -- --       --             ; (i = i1) → EM₁fam (z k j) → A
-- -- -- -- -- -- --       --             ; (j = i0) → A → A
-- -- -- -- -- -- --       --             ; (j = i1) → h (i ∧ k) → A
-- -- -- -- -- -- --       --             })
-- -- -- -- -- -- --       --          (g j → A)

-- -- -- -- -- -- --       --     -- zzzB : SquareP (λ j i → EM₁fam (emcomp g h i j) → A//)
-- -- -- -- -- -- --       --     --          (λ i → λ a → eq//
-- -- -- -- -- -- --       --     --                {a = transport (λ i₂ → h i₂) a}
-- -- -- -- -- -- --       --     --                 (h , toPathP refl) )
-- -- -- -- -- -- --       --     --           {!!}
-- -- -- -- -- -- --       --     --           {!!}
-- -- -- -- -- -- --       --     --          {!!}
-- -- -- -- -- -- --       --     -- zzzB = toPathP refl

-- -- -- -- -- -- --       --     sqG : ∀ g → SquareP (λ j _ → g j → A//)
-- -- -- -- -- -- --       --                (λ i a → (eq// {a = a} (g , toPathP refl)) (~ i))
-- -- -- -- -- -- --       --                (λ _ → [_]//)                     
-- -- -- -- -- -- --       --                (funExtDep
-- -- -- -- -- -- --       --                    {A = λ z₁ → g z₁}
-- -- -- -- -- -- --       --                    {B = λ i _ → A//}
-- -- -- -- -- -- --       --                   {f = λ x → [ transport (λ z₁ → g z₁) x ]//}
-- -- -- -- -- -- --       --                   {g = [_]//}
-- -- -- -- -- -- --       --                  (cong [_]// ∘ fromPathP
-- -- -- -- -- -- --       --                   {A = λ z₁ → g z₁}))
-- -- -- -- -- -- --       --                (funExtDep
-- -- -- -- -- -- --       --                   {A = λ z₁ → g z₁}
-- -- -- -- -- -- --       --                    {B = λ i _ → A//}
-- -- -- -- -- -- --       --                   {f = [_]//}
-- -- -- -- -- -- --       --                   {g = [_]//}
-- -- -- -- -- -- --       --                   (λ P → eq// (g , P)))

-- -- -- -- -- -- --       --     sqG g j i =
-- -- -- -- -- -- --       --        funExtDep {A = λ z₁ → g z₁} {B = λ i _ → A//}
-- -- -- -- -- -- --       --         {f = λ a → (eq// {a = a} (g , toPathP refl)) (~ i) }
-- -- -- -- -- -- --       --         {g = [_]//}
-- -- -- -- -- -- --       --           (λ {x₀} {x₁} p → {!!}) j
-- -- -- -- -- -- --       --       -- (λ i j a → (zzEsq' g (λ P → eq// (g , P))) (~ i)
-- -- -- -- -- -- --       --       --      {a} {transport g a}
-- -- -- -- -- -- --       --       --           (toPathP refl) (~ j))
-- -- -- -- -- -- --       --       -- ◁ {!!}

-- -- -- -- -- -- --       --     sqD : SquareP (λ i j → EM₁fam (emcomp g h i j) → A//)
              
-- -- -- -- -- -- --       --         ((funExtDep (cong [_]// ∘ fromPathP {A =
-- -- -- -- -- -- --       --                    λ z₁ → g z₁})))
-- -- -- -- -- -- --       --         (cong (([_]// {Rt = isTrans↔p}) ∘_)
-- -- -- -- -- -- --       --           (sym (funExt (transportComposite g h)))
-- -- -- -- -- -- --       --           ◁ ((funExtDep (cong [_]// ∘ fromPathP {A =
-- -- -- -- -- -- --       --                    λ z₁ → (g ∙ h) z₁}))))
              
              
-- -- -- -- -- -- --       --         (λ i a → eq// (h ,
-- -- -- -- -- -- --       --                     (toPathP (λ _ → 
-- -- -- -- -- -- --       --                      transport h
-- -- -- -- -- -- --       --                       (transport g a)))) i)
-- -- -- -- -- -- --       --         (funExtDep (λ P → eq// (h , P)))
-- -- -- -- -- -- --       --     sqD i j = {!!}

-- -- -- -- -- -- --       --     zzz : SquareP (λ i j → EM₁fam (emcomp g h i j) → A//)
-- -- -- -- -- -- --       --             (funExtDep (λ P → eq// (g , P)))
-- -- -- -- -- -- --       --             (funExtDep (λ P → eq// (g ∙ h , P)))
-- -- -- -- -- -- --       --             refl
-- -- -- -- -- -- --       --             (funExtDep (λ P → eq// (h , P)))
-- -- -- -- -- -- --       --     zzz i j = hcomp (λ k →
-- -- -- -- -- -- --       --           λ { (i = i0) → sqG g j k
-- -- -- -- -- -- --       --             ; (i = i1) → {!!}
-- -- -- -- -- -- --       --             ; (j = i0) → λ a →
-- -- -- -- -- -- --       --                 zz {a} {transport (λ i₂ → g i₂) a}
-- -- -- -- -- -- --       --                   (toPathP refl)
-- -- -- -- -- -- --       --                     (toPathP (refl {x =
-- -- -- -- -- -- --       --                      transport (λ i₁ → h i₁)
-- -- -- -- -- -- --       --                       (transport (λ i₂ → g i₂) a)})) i (~ k) 
-- -- -- -- -- -- --       --             ; (j = i1) → funExtDep (λ P → eq// (h , P)) i
-- -- -- -- -- -- --       --             })
-- -- -- -- -- -- --       --          (sqD i j)

-- -- -- -- -- -- --       -- in zzz
-- -- -- -- -- -- --       --     -- zz' ▷
-- -- -- -- -- -- --       --     --  (sym (fromPathP (compPathP→filler
-- -- -- -- -- -- --       --     --              (λ x → x)
-- -- -- -- -- -- --       --     --         (funExtDep (λ P → eq// (g , P)))
-- -- -- -- -- -- --       --     --         (funExtDep (λ P → eq// (h , P))))) ∙
-- -- -- -- -- -- --       --     --          {!!})
       
-- -- -- -- -- -- --       --      -- (
-- -- -- -- -- -- --       --      --  (sym (invEq≡→equivFun≡ funExtDepEquiv
-- -- -- -- -- -- --       --      --       {a = (λ P → eq// ((snd lg GroupStr.· g) h , P))}
-- -- -- -- -- -- --       --      --      ( (λ P i → compPathP→
-- -- -- -- -- -- --       --      --       (λ x → x)
-- -- -- -- -- -- --       --      --        (funExtDep (λ P → eq// (g , P)))
-- -- -- -- -- -- --       --      --        (funExtDep (λ P → eq// (h , P))) i (P i))
-- -- -- -- -- -- --       --      --        ≡⟨ {! !} ⟩ {!!}
-- -- -- -- -- -- --       --      --        ≡⟨ {!!} ⟩ 
-- -- -- -- -- -- --       --      --        (λ P → eq// ((snd lg GroupStr.· g) h , P)) ∎))))

-- -- -- -- -- -- --   isGroupoidΣEm₁fam : isGroupoid (Σ EMG (fst ∘ EM₁HFam))
-- -- -- -- -- -- --   isGroupoidΣEm₁fam = isOfHLevelΣ 3 emsquash
-- -- -- -- -- -- --                     (isSet→isGroupoid ∘ snd ∘ EM₁HFam)

-- -- -- -- -- -- --   from : A// → Σ _ EM₁fam
-- -- -- -- -- -- --   from = Rrec.f w
-- -- -- -- -- -- --    where
-- -- -- -- -- -- --     w : Rrec (Σ EMG EM₁fam)
-- -- -- -- -- -- --     Rrec.Bgpd w = isOfHLevelΣ 3 emsquash
-- -- -- -- -- -- --                     (isSet→isGroupoid ∘ snd ∘ EM₁HFam)
-- -- -- -- -- -- --     Rrec.fb w x = embase , x
-- -- -- -- -- -- --     Rrec.feq w (p , P) = ΣPathP ((emloop p) , P)
-- -- -- -- -- -- --     fst (Rrec.fsq w (r , _) (s , _) i i₁) = emcomp r s i i₁
-- -- -- -- -- -- --     snd (Rrec.fsq w (r , R) (s , S) i i₁) = compPathP-filler R S i i₁


-- -- -- -- -- -- -- --   fromTo : section from to
-- -- -- -- -- -- -- --   fromTo = uncurry (EMelimSet.f w)
-- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- --      w : EMelimSet lg (λ z →
-- -- -- -- -- -- -- --            (y : EM₁fam z) → from (to (z , y)) ≡ (z , y))
-- -- -- -- -- -- -- --      EMelimSet.isSetB w - = isSetΠ λ _ → isGroupoidΣEm₁fam _ _
-- -- -- -- -- -- -- --      EMelimSet.b w _ = refl
-- -- -- -- -- -- -- --      EMelimSet.bPathP w g =
-- -- -- -- -- -- -- --       let z' = retEq (funExtDepEquiv)
-- -- -- -- -- -- -- --                 λ P → eq// {Rt = isTrans↔p} (g , P)

-- -- -- -- -- -- -- --       in funExtDep λ {x₀} {x₁} P →
-- -- -- -- -- -- -- --            flipSquare λ i → cong (from) (z' i P)                 
               
-- -- -- -- -- -- -- -- --   toFrom : retract from to
-- -- -- -- -- -- -- -- --   toFrom = RelimSet.f w
-- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- --     w : RelimSet (λ z → to (from z) ≡ z)
-- -- -- -- -- -- -- -- --     RelimSet.truncB w _ = squash// _ _
-- -- -- -- -- -- -- -- --     RelimSet.fb w _ = refl
-- -- -- -- -- -- -- -- --     RelimSet.fbEq w = uncurry λ g → 
-- -- -- -- -- -- -- -- --      funExt⁻ λ i P j →
-- -- -- -- -- -- -- -- --        (retEq funExtDepEquiv) (λ p → eq// (g , p)) j P i 
     
-- -- -- -- -- -- -- -- -- -- module EMFam {ℓ} {A : Type ℓ} (isSetA : isSet A)
            
-- -- -- -- -- -- -- -- -- --               where

-- -- -- -- -- -- -- -- -- --   open GroupStr (snd (Symmetric-Group _ isSetA))
-- -- -- -- -- -- -- -- -- --   -- module M = IsGroupHom (snd m)

  

-- -- -- -- -- -- -- -- -- --   -- actR : A → A → Type (ℓ-max ℓ ℓ')
-- -- -- -- -- -- -- -- -- --   -- actR x y = Σ ⟨ G ⟩ λ g → y ≡ fst (fst m g) x 

-- -- -- -- -- -- -- -- -- --   -- actRTrans : ∀ x y z → actR x y → actR y z → actR x z 
-- -- -- -- -- -- -- -- -- --   -- actRTrans x y z (g , p) (h , q) = (g · h) ,
-- -- -- -- -- -- -- -- -- --   --   q ∙∙ cong (fst (fst m h)) p ∙∙ sym (funExt⁻ (cong fst (M.pres· g h)) x)



-- -- -- -- -- -- -- -- -- -- -- TypeOfHLevel≡ : (n : HLevel) {X Y : TypeOfHLevel ℓ n} → ⟨ X ⟩ ≡ ⟨ Y ⟩ → X ≡ Y

  
-- -- -- -- -- -- -- -- -- --   TypeOfHLevel∙ : (n : HLevel) {X Y Z : TypeOfHLevel ℓ n} → (p : ⟨ X ⟩ ≡ ⟨ Y ⟩) → (q : ⟨ Y ⟩ ≡ ⟨ Z ⟩) 
-- -- -- -- -- -- -- -- -- --                    →  TypeOfHLevel≡ n {X = X} {Y = Y}  p
-- -- -- -- -- -- -- -- -- --                        ∙ TypeOfHLevel≡ n {X = Y} {Y = Z}  q ≡ TypeOfHLevel≡ n ( p ∙ q)
-- -- -- -- -- -- -- -- -- --   fst (TypeOfHLevel∙ n p q i i₁) = (p ∙ q) i₁
-- -- -- -- -- -- -- -- -- --   snd (TypeOfHLevel∙ n {_ , X} {_ , Y} {_ , Z} p q i i₁) =
-- -- -- -- -- -- -- -- -- --      isSet→SquareP (λ i i₁ → isProp→isSet (isPropIsOfHLevel {A = (p ∙ q) i₁} n))
-- -- -- -- -- -- -- -- -- --         (λ i₁ → snd ((TypeOfHLevel≡ n {X = _ , X} {Y = _ , Y} p
-- -- -- -- -- -- -- -- -- --            ∙ TypeOfHLevel≡ n {X = _ , Y} {Y = _ , Z} q) i₁))
-- -- -- -- -- -- -- -- -- --         (λ i₁ → snd (TypeOfHLevel≡ n {X = _ , X} {Y = _ , Z} (p ∙ q) i₁)) refl refl i i₁

-- -- -- -- -- -- -- -- -- --   TypeOfHLevel∙' : (n : HLevel) {X : TypeOfHLevel ℓ n} → (p : ⟨ X ⟩ ≡ ⟨ X ⟩) → (q : ⟨ X ⟩ ≡ ⟨ X ⟩) 
-- -- -- -- -- -- -- -- -- --                    →  TypeOfHLevel≡ n {X = X} {Y = X}  p
-- -- -- -- -- -- -- -- -- --                        ∙ TypeOfHLevel≡ n {X = X} {Y = X}  q ≡ TypeOfHLevel≡ n ( p ∙ q)
-- -- -- -- -- -- -- -- -- --   fst (TypeOfHLevel∙' n p q i i₁) = (p ∙ q) i₁
-- -- -- -- -- -- -- -- -- --   snd (TypeOfHLevel∙' n {_ , X} p q i i₁) =
-- -- -- -- -- -- -- -- -- --      isSet→SquareP (λ i i₁ → isProp→isSet (isPropIsOfHLevel {A = (p ∙ q) i₁} n))
-- -- -- -- -- -- -- -- -- --         (λ i₁ → snd ((TypeOfHLevel≡ n {X = _ , X} {Y = _ , X} p
-- -- -- -- -- -- -- -- -- --            ∙ TypeOfHLevel≡ n {X = _ , X} {Y = _ , X} q) i₁))
-- -- -- -- -- -- -- -- -- --         (λ i₁ → snd (TypeOfHLevel≡ n {X = _ , X} {Y = _ , X} (p ∙ q) i₁)) refl refl i i₁



-- -- -- -- -- -- -- -- -- --   -- AhSet≡ : ⟨ G ⟩ → Path (hSet ℓ) (A , isSetA) (A , isSetA)  
-- -- -- -- -- -- -- -- -- --   -- AhSet≡ = {!!}

-- -- -- -- -- -- -- -- -- --   AhSet≡ : A ≃ A → Path (hSet ℓ) (A , isSetA) (A , isSetA)
-- -- -- -- -- -- -- -- -- --   AhSet≡ = TypeOfHLevel≡ 2 ∘ ua


-- -- -- -- -- -- -- -- -- --   G≡ : (A ≃ A) → Path (hSet ℓ) (A , isSetA) (A , isSetA)  
-- -- -- -- -- -- -- -- -- --   G≡ = AhSet≡

-- -- -- -- -- -- -- -- -- --   GSq : (g h : A ≃ A) →
-- -- -- -- -- -- -- -- -- --       Square
-- -- -- -- -- -- -- -- -- --         (G≡ g)
-- -- -- -- -- -- -- -- -- --         (G≡ (g · h))
-- -- -- -- -- -- -- -- -- --         (λ j → A , isSetA)
-- -- -- -- -- -- -- -- -- --         (G≡ h)
-- -- -- -- -- -- -- -- -- --   GSq g h =
-- -- -- -- -- -- -- -- -- --     ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- --       ( (compPath-filler (ua (g)) (ua (h))) ▷
-- -- -- -- -- -- -- -- -- --         (sym (uaCompEquiv _ _)))

-- -- -- -- -- -- -- -- -- -- --   GSq-filler : (g h : fst G) → 
-- -- -- -- -- -- -- -- -- -- --          PathP (λ k → Square 
-- -- -- -- -- -- -- -- -- -- --                          (ua (fst m g))
-- -- -- -- -- -- -- -- -- -- --                          (((λ i → uaCompEquiv (fst m g) (fst m h) (~ i)) ∙
-- -- -- -- -- -- -- -- -- -- --                             (λ i → ua (snd m .IsGroupHom.pres· g h (~ i))))
-- -- -- -- -- -- -- -- -- -- --                            k)
-- -- -- -- -- -- -- -- -- -- --                          refl
-- -- -- -- -- -- -- -- -- -- --                          λ i → ua (fst m h) i)
-- -- -- -- -- -- -- -- -- -- --            ((compPath-filler (ua (fst m g)) (ua (fst m h))))
-- -- -- -- -- -- -- -- -- -- --            (λ i j → fst ((GSq g h) i j))
-- -- -- -- -- -- -- -- -- -- --   GSq-filler g h =
-- -- -- -- -- -- -- -- -- -- --    doubleWhiskFiller refl
-- -- -- -- -- -- -- -- -- -- --      (compPath-filler (ua (fst m g)) (ua (fst m h)))
-- -- -- -- -- -- -- -- -- -- --       ((sym (uaCompEquiv _ _) ∙ cong ua (sym ((snd m) .IsGroupHom.pres· g h))))

-- -- -- -- -- -- -- -- -- -- --   paP : (g : fst G) → PathP (λ j → fst (G≡ g j) → A) (idfun A) (invEq (fst m g))
-- -- -- -- -- -- -- -- -- -- --   paP g = sym (funExt (retEq (fst m g)))
-- -- -- -- -- -- -- -- -- -- --                    ◁ (λ j x → (invEq (fst m g)) (ua-unglue ((fst m) g) j x))

-- -- -- -- -- -- -- -- -- -- --   paP' : (g : fst G) → PathP (λ j → fst (G≡ g j) → A) (equivFun (fst m g)) (idfun _)
-- -- -- -- -- -- -- -- -- -- --   paP' g i = ua-unglue (fst m g) i

-- -- -- -- -- -- -- -- -- -- --   -- paP· : (g h : fst G) →
-- -- -- -- -- -- -- -- -- -- --   --            PathP (λ j → fst (G≡ (g · h) j) → A)
-- -- -- -- -- -- -- -- -- -- --   --             (equivFun (fst m h) ∘ equivFun (fst m g)) (idfun A)
-- -- -- -- -- -- -- -- -- -- --   -- paP· g h = {!M.pres· g h!}

-- -- -- -- -- -- -- -- -- -- --   -- unglueEMfam : (g h : fst G) → SquareP (λ i j → fst (GSq g h i j) → A)
-- -- -- -- -- -- -- -- -- -- --   --                 {idfun _} {invEq (fst m g)}
-- -- -- -- -- -- -- -- -- -- --   --                 (paP g)
-- -- -- -- -- -- -- -- -- -- --   --                 {idfun _} {invEq (fst m g) ∘ invEq (fst m h)}
-- -- -- -- -- -- -- -- -- -- --   --                 (paP (g · h) ▷ cong invEq (M.pres· g h))
-- -- -- -- -- -- -- -- -- -- --   --                 refl
-- -- -- -- -- -- -- -- -- -- --   --                 (congP (λ _ → invEq (fst m g) ∘_) (paP h))
                  
-- -- -- -- -- -- -- -- -- -- --   -- unglueEMfam = {!!}

-- -- -- -- -- -- -- -- -- -- --   -- unglueEMfam' : (g h : fst G) → SquareP (λ i j → fst (GSq g h i j) → A)
-- -- -- -- -- -- -- -- -- -- --   --                 {equivFun (fst m h) ∘ equivFun (fst m g)} {equivFun (fst m h)}
-- -- -- -- -- -- -- -- -- -- --   --                 (λ i → equivFun (fst m h) ∘ ua-unglue (fst m g) i)
-- -- -- -- -- -- -- -- -- -- --   --                 {equivFun (fst m h) ∘ equivFun (fst m g)} {idfun _}
-- -- -- -- -- -- -- -- -- -- --   --                 -- ({!(λ i → ua-unglue ( fst m h ∙) i)!} ▷ {!!})
-- -- -- -- -- -- -- -- -- -- --   --                 (cong fst (sym (M.pres· g h))
-- -- -- -- -- -- -- -- -- -- --   --                   ◁ (λ i → ua-unglue (fst m (g · h)) i))
-- -- -- -- -- -- -- -- -- -- --   --                 refl
-- -- -- -- -- -- -- -- -- -- --   --                 λ i → ua-unglue (fst m h) i
                  
-- -- -- -- -- -- -- -- -- -- --   -- unglueEMfam' = {!!}

-- -- -- -- -- -- -- -- -- -- --   glueP : ∀ g → PathP (λ j → A → fst (G≡ g j)) (idfun A) (fst (fst m g))
-- -- -- -- -- -- -- -- -- -- --   glueP g = (λ i a → ua-glue (fst m g) i
-- -- -- -- -- -- -- -- -- -- --       (λ { (i = i0) → a }) (inS (fst (fst m g) a)))
      
-- -- -- -- -- -- -- -- -- -- --   -- glueEMfam : (g h : fst G) → SquareP (λ i j → A → fst (GSq g h i j))
-- -- -- -- -- -- -- -- -- -- --   --                 {idfun _} {fst (fst m g)}
-- -- -- -- -- -- -- -- -- -- --   --                 (glueP g)
-- -- -- -- -- -- -- -- -- -- --   --                 {idfun _} {fst (fst m h) ∘ fst (fst m g)}
-- -- -- -- -- -- -- -- -- -- --   --                 (glueP (g · h) ▷ cong fst (M.pres· g h))
-- -- -- -- -- -- -- -- -- -- --   --                 refl
-- -- -- -- -- -- -- -- -- -- --   --                 (congP (λ _ → _∘ fst (fst m g)) (glueP h))
                  
-- -- -- -- -- -- -- -- -- -- --   -- glueEMfam g h = {!!}



-- -- -- -- -- -- -- -- -- --   EMG = EM₁ (Symmetric-Group _ isSetA)

-- -- -- -- -- -- -- -- -- --   EM₁HFam : EMG → hSet ℓ
-- -- -- -- -- -- -- -- -- --   EM₁HFam = elimEM (Symmetric-Group _ isSetA)
-- -- -- -- -- -- -- -- -- --    ( λ _ → isGroupoidHSet) (A , isSetA)
-- -- -- -- -- -- -- -- -- --         G≡ GSq


-- -- -- -- -- -- -- -- -- -- module EMΣ {ℓ ℓ'} {A : Type ℓ} {G : Group ℓ'} (isSetA : isSet A)
-- -- -- -- -- -- -- -- -- --              (m : GroupHom G (Symmetric-Group _ isSetA))
-- -- -- -- -- -- -- -- -- --               where

-- -- -- -- -- -- -- -- -- --   open GroupStr (snd G)
-- -- -- -- -- -- -- -- -- --   module M = IsGroupHom (snd m)

  

-- -- -- -- -- -- -- -- -- --   actR : A → A → Type (ℓ-max ℓ ℓ')
-- -- -- -- -- -- -- -- -- --   actR x y = Σ ⟨ G ⟩ λ g → y ≡ fst (fst m g) x 

-- -- -- -- -- -- -- -- -- --   actRTrans : ∀ x y z → actR x y → actR y z → actR x z 
-- -- -- -- -- -- -- -- -- --   actRTrans x y z (g , p) (h , q) = (g · h) ,
-- -- -- -- -- -- -- -- -- --     q ∙∙ cong (fst (fst m h)) p ∙∙ sym (funExt⁻ (cong fst (M.pres· g h)) x)



-- -- -- -- -- -- -- -- -- -- -- TypeOfHLevel≡ : (n : HLevel) {X Y : TypeOfHLevel ℓ n} → ⟨ X ⟩ ≡ ⟨ Y ⟩ → X ≡ Y

  
-- -- -- -- -- -- -- -- -- --   TypeOfHLevel∙ : (n : HLevel) {X Y Z : TypeOfHLevel ℓ n} → (p : ⟨ X ⟩ ≡ ⟨ Y ⟩) → (q : ⟨ Y ⟩ ≡ ⟨ Z ⟩) 
-- -- -- -- -- -- -- -- -- --                    →  TypeOfHLevel≡ n {X = X} {Y = Y}  p
-- -- -- -- -- -- -- -- -- --                        ∙ TypeOfHLevel≡ n {X = Y} {Y = Z}  q ≡ TypeOfHLevel≡ n ( p ∙ q)
-- -- -- -- -- -- -- -- -- --   fst (TypeOfHLevel∙ n p q i i₁) = (p ∙ q) i₁
-- -- -- -- -- -- -- -- -- --   snd (TypeOfHLevel∙ n {_ , X} {_ , Y} {_ , Z} p q i i₁) =
-- -- -- -- -- -- -- -- -- --      isSet→SquareP (λ i i₁ → isProp→isSet (isPropIsOfHLevel {A = (p ∙ q) i₁} n))
-- -- -- -- -- -- -- -- -- --         (λ i₁ → snd ((TypeOfHLevel≡ n {X = _ , X} {Y = _ , Y} p
-- -- -- -- -- -- -- -- -- --            ∙ TypeOfHLevel≡ n {X = _ , Y} {Y = _ , Z} q) i₁))
-- -- -- -- -- -- -- -- -- --         (λ i₁ → snd (TypeOfHLevel≡ n {X = _ , X} {Y = _ , Z} (p ∙ q) i₁)) refl refl i i₁

-- -- -- -- -- -- -- -- -- --   TypeOfHLevel∙' : (n : HLevel) {X : TypeOfHLevel ℓ n} → (p : ⟨ X ⟩ ≡ ⟨ X ⟩) → (q : ⟨ X ⟩ ≡ ⟨ X ⟩) 
-- -- -- -- -- -- -- -- -- --                    →  TypeOfHLevel≡ n {X = X} {Y = X}  p
-- -- -- -- -- -- -- -- -- --                        ∙ TypeOfHLevel≡ n {X = X} {Y = X}  q ≡ TypeOfHLevel≡ n ( p ∙ q)
-- -- -- -- -- -- -- -- -- --   fst (TypeOfHLevel∙' n p q i i₁) = (p ∙ q) i₁
-- -- -- -- -- -- -- -- -- --   snd (TypeOfHLevel∙' n {_ , X} p q i i₁) =
-- -- -- -- -- -- -- -- -- --      isSet→SquareP (λ i i₁ → isProp→isSet (isPropIsOfHLevel {A = (p ∙ q) i₁} n))
-- -- -- -- -- -- -- -- -- --         (λ i₁ → snd ((TypeOfHLevel≡ n {X = _ , X} {Y = _ , X} p
-- -- -- -- -- -- -- -- -- --            ∙ TypeOfHLevel≡ n {X = _ , X} {Y = _ , X} q) i₁))
-- -- -- -- -- -- -- -- -- --         (λ i₁ → snd (TypeOfHLevel≡ n {X = _ , X} {Y = _ , X} (p ∙ q) i₁)) refl refl i i₁



-- -- -- -- -- -- -- -- -- --   -- AhSet≡ : ⟨ G ⟩ → Path (hSet ℓ) (A , isSetA) (A , isSetA)  
-- -- -- -- -- -- -- -- -- --   -- AhSet≡ = {!!}

-- -- -- -- -- -- -- -- -- --   AhSet≡ : A ≃ A → Path (hSet ℓ) (A , isSetA) (A , isSetA)
-- -- -- -- -- -- -- -- -- --   AhSet≡ = TypeOfHLevel≡ 2 ∘ ua


-- -- -- -- -- -- -- -- -- --   G≡ : ⟨ G ⟩ → Path (hSet ℓ) (A , isSetA) (A , isSetA)  
-- -- -- -- -- -- -- -- -- --   G≡ = AhSet≡ ∘ (fst m)

-- -- -- -- -- -- -- -- -- --   GSq : (g h : fst G) →
-- -- -- -- -- -- -- -- -- --       Square
-- -- -- -- -- -- -- -- -- --         (G≡ g)
-- -- -- -- -- -- -- -- -- --         (G≡ (g · h))
-- -- -- -- -- -- -- -- -- --         (λ j → A , isSetA)
-- -- -- -- -- -- -- -- -- --         (G≡ h)
-- -- -- -- -- -- -- -- -- --   GSq g h =
-- -- -- -- -- -- -- -- -- --     ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- --       ( (compPath-filler (ua (fst m g)) (ua (fst m h))) ▷
-- -- -- -- -- -- -- -- -- --         (sym (uaCompEquiv _ _) ∙ cong ua (sym ((snd m) .IsGroupHom.pres· g h))))

-- -- -- -- -- -- -- -- -- --   GSq-filler : (g h : fst G) → 
-- -- -- -- -- -- -- -- -- --          PathP (λ k → Square 
-- -- -- -- -- -- -- -- -- --                          (ua (fst m g))
-- -- -- -- -- -- -- -- -- --                          (((λ i → uaCompEquiv (fst m g) (fst m h) (~ i)) ∙
-- -- -- -- -- -- -- -- -- --                             (λ i → ua (snd m .IsGroupHom.pres· g h (~ i))))
-- -- -- -- -- -- -- -- -- --                            k)
-- -- -- -- -- -- -- -- -- --                          refl
-- -- -- -- -- -- -- -- -- --                          λ i → ua (fst m h) i)
-- -- -- -- -- -- -- -- -- --            ((compPath-filler (ua (fst m g)) (ua (fst m h))))
-- -- -- -- -- -- -- -- -- --            (λ i j → fst ((GSq g h) i j))
-- -- -- -- -- -- -- -- -- --   GSq-filler g h =
-- -- -- -- -- -- -- -- -- --    doubleWhiskFiller refl
-- -- -- -- -- -- -- -- -- --      (compPath-filler (ua (fst m g)) (ua (fst m h)))
-- -- -- -- -- -- -- -- -- --       ((sym (uaCompEquiv _ _) ∙ cong ua (sym ((snd m) .IsGroupHom.pres· g h))))

-- -- -- -- -- -- -- -- -- --   paP : (g : fst G) → PathP (λ j → fst (G≡ g j) → A) (idfun A) (invEq (fst m g))
-- -- -- -- -- -- -- -- -- --   paP g = sym (funExt (retEq (fst m g)))
-- -- -- -- -- -- -- -- -- --                    ◁ (λ j x → (invEq (fst m g)) (ua-unglue ((fst m) g) j x))

-- -- -- -- -- -- -- -- -- --   paP' : (g : fst G) → PathP (λ j → fst (G≡ g j) → A) (equivFun (fst m g)) (idfun _)
-- -- -- -- -- -- -- -- -- --   paP' g i = ua-unglue (fst m g) i

-- -- -- -- -- -- -- -- -- --   -- paP· : (g h : fst G) →
-- -- -- -- -- -- -- -- -- --   --            PathP (λ j → fst (G≡ (g · h) j) → A)
-- -- -- -- -- -- -- -- -- --   --             (equivFun (fst m h) ∘ equivFun (fst m g)) (idfun A)
-- -- -- -- -- -- -- -- -- --   -- paP· g h = {!M.pres· g h!}

-- -- -- -- -- -- -- -- -- --   -- unglueEMfam : (g h : fst G) → SquareP (λ i j → fst (GSq g h i j) → A)
-- -- -- -- -- -- -- -- -- --   --                 {idfun _} {invEq (fst m g)}
-- -- -- -- -- -- -- -- -- --   --                 (paP g)
-- -- -- -- -- -- -- -- -- --   --                 {idfun _} {invEq (fst m g) ∘ invEq (fst m h)}
-- -- -- -- -- -- -- -- -- --   --                 (paP (g · h) ▷ cong invEq (M.pres· g h))
-- -- -- -- -- -- -- -- -- --   --                 refl
-- -- -- -- -- -- -- -- -- --   --                 (congP (λ _ → invEq (fst m g) ∘_) (paP h))
                  
-- -- -- -- -- -- -- -- -- --   -- unglueEMfam = {!!}

-- -- -- -- -- -- -- -- -- --   -- unglueEMfam' : (g h : fst G) → SquareP (λ i j → fst (GSq g h i j) → A)
-- -- -- -- -- -- -- -- -- --   --                 {equivFun (fst m h) ∘ equivFun (fst m g)} {equivFun (fst m h)}
-- -- -- -- -- -- -- -- -- --   --                 (λ i → equivFun (fst m h) ∘ ua-unglue (fst m g) i)
-- -- -- -- -- -- -- -- -- --   --                 {equivFun (fst m h) ∘ equivFun (fst m g)} {idfun _}
-- -- -- -- -- -- -- -- -- --   --                 -- ({!(λ i → ua-unglue ( fst m h ∙) i)!} ▷ {!!})
-- -- -- -- -- -- -- -- -- --   --                 (cong fst (sym (M.pres· g h))
-- -- -- -- -- -- -- -- -- --   --                   ◁ (λ i → ua-unglue (fst m (g · h)) i))
-- -- -- -- -- -- -- -- -- --   --                 refl
-- -- -- -- -- -- -- -- -- --   --                 λ i → ua-unglue (fst m h) i
                  
-- -- -- -- -- -- -- -- -- --   -- unglueEMfam' = {!!}

-- -- -- -- -- -- -- -- -- --   glueP : ∀ g → PathP (λ j → A → fst (G≡ g j)) (idfun A) (fst (fst m g))
-- -- -- -- -- -- -- -- -- --   glueP g = (λ i a → ua-glue (fst m g) i
-- -- -- -- -- -- -- -- -- --       (λ { (i = i0) → a }) (inS (fst (fst m g) a)))
      
-- -- -- -- -- -- -- -- -- --   -- glueEMfam : (g h : fst G) → SquareP (λ i j → A → fst (GSq g h i j))
-- -- -- -- -- -- -- -- -- --   --                 {idfun _} {fst (fst m g)}
-- -- -- -- -- -- -- -- -- --   --                 (glueP g)
-- -- -- -- -- -- -- -- -- --   --                 {idfun _} {fst (fst m h) ∘ fst (fst m g)}
-- -- -- -- -- -- -- -- -- --   --                 (glueP (g · h) ▷ cong fst (M.pres· g h))
-- -- -- -- -- -- -- -- -- --   --                 refl
-- -- -- -- -- -- -- -- -- --   --                 (congP (λ _ → _∘ fst (fst m g)) (glueP h))
                  
-- -- -- -- -- -- -- -- -- --   -- glueEMfam g h = {!!}



-- -- -- -- -- -- -- -- -- --   EMG = EM₁ G

-- -- -- -- -- -- -- -- -- --   EM₁HFam : EMG → hSet ℓ
-- -- -- -- -- -- -- -- -- --   EM₁HFam = EMrec.f w
-- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- --      w : EMrec G isGroupoidHSet
-- -- -- -- -- -- -- -- -- --      EMrec.b w = A , isSetA
-- -- -- -- -- -- -- -- -- --      EMrec.bloop w = G≡ 
-- -- -- -- -- -- -- -- -- --      EMrec.bComp w = GSq


-- -- -- -- -- -- -- -- -- -- -- -- --   EM₁HFam : EMG → hSet ℓ
-- -- -- -- -- -- -- -- -- -- -- -- --   EM₁HFam = elimEM G
-- -- -- -- -- -- -- -- -- -- -- -- --    ( λ _ → isGroupoidHSet) (A , isSetA)
-- -- -- -- -- -- -- -- -- -- -- -- --         (TypeOfHLevel≡ 2 ∘ ua ∘ fst m )
-- -- -- -- -- -- -- -- -- -- -- -- --            λ g h → compPath-filler _ _
-- -- -- -- -- -- -- -- -- -- -- -- --              ▷
-- -- -- -- -- -- -- -- -- -- -- -- --                 (TypeOfHLevel∙' 2 {X = A , isSetA} (ua (fst m g)) (ua (fst m h)))
-- -- -- -- -- -- -- -- -- -- -- -- --               ∙ cong (TypeOfHLevel≡ 2) (sym (uaCompEquiv _ _)
-- -- -- -- -- -- -- -- -- -- -- -- --              ∙ cong ua ( sym ((snd m) .IsGroupHom.pres· g h)))

-- -- -- -- -- -- -- -- -- --   EM₁Fam : EMG → Type ℓ
-- -- -- -- -- -- -- -- -- --   EM₁Fam = fst ∘ EM₁HFam


-- -- -- -- -- -- -- -- -- -- -- -- --   -- record EMTrunc : Type {!ℓ!} where
-- -- -- -- -- -- -- -- -- -- -- -- --   --   field
-- -- -- -- -- -- -- -- -- -- -- -- --   --     loop : EMG
-- -- -- -- -- -- -- -- -- -- -- -- --   --     val : ⟨ EM₁Fam loop ⟩ 

-- -- -- -- -- -- -- -- -- --   EMtrunc = Σ EMG EM₁Fam

-- -- -- -- -- -- -- -- -- --   vanTrunc : Type (ℓ-max ℓ ℓ')
-- -- -- -- -- -- -- -- -- --   vanTrunc = A // actRTrans

-- -- -- -- -- -- -- -- -- --   -- module recEMtrunc2 {ℓ'} {B : Type ℓ'} (truncB : isGroupoid B)
-- -- -- -- -- -- -- -- -- --   --                   (b : A → B)
-- -- -- -- -- -- -- -- -- --   --                   (p₀ : (g : ⟨ G ⟩) → (a : A) → singl (b a))
-- -- -- -- -- -- -- -- -- --   --                   (bIds : GroupHom G (idEquivsG B))
-- -- -- -- -- -- -- -- -- --   --                   where

-- -- -- -- -- -- -- -- -- --   --   fp : (g : fst G) → (a : A) → Path (singl (b a)) (_ , refl) (_ , refl) 
-- -- -- -- -- -- -- -- -- --   --   fp g a = ΣPathP ({!!} , {!!})

-- -- -- -- -- -- -- -- -- --   --   f : EMG → (a : A) → singl (b a)
-- -- -- -- -- -- -- -- -- --   --   f = elimSet G
-- -- -- -- -- -- -- -- -- --   --    (λ _ → isSetΠ λ _ → isProp→isSet isPropSingl)
-- -- -- -- -- -- -- -- -- --   --    (λ _ → _ , refl)
-- -- -- -- -- -- -- -- -- --   --    (funExt ∘ fp)
-- -- -- -- -- -- -- -- -- --   --    -- λ g → funExt λ a → ΣPathP ({!cong fst (snd ((fst bIds) g)) !} , {!!}) 


-- -- -- -- -- -- -- -- -- -- -- funExtDepSq : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} (B : A → Type ℓ') (C : Type ℓ'')
-- -- -- -- -- -- -- -- -- -- --                 → (aSq : I → I → A)
-- -- -- -- -- -- -- -- -- -- --          {a₀₀ : B (aSq i0 i0) → C} {a₀₁ : B (aSq i0 i1) → C}
-- -- -- -- -- -- -- -- -- -- --           (a₀₋ : PathP (λ j → B (aSq i0 j) → C) a₀₀ a₀₁)
-- -- -- -- -- -- -- -- -- -- --          {a₁₀ : B (aSq i1 i0) → C} {a₁₁ : B (aSq i1 i1) → C}
-- -- -- -- -- -- -- -- -- -- --          (a₁₋ : PathP (λ j → B (aSq i1 j) → C) a₁₀ a₁₁)
-- -- -- -- -- -- -- -- -- -- --          (a₋₀ : PathP (λ i → B (aSq i i0) → C) a₀₀ a₁₀)
-- -- -- -- -- -- -- -- -- -- --          (a₋₁ : PathP (λ i → B (aSq i i1) → C) a₀₁ a₁₁) 
-- -- -- -- -- -- -- -- -- -- --                 → (

-- -- -- -- -- -- -- -- -- -- --                 SquareP (λ i j → B (aSq i j))
-- -- -- -- -- -- -- -- -- -- --                      {!!} {!!} {!!} {!!}
                     
-- -- -- -- -- -- -- -- -- -- --                      -- a₀₋
-- -- -- -- -- -- -- -- -- -- --                      -- a₁₋
-- -- -- -- -- -- -- -- -- -- --                      -- a₋₀
-- -- -- -- -- -- -- -- -- -- --                      -- a₋₁
-- -- -- -- -- -- -- -- -- -- --                   → Square {A = C}
-- -- -- -- -- -- -- -- -- -- --                       {!!}
-- -- -- -- -- -- -- -- -- -- --                       {!!}
-- -- -- -- -- -- -- -- -- -- --                       {!!}
-- -- -- -- -- -- -- -- -- -- --                       {!!})
-- -- -- -- -- -- -- -- -- -- --                 → SquareP (λ i j → B (aSq i j) → C)
-- -- -- -- -- -- -- -- -- -- --                    a₀₋ a₁₋ a₋₀ a₋₁                     
-- -- -- -- -- -- -- -- -- -- -- funExtDepSq = {!!}




-- -- -- -- -- -- -- -- -- -- -- module recEMtrunc→ {ℓ ℓ'} {A : Type ℓ} (isSetA : isSet A)
-- -- -- -- -- -- -- -- -- -- --                           {B : Type ℓ'} (isGrpB : isGroupoid B)
-- -- -- -- -- -- -- -- -- -- --              -- (m : GroupHom G (idEquivsG A))
-- -- -- -- -- -- -- -- -- -- --              -- (C : Type ℓc) (isSetC : isSet C)
-- -- -- -- -- -- -- -- -- -- --              -- {ℓ''} {B : Type ℓ''} (truncB : isGroupoid B)
-- -- -- -- -- -- -- -- -- -- --              where
             
-- -- -- -- -- -- -- -- -- -- --   module EMa = EMΣ isSetA idGroupHom

-- -- -- -- -- -- -- -- -- -- --   EMG = EMa.EMG

-- -- -- -- -- -- -- -- -- -- --   EM₁Fam : EMG → Type (ℓ-max ℓ ℓ')
-- -- -- -- -- -- -- -- -- -- --   EM₁Fam x = EMa.EM₁Fam x → B

-- -- -- -- -- -- -- -- -- -- --   emΣ = Σ EMG EM₁Fam

-- -- -- -- -- -- -- -- -- -- --   isGroupoidEmΣ : isGroupoid emΣ
-- -- -- -- -- -- -- -- -- -- --   isGroupoidEmΣ = isGroupoidΣ emsquash λ _ → isGroupoidΠ λ _ → isGrpB

-- -- -- -- -- -- -- -- -- -- --   record _↔ₛ_ (x y : A → B) : Type (ℓ-max ℓ ℓ') where
-- -- -- -- -- -- -- -- -- -- --     constructor ↔s
-- -- -- -- -- -- -- -- -- -- --     field
-- -- -- -- -- -- -- -- -- -- --       F≃ : (A ≃ A)
-- -- -- -- -- -- -- -- -- -- --       l≡ : x  ≡ y ∘ fst F≃

-- -- -- -- -- -- -- -- -- -- --   isTrans↔ₛ : BinaryRelation.isTrans _↔ₛ_
-- -- -- -- -- -- -- -- -- -- --   isTrans↔ₛ a b c (↔s e p) (↔s f q) = 
-- -- -- -- -- -- -- -- -- -- --     ↔s (e ∙ₑ f) (p ∙ cong (_∘ (fst e)) q)

-- -- -- -- -- -- -- -- -- -- -- --   -- record _↔ₛ_ (x y : A → B) : Type (ℓ-max ℓ ℓ') where
-- -- -- -- -- -- -- -- -- -- -- --   --   constructor ↔s
-- -- -- -- -- -- -- -- -- -- -- --   --   field
-- -- -- -- -- -- -- -- -- -- -- --   --     F≃ : (A ≃ A)
-- -- -- -- -- -- -- -- -- -- -- --   --     l≡ : PathP (λ i → ua F≃ i → B) x y

-- -- -- -- -- -- -- -- -- -- -- --   -- isTrans↔ₛ : BinaryRelation.isTrans _↔ₛ_
-- -- -- -- -- -- -- -- -- -- -- --   -- isTrans↔ₛ a b c (↔s e p) (↔s f q) =
-- -- -- -- -- -- -- -- -- -- -- --   --   ↔s (e ∙ₑ f) ({!!} ◁ {!!} ▷ {!!})


-- -- -- -- -- -- -- -- -- -- --   A→// : Type (ℓ-max ℓ ℓ')
-- -- -- -- -- -- -- -- -- -- --   A→// = (A → B) // isTrans↔ₛ

-- -- -- -- -- -- -- -- -- -- --   fromPathP→ : (g : A ≃ A) {x₀ x₁ : A → B} →
-- -- -- -- -- -- -- -- -- -- --                 PathP (λ z → ua g z → B) x₀ x₁
-- -- -- -- -- -- -- -- -- -- --                 → x₀ ≡ (x₁ ∘ (fst g))
-- -- -- -- -- -- -- -- -- -- --   fromPathP→ g p i a = p i (ua-gluePath g (refl {x = (fst g) a}) i) 
    
-- -- -- -- -- -- -- -- -- -- --   loopP : ∀ g → PathP (λ i → (ua g i → B) → A→//) [_]// [_]//
-- -- -- -- -- -- -- -- -- -- --   loopP g =     
-- -- -- -- -- -- -- -- -- -- --     (λ i f  → [ f ∘ EMa.glueP g i ]// ) ▷
-- -- -- -- -- -- -- -- -- -- --     funExt λ x → eq// {a = x ∘ fst g} {x} (↔s g refl)
    
-- -- -- -- -- -- -- -- -- -- --     -- λ i f → 
-- -- -- -- -- -- -- -- -- -- --     --  eq// {a = {!f ∘ fst g!}}
-- -- -- -- -- -- -- -- -- -- --     --       {b = {!!}} (↔s g {!!}) i


  

-- -- -- -- -- -- -- -- -- -- --   to// : (x : EMG) (y : EMa.EM₁Fam x → B) → A→//
-- -- -- -- -- -- -- -- -- -- --   to// = elimEM _ (λ _ → isGroupoidΠ λ _ → squash//)
-- -- -- -- -- -- -- -- -- -- --     [_]//
-- -- -- -- -- -- -- -- -- -- --     loopP
-- -- -- -- -- -- -- -- -- -- --      zz  
-- -- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- -- --       -- zzR :
-- -- -- -- -- -- -- -- -- -- --       --    SquareP (λ i j → EM₁Fam (emcomp (idEquiv A) (idEquiv A) i j) → A→//)
-- -- -- -- -- -- -- -- -- -- --       --      (loopP (idEquiv A))
-- -- -- -- -- -- -- -- -- -- --       --    (loopP ((Symmetric-Group A isSetA .snd GroupStr.· (idEquiv A)) (idEquiv A)))
-- -- -- -- -- -- -- -- -- -- --       --    (λ j → [_]//) (loopP (idEquiv A))
-- -- -- -- -- -- -- -- -- -- --       -- zzR = {!!}


-- -- -- -- -- -- -- -- -- -- --       zz' : (g h : A ≃ A) →
-- -- -- -- -- -- -- -- -- -- --          SquareP (λ i j → (EMa.EM₁Fam (emcomp g h i j) → B) → A→//)
-- -- -- -- -- -- -- -- -- -- --           ((λ i f →  [ f ∘ EMa.glueP g i ]//))
-- -- -- -- -- -- -- -- -- -- --           (λ i f → [ f ∘ (EMa.glueP (g ∙ₑ h)) i ]// )
-- -- -- -- -- -- -- -- -- -- --            refl
           
-- -- -- -- -- -- -- -- -- -- --             λ i f →  [ f ∘ EMa.glueP h i ∘ fst g ]// 
-- -- -- -- -- -- -- -- -- -- --            -- (congP (λ _ z → _∘ {!(z ∘ g)!}) (EMa.glueP h))
-- -- -- -- -- -- -- -- -- -- --       zz' g h = {!!}
-- -- -- -- -- -- -- -- -- -- --         -- [ f ∘ (EMa.glueEMfam g h i j) ]//
-- -- -- -- -- -- -- -- -- -- --         -- -- {!!} ∘ {!(_∘ (EMa.glueEMfam g h i j))!}

-- -- -- -- -- -- -- -- -- -- --       zz : (g h : A ≃ A) →
-- -- -- -- -- -- -- -- -- -- --          SquareP (λ i j → EM₁Fam (emcomp g h i j) → A→//) (loopP g)
-- -- -- -- -- -- -- -- -- -- --          (loopP ((Symmetric-Group A isSetA .snd GroupStr.· g) h))
-- -- -- -- -- -- -- -- -- -- --          (λ j → [_]//) (loopP h)
-- -- -- -- -- -- -- -- -- -- --       zz g h i j f = {!!}
-- -- -- -- -- -- -- -- -- -- --         -- {!!} ∘ {!(_∘ (EMa.glueEMfam g h i j))!}
-- -- -- -- -- -- -- -- -- -- --       -- funExtDepSq _ _ _ _
-- -- -- -- -- -- -- -- -- -- --       --   λ {_} {_} {a₀₋} {_} {_} {_} {_} {a₋₁}
-- -- -- -- -- -- -- -- -- -- --       --     sqA → {!!} ▷
-- -- -- -- -- -- -- -- -- -- --       --       λ j → {!(λ i →
-- -- -- -- -- -- -- -- -- -- --       --    loopP ((Symmetric-Group A isSetA .snd GroupStr.· g) h) i (a₁₋ i))!}
          
-- -- -- -- -- -- -- -- -- -- --         --{!compPath-filler ? ?!} ▷ {!!}
-- -- -- -- -- -- -- -- -- -- --         -- (hcomp
-- -- -- -- -- -- -- -- -- -- --         --     (λ k →
-- -- -- -- -- -- -- -- -- -- --         --        λ {
-- -- -- -- -- -- -- -- -- -- --         --          (i = i0) → {!!}               
-- -- -- -- -- -- -- -- -- -- --         --        ; (i = i1) → {!!}
-- -- -- -- -- -- -- -- -- -- --         --        ; (j = i0) → {!!}
-- -- -- -- -- -- -- -- -- -- --         --        ; (j = i1) → {!!}
-- -- -- -- -- -- -- -- -- -- --         --        }) {!!}) ∘ 
-- -- -- -- -- -- -- -- -- -- --         -- {!EMa.unglueEMfam g h i j!}



-- -- -- -- -- -- -- -- -- -- --   loopP⁻ : (g : A ≃ A) {x₀ x₁ : A → B}
-- -- -- -- -- -- -- -- -- -- --               → x₀ ≡ x₁ ∘ fst g
-- -- -- -- -- -- -- -- -- -- --               → PathP (λ i → ua g i → B)
-- -- -- -- -- -- -- -- -- -- --                   x₀ x₁               
-- -- -- -- -- -- -- -- -- -- --   loopP⁻ g {x₀} {x₁} p =
-- -- -- -- -- -- -- -- -- -- --     sym (cong (x₀ ∘_) (funExt (retEq g)))
-- -- -- -- -- -- -- -- -- -- --     ◁ (λ i → p i ∘ invEq g ∘ ua-unglue g i) ▷
-- -- -- -- -- -- -- -- -- -- --      cong (x₁ ∘_) (funExt (secEq g))


-- -- -- -- -- -- -- -- -- -- -- -- isGroupoidEmΣ
-- -- -- -- -- -- -- -- -- -- --   from// : A→// → emΣ
-- -- -- -- -- -- -- -- -- -- --   from// = rec// _ isGroupoidEmΣ
-- -- -- -- -- -- -- -- -- -- --     (embase ,_) p//
-- -- -- -- -- -- -- -- -- -- --      λ r s → compPath-filler _ _ ▷ p//∙ r s

-- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- --       p// : {a b : A → B} → a ↔ₛ b → (embase , a) ≡ (embase , b)
-- -- -- -- -- -- -- -- -- -- --       p// (↔s e p) = ΣPathP ((emloop e) , loopP⁻ e p)

-- -- -- -- -- -- -- -- -- -- --       p//∙ : {a b c : A → B} (r : a ↔ₛ b) (s : b ↔ₛ c) →
-- -- -- -- -- -- -- -- -- -- --                 p// r ∙ p// s
-- -- -- -- -- -- -- -- -- -- --                 ≡
-- -- -- -- -- -- -- -- -- -- --                 (p// (isTrans↔ₛ _ _ _ r s)) 
-- -- -- -- -- -- -- -- -- -- --       p//∙ {a} {b} {c} (↔s e p) (↔s f q) = ΣPathP∙ _ _ _ _
-- -- -- -- -- -- -- -- -- -- --         ∙ cong ΣPathP w
-- -- -- -- -- -- -- -- -- -- --         where
 
-- -- -- -- -- -- -- -- -- -- --           ww : SquareP
-- -- -- -- -- -- -- -- -- -- --                   (λ i j → EMa.EM₁Fam
-- -- -- -- -- -- -- -- -- -- --              (emloop-comp (Symmetric-Group A isSetA) e
-- -- -- -- -- -- -- -- -- -- --               f (~ i) j) →
-- -- -- -- -- -- -- -- -- -- --              B)
-- -- -- -- -- -- -- -- -- -- --              (compPathP→ (EMa.EM₁Fam) (loopP⁻ e p) (loopP⁻ f q))
-- -- -- -- -- -- -- -- -- -- --              (loopP⁻ (e ∙ₑ f) (p ∙ cong (_∘ fst e) q))
-- -- -- -- -- -- -- -- -- -- --              refl refl
-- -- -- -- -- -- -- -- -- -- --           ww i j = {!!}

-- -- -- -- -- -- -- -- -- -- --           w : ((emloop e) ∙ (emloop f) , compPathP→ (EMa.EM₁Fam) (loopP⁻ e p)
-- -- -- -- -- -- -- -- -- -- --                  (loopP⁻ f q))
-- -- -- -- -- -- -- -- -- -- --                 ≡
-- -- -- -- -- -- -- -- -- -- --                 ((emloop ( e ∙ₑ f)) ,
-- -- -- -- -- -- -- -- -- -- --                  (loopP⁻ (e ∙ₑ f) (p ∙ cong (_∘ (fst e)) q)))
-- -- -- -- -- -- -- -- -- -- --           fst (w i) = (emloop-comp _ e f) (~ i)
-- -- -- -- -- -- -- -- -- -- --           snd (w i) j = ww i j
          
-- -- -- -- -- -- -- -- -- -- -- --   iso-em-// : Iso emΣ A→//
-- -- -- -- -- -- -- -- -- -- -- --   Iso.fun iso-em-// = uncurry to//
-- -- -- -- -- -- -- -- -- -- -- --   Iso.inv iso-em-// = from//
-- -- -- -- -- -- -- -- -- -- -- --   Iso.rightInv iso-em-// =
-- -- -- -- -- -- -- -- -- -- -- --     elimSet// _ (λ _ → squash// _ _)
-- -- -- -- -- -- -- -- -- -- -- --      (λ _ → refl) λ {a} {b} r → {!!}
-- -- -- -- -- -- -- -- -- -- -- --   Iso.leftInv iso-em-// =
-- -- -- -- -- -- -- -- -- -- -- --      uncurry (elimSet _ (λ _ → isSetΠ λ _ → isGroupoidEmΣ _ _)
-- -- -- -- -- -- -- -- -- -- -- --       (λ _ → refl) {!!})
 
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- open GroupStr (snd G)  
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- module M = IsGroupHom (snd m)

-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- relIdEq : A → A → Type (ℓ-max ℓ ℓ')
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- relIdEq x y = Σ ⟨ G ⟩  λ g → fst (fst ((fst m) g)) x ≡  y 

-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- -- relIdEq' : A → A → Type (ℓ-max ℓ ℓ')
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- -- relIdEq' x y = ⟨ G ⟩ × (x ≡ y) 


-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- relIdEqTrans : BinaryRelation.isTrans relIdEq
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- relIdEqTrans a b c (g , p) (h , q) =
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --   (g · h) , ( (funExt⁻ (cong (fst ∘ fst) (M.pres· g h)) a) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- --   --     cong (fst (fst (fst m h))) p ) ∙ q

-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- RelId// =  (_//_ A {R = relIdEq} relIdEqTrans)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module recEMtrunc→More {ℓ ℓ'} {A : Type ℓ} {G : Group ℓ'} (isGrpA : isGroupoid A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (m : GroupHom G (idEquivsG A))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --             where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open GroupStr (snd G)  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   module M = IsGroupHom (snd m)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   module M/ = recEMtrunc→ isGrpA m

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mr : GroupHom G (idEquivsG A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst mr _ = _ , refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   IsGroupHom.pres· (snd mr) = λ _ _ → isPropSingl _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   IsGroupHom.pres1 (snd mr) = isPropSingl _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   IsGroupHom.presinv (snd mr) = λ _ → isPropSingl _ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mr=m : mr ≡ m
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mr=m = GroupHom≡ (funExt λ _ → isPropSingl _ _)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   module M/r = recEMtrunc→ isGrpA mr

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ≡r// : Iso (EM₁ G × A) M/r.RelId//
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.fun ≡r// (_ , a) = [ a ]//
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.inv ≡r// =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     rec// _ {!!} (embase ,_) (λ (g , p) → cong₂ _,_ (emloop g) p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       λ gp hq →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         let (g , p) = gp
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (h , q) = hq
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         in (λ i j → (emcomp  g h i j  , compPath-filler p q i j)) ▷
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --           cong (cong₂ _,_ (emloop (g · h)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (( GL.lUnit _ ∙ cong (_∙ (p ∙ q))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (compPathRefl ∙ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --             )) ∙ GL.assoc _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --           -- λ i → cong₂ _,_ (emloop (g · h)) {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.rightInv ≡r// = elimSet//
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    _ (λ _ → squash// _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ a → refl) λ (g , p) → λ i i₁ → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.leftInv ≡r// = uncurry (flip (λ x → elimSet _ (λ _ → {!!}) (refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      λ g → toPathP λ i i₁ → {!!} , x))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- -- relIdEqTrans' : BinaryRelation.isTrans relIdEq'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- -- relIdEqTrans' a b c (g , p) (h , q) = (g · h) , ((refl ∙ p) ∙ q)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- --   -- (g · h) , ( (funExt⁻ (cong (fst ∘ fst) (M.pres· g h)) a) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- --   --   cong (fst (fst (fst m h))) p ) ∙ q

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- -- zz : A // relIdEqTrans → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- -- zz = rec// _ isGrpA (idfun _) (λ (g , p) → funExt⁻ (cong fst (snd (fst m g))) _ ∙ p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Eq≡Eq' : (_//_ A {R = relIdEq} relIdEqTrans) ≡ (_//_ A {R = relIdEq'} relIdEqTrans')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Eq≡Eq' i = _//_ A {R = λ x y → Σ ⟨ G ⟩ λ g → cong fst (snd ((fst m) g)) (~ i) x ≡ y }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   λ a b c (g , p) (h , q) → (g · h) , λ i₁ → {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- iso// : Iso (EM₁ G × A) (_//_ A {R = relIdEq} relIdEqTrans)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Iso.fun iso// = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Iso.inv iso// = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Iso.rightInv iso// = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Iso.leftInv iso// = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module recEMtrunc→ {ℓ ℓ' ℓc} {A : Type ℓ} {G : Group ℓ'} (isSetA : isSet A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (m : GroupHom G (Symmetric-Group _ isSetA))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (C : Type ℓc) (isSetC : isSet C)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              {ℓ''} {B : Type ℓ''} (truncB : isGroupoid B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open EMΣ _ (SymmetricGroup→Hom {A = A} {isSetA = isSetA} isSetC )

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   module recEMΣ (b : (y : A → C) → B) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     bP : (g : A ≃ A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            PathP (λ i → (y : ua (preCompEquiv {C = C} (invEquiv g)) i) → B) b b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     bP g i x = {!b (ua-unglue (preCompEquiv {C = C} (invEquiv g)) i x)!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- {!funTypeTransp ? ? ? ?!} ▷ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- toPathP ({!funTypeTransp   !} ∙ {!!})

    

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- f : EMtrunc → B
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- f = uncurry
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --      (elimEM _ (λ _ → isGroupoidΠ λ _ → truncB)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --        b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --        bP
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --        {!!})


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     f : EMtrunc → B
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     f = uncurry
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (elimEM _ (λ _ → isGroupoidΠ λ _ → truncB)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            bP
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            {!!})

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- module recEMtruncSingl {ℓ'} {B : Type ℓ'} (truncB : isGroupoid B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                   (b : A → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                   -- (p : (g : ⟨ G ⟩) → PathP (λ i → ua (fst m g ) i → B) b b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                   -- (p₀ : (g : ⟨ G ⟩) → (a : A) → b a ≡ b (fst m g .fst a))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                   -- (bIds : GroupHom G (idEquivsG B))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                       where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     f : (x : EMG) (y : EM₁Fam x) → singl {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     f = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   module recEMtrunc {ℓ'} {B : Type ℓ'} (truncB : isGroupoid B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (b : A → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     -- (p : (g : ⟨ G ⟩) → PathP (λ i → ua (fst m g ) i → B) b b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (p₀ : (g : ⟨ G ⟩) → (a : A) → b a ≡ b (fst m g .fst a))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (bIds : GroupHom G (idEquivsG B))
                    
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     -- (s₀ : (g h : ⟨ G ⟩)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     --   → PathP (λ k →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     --    PathP (λ j → ua (snd m .IsGroupHom.pres· g h k) j → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     --      b b )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     --  (ua→ (p₀ (g · h)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     --  (ua→ λ a → p₀ g a ∙ p₀ h (fst m g .fst a)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     module BID = IsGroupHom (snd bIds)
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     bE : (g : ⟨ G ⟩) → B → B
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     bE = fst ∘ fst ∘ fst bIds
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     p* : (g : ⟨ G ⟩) → (x : B) → x ≡ bE g x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     p* = funExt⁻ ∘ cong fst ∘ snd ∘ fst bIds

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     p*· : (g h : ⟨ G ⟩) → (a : A) → PathP
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       (λ i →  b a ≡ fst (fst (BID.pres· g h i)) (b a))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       (λ i → fst (snd (fst bIds (g · h)) i) (b a))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       λ i → snd (fst bIds h) i .fst (snd (fst bIds g) i .fst (b a))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     p*· g h a i = funExt⁻ (cong fst (snd (BID.pres· g h i))) (b a)



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- p : ∀ g → (a : A) → b a ≡ b (fst m g .fst a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- p = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- p : (g : ⟨ G ⟩) → PathP (λ i → ua (fst m g ) i → B) b b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- p g = ua→ (p₀ g)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- bSA : (g : ⟨ G ⟩) → singl b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- bSA g = b ∘ fst m g .fst , funExt (p₀ g)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     bSB : (g : ⟨ G ⟩) → singl b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     bSB g = bE g ∘ b , cong (_∘ b) ((cong fst ∘ snd ∘ fst bIds) g)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- p2 : (g : ⟨ G ⟩) → PathP (λ i → ua (fst m g ) i → B) b b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- p2 g = snd (bSA g) ◁ (λ i → b ∘ (ua-unglue (fst m g) i) )



   

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     module Rec 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (p₀* : (g : ⟨ G ⟩) → (a : A) → b (fst m g .fst a) ≡ bE g (b a))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (s₀ : (g : ⟨ G ⟩) → (a : A) → p* g (b a) ∙ sym (p₀* g a) ≡ p₀ g a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       p : (g : ⟨ G ⟩) → PathP (λ i → ua (fst m g ) i → B) b b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       p g = (snd (bSB g) ∙ sym (funExt (p₀* g))) ◁ (λ i → b ∘ (ua-unglue (fst m g) i) )

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       p2S : (g : ⟨ G ⟩) → ∀ a → Path (singl (b a)) (_ , refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (bE g (b a) , funExt⁻ ((cong fst ∘ snd ∘ fst bIds) g) ( b a))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       p2S g a i = {!!} , {!!}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       f' : (x : EMG) (y : EM₁Fam x) → B
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       f' = elimEM G (λ _ → isGroupoidΠ λ _ → truncB)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           s


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           bdS : (g h : ⟨ G ⟩) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                Square {A = Type (ℓ-max ℓ ℓ')}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (λ i → (a : ua (fst m g ) i) → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (λ i → (a : ua (fst m (g · h) ) i) → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (λ i → (a : ua (fst m h ) i) → B)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           bdS g h = λ i j → ( (compPath-filler _ _) ▷
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (sym (uaCompEquiv (fst m g) (fst m h))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ∙ cong ua (sym ((snd m) .IsGroupHom.pres· g h)))) i j → B

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           s : (g h : ⟨ G ⟩) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              SquareP (λ i j → ( (compPath-filler _ _) ▷
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (sym (uaCompEquiv _ _) ∙ cong ua (sym ((snd m) .IsGroupHom.pres· g h)))) i j → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (p g)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (p (g · h))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (p h)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           s g h i j =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             comp (λ k → doubleWhiskFiller refl (compPath-filler _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               ((sym (uaCompEquiv _ _) ∙ cong ua (sym ((snd m) .IsGroupHom.pres· g h)))) k i j
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (λ k → λ { (i = i0) → (p g) j
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        ; (i = i1) → sR k j 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        ; (j = i0) → b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        ; (j = i1) → (p h) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (compPathP→filler (λ x → x) (p g) (p h) i j)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              where



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                pp : PathP (λ j₁ → (ua (fst m g) ∙ ua (fst m h)) j₁ → B) b b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                pp = (compPathP→ (λ x → x) (p g) (p h))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                ppMid : PathP (λ j → ua ((fst m g) ∙ₑ (fst m h)) j → B) b b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                ppMid = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                -- ua→ λ a → p₀ g a ∙ p₀ h (fst m g .fst a)  



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                sRl : SquareP (λ k j → uaCompEquiv (fst m g) (fst m h) k j → B )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        ppMid      
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        pp
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        (λ _ → b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        λ _ → b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                sRl = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                -- postS : (a : A) → Square {A = singl (b a)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                --     (p2S g a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                --     (p2S (g · h) a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                --     refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                --     (isPropSingl _ _  ∙∙ (p2S h a) ∙∙ isPropSingl _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                -- postS i j  = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                postS' : (a : A) → Square {A = singl (b a)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (p2S g a ∙ (isPropSingl _ _  ∙∙ (p2S h a) ∙∙ isPropSingl _ _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (p2S (g · h) a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                postS' i j  = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                -- unglueGH : ∀ k j → ua (snd m .IsGroupHom.pres· g h k) j → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                -- unglueGH k j = ua-unglue (snd m .IsGroupHom.pres· g h k) j



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                sRrJ0 : Square {A = (A → B)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            (cong (b ∘_) (cong fst (snd m .IsGroupHom.pres· g h)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            (funExt (p₀* (g · h)) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                               cong (_∘ b) (sym ((cong fst ∘ snd ∘ fst bIds) (g · h)))) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            (funExt λ a → sym (p₀ h (fst m g .fst a)) ∙ sym (p₀ g a))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                sRrJ0 = {!s₀ (g · h)!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                -- sRrJ1 : Square {A = (A → B)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                --             refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                --             refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                --             (cong (_∘ b) (sym (funExt (p* (g · h)))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                --             (cong (_∘ b) (sym (funExt (p* (g · h)))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                -- sRrJ1 l _ = (cong (_∘ b) (sym (funExt (p* (g · h))))) l


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                sRr : PathP (λ k →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                          PathP (λ j → ua (snd m .IsGroupHom.pres· g h k) j → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            b b )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        (p (g · h))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        ppMid

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                sRr k j = comp (λ l → ua (snd m .IsGroupHom.pres· g h k) j  → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  {φ = k ∨ j ∨ ~ k ∨ ~ j}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (λ l → λ { (k = i0) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           ; (k = i1) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           ; (j = i0) → sRrJ0 l k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           ; (j = i1) → (cong (_∘ b) (sym (funExt (p* (g · h))))) l
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           }) (( λ a → fst (postS' a k j) ) ∘
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                              (ua-unglue (snd m .IsGroupHom.pres· g h k) j)) 
               


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                sR : SquareP (λ k j → ((λ i₁ → uaCompEquiv (fst m g) (fst m h) (~ i₁)) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                      (λ i₁ → ua (snd m .IsGroupHom.pres· g h (~ i₁))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                               k j →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                               B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        pp 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        (p (g · h))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        (λ _ → b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        λ _ → b
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                sR = compPathP'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    {B = λ x → PathP (λ j → x j → B) b b}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      {p = sym (uaCompEquiv (fst m g) (fst m h))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      {q = sym (cong ua ((snd m .IsGroupHom.pres· g h)))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      (symP sRl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      (symP sRr)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                -- sL : SquareP (λ i j → compPath-filler (ua (fst m g)) (ua (fst m h)) i j → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                --        (p g)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                --        pp
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                --        (λ _ → b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                --        (p h)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                -- sL = compPathP→filler (λ x → x) (p g) (p h) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- compPath-filler (ua (fst m g)) (ua (fst m h)) i j → B


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (ua (fst m g)) (ua (fst m h))

    
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     f : EMtrunc → B
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     f = uncurry f'



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- constFunHLev : ∀ {ℓ'} (B : Type ℓ') →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                 Iso (Σ (B → B) λ f → ∀ x → f x ≡ x) (∀ (x : B) → singl x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Iso.fun (constFunHLev B) x x₁ = (fst x x₁) , (sym (snd x x₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Iso.inv (constFunHLev B) x = (fst ∘ x) , (sym ∘ snd ∘ x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Iso.rightInv (constFunHLev B) b = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Iso.leftInv (constFunHLev B) a = refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- recEMtrunc : ∀ {ℓ'} (B : Type ℓ') → (isGroupoid B) → (A → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --             → (m' : GroupHom G (Symmetric-Group _ isSetA)) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- recEMtrunc = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- to : A // actRTrans → Σ (EM₁ G) (fst ∘ EM₁Fam)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- to = rec// actRTrans
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ x → embase , x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ r → ΣPathP ((emloop (fst r)) , toPathP (transportRefl _ ∙ sym (snd r))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- from : (e : EM₁ G) → (fst (EM₁Fam e)) → A // actRTrans
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- from = elimEM
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   G (λ _ → isGroupoidΠ λ _ → squash//)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    [_]//
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ g → ua→ λ a → eq// (g , refl))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- isoGQΣ : Iso (A // actRTrans) (Σ _ (fst ∘ EM₁Fam))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Iso.fun isoGQΣ = to
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Iso.inv isoGQΣ = uncurry from
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Iso.rightInv isoGQΣ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Iso.leftInv isoGQΣ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   elimSet// actRTrans (λ _ → squash// _ _) (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     λ {a} {b} (r , p)  → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         -- {!!} ▷ (λ _ → eq// {a = a} {b} (r , p))
  


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ {ℓ} {A B : Type ℓ} (f : A → B) where 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG : FreeGroup A → FreeGroup B
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG (η x) = η (f x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG (x · x₁) = mapFG x · mapFG x₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG ε = ε
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG (inv x) = inv (mapFG x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG (assoc x x₁ x₂ i) = (assoc (mapFG x) (mapFG x₁) (mapFG x₂) i) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG (idr x i) = idr (mapFG x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG (idl x i) = idl (mapFG x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG (invr x i) = invr (mapFG x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG (invl x i) = invl (mapFG x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   mapFG (trunc x y p q i i₁) = (trunc _ _ (cong mapFG p) (cong mapFG q) i i₁)
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data PermR : ℕ → Type₀ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   invo : ∀ {n} → PermR (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   braid : ∀ {n} → PermR (suc (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   comm : ∀ {n} → Fin n → PermR (suc (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   suc : ∀ {n} → PermR n → PermR (suc n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- permRel : ∀ n → PermR n → FreeGroup (Fin n) × FreeGroup (Fin n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- permRel .(suc _) invo = η zero , (inv (η zero))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- permRel .(suc (suc _)) braid = (η zero · η one) · η zero , (η one · η zero) · η one
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- permRel .(suc (suc _)) (comm x) = (η zero · η (suc (suc x))) , (η (suc (suc x)) · η zero)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- permRel .(suc _) (suc x) = map-× (mapFG suc) (mapFG suc) (permRel _ x) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Perm : ℕ → Group ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Perm n = Presented (permRel (predℕ n))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators : ∀ {n} → ⟨ Perm (suc n) ⟩  → PT.∥ List (Fin n) ∥₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (η x) = PT.∣ [ x ] ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (x · x₁) = PT.map2 _++_ (toGenerators x) (toGenerators x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators ε = PT.∣ [] ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (inv x) = PT.map rev (toGenerators x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (assoc x x₁ x₂ i) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   PT.squash₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (PT.map2 _++_ (toGenerators x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (PT.map2 _++_ (toGenerators x₁) (toGenerators x₂)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (PT.map2 _++_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (PT.map2 _++_ (toGenerators x) (toGenerators x₁)) (toGenerators x₂))  i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (idr x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (idl x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (invr x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (invl x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (rel i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toGenerators (trunc x x₁ x₂ y i i₁) = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucPermFDMorphism : ∀ n → GroupHom (SymData n) (SymData (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (sucPermFDMorphism n) = sucPerm
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (sucPermFDMorphism n)) x y =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc (y .fst (x .fst k)) }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (sucPermFDMorphism n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc k }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (sucPermFDMorphism n)) x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc (snd x .equiv-proof k .fst .fst) }

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- punchHeadInOutL : ∀ {n} (k : Fin (suc n)) → Σ (List (Fin n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   λ l → concatG (SymData _) (map adjTransposition l) ≡ PunchHeadInOut≃ k 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- punchHeadInOutL {n} zero = [] , refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (punchHeadInOutL {suc n} (suc k)) = zero ∷ map suc (fst (punchHeadInOutL k))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (punchHeadInOutL {suc n} (suc k)) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   cong ( swap0and1≃ ∙ₑ_)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ({!!} ∙ cong sucPerm (snd (punchHeadInOutL k)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedSym : ∀ n → ⟨ GeneratedBy (SymData (suc n)) adjTransposition ⟩ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedSym zero = λ _ → PT.∣ [] , equivEq (funExt λ x → isContr→isProp isContrFin1 _ _) ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedSym (suc n) e = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let (e' , p) = unwindPermHead e
      
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in PT.map (λ (l , p') → map suc l ++ fst (punchHeadInOutL (equivFun e zero))   ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (cong {x = (map adjTransposition
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (map suc l ++
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         fst (punchHeadInOutL (equivFun e zero))))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          {y = map adjTransposition (map suc l)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ++ map adjTransposition (fst (punchHeadInOutL (fst e zero)))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (concatG (SymData (suc (suc n))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∙ sym (concatG· {G = (SymData (suc (suc n)))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (map adjTransposition (map suc l))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (map adjTransposition (fst (punchHeadInOutL (equivFun e zero)))))
           
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ∙ cong₂ _∙ₑ_ ({!!} ∙ cong sucPerm p') (snd (punchHeadInOutL (equivFun e zero)))) ∙ sym p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (generatedSym n e')


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators : ∀ n → ⟨ GeneratedBy (Perm n) η ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators = {!!}





-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (η x) = PT.∣ [ x ] , sym (idr (η x)) ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (x · x₁) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   PT.map2 (λ (x , p) (y , q) → (x ++ y) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ({!!} ∙ cong₂ _·_ p q))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (PermGenerators n x) (PermGenerators n x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n ε =  PT.∣ [] , refl ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (inv x) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    PT.map (λ (x , p) → rev x ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (PermGenerators n x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (assoc x x₁ x₂ i) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    isProp→PathP {!!} {!!} {!!} i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i0 ⊢ PermGenerators n (x · (x₁ · x₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i1 ⊢ PermGenerators n ((x · x₁) · x₂)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (idr x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (idl x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (invr x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (invl x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (rel i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermGenerators n (trunc x x₁ x₂ y i i₁) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ : ∀ {n} → ⟨ Perm (suc n) ⟩  → Fin (suc n) ≃ Fin (suc n) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (η x) = adjTransposition x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (x · y) = to≃ x ∙ₑ to≃ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ ε = idEquiv _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (inv x) = invEquiv (to≃ x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (assoc x x₁ x₂ i) = (compEquiv-assoc (to≃ x) (to≃ x₁) (to≃ x₂)) i 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (idr x i) = compEquivEquivId (to≃ x) (~ i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (idl x i) = compEquivIdEquiv (to≃ x) (~ i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (invr x i) = invEquiv-is-rinv (to≃ x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (invl x i) = invEquiv-is-linv (to≃ x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel invo i) = swap0and1≃=invEquivSwap0and1 i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel braid i) = swap0and1Braid i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (rel (comm x) i) = commTranspositions x i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (to≃ (rel (suc {suc n} ix) i)) zero = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (to≃ (rel (suc {suc n} ix) i)) (suc x) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (to≃ (rel (suc {suc n} ix) i)) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- ({!!} ∙∙ (λ i → sucPerm (to≃ (rel ix i))) ∙∙ equivEq {!!}) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (trunc x x₁ x₂ y i i₁) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL : ∀ {ℓ} {A : Type ℓ} {n} → V.Vec A n → ⟨ Perm n ⟩ → V.Vec A n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL (x₁ V.∷ x₂ V.∷ l) (η zero) = (x₂ V.∷ x₁ V.∷ l)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL (x₁ V.∷ x₂ V.∷ l) (η (suc x)) = (x₁ V.∷ (onL (x₂ V.∷ l) (η x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (x · x₁) = onL (onL l x) x₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l ε = l
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (inv x) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (assoc x x₁ x₂ i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (idr x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (idl x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (invr x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (invl x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (rel ix i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- onL l (trunc x x₁ x₂ y i i₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i0 ⊢ to≃ (fromFree (mapFG suc (fst (permRel (suc n) ix))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i1 ⊢ to≃ (fromFree (mapFG suc (snd (permRel (suc n) ix))))





-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GeneratedBy : ∀ {ℓ ℓg} → (G : Group ℓ) → (A : Type ℓg) → (A → fst G) → hProp (ℓ-max ℓ ℓg)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (GeneratedBy G A f) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (x : fst G) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ∃ (List A) (λ l → x ≡ foldr (GroupStr._·_ (snd G) ∘ f) (GroupStr.1g (snd G)) l )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (GeneratedBy G A f) = isPropΠ λ _ → PT.squash₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GeneratedBy' : ∀ {ℓ ℓg} → (G : Group ℓ) → (A : Type ℓg) → (A → fst G) → hProp (ℓ-max ℓ ℓg)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (GeneratedBy' G A f) = PT.∥ (  (x : fst G) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Σ (List A) (λ l → x ≡ foldr (GroupStr._·_ (snd G) ∘ f) (GroupStr.1g (snd G)) l )) ∥₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (GeneratedBy' G A f) = PT.squash₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hasS→≃ : ∀ {ℓ} → {A B : Type ℓ} → (f : A → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → PT.∥ Σ (B → A) (λ g → section f g × retract f g ) ∥₁ → isEquiv f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hasS→≃ f = PT.rec (isPropIsEquiv _) λ x → isoToIsEquiv (iso f (fst x) (fst (snd x)) (snd (snd x)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hasSR→≃ : ∀ {ℓ} → {A B : Type ℓ} → (f : A → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → PT.∥ hasSection f ∥₁ → PT.∥ hasRetract f ∥₁ → isEquiv f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hasSR→≃ f = PT.rec2 (isPropIsEquiv _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  λ x x₁ → isoToIsEquiv (biInvEquiv→Iso-right (biInvEquiv _ (fst x) (snd x) (fst x₁) (snd x₁))) 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ {ℓ} (G H : Group ℓ) (A : Type ℓ) (g : _ )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (genG : ⟨ GeneratedBy' G A g ⟩ ) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (m : GroupHom G H)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (genH : ⟨ GeneratedBy' H A (fst m ∘ g) ⟩ )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (f : H .fst → G .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (pp : ∀ a → f (fst m (g a)) ≡ g a )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           -- (m' : GroupHom H G)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open GroupStr (snd G)  

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isEquivM : isEquiv (fst m)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isEquivM = hasS→≃ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (PT.map2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ gH gG →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           let s = λ b → cong (fst m ∘ f) (snd (gH b)) ∙∙ {!!} ∙∙ sym (snd (gH b))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           in
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              , (s
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               , λ a → cong (f ∘ (fst m)) ((snd (gG a)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ∙∙ sym (snd (gG a))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         genH genG)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- (PT.map
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   (λ gH →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --      let f' = (λ x → foldr (GroupStr._·_ (snd G) ∘ g) (GroupStr.1g (snd G)) (fst (gH x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --      in f' , (λ b → {!!} ∙ sym (snd (gH b)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --                ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   genH ) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- (PT.map2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   (λ gH gG →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --      let f'' : H .fst → G .fst 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --          f'' = (λ x → foldr (GroupStr._·_ (snd G) ∘ g) (GroupStr.1g (snd G)) (fst (gH x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --          -- f' = λ x → foldr (GroupStr._·_ (snd G) ∘ g) (GroupStr.1g (snd G))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --          --   (fst (gG (f'' x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --      in f'' , λ a → {!sym (snd (gH (fst m a)))!}  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --                )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   genH genG ) 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- genH' : ⟨ GeneratedBy H A (fst m ∘ g) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- genH' = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- foldM : ∀ xs → fst m (foldr (λ x₂ → snd G GroupStr.· g x₂) 1g xs) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      foldr (λ x₂ → snd H GroupStr.· h x₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     (GroupStr.1g (snd H)) xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- foldM = {!!} 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- foldM' : ∀ xs → fst m' (foldr (λ x₂ → snd H GroupStr.· h x₂) (GroupStr.1g (snd H)) xs) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      foldr (λ x₂ → snd G GroupStr.· g x₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     (GroupStr.1g (snd G)) xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- foldM' = {!!} 




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- sec : section (fst m) (fst m')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- sec x = PT.rec2 {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ (xs , p) (ys , q) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      let z = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      in cong (fst m ∘ fst m') p ∙ {!!} ∙ sym p ) (genH x) (genH (fst m (fst m' x)))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   sec : section (fst m) (fst m')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   sec x = PT.rec2 {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ (x , p) (y , q) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        let z = sym q ∙ cong (fst m') p

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        in {!!} ∙ (foldM x) ∙ sym p ) (genH x) (genG (fst m' x))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- isInjectiveGen : isInjective m
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- isInjectiveGen x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   PT.rec2 (isPropΠ λ _ → is-set _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     (λ x₂ x₃ p →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       let pp = sym p ∙ snd x₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       in snd x₂ ∙ {!pp!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     (genG x) (genH (fst m x))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucPermFDMorphism : ∀ n → GroupHom (SymData n) (SymData (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (sucPermFDMorphism n) = sucPerm
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (sucPermFDMorphism n)) x y =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc (y .fst (x .fst k)) }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (sucPermFDMorphism n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc k }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (sucPermFDMorphism n)) x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc (snd x .equiv-proof k .fst .fst) }

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data PLaws  : {n : ℕ} → List (Fin n) → List (Fin n) → Type where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pInvo : ∀ {n} → PLaws {suc n} (zero ∷ zero ∷ []) []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pComm : ∀ {n} → ∀ k → PLaws {suc (suc n)} (zero ∷ suc (suc k) ∷ []) (suc (suc k) ∷ zero ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   pBraid : ∀ {n} → PLaws {suc (suc n)} (zero ∷ one ∷ zero ∷ []) (one ∷ zero ∷ one ∷ [])
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   p↑ : ∀ {n k k'} → PLaws {n} k k' → PLaws {suc n} (map suc k) (map suc k')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   p← : ∀ {n k k' x} → PLaws {n} k k' → PLaws {n} (x ∷ k) (x ∷ k')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   p→ : ∀ {n k k' x} → PLaws {n} k k' → PLaws {n} (k ∷ʳ x) (k' ∷ʳ x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucPL : ∀ {n} → (_ / PLaws {n}) → (_ / PLaws {suc n}) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucPL =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   rec/ squash/ ([_]/ ∘ map suc) (λ _ _ → eq/ _ _ ∘ p↑)
  

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷ʳPL : ∀ {n} → ∀ x → (_ / PLaws {n}) → (_ / PLaws {n}) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷ʳPL x = rec/ squash/ ([_]/ ∘ (_∷ʳ x)) (λ _ _ → eq/ _ _ ∘ p→)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷PL : ∀ {n} → ∀ x → (_ / PLaws {n}) → (_ / PLaws {n}) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ∷PL x = rec/ squash/ ([_]/ ∘ (x ∷_)) (λ _ _ → eq/ _ _ ∘ p←)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- map-++ : ∀ {ℓ} {A B : Type ℓ} (f : A → B) → ∀ xs ys → map f (xs ++ ys) ≡ (map f xs) ++ (map f ys) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- map-++ f [] ys = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- map-++ f (x ∷ xs) ys = cong (_ ∷_) (map-++ f xs ys)



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- rev-map : ∀ {ℓ} {A B : Type ℓ} (f : A → B) → ∀ xs → map f (rev xs) ≡ rev (map f xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- rev-map f = ind refl λ {a} {l} p → map-++ f (rev l) [ a ] ∙ cong (_∷ʳ f a) p

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- w : ∀ n → (a b : List (Fin n)) → PLaws {n} a b → Path (_ / PLaws {n}) [ rev a ]/ [ rev b ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- w _ _ _ pInvo = eq/ _ _ pInvo
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- w _ _ _ (pComm k) = sym (eq/ _ _ (pComm k))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- w _ _ _ pBraid = eq/ _ _ pBraid
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- w _ _ _ (p↑ {n} {a} {b} p) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  let w' = w _ _ _ p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      p' = cong sucPL w'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  in cong [_]/ (sym (rev-map _ a)) ∙∙ p' ∙∙ cong [_]/ (rev-map _ b)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- w _ _ _ (p← {x = x} p) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  let w' = w _ _ _ p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  in cong (∷ʳPL x) w'

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- w _ _ _ (p→ {k = k} {k' = k'} {x = x} p) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  let w' = w _ _ _ p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in cong [_]/ (rev-snoc k _) ∙∙ cong (∷PL x) w' ∙∙  sym (cong [_]/ (rev-snoc k' _))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- www : ∀ n → (a b c : List (Fin n)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       PLaws b c → Path (_ / PLaws {n}) [ a ++ b ]/ [ a ++ c ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- www n [] b c x = eq/ _ _ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- www n (x₁ ∷ a) b c x = cong (∷PL x₁) (www n a b c x)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- www2 : ∀ n → (a b c : List (Fin n)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       PLaws a b → Path (_ / PLaws {n}) [ a ++ c ]/ [ b ++ c ]/

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- www2 n a b [] x = cong [_]/ (++-unit-r _) ∙∙ eq/ _ _ x ∙∙ cong [_]/ (sym (++-unit-r _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- www2 n a b (x₁ ∷ c) x = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    cong [_]/ (sym (++-assoc a [ x₁ ] c)) ∙∙ www2 _ _ _ c (p→ {x = x₁} x) ∙∙ cong [_]/ (++-assoc b [ x₁ ] c)  

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _∙Perm_ : ∀ {n} → _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _∙Perm_ {n} = rec2 squash/ (λ x y → [ x ++ y ]/) (www2 n) (www n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cyclePerm : ∀ {n} → (k : Fin (suc n)) →  (_ / PLaws {n})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cyclePerm {n} zero = [ [] ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cyclePerm {suc n} (suc k) = [  [ zero ]  ]/ ∙Perm sucPL (cyclePerm k)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- assocPerm : ∀ {n} → (x y z : List (Fin n) / PLaws) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (x ∙Perm (y ∙Perm z)) ≡ ((x ∙Perm y) ∙Perm z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- assocPerm = elimProp3 (λ _ _ _ → squash/ _ _) λ a b c → cong [_]/ (sym (++-assoc a b c))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- permInvo : ∀ {n} → ∀ a → PLaws {n} (a ∷ a ∷ []) []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- permInvo zero = pInvo
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- permInvo (suc a) = p↑ (permInvo a)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Perm' : ℕ → Group ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (Perm' n) = _ / PLaws {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GroupStr.1g (snd (Perm' n)) = [ [] ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GroupStr._·_ (snd (Perm' n)) = _∙Perm_ {n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GroupStr.inv (snd (Perm' n)) = rec/ squash/ ([_]/ ∘ rev) (λ a b p → w n a b p)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GroupStr.isGroup (snd (Perm' n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   makeIsGroup
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     squash/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     assocPerm
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (elimProp/ (λ _ → squash/ _ _) λ _ → cong ([_]/) (++-unit-r _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ((elimProp/ (λ _ → squash/ _ _) λ _ → refl))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (elimProp/ (λ _ → squash/ _ _) (ind refl λ {a = a} {l}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       p → sym (assocPerm [ [ a ] ]/ [ l ]/ [ rev ([ a ] ++ l) ]/)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ∙ cong ([ [ a ] ]/ ∙Perm_) ( assocPerm [ l ]/ [ rev l ]/ [ _ ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ∙ cong (_∙Perm [ [ a ] ]/) p) ∙ eq/ _ _ (permInvo a)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (elimProp/ (λ _ → squash/ _ _) (ind refl λ {a = a} {l}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       p → sym (assocPerm [ rev l ]/ [ [ a ] ]/ [ _ ]/)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ∙ cong ([ rev l ]/ ∙Perm_) ( assocPerm [ [ a ] ]/ [ [ a ] ]/ [ _ ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ∙ cong (_∙Perm [ l ]/) (eq/ _ _ (permInvo a))) ∙ p))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evenTest : ℕ → Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evenTest zero = true
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- evenTest (suc x) = not (evenTest x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Perm : ℕ → Group ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Perm = Perm' ∘ predℕ

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucPermMorphism : ∀ n → GroupHom (Perm n) (Perm (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucPermMorphism zero = idGroupHom
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (sucPermMorphism (suc n)) = sucPL
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (sucPermMorphism (suc n))) =  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  elimProp2 (λ _ _ → squash/ _ _ )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    λ a b → cong [_]/ (map-++ suc a b)  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (sucPermMorphism (suc n))) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (sucPermMorphism (suc n))) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  elimProp/ (λ _ → squash/ _ _) λ a → cong [_]/ (rev-map suc a)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInjectiveSucPermMorphism : ∀ n → isInjective (sucPermMorphism n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInjectiveSucPermMorphism zero = λ _ → idfun _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInjectiveSucPermMorphism (suc n) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   elimProp/ (λ _ → isPropΠ λ _ → squash/ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!} --(ind (λ _ → refl) λ x x₁ → {!!})

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInjectiveSucPermFDMorphism : ∀ n → isInjective (sucPermFDMorphism n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInjectiveSucPermFDMorphism = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedPerm : ∀ n → ⟨ GeneratedBy (Perm' n) (Fin n) ([_]/ ∘ [_]) ⟩ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedPerm n = elimProp/ (λ _ → PT.squash₁ )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  (ind PT.∣ [] , refl ∣₁ (λ {a} → PT.map λ x → a ∷ fst x , cong ([ [ a ] ]/ ∙Perm_) (snd x)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedSym : ∀ n → ⟨ GeneratedBy (SymData (suc n)) (Fin n) adjTransposition ⟩ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedSym zero = λ _ → PT.∣ [] , equivEq (funExt λ x → isContr→isProp isContrFin1 _ _) ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- generatedSym (suc n) e =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let (e' , p) = unwindPermHead e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in PT.map (λ (l , p') → map suc l ++ {!!}  , p ∙ {!!}) (generatedSym n e')

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH : ∀ n → (a b : List (Fin n)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       PLaws a b → ∀ k →  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       fst (foldr (λ k y → adjTransposition k ∙ₑ y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (idEquiv (Fin (suc n))) a) k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       fst (foldr (λ k y → adjTransposition k ∙ₑ y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (idEquiv (Fin (suc n))) b) k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH _ _ _ pInvo = λ { zero → refl ; one → refl ; (suc (suc k)) → refl }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH _ _ _ (pComm k') = λ { zero → refl ; one → refl ; (suc (suc k)) → refl }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH _ _ _ pBraid = λ { zero → refl ; one → refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ; (suc (suc zero)) → refl ; (suc (suc (suc k))) → refl}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH _ _ _ (p↑ {k = k} {k'} x) zero = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH _ _ _ (p↑ {k = k} {k'} x) (suc j) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {!!} ∙∙ cong suc (PermHomH _ k k' x j) ∙∙ {!!} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH _ _ _ (p← x) k = {!PermHomH _ _ _ (x) k!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHomH _ _ _ (p→ x) k = {!PermHomH _ _ _ (x) k!}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toPerm : ∀ n → fst (SymData (suc n)) → fst (Perm' n) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toPerm zero x = [ [] ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toPerm (suc n) e =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let (e' , p) = unwindPermHead e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in  sucPL (toPerm n e') ∙Perm cyclePerm (equivFun e zero) 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fold-rev : ∀ {ℓ} (G : Group ℓ) → (xs : List (fst G)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   foldr (GroupStr._·_ (snd G)) (GroupStr.1g (snd G)) (rev xs) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     GroupStr.inv (snd G) (foldr ((GroupStr._·_ (snd G))) ((GroupStr.1g (snd G))) xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fold-rev = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fold-rev' : ∀ {ℓ ℓg} (G : Group ℓ) (A : Type ℓg) (f : A → fst G) → (xs : List A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   foldr (GroupStr._·_ (snd G) ∘ f) (GroupStr.1g (snd G)) (rev xs) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     GroupStr.inv (snd G) (foldr ((GroupStr._·_ (snd G)) ∘ f) ((GroupStr.1g (snd G))) xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fold-rev' G A f [] = sym (GroupTheory.inv1g G)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fold-rev' G A f (x ∷ xs) = {!!} ∙ sym ((GroupTheory.invDistr G) _ _)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHom : ∀ n → GroupHom (Perm' n) (SymData (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (PermHom n) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   rec/ (isSetΣ (isSet→ isSetFin) (λ _ → isProp→isSet (isPropIsEquiv _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (foldr (λ k y → adjTransposition k ∙ₑ y ) (idEquiv _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ a b x → equivEq (funExt (PermHomH n a b x)))



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (PermHom n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   elimProp2 (λ _ _ → isSetΣ (isSet→ isSetFin) (λ _ → isProp→isSet (isPropIsEquiv _)) _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (ind (λ _ → sym (compEquivIdEquiv _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        λ {a} p b → cong (compEquiv (adjTransposition a)) (p b) ∙ compEquiv-assoc _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (PermHom n)) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (PermHom n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  elimProp/ (λ _ → isSetΣ (isSet→ isSetFin) (λ _ → isProp→isSet (isPropIsEquiv _)) _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   λ l → fold-rev' (SymData (suc n)) (Fin n) adjTransposition l


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHL : ∀ n → ∀ e → PermHom (suc n) .fst (sucPL (toPerm _ e)) ≡ sucPerm e 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHL = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHRRR : ∀ n → ∀ k → [ [ k ] ]/ ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                             (toPerm n (fst (PermHom _) [ [ k ] ]/))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHRRR (suc n) k = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHRRR (suc n) (suc k) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHRR : ∀ n → ∀ k → cyclePerm (suc k) ≡ (toPerm n (fst (PermHom _) (cyclePerm (suc k))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHRR .(suc _) zero = isSurPermHomHRRR _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHRR .(suc (suc n)) (suc {suc n} k) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- cong (λ x → ([ [ zero ] ]/ ∙Perm sucPL x)) (isSurPermHomHRR _ k) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --  {!!} ∙ cong (toPerm _) (sym (IsGroupHom.pres· (snd (PermHom (suc _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --   [ [ zero ] ]/ (sucPL (cyclePerm (fst {!!} {!!})))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHR : ∀ n → ∀ k → fst (PermHom n) (cyclePerm k) ≡ (PunchHeadInOut≃ {suc n} k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHR n zero = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHR .(suc _) one = equivEq refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomHR .(suc _) (suc (suc k)) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   IsGroupHom.pres· (snd (PermHom (suc _))) [ [ zero ] ]/ (sucPL (cyclePerm (suc k) ))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ∙ cong₂ _∙ₑ_ (compEquivEquivId _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ((cong {x = (cyclePerm (suc k) )} {y = (toPerm _ (fst (PermHom _) (cyclePerm (suc k))))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ((fst (PermHom _)) ∘ sucPL) (isSurPermHomHRR _ k) ∙ isSurPermHomHL _ (fst (PermHom _) (cyclePerm (suc k))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ∙ (cong sucPerm (isSurPermHomHR _ (suc k))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomH : ∀ n → ∀ x → PermHom n .fst (toPerm n x) ≡ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomH zero x = equivEq (funExt λ x → isContr→isProp isContrFin1 _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHomH (suc n) e =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  let (e' , p) = unwindPermHead e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  in  (IsGroupHom.pres· (snd (PermHom (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (sucPL (toPerm _ e')) (cyclePerm (equivFun e zero))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ∙ cong₂ {x = PermHom _ .fst (sucPL (toPerm _ e'))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            {y = sucPerm e'}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      _∙ₑ_ {!!} {!!}) ∙ sym p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- (isSurPermHomHL _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- (isSurPermHomHR _ (equivFun e zero))) ∙ sym p

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHom : ∀ n → isSurjective (PermHom n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isSurPermHom n x =  PT.∣ (toPerm _ x) , isSurPermHomH n x ∣₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInjPermHom : ∀ n → isInjective (PermHom n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInjPermHom n =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  elimProp/ (λ _ → isPropΠ λ _ → squash/ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (ind (λ _ → refl) λ {a} _ p →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- ∙ eq/ _ _ (permInvo a))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unwindPerm : ∀ n → (a : (_ / PLaws {suc n})) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  Σ (Fin (suc (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    λ k → Σ ((_ / PLaws {n})) λ e' → sucPL e' ∙Perm cyclePerm k ≡ a 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHom : ∀ n → GroupHom (Perm (suc n)) (SymData (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (PermHom zero) _ = idEquiv _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (PermHom zero)) _ _ = equivEq refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (PermHom zero)) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (PermHom zero)) _ = equivEq refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (PermHom (suc n)) e =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let (k , e' , p) = unwindPerm _ e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in sucPerm ((fst (PermHom n)) e') ∙ₑ PunchHeadInOut≃ k 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (PermHom (suc n))) = {!!}
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (PermHom (suc n))) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (PermHom (suc n))) = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermHom⁻ : ∀ n → GroupHom (SymData (suc n)) (Perm (suc n)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (PermHom⁻ zero) _ = [ [] ]/
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (PermHom⁻ zero)) _ _ = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (PermHom⁻ zero)) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (PermHom⁻ zero)) _ = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (PermHom⁻ (suc n)) e =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let (e' , p) = unwindPermHead e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in  sucPL ((fst (PermHom⁻ n)) e') ∙Perm cyclePerm (equivFun e zero) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (PermHom⁻ (suc n))) x y =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (PermHom⁻ (suc n))) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  (GroupStr.·IdR (snd (Perm (suc (suc n)))) (sucPL
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (fst (PermHom⁻ n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (isoToEquiv
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          _ ))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ∙ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- cong sucPL (GroupStr.·IdR (snd (Perm (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --   {!(fst (PermHom⁻ n) _)!}) ∙ {!!} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (PermHom⁻ (suc n))) e =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let (e' , p) = unwindPermHead e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in {!!}  

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unwindPerm = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cyclePermAgree : ∀ n → ∀ k → (PunchHeadInOut≃ k) ≡ fst (PermHom (suc n)) (cyclePerm k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- cyclePermAgree = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- wPP : ∀ n → (a b : List (Fin n)) → PLaws a b → evenTest (length a) ≡ evenTest (length b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- wPP .(suc _) .(zero ∷ zero ∷ []) .[] pInvo = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- wPP .(suc (suc _)) .(zero ∷ suc (suc k) ∷ []) .(suc (suc k) ∷ zero ∷ []) (pComm k) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- wPP .(suc (suc _)) .(zero ∷ one ∷ zero ∷ []) .(one ∷ zero ∷ one ∷ []) pBraid = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- wPP .(suc _) .(map suc _) .(map suc _) (p↑ {k = k} {k'} x) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  cong evenTest (length-map suc k) ∙∙ wPP _ _ _ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∙∙ sym (cong evenTest (length-map suc k'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- wPP n .(_ ∷ _) .(_ ∷ _) (p← x) = cong not (wPP _ _ _ x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- wPP n .(_ ∷ʳ _) .(_ ∷ʳ _) (p→ x) = {!!} ∙∙ cong not (wPP _ _ _ x) ∙∙ {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- parity : ∀ {n} → (_ / PLaws {n}) → Bool
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- parity {n} = rec/ isSetBool (evenTest ∘ length ) (wPP n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unwindPerm : ∀ n → (a : (_ / PLaws {suc n})) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  Σ (Fin (suc (suc n)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    λ k → Σ ((_ / PLaws {n})) λ e' → sucPL e' ∙Perm cyclePerm k ≡ a 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unwindPerm zero x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   if parity x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   then zero , [ [] ]/ , {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   else one , [ [] ]/ , {!!}
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unwindPerm (suc n) a = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (sucPermFDMorphism n) = sucPerm
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (sucPermFDMorphism n)) x y =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc (y .fst (x .fst k)) }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (sucPermFDMorphism n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc k }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (sucPermFDMorphism n)) x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq λ { i zero → zero ; i (suc k) → suc (snd x .equiv-proof k .fst .fst) }




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PermParity : ∀ n → GroupHom (Perm' n) BoolGroup
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (PermParity n) = rec/ isSetBool (evenTest ∘ length ) (wPP n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (snd (PermParity n)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   elimProp2 (λ _  _ → isSetBool _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- elimProp/ {!!} (ind (elimProp/ (λ _ → isSetBool _ _) (λ _ → refl))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --   λ {a} {l} → ind {B = λ l → ((y : List (Fin n) / PLaws) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --       rec/ isSetBool (λ x → evenTest (length x)) (wPP n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --       ((Perm n .snd GroupStr.· [ l ]/) y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --       ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --       (BoolGroup .snd GroupStr.· evenTest (length l))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --       (rec/ isSetBool (λ x → evenTest (length x)) (wPP n) y)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      (y : List (Fin n) / PLaws) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      rec/ isSetBool (λ x → evenTest (length x)) (wPP n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      ((Perm n .snd GroupStr.· [ a ∷ l ]/) y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      (BoolGroup .snd GroupStr.· not (evenTest (length l)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      (rec/ isSetBool (λ x → evenTest (length x)) (wPP n) y)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --       (λ p → elimProp/ {!!} {!!}) (λ p p' → elimProp/ {!!} {!!}) l) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (snd (PermParity n)) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (snd (PermParity n)) = elimProp/ (λ _ → isSetBool _ _) {!!}
