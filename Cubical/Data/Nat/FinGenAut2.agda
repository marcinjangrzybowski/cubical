{-# OPTIONS --safe #-}
module Cubical.Data.Nat.FinGenAut2 where

open import Cubical.Data.Nat.Base as ℕ hiding (_·_)
open import Cubical.Data.Nat.Properties


-- open import Cubical.Data.Fin.Properties as FP
open import Cubical.Data.Empty as ⊥

open import Cubical.Functions.Involution

open import Cubical.Foundations.Everything
-- open import Cubical.Data.Empty as ⊥
-- open import Cubical.Data.Nat as ℕ hiding (_·_)
-- open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe as Mb
import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Sum as ⊎


open import Cubical.Data.Nat.Order.Recursive

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Algebra.Group

open import Cubical.Algebra.SymmetricGroup

import Cubical.Functions.Logic as L

open import Cubical.Functions.Embedding

open import Cubical.Data.List as Li

open import Cubical.HITs.SequentialColimit as SC

import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.HITs.GroupoidQuotients as GQ
  renaming ([_] to [_]// ; RelimProp to  RelimProp// ; Rrec to Rrec//)


-- open import Cubical.Algebra.Group.Morphisms

-- open import Cubical.Algebra.Group.Generators




private
  variable
    ℓ : Level


-- infixr 9 _∘'_

-- _∘'_ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
--         → (g : B → C) → (f : A → B) → A → C 
-- g ∘' f = λ x → g (f x)
-- {-# INLINE _∘'_ #-}


infixr 4  _=→_



_=→_ : ∀ {ℓ} {A : Type ℓ} {f g : ℕ → A}
            → f zero ≡ g zero
            → (f ∘ suc ≡ g ∘ suc )
            → f ≡ g
_=→_ x x₁ i zero = x i
_=→_ x x₁ i (suc x₂) = x₁ i x₂


infixr 4  _sq→_

_sq→_ : ∀ {ℓ} {A : Type ℓ} {f g f' g'  : ℕ → A}
            → {fg : f ≡ g}
              {f'g' : f' ≡ g'}
              {ff' : f ≡ f'}
              {gg' : g ≡ g'}
            → Square (funExt⁻ fg zero)
                     (funExt⁻ f'g' zero)
                     (funExt⁻ ff' zero)
                     (funExt⁻ gg' zero)  
            → Square (cong (_∘ suc) fg)
                     (cong (_∘ suc) f'g')
                     (cong (_∘ suc) ff')
                     (cong (_∘ suc) gg') 
            → Square (fg)
                     (f'g')
                     (ff')
                     (gg')
(x sq→ x₁) i i₁ zero = x i i₁
(x sq→ x₁) i i₁ (suc x₂) = x₁ i i₁ x₂

infixr 4  _sqP→_


_sqP→_ : ∀ {ℓ} {A : I → I → ℕ → Type ℓ}
           -- {f g f' g'  : ℕ → A}
           {f : ∀ n → A i0 i0 n}
           {f' : ∀ n → A i1 i0 n}
           {g : ∀ n → A i0 i1 n}
           {g' : ∀ n → A i1 i1 n}

            → {fg : PathP (λ i → ∀ n → A i0 i n) f g}
              {f'g' : PathP (λ i → ∀ n → A i1 i n) f' g'}
              {ff' : PathP (λ i → ∀ n → A i i0 n) f f'}
              {gg' : PathP (λ i → ∀ n → A i i1 n) g g'}            
            → SquareP (λ i j → A i j 0)
                     (funExt⁻ fg zero)
                     (funExt⁻ f'g' zero)
                     (funExt⁻ ff' zero)
                     (funExt⁻ gg' zero) 
            → SquareP (λ i j → ∀ n → A i j (suc n))
                     (congP (λ _ → _∘ suc) fg)
                     (congP (λ _ → _∘ suc) f'g')
                     (congP (λ _ → _∘ suc) ff')
                     (congP (λ _ → _∘ suc) gg')
            → SquareP (λ i j → ∀ n → A i j n)
                     (fg)
                     (f'g')
                     (ff')
                     (gg')
(x sqP→ x₁) i i₁ zero = x i i₁
(x sqP→ x₁) i i₁ (suc x₂) = x₁ i i₁ x₂



infixr 5 _∷_

data FGℕ≃ℕ : Type where
  
  ε     : FGℕ≃ℕ
  _∷_ : ℕ → FGℕ≃ℕ → FGℕ≃ℕ

  invo : ∀ k → isInvolution (k ∷_)
  braid : ∀ k → ∀ xs →  
            k ∷ suc k ∷     k ∷ xs
      ≡ suc k ∷     k ∷ suc k ∷ xs
  comm : ∀ k l → commT k l → ∀ xs →
        k ∷ l ∷ xs
      ≡ l ∷ k ∷ xs
  
  trunc : isSet FGℕ≃ℕ

η : ℕ → FGℕ≃ℕ
η = _∷ ε 

record RelimProp {ℓ} (A : FGℕ≃ℕ → Type ℓ) : Type ℓ where
  field
    isPropA : ∀ x → isProp (A x)
    εA : A ε
    ∷A : ∀ k → ∀ {xs} → A xs → A (k ∷ xs)

  f : ∀ x → A x
  f ε = εA
  f (x ∷ x₁) = ∷A x (f x₁)
  f (invo k x i) =
      isProp→PathP (λ i → isPropA (invo k x i))
      (∷A k (∷A k (f x)))
      (f x) i
  f (braid k x i) =
     isProp→PathP (λ i → isPropA (braid k x i))
      (∷A k (∷A (suc k) (∷A k (f x))))
      (∷A (suc k) (∷A k (∷A (suc k) (f x)))) i
  f (comm k l x x₁ i) =
          isProp→PathP (λ i → isPropA (comm k l x x₁  i))
      (∷A k (∷A l (f x₁)))
      (∷A l (∷A k (f x₁))) i
  f (trunc x y p q i i₁) =
         isOfHLevel→isOfHLevelDep 2 (λ x → isProp→isSet (isPropA x))
         _ _ (cong f p) (cong f q) (trunc x y p q) i i₁


-- record RelimProp2 {ℓ} (A : FGℕ≃ℕ → FGℕ≃ℕ → Type ℓ) : Type ℓ where
--   field
--     isPropA : ∀ x y → isProp (A x y)
--     εA : A ε ε
--     ∷A : {!!}

--   f : ∀ x y → A x y
--   f = {!!}

--   -- f : ∀ x → A x
--   -- f ε = εA
--   -- f (x ∷ x₁) = ∷A x (f x₁)
--   -- f (invo k x i) =
--   --     isProp→PathP (λ i → isPropA (invo k x i))
--   --     (∷A k (∷A k (f x)))
--   --     (f x) i
--   -- f (braid k x i) =
--   --    isProp→PathP (λ i → isPropA (braid k x i))
--   --     (∷A k (∷A (suc k) (∷A k (f x))))
--   --     (∷A (suc k) (∷A k (∷A (suc k) (f x)))) i
--   -- f (comm k l x x₁ i) =
--   --         isProp→PathP (λ i → isPropA (comm k l x x₁  i))
--   --     (∷A k (∷A l (f x₁)))
--   --     (∷A l (∷A k (f x₁))) i
--   -- f (trunc x y p q i i₁) =
--   --        isOfHLevel→isOfHLevelDep 2 (λ x → isProp→isSet (isPropA x))
--   --        _ _ (cong f p) (cong f q) (trunc x y p q) i i₁


record Relim {ℓ} (A : FGℕ≃ℕ → Type ℓ) : Type ℓ where
  field
    isSetA : ∀ x → isSet (A x)
    εA : A ε
    ∷A : ∀ k → ∀ {xs} → A xs → A (k ∷ xs)
    invoA : ∀ k {x} x' → PathP (λ i → A (invo k x i))
      (∷A k (∷A k x'))
      x'
    braidA : ∀ k {x} x' → PathP (λ i → A (braid k x i))
      (∷A k (∷A (suc k) (∷A k x')))
      (∷A (suc k) (∷A k (∷A (suc k) x')))
    commA : ∀ k l z {x} x' → PathP (λ i → A (comm k l z x  i))
      (∷A k (∷A l x'))
      (∷A l (∷A k x'))

  f : ∀ x → A x
  f ε = εA
  f (x ∷ x₁) = ∷A x (f x₁)
  f (invo k x i) = invoA k (f x) i
  f (braid k x i) = braidA k (f x) i

  f (comm k l x x₁ i) = commA k l x (f x₁) i
  f (trunc x y p q i i₁) =
         isOfHLevel→isOfHLevelDep 2 (λ x → (isSetA x))
         _ _ (cong f p) (cong f q) (trunc x y p q) i i₁


record Rrec {ℓ} (A : Type ℓ) : Type ℓ where
  field
    isSetA : isSet A
    εA : A
    ∷A : ℕ → A → A
    invoA : ∀ k x → ∷A k (∷A k x) ≡ x
    braidA : ∀ k → ∀ x →
      (∷A k (∷A (suc k) (∷A k x)))
      ≡ (∷A (suc k) (∷A k (∷A (suc k) x)))
    commA : ∀ k l → commT k l → ∀ x →
                     ∷A k (∷A l x) ≡ ∷A l (∷A k x)

  f : FGℕ≃ℕ → A
  f ε = εA
  f (x ∷ x₁) = ∷A x (f x₁)
  f (invo k x i) = invoA k (f x) i
  f (braid k x i) = braidA k (f x) i
  f (comm k l x x₁ i) = commA k l x (f x₁) i
  f (trunc x y p q i i₁) =
    isSetA _ _ (cong f p) (cong f q) i i₁


_·_ : FGℕ≃ℕ → FGℕ≃ℕ → FGℕ≃ℕ
ε · x₁ = x₁
(x ∷ x₂) · x₁ = x ∷ (x₂ · x₁)
invo k x i · x₁ = invo k (x · x₁) i
braid k x i · x₁ = braid k (x  · x₁) i
comm k l x x₂ i · x₁ = comm k l x (x₂  · x₁) i
trunc x x₂ x₃ y i i₁ · x₁ =
  trunc (x · x₁) (x₂ · x₁)
    (cong  (_· x₁) x₃) (cong  (_· x₁) y) i i₁

invo' : ∀ k → (x y : FGℕ≃ℕ) → k ∷ x ≡ y → x ≡ k ∷ y 
invo' k x y p = sym (invo k x) ∙ cong (k ∷_) p

assoc· : ∀ x y z → x · (y · z) ≡ (x · y) · z
assoc· = RelimProp.f w
 where
   w : RelimProp _
   RelimProp.isPropA w _ = isPropΠ2 λ _ _ → trunc _ _
   RelimProp.εA w _ _ = refl
   RelimProp.∷A w _ p _ _  = cong (_ ∷_) (p _ _)
   

idr : ∀ x → (x · ε) ≡ x
idr = RelimProp.f
    (record { isPropA = λ _ → trunc _ _
            ; εA = refl
            ; ∷A = λ _ → cong (_ ∷_) })
   
inv : FGℕ≃ℕ → FGℕ≃ℕ
inv = Rrec.f w

  where
    w : Rrec FGℕ≃ℕ
    Rrec.isSetA w = trunc 
    Rrec.εA w = ε
    Rrec.∷A w k = _· (η k) 
    Rrec.invoA w _ x = sym (assoc· x _ _) ∙ cong (x ·_) (invo _ ε) ∙ idr  x
    Rrec.braidA w k x =
       (cong (_· η _) (sym (assoc· x (η _) (η _))) ∙ sym (assoc· x (η _ · η _) (η _)))
        ∙∙ cong (x ·_) (sym (assoc· (η _) (η _) (η _))
               ∙∙ braid k ε ∙∙ 
                (assoc· (η _) (η _) (η _))) ∙∙
       ((assoc· x (η _ · η _) (η _)) ∙
        cong (_· η _) (assoc· x (η _) (η _)))
    Rrec.commA w k l z x = 
       sym (assoc· x _ _)
        ∙∙ cong (x ·_) (sym (comm k l z ε)) ∙∙
       (assoc· x _ _)

invr : ∀ x → (x · inv x) ≡ ε
invr = RelimProp.f w
 where
   w : RelimProp _
   RelimProp.isPropA w _ = trunc _ _ 
   RelimProp.εA w = refl
   RelimProp.∷A w k {xs} p =
     cong′ (k ∷_)
      (assoc· xs (inv xs) _ ∙ cong (_· η k) p) ∙ invo k ε 

invl : ∀ x → (inv x · x) ≡ ε
invl = RelimProp.f w
 where
   w : RelimProp _
   RelimProp.isPropA w _ = trunc _ _ 
   RelimProp.εA w = refl
   RelimProp.∷A w k {xs} p = sym (assoc· (inv xs) (η k) _) ∙ 
      (cong ((inv xs) ·_) (invo k xs)) ∙ p

FinGenℕ≃ℕ : Group ℓ-zero
FinGenℕ≃ℕ = makeGroup {G = FGℕ≃ℕ}
  ε
  _·_
  (inv)
  trunc
  assoc·
  idr
  (λ _ → refl)
  invr
  invl

swap0and1 : ℕ → ℕ
swap0and1 zero = suc zero
swap0and1 (suc zero) = zero
swap0and1 k@(suc (suc _)) = k

sucFun : (ℕ → ℕ) → (ℕ → ℕ)
sucFun x zero = zero
sucFun x (suc x₁) = suc (x x₁)

predFun : (ℕ → ℕ) → (ℕ → ℕ)
predFun f = predℕ ∘ f ∘ suc

isInjectiveSucFun : ∀ {f} {f'} → sucFun f ≡ sucFun f' → f ≡ f'
isInjectiveSucFun = cong ((predℕ ∘_) ∘ (_∘ suc))

sucIso : Iso ℕ ℕ → Iso ℕ ℕ
sucIso isom = w
  where
    module i = Iso isom

    w : Iso ℕ ℕ
    Iso.fun w = sucFun i.fun
    Iso.inv w = sucFun i.inv
    Iso.rightInv w = ℕ.cases refl (cong suc ∘ i.rightInv)
    Iso.leftInv w = ℕ.cases refl (cong suc ∘ i.leftInv)



sucFunResp∘ : ∀ f g → sucFun f ∘ sucFun g ≡ sucFun (f ∘ g)
sucFunResp∘ f g = refl =→ refl

adjTransposition : ℕ → ℕ → ℕ
adjTransposition zero = swap0and1
adjTransposition (suc x) = sucFun (adjTransposition x)


isInvolSwap0and1 : isInvolution swap0and1
isInvolSwap0and1 = ℕ.cases refl (ℕ.cases refl λ _ → refl)

swap0and1≃ : Iso ℕ ℕ
swap0and1≃ = involIso {f = swap0and1} isInvolSwap0and1


sucFunRespIsInvolution : ∀ f →
     isInvolution f → isInvolution (sucFun f)
sucFunRespIsInvolution f x =
  ℕ.cases refl (cong suc ∘ x)

isInvolutionAdjTransposition : ∀ k → isInvolution (adjTransposition k)
isInvolutionAdjTransposition  =
  ℕ.elim isInvolSwap0and1
    (sucFunRespIsInvolution ∘ adjTransposition)


adjTransposition≃ : ℕ → Iso ℕ ℕ
adjTransposition≃ k = involIso
  {f = adjTransposition k} (isInvolutionAdjTransposition k)

adjTranspositionBraid : ∀ k →
      adjTransposition k ∘
      adjTransposition (suc k) ∘
      adjTransposition k
      ≡
      adjTransposition (suc k) ∘
      adjTransposition k ∘
      adjTransposition (suc k)
adjTranspositionBraid =
  ℕ.elim (refl =→ refl =→ refl =→ refl)
          λ _ x → refl =→ cong (suc ∘_) x
   
-- adjTranspositionBraid≃ : ∀ k →
--       adjTransposition≃ k ∙ₑ
--       adjTransposition≃ (suc k) ∙ₑ
--       adjTransposition≃ k
--       ≡
--       adjTransposition≃ (suc k) ∙ₑ
--       adjTransposition≃ k ∙ₑ
--       adjTransposition≃ (suc k)
-- adjTranspositionBraid≃ k =
--   equivEq (adjTranspositionBraid k)

swap0and1SucSucComm : ∀ f → 
        swap0and1 ∘ sucFun (sucFun f)
      ≡ sucFun (sucFun f) ∘ swap0and1
swap0and1SucSucComm f = refl =→ refl =→ refl  

adjTranspositionComm : ∀ k l → commT k l →
      adjTransposition l ∘ adjTransposition k ≡
      adjTransposition k ∘ adjTransposition l
adjTranspositionComm zero (suc (suc l)) x = sym (swap0and1SucSucComm _)
adjTranspositionComm (suc k) (suc (suc l)) x =
  refl =→ cong (suc ∘_) (adjTranspositionComm k (suc l) x)

adjTranspositionComm' : ∀ k l → commT k l →
      adjTransposition k ∘ adjTransposition l ∘ adjTransposition k ≡
      adjTransposition l
adjTranspositionComm' zero (suc (suc l)) x = refl =→ refl =→ refl
adjTranspositionComm' (suc k) (suc (suc l)) x =
  refl =→ cong (suc ∘_) (adjTranspositionComm' k (suc l) x)


to≃ : FGℕ≃ℕ → Iso ℕ ℕ
to≃ = Rrec.f to≃R
  where

   to≃R : Rrec (Iso ℕ ℕ)
   Rrec.isSetA to≃R = isSet-SetsIso isSetℕ isSetℕ
   -- isOfHLevelIso 2 isSetℕ isSetℕ
   Rrec.εA to≃R = idIso 
   Rrec.∷A to≃R k = compIso (adjTransposition≃ k) --adjTransposition≃ k ∙ₑ_
   Rrec.invoA to≃R k x = SetsIso≡ isSetℕ isSetℕ
      (cong (Iso.fun x ∘_) (funExt (isInvolutionAdjTransposition k)))
      (cong (_∘ Iso.inv x) (funExt (isInvolutionAdjTransposition k)))
   Rrec.braidA to≃R k x =
     SetsIso≡ isSetℕ isSetℕ
      (cong (Iso.fun x ∘_) (adjTranspositionBraid k))
      (cong (_∘ Iso.inv x) (adjTranspositionBraid k))

   Rrec.commA to≃R k l z x =
         SetsIso≡ isSetℕ isSetℕ
      (cong (Iso.fun x ∘_) (adjTranspositionComm k l z))
      (cong (_∘ Iso.inv x) (sym (adjTranspositionComm k l z)))

to≃· : ∀ f g → (to≃ (f · g)) ≡  compIso (to≃ f) (to≃ g)
to≃· = RelimProp.f w
  where
    w : RelimProp _
    RelimProp.isPropA w _ = isPropΠ λ _ → isSet-SetsIso isSetℕ isSetℕ _ _ 
    RelimProp.εA w x = SetsIso≡ isSetℕ isSetℕ
       refl refl
    RelimProp.∷A w k {xs} X g =
      SetsIso≡ isSetℕ isSetℕ
        (cong′ (_∘' adjTransposition k)
          (cong′ Iso.fun (X g)))
        (cong′ (adjTransposition k ∘'_)
          (cong′ Iso.inv (X g)))

to≃Inv : ∀ f → invIso (to≃ f) ≡ (to≃ (inv f))
to≃Inv = RelimProp.f w
  where
    w : RelimProp λ z → invIso (to≃ z) ≡ to≃ (inv z)
    RelimProp.isPropA w _ = isSet-SetsIso isSetℕ isSetℕ _ _
    RelimProp.εA w = SetsIso≡ isSetℕ isSetℕ
       refl refl
    RelimProp.∷A w k {xs} X =
        Iso≡Set-fun isSetℕ isSetℕ _ _
          (λ k → refl)
        ∙∙ cong₂ compIso X (sym (compIsoIdR (adjTransposition≃ k)))
        ∙∙  (sym (to≃· (inv xs) (η k)))
        
kAdjTlem : ∀ k → k ≡ adjTransposition k k → ⊥
kAdjTlem zero = znots
kAdjTlem (suc k) x = kAdjTlem k (cong predℕ x)

kAdjTlemS : ∀ k → (suc k) ≡ adjTransposition k (suc k) → ⊥
kAdjTlemS zero = snotz
kAdjTlemS (suc k) x = kAdjTlemS k (cong predℕ x)

genBy : ∀ f → ⟨ L.∃[ l ] (Li.foldr (_∷_) ε l ≡ f) , trunc _ _  ⟩
genBy = RelimProp.f w
 where
  w : RelimProp _
  RelimProp.isPropA w _ = Prop.squash₁
  RelimProp.εA w =  Prop.∣ [] , refl ∣₁
  RelimProp.∷A w k = Prop.map (uncurry λ x y →
     k ∷ x , cong (k ∷_) y)

-- mbHead : ∀ {ℓ} → {A : Type ℓ} → List A → Maybe A
-- mbHead [] = nothing
-- mbHead (x ∷ _) = just x

-- Cycle : Type
-- Cycle = (ℕ ⊎ (ℕ × ℕ))

-- cyStepS : ℕ → Cycle → Maybe Cycle
-- cyStepS = {!!}

-- cyStep : ℕ → List Cycle → List Cycle
-- cyStep k [] = [ inl k ]
-- cyStep k (x ∷ xs) =
--    Mb.rec {!!} (λ x' → x' ∷ xs) (cyStepS k x)


-- unw : ∀ n (l : List (Fin (suc n))) →
--     Iso.fun (to≃ (Li.foldr (_∷_ ∘' fst) ε l)) zero ≡ zero →
--           Σ (List (Fin n)) λ l' → Li.foldr (_∷_ ∘' fst) ε l
--                   ≡ Li.foldr (_∷_ ∘' suc ∘' fst) ε l'
-- unw = {!!}

-- sh : ∀ n l k → codeℕ (suc n) (Li.length l) →
--        (Li.foldr (_∷_) ε (k ∷ l)) ≡ ε
--         → Σ _ λ l' → (Li.foldr (_∷_) ε (l') ≡ ε)
--           × codeℕ n (Li.length l')
-- sh n (x₂ ∷ []) k x x₁ =
--   [] , (refl , x)
-- sh (suc n) (x₂ ∷ x₃ ∷ l) k x x₁ =
--   {!!}


-- -- injOnL' : ∀ n n' l l' → codeℕ n (Li.length l) → codeℕ n' (Li.length l') → 
-- --   to≃ (Li.foldr (_∷_) ε l) ≡ to≃ (Li.foldr (_∷_) ε l')
-- --   → Li.foldr (_∷_) ε l ≡ Li.foldr (_∷_) ε l'
-- -- injOnL' n n' [] [] _ _ _ = refl
-- -- injOnL' n zero [] (k ∷ l') x ()
-- -- injOnL' zero (suc n') [] (k ∷ l') x x' p = {!!}
-- --   -- invo' _ _ _ {!(injOnL' 1 n' (k ∷ []) l' _ x'
-- --   --   (Iso≡Set-fun isSetℕ isSetℕ _ _
-- --   --     (funExt⁻ ( cong′ (_∘  adjTransposition k) (cong′ Iso.fun p)
-- --   --       ∙ cong′ ((Iso.fun (to≃ (foldr _∷_ ε l'))) ∘_)
-- --   --         (funExt (isInvolutionAdjTransposition k))
-- --   --       ))))!}
-- -- injOnL' (suc n) n' (k ∷ l) l' x x' p = {!!}
-- --     --     cong′ (k ∷_) (injOnL' n (suc n') l (k ∷ l') x x'
-- --     --      {!p!})
-- --     -- ∙ invo _ _


-- -- injOnL : ∀ l l' →
-- --   to≃ (Li.foldr (_∷_) ε l) ≡ to≃ (Li.foldr (_∷_) ε l')
-- --   → Li.foldr (_∷_) ε l ≡ Li.foldr (_∷_) ε l'
-- -- injOnL l l' x = {!l!}
-- -- -- injOnL [] [] x = refl
-- -- -- injOnL [] (k ∷ l') x =
-- -- --   invo' _ _ _ (injOnL (k ∷ []) l'
-- -- --     (Iso≡Set-fun isSetℕ isSetℕ _ _
-- -- --       (funExt⁻ ( cong′ (_∘  adjTransposition k) (cong′ Iso.fun x)
-- -- --         ∙ cong′ ((Iso.fun (to≃ (foldr _∷_ ε l'))) ∘_) (funExt (isInvolutionAdjTransposition k))
-- -- --         ))))
-- -- -- injOnL (k ∷ l) l' x = {!!}
-- -- --   -- cong (k ∷_) (injOnL l (k ∷ l') {!!}) ∙ {!!}


elimByGens : ∀ {ℓ} (A : FGℕ≃ℕ → Type ℓ)
      → (isPropA : ∀ x → isProp (A x))
      → (∀ l → A (Li.foldr (_∷_) ε l))
      → ∀ x → A x
elimByGens A isPropA X =
  Prop.rec (isPropA _)
    (uncurry (λ x y →
      subst A y (X x))) ∘ genBy 

-- injTo≃ : ∀ f → to≃ f ≡ idIso → f ≡ ε
-- injTo≃ = elimByGens
--   _ (λ _ → isPropΠ λ _ → trunc _ _)
--     λ l → injOnL l []


-- injTo≃ : ∀ f → to≃ f ≡ idIso → f ≡ ε
-- injTo≃ =  RelimProp.f w
--  where
--   w : RelimProp λ z → (x : to≃ z ≡ idIso) → z ≡ ε
--   RelimProp.isPropA w _ = isPropΠ λ _ → trunc _ _
--   RelimProp.εA w _ = refl
--   RelimProp.∷A w k {xs} =
--     RelimProp.f ww xs k
--    where
--      ww : RelimProp (λ xs → ∀ k → 
--            (to≃ xs ≡ idIso → xs ≡ ε) → to≃ (k ∷ xs) ≡ idIso → k ∷ xs ≡ ε)
--      RelimProp.isPropA ww = {!!}
--      RelimProp.εA ww k x x₁ = {!!}
--      RelimProp.∷A ww k {xs} x  k' x₁ x₂ =
--         {!x₁!}
     
-- -- injTo≃' : ∀ f → (to≃ f ≡ idIso → f ≡ ε)
-- --                 × (∀ k → (to≃ f ≡ adjTransposition≃ k → f ≡ η k))
-- -- injTo≃' = RelimProp.f w
-- --  where
-- --   w : RelimProp λ z →
-- --                     (to≃ z ≡ idIso → z ≡ ε) ×
-- --                     ((k : ℕ) → to≃ z ≡ adjTransposition≃ k → z ≡ η k)
-- --   RelimProp.isPropA w = {!!}
-- --   fst (RelimProp.εA w) _ = refl
-- --   snd (RelimProp.εA w) k p = ⊥.rec (kAdjTlem k (funExt⁻ (cong Iso.fun p) k))
-- --   fst (RelimProp.∷A w k {xs} x) p =
-- --     cong (k ∷_) (snd x k
-- --        {!sym (to≃· (η k) xs) ∙ p!}) ∙ invo k ε
-- --   snd (RelimProp.∷A w k {xs} x) k' p =
-- --     let p' : to≃ (xs) ≡ compIso (adjTransposition≃ k') (adjTransposition≃ k')
-- --         p' = {!p!}

-- --         p'' : to≃ (xs) ≡ to≃ (k' ∷ k ∷ ε)
-- --         p'' = p' ∙ {!!} ∙ sym (to≃· (η k') (η k))

-- --         z = {!snd x k'!}
-- --     in {! !}




-- -- injTo≃ : ∀ f → to≃ f ≡ idIso → f ≡ ε
-- -- injTo≃ = RelimProp.f w
-- --  where
-- --   w : RelimProp (λ z → to≃ z ≡ idIso → z ≡ ε)
-- --   RelimProp.isPropA w _ = isPropΠ λ _ → trunc _ _
-- --   RelimProp.εA w _ = refl
-- --   RelimProp.∷A w k {xs} x P =
-- --     let z = sym (to≃· (η k) xs)
-- --         z' : to≃ xs ≡ adjTransposition≃ k
-- --         z' = {!z ∙ P!}
-- --     in {!!}


isConstFrom : (ℕ → ℕ) → ℕ → hProp ℓ-zero
isConstFrom f k = (∀ x → k ≤ x → f x ≡ x) , isPropΠ2 λ _ _ → isSetℕ _ _  

-- -- isSmalest : ∀ {ℓ} → (ℕ → hProp ℓ) → (ℕ → hProp ℓ) 
-- -- isSmalest x n = x n L.⊓ (L.∀[ n' ] (x n') L.⇒ ((n ≤ n') , isProp≤))

    
-- isFinGen≃ : Iso ℕ ℕ → hProp ℓ-zero
-- isFinGen≃ e = L.∃[ k ] isConstFrom (Iso.fun e) k

-- -- -- isPropΣisSmalest : ∀ {ℓ} P → isProp (Σ _ (fst ∘ isSmalest {ℓ} P))
-- -- -- isPropΣisSmalest P (n , (Pn , nSmlst)) (m , (Pm , mSmlst)) with n ≟ m
-- -- -- ... | lt x = ⊥.rec (<-asym {m = {!m!}} {n = {!m!}} x (mSmlst n Pn)) 
-- -- -- ... | eq x = Σ≡Prop (snd ∘ isSmalest P) x
-- -- -- ... | gt x = ⊥.rec (<-asym {m = {!!}} {n = {!!}} x (nSmlst m Pm))

open Minimal

isFinGen≃' : Iso ℕ ℕ → hProp ℓ-zero
isFinGen≃' e = Σ ℕ (Least (fst ∘  (isConstFrom (Iso.fun e))))
  , isPropΣLeast (snd ∘ isConstFrom (Iso.fun e))

isLB : Iso ℕ ℕ → ℕ → Type
isLB e = (Least (fst ∘  (isConstFrom (Iso.fun e))))

-- -- isFinGen≃'0→e≡idEquiv : ∀ e → (fst (isConstFrom e 0))
-- --                               → e ≡ idfun _
-- -- isFinGen≃'0→e≡idEquiv e X = funExt λ x → X x _

-- -- -- isConstFrom→smalestBound :
-- -- --       ∀ f
-- -- --     → ⟨ L.∃[ k ] isConstFrom f k ⟩
-- -- --     → Σ ℕ (fst ∘ isSmalest (isConstFrom f))
-- -- -- isConstFrom→smalestBound f =
-- -- --   Prop.rec (isPropΣisSmalest (isConstFrom f))
-- -- --    (uncurry w)
-- -- --  where
-- -- --    w : (n : ℕ) (y : ⟨ isConstFrom f n ⟩) →
-- -- --          Σ ℕ (fst ∘ isSmalest (isConstFrom f))
-- -- --    w zero y = zero , ( y , λ  _ _ → _ )
-- -- --    w (suc n) y with discreteℕ (f n) n
-- -- --    ... | yes p = w n λ k → ⊎.rec (y k) (λ q → cong f (sym q) ∙∙ p ∙∙ q)
-- -- --                    ∘ ≤-split
-- -- --    ... | no ¬p = suc n ,
-- -- --       (y , {!!})
-- -- --         -- λ m z → ⊎.rec (idfun _)
-- -- --         -- (λ q → ⊥.rec (¬p (z n q)) ) ({!!}) )

predFun-isConstFrom : ∀ f k
   → ⟨ isConstFrom f (suc k) ⟩
   → ⟨ isConstFrom (predFun f) k ⟩
predFun-isConstFrom f k X n x₂ =
  cong predℕ (X (suc n) (x₂))

sucFun-isConstFrom : ∀ f k
   → ⟨ isConstFrom f k ⟩
   → ⟨ isConstFrom (sucFun f) (suc k) ⟩
sucFun-isConstFrom f k X =
 ℕ.cases (λ _ → refl) λ n → cong suc ∘ X n


-- -- section-isConstFrom : ∀ f g k → section g f 
-- --    → ⟨ isConstFrom f k ⟩
-- --    → ⟨ isConstFrom g k ⟩
-- -- section-isConstFrom f g k S X j j< =
-- --   cong g (sym (X j j<)) ∙ S j

-- FinGen≃ : Type₀
-- FinGen≃ = Σ (ℕ ≃ ℕ) (fst ∘ isFinGen≃)

FinGen≃' : Type₀
FinGen≃' = Σ (Iso ℕ ℕ) (fst ∘ isFinGen≃')



isConstFrom∘ : ∀ f k g l →
   ⟨ isConstFrom f k ⟩ → ⟨ isConstFrom g l ⟩
   →  ⟨ isConstFrom (f ∘ g) (max l k) ⟩
isConstFrom∘ f l g k s r j j< =
     let j= = r j (≤-trans {k = k}
                {m = max k l} {n = j} (left-≤-max k l) j<)
     in s _ (subst (l ≤_) (sym j=)
      (≤-trans {l} {max k l} {j} (right-≤-max k l) j<)
      ) ∙ j= 

-- isConstFrom∘-n : ∀ f k g l →
--    ⟨ isConstFrom f k ⟩ → ⟨ isConstFrom g l ⟩
--    → ℕ
-- isConstFrom∘-n = {!!}

isConstFrom∘'Σ : ∀ f k g l →
      Least (fst ∘ isConstFrom f) k → Least (fst ∘ isConstFrom g) l
   →  Σ _ λ n → Least (fst ∘ (isConstFrom (f ∘ g))) n 
isConstFrom∘'Σ f k g l F G =
   AllFrom.ΣallFromP→LeastAllFromP _
     (λ _ → discreteℕ _ _) ((max l k) , isConstFrom∘ f k g l (fst F) (fst G))
  

     -- let j= = r j (≤-trans {k = k}
     --            {m = max k l} {n = j} (left-≤-max k l) j<)
     -- in s _ (subst (l ≤_) (sym j=)
     --  (≤-trans {l} {max k l} {j} (right-≤-max k l) j<)
     --  ) ∙ j= 


isFinGen≃∘ : FinGen≃' → FinGen≃' → FinGen≃'
fst (isFinGen≃∘ (e , _) (f , _)) = compIso e f
snd (isFinGen≃∘ (_ , p) (_ , q)) =
   isConstFrom∘'Σ _ (fst q) _ (fst p)
     (snd q) (snd p)

isConstFrom-adjTransposition : ∀ k →
  ⟨ isConstFrom (adjTransposition k) (suc (suc k)) ⟩
isConstFrom-adjTransposition =
   ℕ.elim {A = λ k → ⟨ isConstFrom (adjTransposition k) (suc (suc k)) ⟩}
      (ℕ.cases (⊥.rec) (ℕ.cases (⊥.rec)
         λ _ _ → refl))
      (λ n X → sucFun-isConstFrom _ _ X) 

isConstFrom-adjTransposition<m : ∀ k m →
  ⟨ isConstFrom (adjTransposition k) m ⟩
  → suc (suc k) ≤ m
isConstFrom-adjTransposition<m k m p =
  ¬<-≥ m (suc (suc k)) λ x → kAdjTlemS k (sym ((p (suc k) x)))

adjTransposition-compute : ∀ k → 
  adjTransposition k (suc k) ≡ k
adjTransposition-compute zero = refl
adjTransposition-compute (suc k) = cong suc (adjTransposition-compute k)

isConstFrom-adjTranspositionL : ∀ k →
  Least (fst ∘ isConstFrom (adjTransposition k)) (suc (suc k))
fst (isConstFrom-adjTranspositionL k) = isConstFrom-adjTransposition k
snd (isConstFrom-adjTranspositionL k) =
  λ n x X →
     ¬sucK λ x₁ → X x₁ ∘' (≤-trans {n} {suc k} x)

  where
    ¬sucK : ¬ ⟨ isConstFrom (adjTransposition k) (suc k) ⟩
    ¬sucK X = 
       snotid (sym (X (suc k) (≤-refl k)) ∙ (adjTransposition-compute k))
  

-- -- isConstFrom-adjTransposition : ∀ k →
-- --   ⟨ isConstFrom (adjTransposition k) (suc (suc k)) ⟩
-- -- isConstFrom-adjTransposition =
-- --    ℕ.elim {A = λ k → ⟨ isConstFrom (adjTransposition k) (suc (suc k)) ⟩}
-- --       (ℕ.cases (⊥.rec) (ℕ.cases (⊥.rec)
-- --          λ _ _ → refl))
-- --       (λ n X → sucFun-isConstFrom _ _ X) 


isFinGen'AdjTransposition≃ : ∀ k → ⟨ isFinGen≃' (adjTransposition≃ k) ⟩
isFinGen'AdjTransposition≃ k = (suc (suc k)) ,  isConstFrom-adjTranspositionL k
  -- Prop.∣ (suc (suc k)) , isConstFrom-adjTransposition k ∣₁


idFinGen≃' : FinGen≃'
idFinGen≃' = idIso , zero , (λ _ _ → refl) , λ n n<0 _ → n<0

to≃' : FGℕ≃ℕ → FinGen≃'
to≃' x = to≃ x , RelimProp.f w  x
   where
     w : RelimProp (fst ∘ isFinGen≃' ∘ to≃)
     RelimProp.isPropA w = snd ∘ isFinGen≃' ∘ to≃
     RelimProp.εA w = snd idFinGen≃'
     RelimProp.∷A w k {xs} z = snd (isFinGen≃∘
       (adjTransposition≃ k , isFinGen'AdjTransposition≃ k) (to≃ xs , z)) 

-- -- -- to≃'' : FGℕ≃ℕ → FinGen≃'
-- -- -- to≃'' x = to≃ x , RelimProp.f w  x
-- -- --    where
-- -- --      w : RelimProp (fst ∘ isFinGen≃' ∘ to≃)
-- -- --      RelimProp.isPropA w = snd ∘ isFinGen≃' ∘ to≃
-- -- --      RelimProp.εA w = zero , (λ _ _ → refl) , λ _ _ → zero-≤
-- -- --      RelimProp.∷A w k {xs} z =
-- -- --        (max _ (fst z)) ,
-- -- --         (isConstFrom∘ _ _ _ _ (fst (snd z)) (isConstFrom-adjTransposition k) ,
-- -- --           {!to≃· ? ?!})
-- -- --        -- snd (isFinGen≃∘
-- -- --        --   (adjTransposition≃ k , isFinGenAdjTransposition≃ k) (to≃ xs , z)) 

-- -- -- -- -- getBnd : FGℕ≃ℕ → ℕ
-- -- -- -- -- getBnd = fst ∘ snd ∘ to≃''

-- -- -- -- -- getBnd· : ∀ e f → 
-- -- -- -- --          getBnd (e · f) RO.≤ max (getBnd e) (getBnd f) 
-- -- -- -- -- getBnd· = RelimProp.f w
-- -- -- -- --   where
-- -- -- -- --     w : RelimProp
-- -- -- -- --           (λ z → (f : FGℕ≃ℕ) → getBnd (z · f) RO.≤ max (getBnd z) (getBnd f))
-- -- -- -- --     RelimProp.isPropA w e = isPropΠ λ f → RO.isProp≤
-- -- -- -- --       {getBnd (e · f)} {max (getBnd e) (getBnd f)} 
-- -- -- -- --     RelimProp.εA w f = RO.≤-refl (getBnd f)
-- -- -- -- --     RelimProp.∷A w k {xs} g = {!!}
    
rotIso : ℕ → Iso ℕ ℕ
rotIso zero = swap0and1≃
rotIso (suc n) = compIso swap0and1≃ (sucIso (rotIso n))

rot : ℕ → ℕ → ℕ
rot = Iso.fun ∘ rotIso
 
rotIso' : ℕ → Iso ℕ ℕ
rotIso' = ℕ.cases idIso rotIso

rot' : ℕ → ℕ → ℕ
rot' = Iso.fun ∘ rotIso'

rot'-k : ∀ k → rot' k zero ≡ k
rot'-k = ℕ.cases refl (ℕ.elim refl λ _ → cong suc) 

rot'-zero : ∀ k →  (Iso.inv (rotIso' k)) k ≡ zero
rot'-zero = ℕ.cases refl (ℕ.elim refl λ _ → cong (swap0and1 ∘ suc)) 

rot'-≢k→≢0 : ∀ k n → ¬ k ≡ n → ¬ zero ≡ (Iso.inv (rotIso' k)) n 
rot'-≢k→≢0 k n p q =
   p (sym (rot'-k k)
    ∙ cong (Iso.fun (rotIso' k)) q ∙ (Iso.rightInv (rotIso' k) n))

swap<1lem : ∀ k → 1 ≤ k → 1 ≤ swap0and1 (suc k)
swap<1lem (suc k) x = _

lemmm>0 : ∀ e0 e1 → e1 ≤ e0 → 0 < (Iso.inv (rotIso e0) e1)
lemmm>0 zero zero x = _
lemmm>0 (suc e0) zero x = _
lemmm>0 (suc e0) (suc e1) x = swap<1lem (Iso.inv (rotIso e0) e1) (lemmm>0 e0 e1 x)


rot'-<k : ∀ k n → n < k → suc n ≡ (Iso.inv (rotIso' k) n)                   
rot'-<k (suc zero) zero x = refl
rot'-<k (suc (suc k)) zero x = refl
rot'-<k (suc (suc k)) (suc n) x =
  cong suc (rot'-<k (suc k) n x) ∙
    sym (isConstFrom-adjTransposition 0
       _ (lemmm>0 k n x)) 


-- -- -- -- isConstFromSwap0And1 : ∀ n → ⟨ isConstFrom swap0and1 (2 + n) ⟩
-- -- -- -- isConstFromSwap0And1 x _ = refl

rotIsoConst : ∀ k → ⟨ isConstFrom (Iso.fun (rotIso' k)) (suc k)⟩
rotIsoConst zero _ _ = refl
rotIsoConst (suc zero) (suc (suc x)) _ = refl
rotIsoConst (suc (suc k)) (suc (suc (suc x))) x₁ =
  cong suc (rotIsoConst (suc k) (suc (suc x)) x₁)

constFromInvIso : ∀ k → (e : Iso ℕ ℕ)
        → ⟨ isConstFrom (Iso.fun e) k ⟩
        → ⟨ isConstFrom (Iso.inv e) k ⟩
        
constFromInvIso k e X n k≤n =
  sym (cong (Iso.inv e) (X n k≤n)) ∙ Iso.leftInv e n

rotIsoConstInv : ∀ k → ⟨ isConstFrom (Iso.inv (rotIso' k)) (suc k)⟩
rotIsoConstInv k =
  constFromInvIso (suc k)
    (rotIso' k) (rotIsoConst k)


rot'-k< : ∀ k n → k < n → (Iso.inv (rotIso' k) n) ≡ n
rot'-k< = rotIsoConstInv


rot'<'' : ∀ e1 e0 → e1 < suc e0 →
         e1 ≡ Iso.fun (sucIso (rotIso' e0)) (swap0and1 (suc e1))

rot'<'' zero e0 x = refl
rot'<'' (suc zero) (suc zero) x = refl
rot'<'' (suc zero) (suc (suc e0)) x = refl
rot'<'' (suc (suc e1)) (suc (suc e0)) x =
  cong suc (rot'<'' (suc e1) (suc e0) x)


rot'< : ∀ e1 e0 → e1 < suc e0 →
        predℕ (Iso.inv swap0and1≃ (Iso.inv (sucIso (rotIso' e0)) e1))
             ≡ e1

rot'< e1 e0 x = cong predℕ (cong swap0and1
                 (cong (Iso.inv (sucIso (rotIso' e0))) (rot'<'' e1 e0 x)
     ∙ Iso.leftInv (sucIso (rotIso' e0)) _)
                  ∙ isInvolSwap0and1 _)


-- lemmm>0' : ∀ e0 e1 → e1 < e0 → 0 < (Iso.inv (rotIso' e0) e1)
-- lemmm>0' = ? 

lwmmm : ∀ k → 0 < k → predℕ
      (swap0and1
       (suc (swap0and1 (suc (swap0and1 (suc k))))))
      ≡
      suc
      (predℕ
       (swap0and1 (suc (swap0and1 (suc k)))))
lwmmm zero ()
lwmmm (suc k) _ = refl


lwmm : ∀ e0 e1 → e1 ≤ e0 → predℕ (swap0and1 (suc (Iso.inv (rotIso e0) e1))) ≡
      suc
      (predℕ (swap0and1 (sucFun (Iso.inv (cases idIso rotIso e0)) e1)))
lwmm zero zero x = refl
lwmm (suc e0) zero x = refl
lwmm (suc zero) (suc zero) x = refl
lwmm (suc (suc e0)) (suc zero) x = refl
lwmm (suc (suc e0)) (suc (suc e1)) x = lwmmm ((Iso.inv (rotIso e0) e1)) (lemmm>0 e0 e1 x)



predℕIso-sec : (e : Iso ℕ ℕ) → Iso.fun e zero ≡ zero
           → section (predFun (Iso.fun e)) (predFun (Iso.inv e))
predℕIso-sec e x b = 
  cong predℕ (cong (Iso.fun e)
    (sym (suc-predℕ _ λ p → snotz (sym (Iso.rightInv e (suc b))
      ∙ cong (Iso.fun e) p ∙ x)))
   ∙ Iso.rightInv e (suc b))

predℕIso : (e : Iso ℕ ℕ) → Iso.fun e zero ≡ zero
           → Iso ℕ ℕ
Iso.fun (predℕIso e x) = predFun (Iso.fun e)
Iso.inv (predℕIso e x) = predFun (Iso.inv e)
Iso.rightInv (predℕIso e x) = predℕIso-sec e x
Iso.leftInv (predℕIso e x) = predℕIso-sec (invIso e)
      (sym (cong (Iso.inv e) x) ∙ (Iso.leftInv e) zero)


unwindIso : Iso ℕ ℕ → Iso ℕ ℕ
unwindIso isom =
  predℕIso (compIso isom (invIso (rotIso' (Iso.fun isom zero))))
           ((rot'-zero (Iso.fun isom zero)))

sucPredIso : (e : Iso ℕ ℕ) → ∀ p → e ≡ sucIso (predℕIso e p)
sucPredIso e p = Iso≡Set isSetℕ isSetℕ _ _
  (ℕ.cases p λ n → suc-predℕ _
       λ p' → snotz (isoFunInjective e _ _ (p' ∙ sym p)))
  (ℕ.cases p⁻
      λ n → suc-predℕ _ λ p' → snotz (isoInvInjective e _ _ (p' ∙ sym p⁻)))

  where
    p⁻ : e .Iso.inv zero ≡ 0
    p⁻ = sym (cong (Iso.inv e) p) ∙ Iso.leftInv e zero

unwindedIso= : (e : Iso ℕ ℕ) →
                  e ≡ compIso (sucIso (unwindIso e)) (rotIso' (Iso.fun e zero))
unwindedIso= e =
  Iso≡Set isSetℕ isSetℕ _ _
    (λ x → sym (Iso.rightInv (rotIso' (Iso.fun e zero)) (Iso.fun e x)))
    (λ x → cong (e .Iso.inv) (sym (Iso.rightInv (rotIso' (Iso.fun e zero)) x)) )
    ∙ cong (λ x → compIso x (rotIso' (Iso.fun e zero)))
              (sucPredIso _ _)

unwindIsoIsoRI : ∀ k x → unwindIso (compIso (sucIso x) (rotIso' k)) ≡ x
unwindIsoIsoRI k x =
   Iso≡Set isSetℕ isSetℕ _ _
     (λ n →
       cong (λ z → predℕ
      (Iso.inv (rotIso' z)
       (Iso.fun (rotIso' k) (suc (Iso.fun x n))))) (rot'-k k)
         ∙ cong predℕ (Iso.leftInv (rotIso' k) _))
     λ n → cong (predℕ ∘ (sucFun (Iso.inv x)))
             (cong  (λ z → (Iso.inv (rotIso' k)
                        (Iso.fun (rotIso' z) (suc n)))) (rot'-k k) ∙
                         Iso.leftInv (rotIso' k) (suc n))
        
unwindIsoIso : Iso (Iso ℕ ℕ) (ℕ × (Iso ℕ ℕ))
unwindIsoIso = w
  where
    w : Iso (Iso ℕ ℕ) (ℕ × Iso ℕ ℕ)
    Iso.fun w x = (Iso.fun x zero) , (unwindIso x) 
    Iso.inv w (k , x) = compIso (sucIso x) (rotIso' k)
    Iso.rightInv w (k , x) = ΣPathP (rot'-k k , unwindIsoIsoRI k x)
    Iso.leftInv w x = sym (unwindedIso= x)

unwindIsoIdIso : unwindIso idIso ≡ idIso
unwindIsoIdIso = Iso≡Set-fun isSetℕ isSetℕ _ _ λ _ → refl

-- isInjectiveSucIso : (e f : Iso ℕ ℕ) → sucIso e ≡ sucIso f → e ≡ f
-- isInjectiveSucIso = {!!}


unwindIsoAdjT : ∀ k →
  unwindIso (adjTransposition≃ (suc k)) ≡ adjTransposition≃ k
unwindIsoAdjT k =
 Iso≡Set-fun isSetℕ isSetℕ _ _ λ _ → refl

unwindConstFrom : ∀ k f → ⟨ isConstFrom f (suc k) ⟩
                        → ⟨ isConstFrom (predFun f) k ⟩
unwindConstFrom k f x n k≤n =
  cong predℕ (x (suc n) k≤n)

constFromPres< : ∀ k e → ⟨ isConstFrom (Iso.fun e) k ⟩
                        → ∀ n → n < k → (Iso.fun e n) < k
constFromPres< k f X n n<k = 
  ¬<-≥ k (suc (Iso.fun f n))
    λ x → 
      let X' = constFromInvIso k f X
          z = injSuc (cong suc (sym (Iso.leftInv f n) ∙ X' (Iso.fun f n) x))
          q = subst (k ≤_) (sym z) x
      in <→≥→⊥ {n} {k} n<k q

unwindConstFromIso : ∀ k e → ⟨ isConstFrom (Iso.fun e) (suc k) ⟩
                           → ⟨ isConstFrom (Iso.fun (unwindIso e)) k ⟩
unwindConstFromIso k e X =
  let zz = isConstFrom∘ (Iso.inv ((rotIso' (Iso.fun e zero))))
                (suc (Iso.fun e zero)) (Iso.fun e) (suc k)
                 (rotIsoConstInv (Iso.fun e zero)) X

      zz' : ⟨ isConstFrom _ (suc k) ⟩
      zz' = subst {x = max (suc k) ((suc (Iso.fun e zero))) }
           (fst ∘ isConstFrom _ ) (cong suc (left-≤-→max≡ k (Iso.fun e zero)
             (constFromPres< (suc k) e X zero _))) zz
  in predFun-isConstFrom 
      ( (Iso.inv (rotIso' (Iso.fun e zero))) ∘ (Iso.fun e)) k
        zz'

constFromIsoH : (Iso ℕ ℕ) → ℕ → hProp ℓ-zero
constFromIsoH = isConstFrom ∘ Iso.fun

IsoCF : ℕ → Type
IsoCF k = Σ _ λ isom → ⟨ constFromIsoH isom k ⟩

IsoCFpres<n : ∀ n → (e : IsoCF n) →
                ∀ k →
                  (k < n) → (Iso.fun (fst e) k < n) 
IsoCFpres<n n e k q with suc (Iso.fun (fst e) k) ≤? n
... | yes p = p
... | no ¬p =
   ⊥.rec (¬p (subst (_≤ n)
     (cong suc 
     (sym (Iso.leftInv (fst e) _) ∙ (constFromInvIso n (fst e) (snd e) _
       ((¬<-≥ (Iso.fun (fst e) k) n ¬p))))) q))
     


getLeastB : ∀ f → _ →
             Σ _ λ n' → Least (fst ∘ isConstFrom f ) n'
getLeastB f = AllFrom.ΣallFromP→LeastAllFromP _
     (λ _ → discreteℕ _ _)

unwindIsoIsoCF : ∀ n → Iso (IsoCF (suc n)) (Fin (suc n) × IsoCF n)
unwindIsoIsoCF n = w
  where
    module u = Iso unwindIsoIso

    w : Iso (IsoCF (suc n)) (Fin (suc n) × IsoCF n)
    Iso.fun w (x , p) =
      let (k , isom') = u.fun x
      in (k , constFromPres< (suc n) x
            p _ _) , (isom' , unwindConstFromIso n x p)
    Iso.inv w ((k , k<) , (isom , isomCF)) =
      let isom' = u.inv (k , isom)
          p' = 
             isConstFrom∘ (λ z → Iso.fun (rotIso' k) z) (suc k)
               _ (suc n)
                (rotIsoConst k) (sucFun-isConstFrom (Iso.fun isom) n isomCF)
      in isom' , λ x x₁ → p' x
        (subst (_≤ x) (sym (left-≤-→max≡ (suc n) (suc k) k<)) x₁)
    Iso.rightInv w ((k , k<) , (isom , isomCF)) =
      let p = u.rightInv (k , isom)
      in ΣPathP ((≡Fin {suc n} (cong fst p)) ,
          Σ≡Prop (λ x → snd (constFromIsoH x n)) (cong snd p))
    Iso.leftInv w (isom , _) =
      Σ≡Prop ((λ x → snd (constFromIsoH x (suc n))))
        (u.leftInv isom)

FinGen'≃≡ : ℕ → Type
FinGen'≃≡ n =
  Σ FinGen≃' λ k → fst (snd k) ≡ n 


FinGen'≃< : ℕ → Type
FinGen'≃< n =
  Σ FinGen≃' λ k → fst (snd k) ≤ n 

CF<Iso : ∀ n → Iso (FinGen'≃< n) (IsoCF n)
CF<Iso n = compIso Σ-assoc-Iso
  (Σ-cong-iso-snd w)
 where
  w : (x : Iso ℕ ℕ) →
        Iso _ _
  Iso.fun (w x) x₁ x₂ x₃ = fst (snd (fst x₁)) x₂
    (≤-trans {fst (fst x₁)} {n} {x₂} ((snd x₁)) x₃)
     
  Iso.inv (w x) z = getLeastB _ (n , z) ,
      AllFrom.ΣallFromP→LeastAllFromP< _
        (λ _ → discreteℕ _ _) n n z (≤-refl n)
  Iso.rightInv (w x) _ = snd (constFromIsoH x n) _ _
  Iso.leftInv (w x) _ = isPropΣ (snd (isFinGen≃' x))
    (λ (k , _) → isProp≤ {k} {n} ) _ _


unwindIsoIsoFG< : ∀ n → Iso (FinGen'≃< (suc n))
                          (Fin (suc n) × FinGen'≃< n)
unwindIsoIsoFG< n =
  compIso (CF<Iso (suc n))
     (compIso (unwindIsoIsoCF n)
       (prodIso idIso (invIso (CF<Iso n))))


-- -- isFinGen≃→isFinGen≃' : ∀ e → ⟨ isFinGen≃ e ⟩ → ⟨ isFinGen≃' e ⟩
-- -- isFinGen≃→isFinGen≃' e =
-- --   Prop.rec (snd (isFinGen≃' e))
-- --            (AllFrom.ΣallFromP→LeastAllFromP _
-- --              λ n → discreteℕ (fst e n) n)



-- sucPerm*R : ∀ n → Rrec {n = n} (Perm (suc n))
-- Rrec.isSetA (sucPerm*R n) = trunc
-- Rrec.εA (sucPerm*R n) = ε
-- Rrec.∷A (sucPerm*R (suc n)) = _∷_ ∘ suc
-- Rrec.invoA (sucPerm*R (suc n)) _ = invo _
-- Rrec.braidA (sucPerm*R (suc (suc n))) _ = braid _
-- Rrec.commA (sucPerm*R (suc (suc n))) k (suc l) v = comm _ _ v

-- sucPerm* : ∀ n → Perm n →  Perm (suc n)
-- sucPerm* n = Rrec.f (sucPerm*R n)

RsucFGℕ≃ℕ : Rrec FGℕ≃ℕ
Rrec.isSetA RsucFGℕ≃ℕ = trunc 
Rrec.εA RsucFGℕ≃ℕ = ε
Rrec.∷A RsucFGℕ≃ℕ x = suc x ∷_
Rrec.invoA RsucFGℕ≃ℕ k = invo (suc k)
Rrec.braidA RsucFGℕ≃ℕ k x = braid (suc k) x
Rrec.commA RsucFGℕ≃ℕ k (suc l) x = comm (suc k) (suc (suc l)) x

sucFGℕ≃ℕ  : FGℕ≃ℕ → FGℕ≃ℕ 
sucFGℕ≃ℕ = Rrec.f RsucFGℕ≃ℕ

sucSucComm : ∀ x → sucFGℕ≃ℕ (sucFGℕ≃ℕ x) · η zero ≡
              (η zero · sucFGℕ≃ℕ (sucFGℕ≃ℕ x)) 
sucSucComm = RelimProp.f w
 where
  w : RelimProp
        (λ z →
           (sucFGℕ≃ℕ (sucFGℕ≃ℕ z) · η zero) ≡
           (η zero · sucFGℕ≃ℕ (sucFGℕ≃ℕ z)))
  RelimProp.isPropA w _ = trunc _ _
  RelimProp.εA w = refl
  RelimProp.∷A w k p =
    cong′ (suc (suc k) ∷_) p ∙
    sym (comm _ _ _ _) 

sucFGℕ≃ℕresp· : ∀ a b → sucFGℕ≃ℕ (a · b) ≡ (sucFGℕ≃ℕ a · sucFGℕ≃ℕ b)
sucFGℕ≃ℕresp· = RelimProp.f w
 where
  w : RelimProp
        (λ z → (b : FGℕ≃ℕ) → sucFGℕ≃ℕ (z · b) ≡ (sucFGℕ≃ℕ z · sucFGℕ≃ℕ b))
  RelimProp.isPropA w _ = isPropΠ λ _ → trunc _ _
  RelimProp.εA w _ = refl
  RelimProp.∷A w k = cong (suc k ∷_) ∘_

rotFG : ℕ → FGℕ≃ℕ
rotFG zero = ε
rotFG (suc x) = zero ∷ sucFGℕ≃ℕ (rotFG x)


resp·to≃ : ∀ f g → compIso (to≃ f) (to≃ g) ≡ to≃ (f · g) 
resp·to≃ = RelimProp.f w
  where
    w : RelimProp (λ z → (g : FGℕ≃ℕ) → compIso (to≃ z) (to≃ g) ≡ to≃ (z · g))
    RelimProp.isPropA w _ =
      isPropΠ λ _ → isSet-SetsIso isSetℕ isSetℕ _ _
      -- isPropΠ λ _ → isOfHLevel≃ 2 (isSetℕ) (isSetℕ) _ _
    RelimProp.εA w g = compIsoIdL _ 
    RelimProp.∷A w k {xs} X g =
      Iso≡Set isSetℕ isSetℕ _ _ (λ x → refl) (λ x → refl)
        ∙ cong′ (compIso _) (X g)


from≃ : (x : Iso ℕ ℕ) → (k : ℕ) →
     ⟨ isConstFrom (Iso.fun x) k ⟩
     → FGℕ≃ℕ 
from≃ x zero _ = ε
from≃ x (suc n) X =
  let ((k , k<) , (x' , X')) = Iso.fun (unwindIsoIsoCF n)
          ( x , X)
  in sucFGℕ≃ℕ (from≃ x' n X') · rotFG k

from≃HLP : (x : Iso ℕ ℕ) → (k : ℕ) →
     ⟨ isConstFrom (Iso.fun x) (suc k) ⟩
     → FGℕ≃ℕ 
from≃HLP x n X =
  let ((k , k<) , (x' , X')) = Iso.fun (unwindIsoIsoCF n)
          ( x , X)
  in from≃ x' n X'


from≃lem' : (x x' : Iso ℕ ℕ) →       
      (k' : ℕ) →
     (p : ⟨ isConstFrom (Iso.fun x) zero ⟩) → 
     (p' : ⟨ isConstFrom (Iso.fun x') k' ⟩)
     → x ≡ x' → from≃ x zero p ≡ from≃ x' k' p'  
from≃lem' x x' zero p p' x₁ = refl
from≃lem' x x' (suc k') p p' P =
     cong₂' _·_ (cong′ sucFGℕ≃ℕ {x = ε}
   (from≃lem' _ _ k' (λ j j< → snd (snd (Iso.fun (unwindIsoIsoCF zero)
    (x , λ x₁ x₂ → p x₁ tt))) j tt) _
    (cong′ (fst ∘ snd ∘ Iso.fun (unwindIsoIsoCF k'))
     (ΣPathPProp {u = x , subst (λ x → ⟨ constFromIsoH x (suc k') ⟩)
                      (sym P) p'}
                   {v = x' , p'}
                  (λ a → snd ( constFromIsoH a (suc k'))) P))))
      (cong′ rotFG (sym (p zero _) ∙ funExt⁻ (cong Iso.fun P) zero))

from≃lem : (x x' : Iso ℕ ℕ) →       
      (k k' : ℕ) →
     (p : ⟨ isConstFrom (Iso.fun x) k ⟩) → 
     (p' : ⟨ isConstFrom (Iso.fun x') k' ⟩)
     → x ≡ x' → from≃ x k p ≡ from≃ x' k' p'  
from≃lem x x' zero zero p p' P = refl
from≃lem x x' zero (suc k') p p' P = from≃lem' x x' (suc k') p p' P
from≃lem x x' (suc k) zero p p' P =
   sym (from≃lem' x' x (suc k) p' p (sym P))
from≃lem x x' (suc k) (suc k') p p' P =
   cong₂' _·_ (cong′ sucFGℕ≃ℕ pp)
     (cong′ rotFG (funExt⁻ (cong′ Iso.fun P) zero)  )

  where
   pp : _
   pp = from≃lem
     (fst (snd (Iso.fun (unwindIsoIsoCF k) (x , p))))
     (fst (snd (Iso.fun (unwindIsoIsoCF k') (x' , p'))))
     k k'
     ((snd (snd (Iso.fun (unwindIsoIsoCF k) (x , p)))))
     (snd (snd (Iso.fun (unwindIsoIsoCF k') (x' , p'))))
     (Iso≡Set-fun isSetℕ isSetℕ _ _
      λ x i →
       predℕ
      (Iso.inv (cases idIso rotIso (Iso.fun (P i) 0)) (Iso.fun (P i) (suc x))))

-- isoFGri : {!!}
-- isoFGri = {!!}


from≃' : FinGen≃' → FGℕ≃ℕ 
from≃' = uncurry λ x → uncurry λ k → (from≃ x k ∘ fst)


to≃suc : ∀ e → sucFun (Iso.fun (to≃ e)) ≡ Iso.fun (to≃ (sucFGℕ≃ℕ e))
to≃suc = RelimProp.f w
  where
   w : RelimProp (λ z → sucFun (Iso.fun (to≃ z)) ≡ Iso.fun (to≃ (sucFGℕ≃ℕ z)))
   RelimProp.isPropA w _ = isSet→ isSetℕ _ _
   RelimProp.εA w = refl =→ refl
   RelimProp.∷A w k {xs} X = sym (sucFunResp∘ (Iso.fun (to≃ xs))
     (adjTransposition k)) ∙ cong (_∘ sucFun (adjTransposition k)) X

to≃sucIso : ∀ e → sucIso  (to≃ e) ≡ (to≃ (sucFGℕ≃ℕ e))
to≃sucIso e = Iso≡Set-fun isSetℕ isSetℕ _ _
  (funExt⁻ (to≃suc e))


to≃rotFG : ∀ k → Iso.fun (to≃ (rotFG k)) ≡ rot' k
to≃rotFG zero = refl
to≃rotFG (suc zero) = refl
to≃rotFG (suc (suc k)) =

 let z = sucFunResp∘ (Iso.fun (to≃ (sucFGℕ≃ℕ (rotFG k)))) swap0and1
          ∙ cong ( sucFun ) (to≃rotFG (suc k))
 in cong (_∘' sucFun swap0and1 ∘ swap0and1)
      (sym (to≃suc (sucFGℕ≃ℕ (rotFG k)))) ∙ cong (_∘' swap0and1) z

to≃rotFGiso : ∀ k → to≃ (rotFG k) ≡ rotIso' k
to≃rotFGiso zero = refl
to≃rotFGiso (suc zero) = Iso≡Set-fun isSetℕ isSetℕ _ _ λ _ → refl
to≃rotFGiso (suc (suc k)) =
  cong′ (compIso _)
    (Iso≡Set-fun isSetℕ isSetℕ _ _
      (funExt⁻ ( cong′ (_∘' (sucFun swap0and1))
          (cong (Iso.fun) (sym (to≃sucIso ((sucFGℕ≃ℕ (rotFG k))))))
       ∙ sucFunResp∘ (Iso.fun (to≃ (sucFGℕ≃ℕ (rotFG k)))) swap0and1))
     ∙ cong sucIso (to≃rotFGiso (suc k))) 



-- sucFun (Iso.fun (to≃ (sucFGℕ≃ℕ (rotFG k))))

-- (λ x →
--          Iso.fun
--          (Rrec.f Cubical.Data.Nat.FinGenAut2.to≃R
--           (Rrec.f RsucFGℕ≃ℕ (sucFGℕ≃ℕ (rotFG k))))
--          (Iso.fun (adjTransposition≃ 1) x))
--       ≡ (λ x → sucIso (to≃ (zero ∷ sucFGℕ≃ℕ (rotFG k))) .Iso.fun x)

isoFGriLem : (e : Iso ℕ ℕ) → ∀ k →
               (p : ⟨ isConstFrom (Iso.fun e) k ⟩ ) →
                (fst (to≃' (from≃ e k p))) ≡ e
isoFGriLem e zero p =
  Iso≡Set isSetℕ isSetℕ _ _
    (λ x → sym (p x _))
      λ x → sym (constFromInvIso zero e p x _)
  --funExt λ x → sym (p x _)
isoFGriLem e (suc n) p = 
   let ((k , k<) , (e' , p')) = Iso.fun (unwindIsoIsoCF n)
            (e , p)
       z = (isoFGriLem e' n p')
   in  sym (resp·to≃ (sucFGℕ≃ℕ (from≃ e' n p')) (rotFG k))
        ∙ cong₂ compIso
             ((sym (to≃sucIso (from≃ e' n p')) --(to≃suc ((from≃ x' w X')))
                 ∙ cong sucIso z))
             (to≃rotFGiso k)
        ∙ cong fst (Iso.leftInv (unwindIsoIsoCF n) (e , p))



permSeq : Sequence ℓ-zero
Sequence.space permSeq = λ n → IsoCF n
Sequence.map permSeq {k} x = fst x , λ x₁ → snd x x₁ ∘ <-weaken {k}

plFun : Lim→ permSeq → FinGen≃'
plFun = SC.elim _ _  w
  where
    w : ElimData permSeq (λ _ → FinGen≃')
    ElimData.finl w {k} (x , p) =
      let z = getLeastB (Iso.fun x) (k , p)
      in x , z
    ElimData.fpush w (x , p) = Σ≡Prop (snd ∘ isFinGen≃') refl

plInv : FinGen≃' → Lim→ permSeq
plInv (x , (k , (p , q))) =  SC.inl {n = k} (x , p)

<-elim : (A : ℕ → ℕ → Type) → (∀ k n → A k (n + k)) → ∀ k n → k ≤ n → A k n
<-elim A x k n x₁ =
 let z = x k (fst (─Σ k n x₁))
 in subst (A k) (snd (─Σ k n x₁)) z

-- plIso : Iso FinGen≃' (Lim→ permSeq)
-- Iso.fun plIso = plInv
-- Iso.inv plIso = plFun
-- Iso.rightInv plIso = SC.elim _ _  w
--   where

--     lemW : ∀ k n → ∀ e pK pN →
--            Path (Lim→ permSeq)
--              (SC.inl {n = k} (e , pK) )
--              (SC.inl {n = n + k} (e , pN))
--     lemW k zero e pK pN = cong (SC.inl {X = permSeq}
--          {n = k} ∘ (e ,_)) (snd (constFromIsoH e k) pK pN)
--     lemW k (suc n) e pK pN = lemW k n e pK _
--        ∙∙ push (e , λ x x₁ → pK x (≤-trans {k} {n + k} {x} (n≤k+n k) x₁))
--        ∙∙ cong (SC.inl {X = permSeq} {n = suc n + k}
--              ∘ (e ,_)) (snd (constFromIsoH e (suc (n + k))) _ pN)
    
    
--     lemW' : ∀ k n → k ≤ n →  ∀ e pK pN →
--            Path (Lim→ permSeq)
--              (SC.inl {n = k} (e , pK) )
--              (SC.inl {n = n} (e , pN))
--     lemW' = <-elim _ lemW


--     w : ElimData permSeq (λ z → Iso.fun plIso (Iso.inv plIso z) ≡ z)
--     ElimData.finl w {k} (x , p) =
--       let z = (AllFrom.ΣallFromP→LeastAllFromP< _
--               (λ _ → discreteℕ _ _) k k p (≤-refl k))
--       in lemW' _ _ z _ _ _
--     ElimData.fpush w {k} (x , p) =
--       {!!}
      
-- Iso.leftInv plIso (x , (k , (p , q))) =
--   Σ≡Prop (snd ∘ isFinGen≃') refl


-- [Fin→Fin]→[ℕ→ℕ] : ∀ n → ((Fin n) → ℕ)
--                         → ℕ → ℕ
-- [Fin→Fin]→[ℕ→ℕ] zero x x₁ = x₁
-- [Fin→Fin]→[ℕ→ℕ] (suc zero) x x₁ = x₁
-- [Fin→Fin]→[ℕ→ℕ] (suc (suc n)) f zero = (f (zero , tt))
-- [Fin→Fin]→[ℕ→ℕ] (suc (suc n)) f (suc x₁) =
--  suc ([Fin→Fin]→[ℕ→ℕ] (suc n) (f ∘ sucF) x₁)


[Fin→Fin]→[ℕ→ℕ]' : ∀ n → ((Fin n) → ℕ) → ∀ k → Dec (suc k ≤ n) → ℕ 
[Fin→Fin]→[ℕ→ℕ]' n f k (yes p) = f (k , p)
[Fin→Fin]→[ℕ→ℕ]' n f k (no ¬p) = k

[Fin→Fin]→[ℕ→ℕ] : ∀ n → ((Fin n) → ℕ) 
                        → ℕ → ℕ
[Fin→Fin]→[ℕ→ℕ] n f k = [Fin→Fin]→[ℕ→ℕ]' n f k ((suc k) ≤? n)

-- -- [Fin→Fin]→[ℕ→ℕ]compute : ∀ n f → [Fin→Fin]→[ℕ→ℕ]
-- -- [Fin→Fin]→[ℕ→ℕ]compute = ?

CFIso→IsoFin : ∀ n → IsoCF n → Iso (Fin n) (Fin n) 
CFIso→IsoFin n (isom , p) = w
  where

   module u = Iso isom

   w : Iso (Fin n) (Fin n)
   Iso.fun w (k , k<) = u.fun k , IsoCFpres<n n (isom , p) _ k<
   Iso.inv w (k , k<) = u.inv k ,
     IsoCFpres<n n (invIso isom , constFromInvIso n isom p) _ k<
   Iso.rightInv w (k , k<) = ≡Fin {n = n} (u.rightInv k)
   Iso.leftInv w (k , k<) = ≡Fin {n = n} (u.leftInv k)



IsoFin→CFIso : ∀ n → Iso (Fin n) (Fin n) → IsoCF n
IsoFin→CFIso n isom = w
  where

   module u = Iso isom

   
   ri' : (isom : Iso (Fin n) (Fin n)) → 
        (b : ℕ) → ∀ p' p  →
          [Fin→Fin]→[ℕ→ℕ]' n (λ x → fst (Iso.fun isom x))
          ([Fin→Fin]→[ℕ→ℕ]' n (λ x → fst (Iso.inv isom x)) b p')
          p
          ≡ b
   ri' isom b (yes p₁) (yes p) =
     cong′ (fst ∘' Iso.fun isom) (≡Fin {n = n} refl)
       ∙ cong fst (Iso.rightInv isom (b , p₁))
   ri' isom b (yes p) (no ¬p) = ⊥.rec (¬p (snd (Iso.inv isom (b , p))))
   ri' isom b (no ¬p) (yes p) = ⊥.rec (¬p p)
   ri' isom b (no ¬p) (no ¬p₁) = refl

   ri : (isom : Iso (Fin n) (Fin n)) → 
     section ([Fin→Fin]→[ℕ→ℕ] n (fst ∘ (Iso.fun isom)))
             ([Fin→Fin]→[ℕ→ℕ] n (fst ∘ (Iso.inv isom)))
   ri isom b = ri' isom b
                (suc b ≤? n)
                (suc ([Fin→Fin]→[ℕ→ℕ] n (fst ∘ (Iso.inv isom)) b)  ≤? n) 
   
   w : IsoCF n
   Iso.fun (fst w) = [Fin→Fin]→[ℕ→ℕ] n (fst ∘ u.fun)
   Iso.inv (fst w) = [Fin→Fin]→[ℕ→ℕ] n (fst ∘ u.inv)
   Iso.rightInv (fst w) = ri isom
   Iso.leftInv (fst w) = ri (invIso isom)
   snd w m n≤m with (suc m ≤? n)
   ... | yes p = ⊥.rec (<→≥→⊥ {n} {suc m} n≤m p)
   ... | no ¬p = refl
   
IsoIsoCFIsoFin : ∀ n → Iso (IsoCF n) (Iso (Fin n) (Fin n)) 
Iso.fun (IsoIsoCFIsoFin n) = CFIso→IsoFin n
Iso.inv (IsoIsoCFIsoFin n) = IsoFin→CFIso n
Iso.rightInv (IsoIsoCFIsoFin n) e =
   Iso≡Set-fun (isSetFin {n}) (isSetFin {n}) _ _
     (λ x → ≡Fin {n} (w x (suc (fst x) ≤? n)))
 where
   module u = Iso e
   
   w : (x : Fin n) → ∀ q →
          ([Fin→Fin]→[ℕ→ℕ]' n (fst ∘ u.fun) (fst x) q) ≡ fst (u.fun x) 
   w x (yes p) = cong (fst ∘ u.fun) (≡Fin {n = n} refl)
   w x (no ¬p) = ⊥.rec (¬p (snd x))
   
Iso.leftInv (IsoIsoCFIsoFin n) (e , p) =
  Σ≡Prop (λ e → snd (constFromIsoH e n))
    (Iso≡Set-fun isSetℕ isSetℕ _ _
      λ x → w x (suc x ≤? n))
  where
   w : (x : ℕ) → ∀ p → 
      [Fin→Fin]→[ℕ→ℕ]' n (Iso.fun e ∘ fst) x p ≡
      e .Iso.fun x
   w x (yes p) = refl
   w x (no ¬p) = sym (p x (¬<-≥ x n ¬p))



-- to≃η : ∀ k → fst (to≃ (η k)) ≡ adjTransposition k
-- to≃η k = refl

-- to≃rotFG : ∀ k → fst (to≃ (rotFG k)) ≡ rot' k
-- to≃rotFG zero = refl
-- to≃rotFG (suc zero) = refl
-- to≃rotFG (suc (suc k)) =

-- let z = sucFunResp∘ (fst (to≃ (sucFGℕ≃ℕ (rotFG k)))) swap0and1
--          ∙ cong ( sucFun ) (to≃rotFG (suc k))
-- in cong (_∘' sucFun swap0and1 ∘ swap0and1)
--      (sym (to≃suc (sucFGℕ≃ℕ (rotFG k)))) ∙ cong (_∘' swap0and1) z

-- CFisoElim' : ∀ {ℓ} (A : Iso ℕ ℕ  → Type ℓ)
--           → A idIso          
--           → (∀ n → (∀ e → isLB e n →  A e)
--                → ∀ e k → k ≤ n
--                → isLB (compIso  (sucIso e) (rotIso' k))
--                     (suc n) → A (compIso  (sucIso e) (rotIso' k)))
--           → ∀ e n → isLB e n → A e
--           --    → ∀ e k p → A (suc n)
--           --         (compIso  (sucIso e) (adjTransposition≃ k))
--           --         {!isConstFrom∘ ? ? ? ? ? ?!})
--           -- → ∀ n e p → A n e p
-- CFisoElim' A A₀ _ e zero p = {!!}
-- CFisoElim' A A₀ As e (suc n) p =
--   let ((k , k<) , (e' , p')) = Iso.fun (unwindIsoIsoCF n) (e , fst p)
--       z = CFisoElim' A A₀ As e' n (p' , {!!})
--   in {!!}  


-- CFisoElim : ∀ {ℓ} (A : ∀ n → (e : Iso ℕ ℕ)
--     → (Least (fst ∘  (isConstFrom (Iso.fun e)))) n → Type ℓ)
--           → A 0 idIso ((λ _ _ → refl) , λ _ x _ → x)          
--           → (∀ n → (∀ e p → A n e p)
--              → ∀ e k p → A (suc n)
--                   (compIso  (sucIso e) (adjTransposition≃ k))
--                   {!isConstFrom∘ ? ? ? ? ? ?!})
--           → ∀ n e p → A n e p
-- CFisoElim A a0 aS = {!!}

-- isFGLi'lem : ∀ 𝑘 e m m'
--                (p
--                 : ⟨
--                   isConstFrom (Iso.fun (compIso (adjTransposition≃ (suc 𝑘)) e))
--                   (suc m)
--                   ⟩)
--                (p' : ⟨ isConstFrom (Iso.fun e) (suc m') ⟩)  →
--              fst
--              (snd
--               (Iso.fun (unwindIsoIsoCF m)
--                (compIso (adjTransposition≃ (suc 𝑘)) e , p)))
--              ≡
--              compIso (adjTransposition≃ 𝑘)
--              (fst (snd (Iso.fun (unwindIsoIsoCF m') (e , p'))))
-- isFGLi'lem 𝑘 e m m' p p' = {!!}
   -- Iso≡Set isSetℕ isSetℕ _ _
   --    (λ _ → refl)
   --    λ _ → {!!}




rotRotCase : (e0 e1 : ℕ) → Type
rotRotCase e0 e1 =
  (Σ ((Σ _ λ e0' → suc e0' ≡ e0))
       λ ((e0' , _)) →
          (e1 < (suc e0'))
           × ((predℕ (Iso.inv (compIso swap0and1≃ (sucIso (rotIso' e0')))
             (e1))) ≡ e1) × 
               (Iso.inv (rotIso' e1) (suc e0') ≡ suc e0'))





<→rotRotCase : (e0 e1 : ℕ) → e1 < e0 → rotRotCase e0 e1
<→rotRotCase (suc e0) e1 x =
  (e0 , refl) , x , rot'< e1 e0 x , rotIsoConstInv e1 (suc e0) x


rotRotCases : (e0 e1 : ℕ) → ¬ e0 ≡ e1 →
               rotRotCase e1 e0 ⊎ rotRotCase e0 e1
rotRotCases e0 e1 = 
      map-⊎ (<→rotRotCase _ _) (<→rotRotCase _ _)
   ∘ ¬≡ℕ-cases e0 e1

lll : ∀ e0 e1 → e0 < suc e1 → predℕ
      (swap0and1
       (sucFun (Iso.inv (cases idIso rotIso e1))
        e0))
      ≡ predℕ (Iso.inv (rotIso e1) e0)
lll zero zero x = refl
lll e0 (suc e1) x = refl

rotRotElim : (A :  (e0 e1 : ℕ) (e0' e1' : ℕ) → Type ℓ)
          → (∀ e0 e1 → e1 < (suc e0) → A (suc e0) (e1) e0 e1)
          → (∀ e0 e1 → e0 < (suc e1) → A (e0) (suc e1)  e0 e1)
          → (e0 e1 : ℕ) → ¬ e0 ≡ e1
          → A e0 e1 (predℕ (Iso.inv (rotIso' e1) e0)) (predℕ (Iso.inv (rotIso' e0) e1))
rotRotElim A c< c> e0 e1 =


  ⊎.elim (λ ((e0' , p0) , p , q , r) →
          let pe0 : e0' ≡ (predℕ (Iso.inv (rotIso' e0) e1))
              pe0 = cong predℕ (sym r) ∙ cong (predℕ ∘ (Iso.inv (rotIso' e0))) p0
              pe1 : e0 ≡ (predℕ (Iso.inv (rotIso' e1) e0))
              pe1 = sym q ∙ lll e0 e0' p ∙
                 cong₂ (λ e0 → predℕ ∘ (Iso.inv (rotIso' e0))) p0 (λ _ → e0)
          in transport (λ i → A e0 (p0 i) (pe1 i) (pe0 i)) (c> e0 e0' p))
         (λ ((e0' , p0) , p , q , r) → 
           let pe0 : e0' ≡ (predℕ (Iso.inv (rotIso' e1) e0))
               pe0 = cong predℕ (sym r) ∙ cong (predℕ ∘ (Iso.inv (rotIso' e1))) p0
               pe1 : e1 ≡ (predℕ (Iso.inv (rotIso' e0) e1))
               pe1 = sym q ∙∙ lll e1 e0' p ∙∙ 
                    cong (λ e0 → predℕ (Iso.inv (rotIso' e0) e1)) p0 
           in transport (λ i → A (p0 i) e1 (pe0 i) (pe1 i)) (c< e0' e1 p)) 
          
   ∘ rotRotCases _ _



isFGliK0 : ∀ n m → ¬ n ≡ m →
              (sucFGℕ≃ℕ (rotFG (predℕ ((Iso.inv (rotIso' n) m))))) · rotFG n
              ≡ zero ∷ ((sucFGℕ≃ℕ (rotFG (predℕ
                (Iso.inv (rotIso' m) n))) · rotFG m))
isFGliK0 = rotRotElim
  (λ n m n' m' →
     (sucFGℕ≃ℕ (rotFG (m'))) · rotFG n
              ≡ zero ∷ ((sucFGℕ≃ℕ (rotFG (n')) · rotFG m)))
  caseA caseB
 where
  caseA : (e0 e1 : ℕ) →
            e1 < suc e0 →
            (sucFGℕ≃ℕ (rotFG e1) · rotFG (suc e0)) ≡
            zero ∷ (sucFGℕ≃ℕ (rotFG e0) · rotFG e1)
  caseA e0 zero x = cong′ (0 ∷_) (sym (idr _)) 
  caseA (suc e0) (suc e1) x =
    let z = caseA e0 e1 x
    in  cong′ (1 ∷_) (
        ((assoc· ((sucFGℕ≃ℕ (sucFGℕ≃ℕ (rotFG e1)))) (η 0) _ ∙
           cong′ (_· (sucFGℕ≃ℕ (zero ∷ sucFGℕ≃ℕ (rotFG e0))))
             (sucSucComm (rotFG e1))
         ∙ (sym (assoc· (η 0) (sucFGℕ≃ℕ (sucFGℕ≃ℕ (rotFG e1))) _)))
          ∙ cong′ (0 ∷_)
           (sym (sucFGℕ≃ℕresp· (sucFGℕ≃ℕ (rotFG e1)) (zero ∷ sucFGℕ≃ℕ (rotFG e0)))
            ∙ cong sucFGℕ≃ℕ z))
          ∙ cong′ (λ x → 0 ∷ 1 ∷ x)
           (sucFGℕ≃ℕresp· (sucFGℕ≃ℕ (rotFG e0)) (rotFG e1)))
       ∙ sym (braid _ _)
      ∙ cong′ (λ x → 0 ∷ 1 ∷ x)
       ((cong′ (_· (sucFGℕ≃ℕ (rotFG e1)))
         (sym (sucSucComm (rotFG e0))))
         ∙ (sym (assoc· (sucFGℕ≃ℕ (sucFGℕ≃ℕ (rotFG e0))) (η zero) (sucFGℕ≃ℕ (rotFG e1))))) 
         
  caseB : (e0 e1 : ℕ) →
            e0 < suc e1 →
            (sucFGℕ≃ℕ (rotFG e1) · rotFG e0) ≡
            zero ∷ (sucFGℕ≃ℕ (rotFG e0) · rotFG (suc e1))
  caseB e1 e0 x =
    let z = caseA e0 e1 x
    in sym (invo _ _) ∙ sym (cong (zero ∷_) z)


-- blockGLI : (n m : ℕ) → Type
-- blockGLI n m =  < max n m 

FinGen≃'ConstCases : ℕ → Iso ℕ ℕ → Type₀   
FinGen≃'ConstCases x e =
   𝟚.if (𝟚.Dec→Bool (x ≤? 1))
    then e ≡ idIso
    else Unit

FinGen≃'cc : ∀ k e → ⟨ isConstFrom (Iso.fun e) k ⟩
              → FinGen≃'ConstCases k e
FinGen≃'cc zero e x = Iso≡Set-fun isSetℕ isSetℕ _ _ (λ k → x k _)
FinGen≃'cc (suc zero) e x = Iso≡Set-fun isSetℕ isSetℕ _ _  w
  where

    ww : ∀ k → e .Iso.fun 0 ≡ suc k → ⊥
    ww k p = 
      znots (sym (Iso.leftInv e 0) ∙ (cong (Iso.inv e) p)
        ∙ constFromInvIso 1 e x (suc k) _)

    w : (x₁ : ℕ) → e .Iso.fun x₁ ≡ idIso .Iso.fun x₁
    w zero = ≢suc→≡zero ww
    w (suc x₁) = x (suc x₁) _
  

FinGen≃'cc (suc (suc _)) _ _ = _

retract-to≃'-from≃' : section to≃' from≃'
retract-to≃'-from≃' (f , n , (X , LX)) =
  Σ≡Prop (snd ∘ isFinGen≃')
    (isoFGriLem f n X)


isFGli'IdId : ∀ k e
     → (compIso (adjTransposition≃ k) e) ≡ idIso
     → e ≡ idIso → ⊥
isFGli'IdId k e P P' =
  kAdjTlem k (funExt⁻
    (cong′ Iso.fun
      (sym P ∙
        cong′ (compIso (adjTransposition≃ k)) P')) k)

from≃IdIso : ∀ m' p' → from≃ idIso m' p' ≡ ε
from≃IdIso zero p' = refl
from≃IdIso (suc m') p' =
  idr (sucFGℕ≃ℕ
       (from≃ (fst (snd (Iso.fun (unwindIsoIsoCF m') (idIso , p')))) m'
        (snd (snd (Iso.fun (unwindIsoIsoCF m') (idIso , p'))))))
     ∙ 
     cong′ sucFGℕ≃ℕ ( cong₂ (λ e p → from≃ e m' p)
       unwindIsoIdIso
         (isProp→PathP (λ i →
            snd (isConstFrom (Iso.fun (unwindIsoIdIso i)) m')) _ _)
       ∙ from≃IdIso m' λ _ _ → refl)
       
  -- idr (sucFGℕ≃ℕ {!sucFGℕ≃ℕ (from≃ ? m' ?)!})
  --   ∙ {!!} ∙ (cong sucFGℕ≃ℕ (from≃IdIso m' {!!})) ∙ {!!}

from≃adjT : ∀ k m p →
   from≃ (adjTransposition≃ k) m  p ≡ k ∷ ε
from≃adjT k zero p = ⊥.rec (kAdjTlem k (sym (p k _)))
from≃adjT k (suc zero) p =
   ⊥.rec (kAdjTlem k
    (sym (funExt⁻ (cong Iso.fun (FinGen≃'cc 1 (adjTransposition≃ k) p)) k)))
from≃adjT zero (suc (suc zero)) p = refl
from≃adjT zero (suc (suc (suc m))) p =
 let z = (cases ⊥.rec (cases ⊥.rec λ _ _ → refl))
 in from≃lem (adjTransposition≃ zero) (adjTransposition≃ zero)
     (suc (suc (suc m))) (suc (suc m)) p z refl
       ∙ from≃adjT zero (suc (suc m))
      z

from≃adjT (suc k) (suc (suc m)) p =
  (idr (sucFGℕ≃ℕ (from≃HLP (adjTransposition≃ (suc k)) (suc m) p))
     ∙ cong sucFGℕ≃ℕ
       (from≃lem
         (unwindIso (adjTransposition≃ (suc k))) (adjTransposition≃ k)
         (suc m) (suc (suc k))
           (unwindConstFromIso (suc m) (adjTransposition≃ (suc k)) p)
           ((isConstFrom-adjTransposition k))
           (unwindIsoAdjT k)))
    ∙ cong sucFGℕ≃ℕ (from≃adjT k (suc (suc k))
           (isConstFrom-adjTransposition k))

isFGli'Id : ∀ k e m p
     → (p : ⟨ isConstFrom (Iso.fun (compIso (adjTransposition≃ k) e)) m ⟩)
     → e ≡ idIso
     →  from≃ (compIso (adjTransposition≃ k) e) m  p ≡
         k ∷ ε
isFGli'Id k e m p p₁ x =
   cong₂ (λ e p → from≃ e m p)
     (cong (compIso _) x ∙ compIsoIdR _)
       (isProp→PathP (λ i →
            snd (isConstFrom
      (Iso.fun
       (((λ i₁ → compIso (adjTransposition≃ k) (x i₁)) ∙
         compIsoIdR (adjTransposition≃ k))
        i))
      m)) p₁ p)
     ∙ from≃adjT k m p


isFGli''-Hlp : ℕ → ℕ → Type 
isFGli''-Hlp m m' = 
  𝟚.True ( 2 ≤? max m m')

isFGli'-hlp : ∀ k e m m' →
       (⟨ isConstFrom (Iso.fun (compIso (adjTransposition≃ k) e)) m ⟩) → 
       (⟨ isConstFrom (Iso.fun e) m' ⟩) →
       isFGli''-Hlp m m'
 
isFGli'-hlp k e m m' p p' with FinGen≃'cc m' e p' | FinGen≃'cc m ((compIso (adjTransposition≃ k) e)) p
isFGli'-hlp k e zero zero p p' | w | ww = isFGli'IdId k e ww w 
isFGli'-hlp k e zero (suc zero) p p' | w | ww = isFGli'IdId k e ww w
isFGli'-hlp k e zero (suc (suc m')) p p' | w | ww = tt
isFGli'-hlp k e (suc zero) zero p p' | w | ww = isFGli'IdId k e ww w
isFGli'-hlp k e (suc (suc m)) zero p p' | w | ww = tt
isFGli'-hlp k e (suc zero) (suc zero) p p' | w | ww = isFGli'IdId k e ww w
isFGli'-hlp k e (suc zero) (suc (suc m')) p p' | w | ww = tt
isFGli'-hlp k e (suc (suc m)) (suc zero) p p' | w | ww = tt
isFGli'-hlp k e (suc (suc m)) (suc (suc m')) p p' | w | ww = tt


isFGli''M<2 : ∀ n k e m m' p p'
              → e ≡ idIso → m' ≤ n → suc k < n →
            
           from≃ (compIso (adjTransposition≃ k) e) (suc (suc m))  p ≡
           k ∷ from≃ e m' p'
isFGli''M<2 n k e m m' p p' H x k< = 
  let z : k ≤ m
      z = isConstFrom-adjTransposition<m k (suc (suc m))
        (subst (λ e → ⟨ isConstFrom e
            (suc (suc m)) ⟩)
          (cong (_∘ adjTransposition k)
           (cong′ Iso.fun H)) p)
  in isFGli'Id k e (suc (suc m))
      (λ x₁ x₂ → isConstFrom-adjTransposition k x₁
        (≤-trans {suc (suc k)} {suc (suc m)} {x₁} z x₂)) p H
    ∙ cong′ (k ∷_) (sym (from≃IdIso zero λ _ _ → refl)
     ∙ from≃lem idIso e zero m' (λ _ _ → refl) p'
       (sym H))


isFGli''M'<2 : ∀ n k e m m' p p'
              → (compIso (adjTransposition≃ k) e) ≡ idIso
                → (suc (suc m')) ≤ n → suc k < n →
            
           from≃ (compIso (adjTransposition≃ k) e) m  p ≡
           k ∷ from≃ e (suc (suc m')) p'
isFGli''M'<2 n k e m m' p p' H x k< = 
  let H' : adjTransposition≃ k ≡ e
      H' =  Iso≡Set-fun isSetℕ isSetℕ _ _
              (λ x → sym (funExt⁻ (cong′ Iso.fun H) (adjTransposition k x))
                ∙ cong (Iso.fun e) (isInvolutionAdjTransposition k x))
         
  in from≃lem _ _ m m p (λ _ _ → refl) H ∙ from≃IdIso m (λ _ _ → refl) ∙ sym (invo _ _)
      ∙ cong′ (k ∷_) (sym (from≃adjT k (suc (suc k))
        (isConstFrom-adjTransposition k))
         ∙ from≃lem _ _ (suc (suc k)) (suc (suc m'))
             (isConstFrom-adjTransposition k) p' H' )


unwindPermHeadCompSwap0and1FST : (e : Iso ℕ ℕ)
       → unwindIso (unwindIso e) ≡
         unwindIso (unwindIso (compIso swap0and1≃ e))
unwindPermHeadCompSwap0and1FST e = 
  Iso≡Set-fun isSetℕ isSetℕ _ _
    (λ x → cong′ predℕ ((rotRotElim
      (λ e0 e1 e0' e1' →
          ∀ eX (eX≢e0 : ¬ eX ≡ e0) (eX≢e1 : ¬ eX ≡ e1) →
              (Iso.inv (rotIso' e1') (predℕ (Iso.inv (rotIso' e0) eX)))
                ≡
              (Iso.inv (rotIso' e0') (predℕ (Iso.inv (rotIso' e1) eX))))
          w1
          (λ e0 e1 x₁ eX eX≢e0 eX≢e1 →
             sym (w1 e1 e0 x₁ eX eX≢e1 eX≢e0))
          (Iso.fun e 0) (Iso.fun e 1) (znots ∘ isoFunInjective e _ _))
            (Iso.fun e (suc (suc x)))
              ((snotz ∘ isoFunInjective e _ _))
              ((snotz ∘ injSuc ∘ isoFunInjective e _ _)))) 
  where
    w1 : (e0 e1 : ℕ) → e1 < suc e0 → (eX : ℕ) → ¬ eX ≡ suc e0 → ¬ eX ≡ e1 →           
           (Iso.inv (rotIso' e1) (predℕ (Iso.inv (rotIso' (suc e0)) eX)))
         ≡ (Iso.inv (rotIso' e0) (predℕ (Iso.inv (rotIso' e1) eX)))
    w1 e0 e1 x eX x₁ x₂ with ¬≡ℕ-cases _ _ x₁
    ... | inl eX≤e0  =
       let z = suc-predℕ _ (rot'-≢k→≢0 e1 eX (x₂ ∘ sym) ∘ sym)
       in cong′ (Iso.inv (rotIso' e1) ∘ predℕ)
               (sym (rot'-<k (suc e0) eX eX≤e0)) ∙
                (z ∙ rot'-<k e0 (predℕ (Iso.inv (rotIso' e1) eX))
                (⊎.rec (λ eX<e1 → subst (_< e0)
                             (cong predℕ (rot'-<k e1 eX eX<e1))
                                (≤-trans {suc eX} {e1} {e0} eX<e1 x))
                       (λ e1<eX → subst {x = eX}
                             {y = suc (predℕ (Iso.inv (cases idIso rotIso e1) eX))}
                               (_≤ e0)
                          (sym (rot'-k< e1 eX e1<eX) ∙ z) eX≤e0)
                           (¬≡ℕ-cases _ _ x₂)))
    ... | inr x₃ = 
       cong′ (Iso.inv (rotIso' e1) ∘ predℕ)
         (rot'-k< (suc e0) eX x₃)
        ∙∙ rot'-k< e1 (predℕ eX) (≤predℕ (suc e1) eX
          (≤-trans {suc (suc e1)} {suc (suc e0)} {eX} x x₃ ))
        ∙∙ (sym (rot'-k< e0 (predℕ eX) (≤predℕ (suc e0) eX x₃))
          ∙ cong′ (Iso.inv (rotIso' e0) ∘ predℕ)
             (sym (rot'-k< e1 eX (≤-trans {suc e1} {suc e0} {eX}
                x (<-weaken {suc e0} {eX} x₃)))))

isFGli'' : ∀ n k e m m' p p'
              → isFGli''-Hlp m m' → m' ≤ n → suc k < n →
          
           from≃ (compIso (adjTransposition≃ k) e) m  p ≡
           k ∷ from≃ e m' p'
isFGli'' n k e zero (suc (suc m')) p p' H x k< =
   isFGli''M'<2 n k e zero m' p p' (FinGen≃'cc zero _ p) x k<
isFGli'' n k e (suc (suc m)) zero p p' H x k< =
   isFGli''M<2 n k e m zero p p' (FinGen≃'cc zero e p') x k<
isFGli'' n k e (suc zero) (suc (suc m')) p p' H x k< =
   isFGli''M'<2 n k e 1 m' p p' (FinGen≃'cc 1 _ p) x k<
isFGli'' n k e (suc (suc m)) (suc zero) p p' H x k< =
   isFGli''M<2 n k e m 1 p p' (FinGen≃'cc 1 e p') x k<

isFGli'' (suc (suc n)) zero e (suc (suc m)) (suc (suc m')) p p' H x k< = 
 let ee1 = _ --Iso.fun e 1
     ee0 = _ --Iso.fun e 0

     e0 = (Iso.inv (rotIso' ee1) ee0) --Iso.fun e zero
     e1 = _

     e0' = _
     e1' = Iso.inv (rotIso' ee0) ee1
     
     eL = (from≃ _ m _)
     eR = (from≃ _ m' _)
 in cong′ (_· rotFG e1) (sucFGℕ≃ℕresp· (sucFGℕ≃ℕ eL) (rotFG (predℕ e0)))
       ∙ sym (assoc· (sucFGℕ≃ℕ (sucFGℕ≃ℕ eL))
            (sucFGℕ≃ℕ (rotFG (predℕ e0))) (rotFG e1))
       ∙ cong₂' _·_ (cong′ (sucFGℕ≃ℕ ∘' sucFGℕ≃ℕ)
            (from≃lem _ _ m m' _ _ (sym (unwindPermHeadCompSwap0and1FST e))))
            (isFGliK0 ee1 ee0 (snotz ∘ isoFunInjective e _ _))            
       ∙ assoc· (sucFGℕ≃ℕ (sucFGℕ≃ℕ eR))
          (η zero) ((sucFGℕ≃ℕ (rotFG (predℕ e1')) · rotFG e0' ))
       ∙ cong′ (_· ((sucFGℕ≃ℕ (rotFG (predℕ e1')) · rotFG e0' ))) (sucSucComm eR)
       ∙ sym (assoc· (η zero) (sucFGℕ≃ℕ (sucFGℕ≃ℕ eR))
             (sucFGℕ≃ℕ (rotFG (predℕ e1')) · rotFG e0' )) ∙ cong′ (zero ∷_)
          (assoc· (sucFGℕ≃ℕ (sucFGℕ≃ℕ eR))
            (sucFGℕ≃ℕ (rotFG (predℕ e1'))) (rotFG e0') ∙ cong′ (_· rotFG e0')
            (sym (sucFGℕ≃ℕresp· (sucFGℕ≃ℕ eR) (rotFG (predℕ e1')))))


isFGli'' (suc n) (suc 𝑘) e (suc m) (suc m') p p' H m'< 𝑘< =
  let ((k , k<) , (x' , X')) = Iso.fun (unwindIsoIsoCF m') ( e , p')
      ((k* , k<*) , (x'* , X'*)) = Iso.fun (unwindIsoIsoCF m)
            ((compIso (adjTransposition≃ (suc 𝑘)) e) , p)
      X* = (isConstFrom∘ (Iso.fun x') m' _ (suc (suc 𝑘))
            X' ((isConstFrom-adjTransposition 𝑘)))     
  in cong′ (_· (rotFG (Iso.fun e zero)))      
      (cong′ sucFGℕ≃ℕ {x = (from≃ x'* m X'*)}
        (from≃lem x'* ((compIso (adjTransposition≃ 𝑘) x'))
           m ((max ((suc (suc 𝑘))) m'))
           X'* _ (Iso≡Set-fun isSetℕ isSetℕ _ _ (λ _ → refl))
          ∙ isFGli'' n 𝑘 x' ((max ((suc (suc 𝑘))) m')) m'
          X* X' (isFGli'-hlp 𝑘 x' (max (suc (suc 𝑘)) m') m' X* X')  m'< 𝑘<))
    ∙ sym (assoc· (η (suc 𝑘))
      (sucFGℕ≃ℕ (from≃ x' m' X')) (rotFG (Iso.fun e zero)))

isFGli : ∀ k e p → 
           from≃' (isFinGen≃∘ (adjTransposition≃ k
             , isFinGen'AdjTransposition≃ k) (e , p)) ≡
           k ∷ from≃' (e , p)
isFGli k e (n , X) =
  let (_ , (n' , X')) = (isFinGen≃∘ (adjTransposition≃ k
                   , isFinGen'AdjTransposition≃ k) (e , (n , X)))
  in isFGli'' (max (suc (suc k)) n) k e n' n (fst X') (fst X)
         (isFGli'-hlp k e n' n (fst X') (fst X))
         (right-≤-max (suc (suc k)) n)
         ((left-≤-max (suc (suc k)) n)) 

isoFG : Iso FGℕ≃ℕ FinGen≃'
Iso.fun isoFG = to≃'
Iso.inv isoFG = from≃' 
Iso.rightInv isoFG = retract-to≃'-from≃'
Iso.leftInv isoFG = RelimProp.f w
 where   
  w : RelimProp _
  RelimProp.isPropA w _ = trunc _ _
  RelimProp.εA w = refl
  RelimProp.∷A w k {xs} X = isFGli k (fst (to≃' xs)) (snd (to≃' xs)) 
      ∙ cong (k ∷_) X

