{-# OPTIONS --safe #-}
module Cubical.Data.Nat.FinGenAut where

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
open import Cubical.Data.Maybe
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


import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.HITs.GroupoidQuotients as GQ
  renaming ([_] to [_]// ; RelimProp to  RelimProp// ; Rrec to Rrec//)


-- open import Cubical.Algebra.Group.Morphisms

-- open import Cubical.Algebra.Group.Generators


private
  variable
    ℓ : Level


infixr 9 _∘'_

_∘'_ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
        → (g : B → C) → (f : A → B) → A → C 
g ∘' f = λ x → g (f x)
{-# INLINE _∘'_ #-}


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



commT : ℕ → ℕ → Type₀
commT x zero = ⊥
commT x (suc zero) = ⊥
commT zero (suc (suc x₁)) = Unit
commT (suc k) (suc (suc l)) = commT k (suc l)

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


adjTransposition≃ : ℕ → ℕ ≃ ℕ
adjTransposition≃ k = involEquiv
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
  
to≃ : FGℕ≃ℕ → ℕ ≃ ℕ
to≃ = Rrec.f to≃R
  where

   to≃R : Rrec (ℕ ≃ ℕ)
   Rrec.isSetA to≃R = isOfHLevel≃ 2 isSetℕ isSetℕ
   Rrec.εA to≃R = idEquiv _ 
   Rrec.∷A to≃R k = adjTransposition≃ k ∙ₑ_
   Rrec.invoA to≃R k x =
    equivEq (cong (fst x ∘_) (funExt (isInvolutionAdjTransposition k)))
   Rrec.braidA to≃R k x = 
    equivEq (cong ((fst x) ∘_) (adjTranspositionBraid k))
   Rrec.commA to≃R k l z x = 
    equivEq (cong ((fst x) ∘_) (adjTranspositionComm k l z))

to≃· : ∀ f g → fst (to≃ (f · g)) ≡ fst (to≃ f ∙ₑ to≃ g)
to≃· = RelimProp.f w
  where
    w : RelimProp _
    RelimProp.isPropA w _ = isPropΠ λ _ → isSet→ isSetℕ _ _ 
    RelimProp.εA w x = refl
    RelimProp.∷A w k x = cong (_∘ adjTransposition k) ∘ x


isConstFrom : (ℕ → ℕ) → ℕ → hProp ℓ-zero
isConstFrom f k = (∀ x → k ≤ x → f x ≡ x) , isPropΠ2 λ _ _ → isSetℕ _ _  

-- isSmalest : ∀ {ℓ} → (ℕ → hProp ℓ) → (ℕ → hProp ℓ) 
-- isSmalest x n = x n L.⊓ (L.∀[ n' ] (x n') L.⇒ ((n ≤ n') , isProp≤))

    
isFinGen≃ : ℕ ≃ ℕ → hProp ℓ-zero
isFinGen≃ (e , _) = L.∃[ k ] isConstFrom e k

-- isPropΣisSmalest : ∀ {ℓ} P → isProp (Σ _ (fst ∘ isSmalest {ℓ} P))
-- isPropΣisSmalest P (n , (Pn , nSmlst)) (m , (Pm , mSmlst)) with n ≟ m
-- ... | lt x = ⊥.rec (<-asym {m = {!m!}} {n = {!m!}} x (mSmlst n Pn)) 
-- ... | eq x = Σ≡Prop (snd ∘ isSmalest P) x
-- ... | gt x = ⊥.rec (<-asym {m = {!!}} {n = {!!}} x (nSmlst m Pm))

open Minimal

isFinGen≃' : ℕ ≃ ℕ → hProp ℓ-zero
isFinGen≃' (e , _) = Σ ℕ (Least (fst ∘  (isConstFrom e)))
  , isPropΣLeast (snd ∘ isConstFrom e)

isFinGen≃'0→e≡idEquiv : ∀ e → (fst (isConstFrom e 0))
                              → e ≡ idfun _
isFinGen≃'0→e≡idEquiv e X = funExt λ x → X x _

-- isConstFrom→smalestBound :
--       ∀ f
--     → ⟨ L.∃[ k ] isConstFrom f k ⟩
--     → Σ ℕ (fst ∘ isSmalest (isConstFrom f))
-- isConstFrom→smalestBound f =
--   Prop.rec (isPropΣisSmalest (isConstFrom f))
--    (uncurry w)
--  where
--    w : (n : ℕ) (y : ⟨ isConstFrom f n ⟩) →
--          Σ ℕ (fst ∘ isSmalest (isConstFrom f))
--    w zero y = zero , ( y , λ  _ _ → _ )
--    w (suc n) y with discreteℕ (f n) n
--    ... | yes p = w n λ k → ⊎.rec (y k) (λ q → cong f (sym q) ∙∙ p ∙∙ q)
--                    ∘ ≤-split
--    ... | no ¬p = suc n ,
--       (y , {!!})
--         -- λ m z → ⊎.rec (idfun _)
--         -- (λ q → ⊥.rec (¬p (z n q)) ) ({!!}) )

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


section-isConstFrom : ∀ f g k → section g f 
   → ⟨ isConstFrom f k ⟩
   → ⟨ isConstFrom g k ⟩
section-isConstFrom f g k S X j j< =
  cong g (sym (X j j<)) ∙ S j

FinGen≃ : Type₀
FinGen≃ = Σ (ℕ ≃ ℕ) (fst ∘ isFinGen≃)

FinGen≃' : Type₀
FinGen≃' = Σ (ℕ ≃ ℕ) (fst ∘ isFinGen≃')



isConstFrom∘ : ∀ f k g l →
   ⟨ isConstFrom f k ⟩ → ⟨ isConstFrom g l ⟩
   →  ⟨ isConstFrom (f ∘ g) (max l k) ⟩
isConstFrom∘ f l g k s r j j< =
     let j= = r j (≤-trans {k = k}
                {m = max k l} {n = j} (left-≤-max k l) j<)
     in s _ (subst (l ≤_) (sym j=)
      (≤-trans {l} {max k l} {j} (right-≤-max k l) j<)
      ) ∙ j= 


isFinGen≃∘ : FinGen≃ → FinGen≃ → FinGen≃
fst (isFinGen≃∘ (e , _) (f , _)) = e ∙ₑ f
snd (isFinGen≃∘ (_ , p) (_ , q)) = 
  Prop.map2 (λ (k , r) (l , s) →
   max k _ , isConstFrom∘ _ l _ k s r) p q


isConstFrom-adjTransposition : ∀ k →
  ⟨ isConstFrom (adjTransposition k) (suc (suc k)) ⟩
isConstFrom-adjTransposition =
   ℕ.elim {A = λ k → ⟨ isConstFrom (adjTransposition k) (suc (suc k)) ⟩}
      (ℕ.cases (⊥.rec) (ℕ.cases (⊥.rec)
         λ _ _ → refl))
      (λ n X → sucFun-isConstFrom _ _ X) 


isFinGenAdjTransposition≃ : ∀ k → ⟨ isFinGen≃ (adjTransposition≃ k) ⟩
isFinGenAdjTransposition≃ k =
  Prop.∣ (suc (suc k)) , isConstFrom-adjTransposition k ∣₁


to≃' : FGℕ≃ℕ → FinGen≃
to≃' x = to≃ x , RelimProp.f w  x
   where
     w : RelimProp (fst ∘ isFinGen≃ ∘ to≃)
     RelimProp.isPropA w = snd ∘ isFinGen≃ ∘ to≃
     RelimProp.εA w = Prop.∣ zero , (λ _ _ → refl) ∣₁
     RelimProp.∷A w k {xs} z = snd (isFinGen≃∘
       (adjTransposition≃ k , isFinGenAdjTransposition≃ k) (to≃ xs , z)) 

-- to≃'' : FGℕ≃ℕ → FinGen≃'
-- to≃'' x = to≃ x , RelimProp.f w  x
--    where
--      w : RelimProp (fst ∘ isFinGen≃' ∘ to≃)
--      RelimProp.isPropA w = snd ∘ isFinGen≃' ∘ to≃
--      RelimProp.εA w = zero , (λ _ _ → refl) , λ _ _ → zero-≤
--      RelimProp.∷A w k {xs} z =
--        (max _ (fst z)) ,
--         (isConstFrom∘ _ _ _ _ (fst (snd z)) (isConstFrom-adjTransposition k) ,
--           {!to≃· ? ?!})
--        -- snd (isFinGen≃∘
--        --   (adjTransposition≃ k , isFinGenAdjTransposition≃ k) (to≃ xs , z)) 

-- -- -- getBnd : FGℕ≃ℕ → ℕ
-- -- -- getBnd = fst ∘ snd ∘ to≃''

-- -- -- getBnd· : ∀ e f → 
-- -- --          getBnd (e · f) RO.≤ max (getBnd e) (getBnd f) 
-- -- -- getBnd· = RelimProp.f w
-- -- --   where
-- -- --     w : RelimProp
-- -- --           (λ z → (f : FGℕ≃ℕ) → getBnd (z · f) RO.≤ max (getBnd z) (getBnd f))
-- -- --     RelimProp.isPropA w e = isPropΠ λ f → RO.isProp≤
-- -- --       {getBnd (e · f)} {max (getBnd e) (getBnd f)} 
-- -- --     RelimProp.εA w f = RO.≤-refl (getBnd f)
-- -- --     RelimProp.∷A w k {xs} g = {!!}
    
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

-- isConstFromSwap0And1 : ∀ n → ⟨ isConstFrom swap0and1 (2 + n) ⟩
-- isConstFromSwap0And1 x _ = refl

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


-- unwindConstFrom : ∀ k f → ⟨ isConstFrom f (suc k) ⟩
--                         → ⟨ isConstFrom (predFun f) k ⟩
-- unwindConstFrom k f x n k≤n =
--   cong predℕ (x (suc n) k≤n)

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



isFinGen≃→isFinGen≃' : ∀ e → ⟨ isFinGen≃ e ⟩ → ⟨ isFinGen≃' e ⟩
isFinGen≃→isFinGen≃' e =
  Prop.rec (snd (isFinGen≃' e))
           (AllFrom.ΣallFromP→LeastAllFromP _
             λ n → discreteℕ (fst e n) n)



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

rotFG : ℕ → FGℕ≃ℕ
rotFG zero = ε
rotFG (suc x) = zero ∷ sucFGℕ≃ℕ (rotFG x)


from≃ : (x : Iso ℕ ℕ) → (k : ℕ) →
     ⟨ isConstFrom (Iso.fun x) k ⟩
     → FGℕ≃ℕ 
from≃ x zero X = ε
from≃ x (suc n) X =
 let ((k , k<) , (x' , X')) = Iso.fun (unwindIsoIsoCF n)
          ( x , X)
 in sucFGℕ≃ℕ (from≃ x' n X') · rotFG k

resp·to≃ : ∀ f g → to≃ f ∙ₑ to≃ g ≡ to≃ (f · g) 
resp·to≃ = RelimProp.f w
  where
    w : RelimProp (λ z → (g : FGℕ≃ℕ) → to≃ z ∙ₑ to≃ g ≡ to≃ (z · g))
    RelimProp.isPropA w _ =
      isPropΠ λ _ → isOfHLevel≃ 2 (isSetℕ) (isSetℕ) _ _
    RelimProp.εA w g = equivEq refl
    RelimProp.∷A w k {xs} X g =
       equivEq (cong (_∘ adjTransposition k) (cong fst (X g)))
       

to≃suc : ∀ e → sucFun (fst (to≃ e)) ≡ fst (to≃ (sucFGℕ≃ℕ e))
to≃suc = RelimProp.f w
  where
   w : RelimProp (λ z → sucFun (fst (to≃ z)) ≡ fst (to≃ (sucFGℕ≃ℕ z)))
   RelimProp.isPropA w _ = isSet→ isSetℕ _ _
   RelimProp.εA w = refl =→ refl
   RelimProp.∷A w k {xs} X = sym (sucFunResp∘ (fst (to≃ xs))
     (adjTransposition k)) ∙ cong (_∘ sucFun (adjTransposition k)) X

-- to≃η : ∀ k → fst (to≃ (η k)) ≡ adjTransposition k
-- to≃η k = refl

to≃rotFG : ∀ k → fst (to≃ (rotFG k)) ≡ rot' k
to≃rotFG zero = refl
to≃rotFG (suc zero) = refl
to≃rotFG (suc (suc k)) =

 let z = sucFunResp∘ (fst (to≃ (sucFGℕ≃ℕ (rotFG k)))) swap0and1
          ∙ cong ( sucFun ) (to≃rotFG (suc k))
 in cong (_∘' sucFun swap0and1 ∘ swap0and1)
      (sym (to≃suc (sucFGℕ≃ℕ (rotFG k)))) ∙ cong (_∘' swap0and1) z


isoFG : Iso FGℕ≃ℕ FinGen≃'
Iso.fun isoFG = uncurry (λ x y → x , isFinGen≃→isFinGen≃' x y) ∘ to≃'
Iso.inv isoFG = uncurry λ x → uncurry
  (λ n y → from≃ (equivToIso x) n (fst y))
Iso.rightInv isoFG (f , p) =
 Σ≡Prop (snd ∘ isFinGen≃') (equivEq ((isFGri (equivToIso f) (fst p)
  (fst (snd p)))))

 where
  isFGri : ∀ f w (w₁ : ((fst (isConstFrom _ w)))) →
         to≃ (from≃ f w (w₁)) .fst ≡ Iso.fun f
  isFGri f zero X = funExt λ x → sym (X x _)
  isFGri f (suc w) X =
    let ((k , k<) , (x' , X')) = Iso.fun (unwindIsoIsoCF w)
          (f , X)
        z = (isFGri x' w X')
    in cong fst (sym (resp·to≃
        (sucFGℕ≃ℕ (from≃ x' w X')) (rotFG k)))
         ∙ cong₂ _∘'_
            (to≃rotFG k) (sym (to≃suc ((from≃ x' w X'))) ∙ cong sucFun z)
             ∙ cong (Iso.fun ∘ fst) (Iso.leftInv (unwindIsoIsoCF w) (f , X))

Iso.leftInv isoFG = RelimProp.f w
 where   
  w : RelimProp _
  RelimProp.isPropA w _ = trunc _ _
  RelimProp.εA w = refl
  RelimProp.∷A w k {xs} X =
    cong (Iso.inv isoFG) wwL ∙ ww k (to≃ xs) (fst wwLP) (snd wwLP)
      (fst (snd (Iso.fun isoFG xs)))
      (snd ((snd (Iso.fun isoFG xs))))
      ∙ cong (k ∷_) X

   where
    wwLP : fst (isFinGen≃' (adjTransposition≃ k ∙ₑ to≃ xs))
    wwLP = {!!} , {!!}
    
    wwL : (Iso.fun isoFG (k ∷ xs)) ≡
            ((adjTransposition≃ k ∙ₑ to≃ xs) , wwLP)
    wwL = Σ≡Prop (snd ∘ isFinGen≃') refl

    wwε : ∀ k → ∀ lp lr →
         Iso.inv isoFG ((adjTransposition≃ k) , lp)
        ≡
      k ∷ Iso.inv isoFG (idEquiv _ , (zero , lr))
    wwε = {!!}

    ww : ∀ k → ∀ e → ∀ m' lp m lr →
         Iso.inv isoFG ((adjTransposition≃ k ∙ₑ e) , (m' , lp))
        ≡
      k ∷ Iso.inv isoFG (e , (m , lr))
    ww k e zero lp zero lr = {!!}
    ww k e zero lp (suc m) lr = {!!}
    ww k e (suc m') lp zero lr = {!!}
    
    ww zero e (suc m') lp (suc m) lr = {!!}
    ww (suc n) e (suc m') lp (suc m) lr =
      let ((k , k<) , (x' , X')) = Iso.fun (unwindIsoIsoCF m')
             ( equivToIso (adjTransposition≃ (suc n) ∙ₑ e) , fst lp)
          ((k* , k<*) , (x'* , X'*)) = Iso.fun (unwindIsoIsoCF m)
             ( equivToIso e , fst lr)
          
          ww' = ww n (isoToEquiv x'*)
                  {!!} {!!} m (X'* , {!!})
 
      in cong {x = sucFGℕ≃ℕ (from≃ x' m' X')}
              {y = η (suc n)
                · sucFGℕ≃ℕ (from≃ (unwindIso (equivToIso e))
                 m X'*)}
          (_· (rotFG (fst e zero)))
            ({!!}
           ∙  cong sucFGℕ≃ℕ ww' ∙
                  {!!}
                 -- cong′ ((suc n ∷_) ∘' (sucFGℕ≃ℕ ∘' Iso.inv isoFG))
                 --   {!!}
                     -- (Σ≡Prop (snd ∘ isFinGen≃')
                     --   (equivEq {e = isoToEquiv (equivToIso (isoToEquiv x'*))}
                     --            {f = isoToEquiv x'*}
                     --            refl))
                                ) 
       ∙ sym (assoc·
           (η (suc n))
           (sucFGℕ≃ℕ (from≃ (unwindIso (equivToIso e))
           m _))
           (rotFG (fst e zero)))

    -- ww : ∀ k → ∀ e → ∀ lp m lr →
    --      Iso.inv isoFG ((adjTransposition≃ k ∙ₑ e) , lp)
    --     ≡
    --   k ∷ Iso.inv isoFG (e , (m , lr))
    -- ww k e lp zero lr = {!!}
    -- ww zero e lp (suc m) lr = {!!}
    -- ww (suc n) e lp (suc m) lr =
    --   let ((k , k<) , (x' , X')) = Iso.fun (unwindIsoIsoCF m)
    --           (equivToIso e , fst lr)
    --       ww' = ww n (isoToEquiv x') ({!!} , {!!})
    --         ((fst (isFinGen≃→isFinGen≃' (isoToEquiv x') Prop.∣ m , X' ∣₁ )))
    --         (snd (isFinGen≃→isFinGen≃' (isoToEquiv x') Prop.∣ m , X' ∣₁ )) 
           
    --   in cong
    --        {x = sucFGℕ≃ℕ (from≃
    --             ( unwindIso (equivToIso (adjTransposition≃ n ∙ₑ e)))
    --             {!!}
    --             {!!})}
    --        {y = η (suc n) ·
    --           (sucFGℕ≃ℕ (from≃ (unwindIso (equivToIso e))
    --        {!!} {!!})) } (_· (rotFG (fst e zero)))
    --      ({!!} ∙ cong sucFGℕ≃ℕ ww')
    --      ∙ {!!} ∙ sym (assoc· (η (suc n))
    --       (sucFGℕ≃ℕ (from≃ (unwindIso (equivToIso e))
    --        m _))
    --       (rotFG (fst e zero)))
    
    -- ww zero e lp lr = {!!} 
    -- ww (suc k) e lp lr =
      
    --    cong {x = sucFGℕ≃ℕ (from≃
    --             ( unwindIso (equivToIso (adjTransposition≃ k ∙ₑ e)))
    --             {!!}
    --             {!!})}
    --         {y = η (suc k) ·
    --           (sucFGℕ≃ℕ (from≃ (unwindIso (equivToIso e))
    --        {!!} {!!})) }
    --          (_· (rotFG (fst e zero))) {!!}  ∙
    --     sym (assoc· (η (suc k))
    --       (sucFGℕ≃ℕ (from≃ (unwindIso (equivToIso e))
    --        {!!} {!!}))
    --       (rotFG (fst e zero)))

-- sucFGℕ≃ℕ (from≃ x' n X') · rotFG k

-- [Fin→Fin]→[ℕ→ℕ] : ∀ n → ((Fin n) → ℕ)
--                         → ℕ → ℕ
--                         -- ) λ f → ⟨ isConstFrom f n ⟩
-- [Fin→Fin]→[ℕ→ℕ] zero x x₁ = x₁
-- [Fin→Fin]→[ℕ→ℕ] (suc zero) x x₁ = x₁
-- [Fin→Fin]→[ℕ→ℕ] (suc (suc n)) f zero = (f (zero , tt))
-- [Fin→Fin]→[ℕ→ℕ] (suc (suc n)) f (suc x₁) =
--  suc ([Fin→Fin]→[ℕ→ℕ] (suc n) (f ∘ sucF) x₁)

-- -- [Fin→Fin]→[ℕ→ℕ] : ∀ n → ((Fin n) → (Fin n))
-- --                         → ℕ → ℕ
-- --                         -- ) λ f → ⟨ isConstFrom f n ⟩ 
-- -- [Fin→Fin]→[ℕ→ℕ] n f x with (suc x) ≤? n
-- -- ... | yes p = {!!}
-- -- ... | no ¬p = {!!}

-- data Lehmer : Type

-- lenLehmer : Lehmer → ℕ

-- data Lehmer where
--   [] : Lehmer
--   _∷_ : (l : Lehmer) → Fin (suc (lenLehmer l)) → Lehmer




-- lenLehmer [] = zero
-- lenLehmer (x ∷ x₁) = suc (lenLehmer x)



-- -- IsoFin→CFIso : ∀ n → Iso (Fin n) (Fin n) → IsoCF n
-- -- IsoFin→CFIso n isom = w
-- --   where

-- --    module u = Iso isom

-- --    w : IsoCF n
-- --    Iso.fun (fst w) = [Fin→Fin]→[ℕ→ℕ] n (fst ∘ u.fun)
-- --    Iso.inv (fst w) = [Fin→Fin]→[ℕ→ℕ] n (fst ∘ u.inv)
-- --    Iso.rightInv (fst w) = {!!}
-- --    Iso.leftInv (fst w) = {!!}
-- --    snd w = {!!}
   
-- -- IsoIsoCFIsoFin : ∀ n → Iso (IsoCF n) (Iso (Fin n) (Fin n)) 
-- -- Iso.fun (IsoIsoCFIsoFin n) = {!!}
-- -- Iso.inv (IsoIsoCFIsoFin n) = IsoFin→CFIso n
-- -- Iso.rightInv (IsoIsoCFIsoFin n) = {!!}
-- -- Iso.leftInv (IsoIsoCFIsoFin n) = {!!}

-- -- -- -- -- -- -- -- -- sucFGR : Rrec FGℕ≃ℕ
-- -- -- -- -- -- -- -- -- Rrec.isSetA sucFGR = trunc
-- -- -- -- -- -- -- -- -- Rrec.εA sucFGR = ε
-- -- -- -- -- -- -- -- -- Rrec.∷A sucFGR = _∷_ ∘' suc 
-- -- -- -- -- -- -- -- -- Rrec.invoA sucFGR = invo ∘ suc 
-- -- -- -- -- -- -- -- -- Rrec.braidA sucFGR = braid ∘ suc
-- -- -- -- -- -- -- -- -- Rrec.commA sucFGR zero (suc (suc l)) = comm _ _
-- -- -- -- -- -- -- -- -- Rrec.commA sucFGR (suc k) (suc l) = comm _ _


-- -- -- -- -- -- -- -- -- sucFG : FGℕ≃ℕ → FGℕ≃ℕ
-- -- -- -- -- -- -- -- -- sucFG = Rrec.f sucFGR

 




-- -- -- -- -- -- -- -- -- -- FGrot' : ℕ → FGℕ≃ℕ
-- -- -- -- -- -- -- -- -- -- FGrot' zero = ε
-- -- -- -- -- -- -- -- -- -- FGrot' (suc x) = x ∷ sucFG (FGrot' x)

-- -- -- -- -- -- -- -- -- -- left-≤-max≡ : ∀ n m → m ≤ n → max n m ≡ n
-- -- -- -- -- -- -- -- -- -- left-≤-max≡ zero zero x = refl
-- -- -- -- -- -- -- -- -- -- left-≤-max≡ zero (suc m) x = ⊥.rec (¬-<-zero x)
-- -- -- -- -- -- -- -- -- -- left-≤-max≡ (suc n) zero x = refl
-- -- -- -- -- -- -- -- -- -- left-≤-max≡ (suc n) (suc m) x = cong suc (left-≤-max≡ n m (predℕ-≤-predℕ x))


-- -- -- -- -- -- -- -- -- -- isConstFrom-rot' : ∀ k → ⟨ isConstFrom (rot' k) (suc k) ⟩
-- -- -- -- -- -- -- -- -- -- isConstFrom-rot' = ℕ.cases
-- -- -- -- -- -- -- -- -- --   (λ _ _ → refl)
-- -- -- -- -- -- -- -- -- --    (ℕ.elim
-- -- -- -- -- -- -- -- -- --      (isConstFrom-adjTransposition 0)
-- -- -- -- -- -- -- -- -- --      λ n X →
-- -- -- -- -- -- -- -- -- --         (isConstFrom∘ _ _ _ _
-- -- -- -- -- -- -- -- -- --            (sucFun-isConstFrom _ _ X) (isConstFrom-adjTransposition 0)))

-- -- -- -- -- -- -- -- -- -- encodeFinGen≃ : (e : Iso ℕ ℕ) → ∀ k
-- -- -- -- -- -- -- -- -- --       → ⟨ (isConstFrom (Iso.fun e)) k ⟩  
-- -- -- -- -- -- -- -- -- --       → FGℕ≃ℕ
-- -- -- -- -- -- -- -- -- -- encodeFinGen≃ e zero x = ε
-- -- -- -- -- -- -- -- -- -- encodeFinGen≃ e (suc zero) x = ε
-- -- -- -- -- -- -- -- -- -- encodeFinGen≃ e (suc (suc k)) x =
-- -- -- -- -- -- -- -- -- --   encodeFinGen≃ (unwindIso e) (suc k)
-- -- -- -- -- -- -- -- -- --     (predFun-isConstFrom (Iso.fun (invIso (rotIso' (Iso.fun e zero)))
-- -- -- -- -- -- -- -- -- --      ∘ Iso.fun e) (suc k) w) · FGrot' (Iso.fun e zero)

-- -- -- -- -- -- -- -- -- --   where

-- -- -- -- -- -- -- -- -- --     w' : Iso.fun e zero ≤ (suc k)
-- -- -- -- -- -- -- -- -- --     w' with splitℕ-≤ (Iso.fun e zero) (suc k)
-- -- -- -- -- -- -- -- -- --     ... | inl x = x
-- -- -- -- -- -- -- -- -- --     ... | inr x' = ⊥.rec (
-- -- -- -- -- -- -- -- -- --        ¬-<-zero (subst ((suc k) <_)
-- -- -- -- -- -- -- -- -- --          (isoFunInjective e _ _ (x _ x')) x')) 

-- -- -- -- -- -- -- -- -- --     w =
-- -- -- -- -- -- -- -- -- --       subst (fst ∘ (isConstFrom _))
-- -- -- -- -- -- -- -- -- --         (left-≤-max≡ (suc (suc k)) (suc (Iso.fun e zero))
-- -- -- -- -- -- -- -- -- --            (suc-≤-suc w'))
-- -- -- -- -- -- -- -- -- --         (isConstFrom∘ (Iso.inv (rotIso' (Iso.fun e zero)))
-- -- -- -- -- -- -- -- -- --           (suc (Iso.fun e zero)) (Iso.fun e) (suc (suc k))
-- -- -- -- -- -- -- -- -- --            ( section-isConstFrom _ _ (suc (Iso.fun e zero))
-- -- -- -- -- -- -- -- -- --               (Iso.leftInv (rotIso' (Iso.fun e zero)))
-- -- -- -- -- -- -- -- -- --              (isConstFrom-rot' (Iso.fun e zero))) x)


-- -- -- -- -- -- -- -- -- -- from≃' : FinGen≃' → FGℕ≃ℕ
-- -- -- -- -- -- -- -- -- -- from≃' = uncurry λ e →
-- -- -- -- -- -- -- -- -- --   uncurry λ k → uncurry λ X _ → encodeFinGen≃ (equivToIso e) k X

-- -- -- -- -- -- -- -- -- -- FinGen≃'pres< : ∀ n → (e : FinGen≃') →
-- -- -- -- -- -- -- -- -- --              fst (snd e) RO.≤ n → ∀ k → k RO.< n → fst (fst e) k RO.< n 
-- -- -- -- -- -- -- -- -- -- FinGen≃'pres< = {!!}

-- -- -- -- -- -- -- -- -- -- module _ {ℓ} {A : Type ℓ} (Agrp : isGroupoid A) where

-- -- -- -- -- -- -- -- -- --   open ListPath {A = A}

-- -- -- -- -- -- -- -- -- --   lookup' : (l : List A) → ∀ k → k RO.< length l → A 
-- -- -- -- -- -- -- -- -- --   lookup' (x₁ ∷ l) zero x = x₁
-- -- -- -- -- -- -- -- -- --   lookup' (x₁ ∷ l) (suc k) x = lookup' l k x

-- -- -- -- -- -- -- -- -- --   tabulate' : ∀ n → (∀ k → k RO.< n → A) → List A
-- -- -- -- -- -- -- -- -- --   tabulate' zero x = []
-- -- -- -- -- -- -- -- -- --   tabulate' (suc n) x = x zero _ ∷ tabulate' n (x ∘ suc)

-- -- -- -- -- -- -- -- -- --   lookAlways : A → List A → ℕ → A 
-- -- -- -- -- -- -- -- -- --   lookAlways a [] x₁ = a
-- -- -- -- -- -- -- -- -- --   lookAlways a (x ∷ x₂) zero = x
-- -- -- -- -- -- -- -- -- --   lookAlways a (x ∷ x₂) (suc x₁) = lookAlways x x₂ x₁

-- -- -- -- -- -- -- -- -- --   -- idxs : List A → List ℕ
-- -- -- -- -- -- -- -- -- --   -- idxs [] = []
-- -- -- -- -- -- -- -- -- --   -- idxs (x ∷ x₁) = 0 ∷ Li.map suc (idxs x₁)

-- -- -- -- -- -- -- -- -- --   tabOn : List A → (ℕ → A) → List A
-- -- -- -- -- -- -- -- -- --   tabOn [] x₁ = []
-- -- -- -- -- -- -- -- -- --   tabOn (x ∷ x₂) x₁ = x₁ zero ∷ tabOn x₂ (x₁ ∘ suc)

-- -- -- -- -- -- -- -- -- --   remap : List A → (ℕ → ℕ) → List A
-- -- -- -- -- -- -- -- -- --   remap [] _ = []
-- -- -- -- -- -- -- -- -- --   remap l@(x ∷ xs) f = tabOn l (lookAlways x l ∘ f)

-- -- -- -- -- -- -- -- -- --   rr : ∀ l x → tabOn l (λ x₁ → lookAlways x l x₁) ≡ l
-- -- -- -- -- -- -- -- -- --   rr [] x = refl
-- -- -- -- -- -- -- -- -- --   rr (x₁ ∷ l) x = cong (x₁ ∷_) (rr l _)

-- -- -- -- -- -- -- -- -- --   remapId : ∀ l → remap l (λ x₁ → x₁) ≡ l
-- -- -- -- -- -- -- -- -- --   remapId [] = refl
-- -- -- -- -- -- -- -- -- --   remapId (x ∷ l) = cong (x ∷_) (rr l x)

-- -- -- -- -- -- -- -- -- --   swapL : ℕ → List A → List A
-- -- -- -- -- -- -- -- -- --   swapL zero [] = []
-- -- -- -- -- -- -- -- -- --   swapL zero (x ∷ []) = (x ∷ [])
-- -- -- -- -- -- -- -- -- --   swapL zero (x ∷ x₁ ∷ x₂) = x₁ ∷ x ∷ x₂
-- -- -- -- -- -- -- -- -- --   swapL (suc x) [] = []
-- -- -- -- -- -- -- -- -- --   swapL (suc x) (x₁ ∷ x₂) = x₁ ∷ swapL x x₂

-- -- -- -- -- -- -- -- -- --   perm : (e : FGℕ≃ℕ) → (l : List A) → 
-- -- -- -- -- -- -- -- -- --            getBnd e RO.< length l → singl (remap l (fst (to≃ e)))
-- -- -- -- -- -- -- -- -- --   perm = Relim.f w

-- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- --       w : Relim
-- -- -- -- -- -- -- -- -- --             (λ z →
-- -- -- -- -- -- -- -- -- --                (l : List A) →
-- -- -- -- -- -- -- -- -- --                getBnd z RO.< length l → singl (remap l (fst (to≃ z))))
-- -- -- -- -- -- -- -- -- --       Relim.isSetA w = {!!}
-- -- -- -- -- -- -- -- -- --       Relim.εA w l x = l , remapId l
-- -- -- -- -- -- -- -- -- --       Relim.∷A w k X l p =
-- -- -- -- -- -- -- -- -- --         swapL k (fst (X l {!!})) ,
-- -- -- -- -- -- -- -- -- --           {!!} ∙ cong (swapL k) (snd (X l {!!}))
-- -- -- -- -- -- -- -- -- --       Relim.invoA w = {!!}
-- -- -- -- -- -- -- -- -- --       Relim.braidA w = {!!}
-- -- -- -- -- -- -- -- -- --       Relim.commA w = {!!}

-- -- -- -- -- -- -- -- -- --   -- _co∙_ : {x y z : List A} → Cover x y → Cover y z → Cover x z
-- -- -- -- -- -- -- -- -- --   -- _co∙_ {[]} {[]} {[]} p q = tt*
-- -- -- -- -- -- -- -- -- --   -- _co∙_ {x ∷ x₁} {x₂ ∷ y} {x₃ ∷ z} p q =
-- -- -- -- -- -- -- -- -- --   --   fst p ∙ fst q , (snd p co∙ snd q )
  
-- -- -- -- -- -- -- -- -- -- -- --   -- permute : (l : List A) → (e : FinGen≃') →
-- -- -- -- -- -- -- -- -- -- -- --   --            fst (snd e) RO.≤ length l  → List A
-- -- -- -- -- -- -- -- -- -- -- --   -- permute l e x = tabulate' (length l)
-- -- -- -- -- -- -- -- -- -- -- --   --   (λ k x₁ → lookup' l (fst (fst e) k)
-- -- -- -- -- -- -- -- -- -- -- --   --     (FinGen≃'pres< (length l) e x k x₁))



-- -- -- -- -- -- -- -- -- --   infix 4  _↔_


-- -- -- -- -- -- -- -- -- --   record _↔_ (x y : List A) : Type ℓ where
-- -- -- -- -- -- -- -- -- --     constructor prm
-- -- -- -- -- -- -- -- -- --     field
-- -- -- -- -- -- -- -- -- --       F≃ : FGℕ≃ℕ
-- -- -- -- -- -- -- -- -- --       -- l< : fst (snd (to≃'' F≃)) RO.≤ length x
-- -- -- -- -- -- -- -- -- --       l≡ :  Cover (remap x (fst (to≃ F≃))) y
-- -- -- -- -- -- -- -- -- --       -- l< : fst (snd (to≃'' F≃)) RO.≤ length x
-- -- -- -- -- -- -- -- -- --       -- l≡ : ≡mbF (suc (max (length x) (length y)))
-- -- -- -- -- -- -- -- -- --       --       (lookupMb x ∘ fst (to≃ F≃)) (lookupMb y)
-- -- -- -- -- -- -- -- -- --       -- l< : getBnd F≃ RO.< max (length x) (length y)



-- -- -- -- -- -- -- -- -- --   open BinaryRelation (_↔_)

-- -- -- -- -- -- -- -- -- --   isTrans↔' : isTrans 
-- -- -- -- -- -- -- -- -- --   isTrans↔' a' b' c' (prm e' p') (prm f' q') =
-- -- -- -- -- -- -- -- -- --     prm (f' · e') {! !}
-- -- -- -- -- -- -- -- -- --     -- where

      
-- -- -- -- -- -- -- -- -- --       -- zzR : Relim
-- -- -- -- -- -- -- -- -- --       --   (λ e →
-- -- -- -- -- -- -- -- -- --       --    (z : FGℕ≃ℕ) (a b c : List A) →
-- -- -- -- -- -- -- -- -- --       --    Cover (remap a (fst (to≃ e))) b →
-- -- -- -- -- -- -- -- -- --       --    Cover (remap b (fst (to≃ z))) c →
-- -- -- -- -- -- -- -- -- --       --    Cover (remap a (fst (to≃ (z · e)))) c)
-- -- -- -- -- -- -- -- -- --       -- Relim.isSetA zzR = {!!}
-- -- -- -- -- -- -- -- -- --       -- Relim.εA zzR z [] [] [] x x₁ = {!!}
-- -- -- -- -- -- -- -- -- --       -- Relim.εA zzR z (x₂ ∷ a) (x₃ ∷ b) (x₄ ∷ c) x x₁ =
-- -- -- -- -- -- -- -- -- --       --   ({!fst x!} ∙ fst x₁) , {!!}
-- -- -- -- -- -- -- -- -- --       -- Relim.∷A zzR = {!!}
-- -- -- -- -- -- -- -- -- --       -- Relim.invoA zzR = {!!}
-- -- -- -- -- -- -- -- -- --       -- Relim.braidA zzR = {!!}
-- -- -- -- -- -- -- -- -- --       -- Relim.commA zzR = {!!}

-- -- -- -- -- -- -- -- -- --       -- zz : ∀ e f → (a b c : List A) → 
-- -- -- -- -- -- -- -- -- --       --       (p : Cover (remap a (fst (to≃ e))) b)
-- -- -- -- -- -- -- -- -- --       --       (q : Cover (remap b (fst (to≃ f))) c)
-- -- -- -- -- -- -- -- -- --       --       → Cover (remap a (fst (to≃ (f · e)))) c
-- -- -- -- -- -- -- -- -- --       -- zz = Relim.f zzR


-- -- -- -- -- -- -- -- -- -- -- -- -- lookupMb : ∀ {ℓ} {A : Type ℓ} → List A → ℕ → Maybe A
-- -- -- -- -- -- -- -- -- -- -- -- -- lookupMb [] _ = nothing
-- -- -- -- -- -- -- -- -- -- -- -- -- lookupMb (x₁ ∷ x₂) zero  = just x₁
-- -- -- -- -- -- -- -- -- -- -- -- -- lookupMb (x₁ ∷ x₂) (suc x)  = lookupMb x₂ x


-- -- -- -- -- -- -- -- -- -- -- -- -- module _ {ℓ} {A : Type ℓ} where

-- -- -- -- -- -- -- -- -- -- -- -- --   open Iso

-- -- -- -- -- -- -- -- -- -- -- -- --   ≡mbF : ℕ → Rel (ℕ → Maybe A) (ℕ → Maybe A) ℓ
-- -- -- -- -- -- -- -- -- -- -- -- --   ≡mbF zero x y = x ≡ y
-- -- -- -- -- -- -- -- -- -- -- -- --   ≡mbF (suc n) x y = MaybePath.Cover (x zero) (y zero) ×
-- -- -- -- -- -- -- -- -- -- -- -- --     ≡mbF n (x ∘ suc) (y ∘ suc)


-- -- -- -- -- -- -- -- -- -- -- -- --   ≡mbF-Iso-S : ∀ n a b → Iso (≡mbF n a b) (≡mbF (suc n) a b) 
-- -- -- -- -- -- -- -- -- -- -- -- --   ≡mbF-Iso-S zero a b = w 
-- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- --       w : Iso (≡mbF zero a b) (≡mbF 1 a b)
-- -- -- -- -- -- -- -- -- -- -- -- --       fst (fun w p) = MaybePath.encode _ _ (funExt⁻ p zero)
-- -- -- -- -- -- -- -- -- -- -- -- --       snd (fun w p) = cong (_∘ suc) p
-- -- -- -- -- -- -- -- -- -- -- -- --       Iso.inv w = uncurry (_=→_ ∘ MaybePath.decode _ _)
-- -- -- -- -- -- -- -- -- -- -- -- --       rightInv w _ = cong (_, _) (MaybePath.encodeDecode _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- --       leftInv w _ = MaybePath.decodeEncode _ _ _ sq→ refl
      
-- -- -- -- -- -- -- -- -- -- -- -- --   ≡mbF-Iso-S (suc n) a b = w
-- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- --       w : Iso (≡mbF (suc n) a b) (≡mbF (suc (suc n)) a b)
-- -- -- -- -- -- -- -- -- -- -- -- --       w = prodIso idIso (≡mbF-Iso-S n (a ∘ suc) (b ∘ suc))


-- -- -- -- -- -- -- -- -- -- -- -- --   ≡mbF-Iso : ∀ n a b → Iso (a ≡ b) (≡mbF n a b) 
-- -- -- -- -- -- -- -- -- -- -- -- --   ≡mbF-Iso zero _ _ = idIso
-- -- -- -- -- -- -- -- -- -- -- -- --   ≡mbF-Iso (suc n) _ _ = compIso (≡mbF-Iso n _ _) (≡mbF-Iso-S n _ _)

-- -- -- -- -- -- -- -- -- -- -- -- -- infix 4  _↔_


-- -- -- -- -- -- -- -- -- -- -- -- -- record _↔_ {ℓ} {A : Type ℓ} (x y : List A) : Type ℓ where
-- -- -- -- -- -- -- -- -- -- -- -- --   constructor prm
-- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- --     F≃ : FGℕ≃ℕ
-- -- -- -- -- -- -- -- -- -- -- -- --     l≡ : ≡mbF (suc (max (length x) (length y)))
-- -- -- -- -- -- -- -- -- -- -- -- --           (lookupMb x ∘ fst (to≃ F≃)) (lookupMb y)
-- -- -- -- -- -- -- -- -- -- -- -- --     l< : getBnd F≃ RO.< max (length x) (length y)
    



-- -- -- -- -- -- -- -- -- -- -- -- -- -- open _↔_

-- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ {ℓ} {A : Type ℓ} (grpA : isGroupoid A) where 


-- -- -- -- -- -- -- -- -- -- -- -- -- --   open BinaryRelation (_↔_ {A = A})

-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- isTrans↔' : isTrans 
-- -- -- -- -- -- -- -- -- -- -- -- -- --   -- isTrans↔' a b c x x₁ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --   isTrans↔ : isTrans 
-- -- -- -- -- -- -- -- -- -- -- -- -- --   isTrans↔ a b c (prm e p <ab) (prm f q <bc) =
-- -- -- -- -- -- -- -- -- -- -- -- -- --     prm (f · e) {!!} {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --       -- (cong (lookupMb a ∘_) (to≃· f e) ∙∙ cong (_∘ fst (to≃ f)) p ∙∙ q)
-- -- -- -- -- -- -- -- -- -- -- -- -- --       --  (RO.≤<-trans {getBnd (f · e)} {n = min (length a) (length c)} 
-- -- -- -- -- -- -- -- -- -- -- -- -- --       --     (getBnd· f e)
-- -- -- -- -- -- -- -- -- -- -- -- -- --       --     {!!})

-- -- -- -- -- -- -- -- -- -- -- -- -- --   L// : Type ℓ  
-- -- -- -- -- -- -- -- -- -- -- -- -- --   L// = List A // isTrans↔ 


  
-- -- -- -- -- -- -- -- -- -- -- -- -- --   record RR {ℓ'} (B : Type ℓ') : Type (ℓ-max ℓ' ℓ) where
-- -- -- -- -- -- -- -- -- -- -- -- -- --     field
-- -- -- -- -- -- -- -- -- -- -- -- -- --       bGrp : isGroupoid B
-- -- -- -- -- -- -- -- -- -- -- -- -- --       b0 : B
-- -- -- -- -- -- -- -- -- -- -- -- -- --       bS : A → B → B
-- -- -- -- -- -- -- -- -- -- -- -- -- --       bComm : ∀ a a' b → bS a (bS a' b) ≡ bS a' (bS a b)
-- -- -- -- -- -- -- -- -- -- -- -- -- --       bInvo : ∀ a a' b → bComm a a' b ≡ sym (bComm a' a b)


    

-- -- -- -- -- -- -- -- -- -- -- -- -- --     -- mb≡→fold≡ : (a b : List A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- --     --     (λ x → lookupMb a x) ≡ lookupMb b → foldr bS b0 a ≡ foldr bS b0 b
-- -- -- -- -- -- -- -- -- -- -- -- -- --     -- mb≡→fold≡ [] [] _ = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- --     -- mb≡→fold≡ [] (x₁ ∷ b) x = {!funExt⁻ x zero!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --     -- mb≡→fold≡ (x₁ ∷ a) [] x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --     -- mb≡→fold≡ (x₁ ∷ a) (x₂ ∷ b) x =
-- -- -- -- -- -- -- -- -- -- -- -- -- --     --   cong₂ bS (just-inj _ _ (funExt⁻ x zero))
-- -- -- -- -- -- -- -- -- -- -- -- -- --     --    (mb≡→fold≡ a  b (cong (_∘ suc) x) )

-- -- -- -- -- -- -- -- -- -- -- -- -- --     mb≡→fold≡ : (a b : List A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- --         ≡mbF (suc (max (length a) (length b))) (lookupMb a) (lookupMb b) →
-- -- -- -- -- -- -- -- -- -- -- -- -- --            foldr bS b0 a ≡ foldr bS b0 b
-- -- -- -- -- -- -- -- -- -- -- -- -- --     mb≡→fold≡ [] [] (fst₁ , snd₁) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- --     mb≡→fold≡ [] (x ∷ b) ()
-- -- -- -- -- -- -- -- -- -- -- -- -- --     mb≡→fold≡ (x ∷ a) [] ()
-- -- -- -- -- -- -- -- -- -- -- -- -- --     mb≡→fold≡ (x ∷ a) (x₁ ∷ b) (p , ps) =
-- -- -- -- -- -- -- -- -- -- -- -- -- --       cong₂ bS p (mb≡→fold≡ a b ps)

-- -- -- -- -- -- -- -- -- -- -- -- -- --     Relim∷A : (k : ℕ) {xs : FGℕ≃ℕ} →
-- -- -- -- -- -- -- -- -- -- -- -- -- --       ((a b : List A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- --        ≡mbF (suc (max (length a) (length b))) (lookupMb a ∘ fst (to≃ xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- --        (lookupMb b) →
-- -- -- -- -- -- -- -- -- -- -- -- -- --        foldr bS b0 a ≡ foldr bS b0 b) →
-- -- -- -- -- -- -- -- -- -- -- -- -- --       (a b : List A) → 𝟚.True (discreteℕ (length a) (length b)) → 
-- -- -- -- -- -- -- -- -- -- -- -- -- --       ≡mbF (suc (max (length a) (length b)))
-- -- -- -- -- -- -- -- -- -- -- -- -- --       (lookupMb a ∘ fst (to≃ (k ∷ xs))) (lookupMb b) →
-- -- -- -- -- -- -- -- -- -- -- -- -- --       foldr bS b0 a ≡ foldr bS b0 b
-- -- -- -- -- -- -- -- -- -- -- -- -- --     Relim∷A zero {xs} X [] [] =l = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --     Relim∷A zero {xs} X (x ∷ []) (x₁ ∷ []) =l = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --     Relim∷A zero {xs} X (x ∷ x₂ ∷ a) (x₁ ∷ x₃ ∷ b) =l (p , p' , ps) =
-- -- -- -- -- -- -- -- -- -- -- -- -- --       let z = X (x₂ ∷ x ∷ a) (x₁ ∷ x₃ ∷ b)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                   ({!p!} , ({!!} , {!!}))
-- -- -- -- -- -- -- -- -- -- -- -- -- --       in {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --        -- bComm _ _ _ ∙ X (x₂ ∷ x ∷ a) (x₁ ∷ x₃ ∷ b)
-- -- -- -- -- -- -- -- -- -- -- -- -- --        --                ({!p'!} , ({!!} , {!ps!}))
    
-- -- -- -- -- -- -- -- -- -- -- -- -- --     Relim∷A (suc k) {xs} X = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --     -- Relim∷A (suc k) {xs} X a b p = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --     -- rrR' : Relim
-- -- -- -- -- -- -- -- -- -- -- -- -- --     --   (λ z →
-- -- -- -- -- -- -- -- -- -- -- -- -- --     --      (a b : List A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- --     --      ≡mbF (lookupMb a ∘ fst (to≃ z)) (lookupMb b) →
-- -- -- -- -- -- -- -- -- -- -- -- -- --     --      foldr bS b0 a ≡ foldr bS b0 b)
-- -- -- -- -- -- -- -- -- -- -- -- -- --     -- Relim.isSetA rrR _ = isSetΠ3 λ _ _ _ → bGrp _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- --     -- Relim.εA rrR = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --     -- Relim.∷A rrR = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --     -- Relim.invoA rrR = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --     -- Relim.braidA rrR = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --     -- Relim.commA rrR = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --     -- rrR

-- -- -- -- -- -- -- -- -- -- -- -- -- --     rrR : Relim
-- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ z →
-- -- -- -- -- -- -- -- -- -- -- -- -- --          (a b : List A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- --          ≡mbF (suc (max (length a) (length b)))
-- -- -- -- -- -- -- -- -- -- -- -- -- --           (lookupMb a ∘ fst (to≃ z)) (lookupMb b) →
-- -- -- -- -- -- -- -- -- -- -- -- -- --          foldr bS b0 a ≡ foldr bS b0 b)
-- -- -- -- -- -- -- -- -- -- -- -- -- --     Relim.isSetA rrR _ = isSetΠ3 λ _ _ _ → bGrp _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- --     Relim.εA rrR = mb≡→fold≡
-- -- -- -- -- -- -- -- -- -- -- -- -- --     Relim.∷A rrR = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --     Relim.invoA rrR = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --     Relim.braidA rrR = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --     Relim.commA rrR = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --     rr : (e : FGℕ≃ℕ) → ∀ a b → ≡mbF (suc (max (length a) (length b)))
-- -- -- -- -- -- -- -- -- -- -- -- -- --           (lookupMb a ∘ fst (to≃ e)) (lookupMb b) → foldr bS b0 a ≡ foldr bS b0 b
-- -- -- -- -- -- -- -- -- -- -- -- -- --     rr = Relim.f rrR

-- -- -- -- -- -- -- -- -- -- -- -- -- --     fR : Rrec// B
-- -- -- -- -- -- -- -- -- -- -- -- -- --     Rrec//.Bgpd fR = bGrp
-- -- -- -- -- -- -- -- -- -- -- -- -- --     Rrec//.fb fR = foldr bS b0
-- -- -- -- -- -- -- -- -- -- -- -- -- --     Rrec//.feq fR (prm e p l<) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --     Rrec//.fsq fR = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --     f : L// → B  
-- -- -- -- -- -- -- -- -- -- -- -- -- --     f = Rrec//.f fR

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ss : section from≃' to≃''
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ss = RelimProp.f w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     w : RelimProp (λ z → from≃' (to≃'' z) ≡ z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     RelimProp.isPropA w _ = trunc _ _ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     RelimProp.εA w = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     RelimProp.∷A w k x = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- rr : ∀ a → fst (fst (to≃'' (from≃' a))) ≡ fst (fst a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- rr (a , zero , P) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- rr (a , suc zero , P) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- rr (e@(f , _) , suc (suc k) , P) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  to≃· (encodeFinGen≃ (unwindIso (equivToIso (f , _))) (suc k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (predFun-isConstFrom (Iso.fun (invIso (rotIso' (f zero)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ∘ f) (suc k) {!!})) (FGrot' (f zero)) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {!!}





-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Σ≡Prop {!!} (equivEq {!!})

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unwindFinGen≃ : (e : Iso ℕ ℕ) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (Σ (ℕ × Iso ℕ ℕ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                λ (k , e') →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  e ≡ compIso (sucIso e') (rotIso' (Iso.fun e zero)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unwindFinGen≃ x = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  to≃R : Rrec FinGen≃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  Rrec.isSetA to≃R = isOfHLevelΣ 2 (isOfHLevel≃ 2 isSetℕ isSetℕ) {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  Rrec.εA to≃R = idEquiv _ , Prop.∣ zero , (λ _ _ → refl) ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  Rrec.∷A to≃R k = isFinGen≃∘ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  Rrec.invoA to≃R k x = Σ≡Prop {!!} {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   -- equivEq (cong (fst x ∘_) (funExt (isInvolutionAdjTransposition k)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  Rrec.braidA to≃R k x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   -- equivEq (cong ((fst x) ∘_) (adjTranspositionBraid k))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  Rrec.commA to≃R k l z x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   -- equivEq (cong ((fst x) ∘_) (adjTranspositionComm k l z))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    open GroupStr (snd (SymData n))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    to≃R : Rrec {n = n} (fst (SymData n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Rrec.isSetA to≃R = is-set
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Rrec.εA to≃R = 1g
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Rrec.ηA to≃R = adjTransposition*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Rrec.·A to≃R = _∙ₑ_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Rrec.assoc·A to≃R = ·Assoc
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Rrec.idr·A to≃R = ·IdR
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Rrec.idl·A to≃R = ·IdL
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Rrec.invo·A to≃R = adjTransposition*²=idEquiv
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Rrec.braid·A to≃R = adjTransposition*Braid n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Rrec.comm·A to≃R = adjTransposition*Comm n


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Rrec {ℓ} {n : ℕ} (A : Type ℓ) : Type ℓ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     isSetA : isSet A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     εA : A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ηA : Fin (predℕ n) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ·A : A → A → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     assoc·A : ∀ x x₁ x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ·A x (·A x₁ x₂) ≡ ·A (·A x x₁) x₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     idr·A : ∀ x → ·A x εA ≡ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     idl·A : ∀ x → ·A εA x ≡ x

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     invo·A : ∀ k → ·A (ηA k) (ηA k) ≡ εA
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     braid·A : ∀ k → ·A (ηA (weakF n k)) (·A (ηA (sucF n k)) (ηA (weakF n k)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     ≡ ·A (ηA (sucF n k)) (·A (ηA (weakF n k)) (ηA (sucF n k)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     comm·A : ∀ k l → commT n k l →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                ·A (ηA k) (ηA l) ≡ ·A (ηA l) (ηA k)
 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f : Perm n → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (η x) = ηA x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f ε = εA
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (x · x₁) = ·A (f x) (f x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (assoc· x x₁ x₂ i) = assoc·A (f x) (f x₁) (f x₂) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (idr x i) = idr·A (f x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (idl x i) = idl·A (f x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (invo k i) = invo·A k i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (braid k i) = braid·A k i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (comm k l x i) = comm·A k l x i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (trunc x y p q i i₁) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     isSetA
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          _ _ (cong f p) (cong f q) i i₁


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record Relim {ℓ} {n : ℕ} (A : (Perm n) → Type ℓ) : Type ℓ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     isSetA : ∀ x → isSet (A x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     εA : A ε
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ηA : ∀ k → A (η k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ·A : ∀ {x y} → A x → A y → A (x · y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     assoc·A : ∀ {x y z} → (x' : A x) → (y' : A y) → (z' : A z) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        PathP (λ i → A (assoc· x y z i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (·A x' (·A y' z'))  (·A (·A x' y') z')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     idr·A : ∀ {x} → (x' : A x) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        PathP (λ i → A (idr x i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (·A x' εA)  x'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     idl·A : ∀ {x} → (x' : A x) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        PathP (λ i → A (idl x i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (·A εA x')  x'

 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f : ∀ x → A x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (η x) = ηA x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f ε = εA
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (x · x₁) = ·A (f x) (f x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (assoc· x x₁ x₂ i) = assoc·A  (f x) (f x₁) (f x₂) i

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (idr x i) = idr·A (f x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (idl x i) = idl·A (f x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (invo k i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (braid k i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (comm k l x i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (trunc x y p q i i₁) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     isOfHLevel→isOfHLevelDep 2 (λ x → (isSetA x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          _ _ (cong f p) (cong f q) (trunc x y p q) i i₁


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- record RelimProp {ℓ} {n : ℕ} (A : (Perm n) → Type ℓ) : Type ℓ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     isPropA : ∀ x → isProp (A x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     εA : A ε
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ηA : ∀ k → A (η k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ·A : ∀ {x y} → A x → A y → A (x · y)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f : ∀ x → A x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (η x) = ηA x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f ε = εA
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (x · x₁) = ·A (f x) (f x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (assoc· x x₁ x₂ i) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     isProp→PathP (λ i → isPropA (assoc· x x₁ x₂ i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (·A (f x) (·A (f x₁) (f x₂)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (·A (·A (f x) (f x₁)) (f x₂)) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (idr x i) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     isProp→PathP (λ i → isPropA (idr x i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (·A (f x) εA)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (f x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (idl x i) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     isProp→PathP (λ i → isPropA (idl x i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (·A εA (f x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (f x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (invo k i) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      isProp→PathP (λ i → isPropA (invo k i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (·A (ηA k) (ηA k))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (εA) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (braid k i) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     isProp→PathP (λ i → isPropA (braid k i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (·A (ηA (weakF n k)) (·A (ηA (sucF n k)) (ηA (weakF n k))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (·A (ηA (sucF n k)) (·A (ηA (weakF n k)) (ηA (sucF n k)))) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (comm k l x i) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     isProp→PathP (λ i → isPropA (comm k l x i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (·A (ηA k) (ηA l))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (·A (ηA l) (ηA k)) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   f (trunc x y p q i i₁) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     isOfHLevel→isOfHLevelDep 2 (λ x → isProp→isSet (isPropA x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          _ _ (cong f p) (cong f q) (trunc x y p q) i i₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- invP : ∀ n → Perm n → Perm n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- invP n (η x) = η x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- invP n ε = ε
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- invP n (x · x₁) = invP n x₁ · invP n x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- invP n (assoc· x x₁ x₂ i) = assoc· (invP n x₂) (invP n x₁) (invP n x) (~ i)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- invP n (idr x i) = idl (invP n x) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- invP n (idl x i) = idr (invP n x) i

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- invP n (invo k i) = invo k i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- invP n (braid k i) = (sym (assoc· _ _ _) ∙∙ braid k ∙∙ assoc· _ _ _) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- invP n (comm k l x i) = comm k l x (~ i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- invP n (trunc x x₁ x₂ y i i₁) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   trunc (invP n x) (invP n x₁) (cong (invP n) x₂) (cong (invP n) y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ) i i₁


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- invr : ∀ n → (x : Perm n) → (x · invP n x) ≡ ε
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- invr n = RelimProp.f w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     w : RelimProp (λ z → (z · invP n z) ≡ ε)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     RelimProp.isPropA w _ = trunc _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     RelimProp.εA w = idr ε
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     RelimProp.ηA w k = invo k  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     RelimProp.·A w {x} {x₁} p p₁ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (assoc· _ _ _ ∙ cong (_· (invP n x)) (sym (assoc· _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∙ cong (x ·_) p₁ ∙ idr x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∙ p

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- invl : ∀ n → (x : Perm n) → (invP n x · x) ≡ ε
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- invl n = RelimProp.f w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     w : RelimProp (λ z → (invP n z · z) ≡ ε)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     RelimProp.isPropA w _ = trunc _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     RelimProp.εA w = idl ε
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     RelimProp.ηA w k = invo k  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     RelimProp.·A w {x} {x₁} p p₁ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       assoc· _ _ _ ∙ cong (_· x₁) (sym (assoc· _ _ _) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       cong (invP n x₁ ·_) p ∙ idr _ ) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       p₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Permutation : ℕ → Group ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Permutation n = makeGroup {G = Perm n}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ε
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   _·_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (invP n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   trunc
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   assoc·
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   idr
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   idl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (invr n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (invl n) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- adjTransposition*Braid : ∀ n →  (k : Fin (predℕ (predℕ n))) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       adjTransposition* {n} (weakF n k) ∙ₑ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       adjTransposition* (sucF n k) ∙ₑ adjTransposition* (weakF n k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       adjTransposition* (sucF n k) ∙ₑ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       adjTransposition* (weakF n k) ∙ₑ adjTransposition* (sucF n k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- adjTransposition*Braid (suc (suc (suc n))) zero =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  equivEq (refl =→ refl =→  refl =→ refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- adjTransposition*Braid (suc (suc (suc n))) (suc k) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  equivEq (refl =→ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    cong ((suc ∘_ ) ∘ fst)  (adjTransposition*Braid (suc (suc n)) k))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- adjTransposition*Comm : ∀ n → (k l : Fin (predℕ n)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       commT n k l →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       adjTransposition* {n} k ∙ₑ adjTransposition* l ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       adjTransposition* l ∙ₑ adjTransposition* k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- adjTransposition*Comm (suc .(suc (suc _))) zero (suc (suc l)) x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   commSwap0and1SucSuc _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- adjTransposition*Comm (suc .(suc (suc _))) (suc k) (suc (suc l)) x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq (refl =→ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    cong ((suc ∘_ ) ∘ fst)  (adjTransposition*Comm _ k (suc l) x))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ : ∀ n → Perm n → fst (SymData n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ n = Rrec.f (to≃R)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    open GroupStr (snd (SymData n))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    to≃R : Rrec {n = n} (fst (SymData n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Rrec.isSetA to≃R = is-set
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Rrec.εA to≃R = 1g
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Rrec.ηA to≃R = adjTransposition*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Rrec.·A to≃R = _∙ₑ_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Rrec.assoc·A to≃R = ·Assoc
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Rrec.idr·A to≃R = ·IdR
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Rrec.idl·A to≃R = ·IdL
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Rrec.invo·A to≃R = adjTransposition*²=idEquiv
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Rrec.braid·A to≃R = adjTransposition*Braid n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Rrec.comm·A to≃R = adjTransposition*Comm n

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- adjTransposition*Inv : ∀ n k → adjTransposition* {n} k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                             ≡ invEquiv (adjTransposition* {n} k) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- adjTransposition*Inv (suc (suc n)) zero = swap0and1≃=invEquivSwap0and1
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- adjTransposition*Inv (suc (suc n)) (suc k) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   equivEq (refl =→  (cong ((suc ∘_) ∘ fst) (adjTransposition*Inv (suc n) k)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃GH : ∀ n → IsGroupHom (snd (Permutation n)) (to≃ n) (snd (SymData n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres· (to≃GH n) _ _ = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.pres1 (to≃GH n) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- IsGroupHom.presinv (to≃GH n) = RelimProp.f w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     w : RelimProp _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     RelimProp.isPropA w _ = isOfHLevel≃ 2 isSetFin isSetFin _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     RelimProp.εA w = equivEq refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     RelimProp.ηA w k = adjTransposition*Inv n k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     RelimProp.·A w p p₁ = cong₂ _∙ₑ_ p₁ p ∙ equivEq refl 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucPerm*R : ∀ n → Rrec {n = n} (Perm (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Rrec.isSetA (sucPerm*R n) = trunc
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Rrec.εA (sucPerm*R n) = ε
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Rrec.∷A (sucPerm*R (suc n)) = _∷_ ∘ suc
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Rrec.invoA (sucPerm*R (suc n)) _ = invo _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Rrec.braidA (sucPerm*R (suc (suc n))) _ = braid _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Rrec.commA (sucPerm*R (suc (suc n))) k (suc l) v = comm _ _ v

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucPerm* : ∀ n → Perm n →  Perm (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sucPerm* n = Rrec.f (sucPerm*R n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PunchHeadInOutPerm : ∀ n → Fin n → Perm n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PunchHeadInOutPerm (suc n) zero = ε
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- PunchHeadInOutPerm (suc (suc n)) (suc x) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  η zero · sucPerm* _ (PunchHeadInOutPerm _ x)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- from≃ : ∀ n → fst (SymData n) → Perm n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- from≃ zero _ = ε
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- from≃ (suc n) e =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let  (e' , p) = unwindPermHead e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in sucPerm* n (from≃ n e')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        · PunchHeadInOutPerm _ (fst e zero)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃∘sucPerm*≡sucPerm∘to≃R : ∀ n →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   RelimProp (λ z → to≃ (suc n) (sucPerm* n z) ≡ sucPerm (to≃ n z))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RelimProp.isPropA (to≃∘sucPerm*≡sucPerm∘to≃R n) _ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  isOfHLevel≃ 2 isSetFin isSetFin _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RelimProp.εA (to≃∘sucPerm*≡sucPerm∘to≃R n) = equivEq (refl =→ refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RelimProp.ηA (to≃∘sucPerm*≡sucPerm∘to≃R (suc n)) k = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RelimProp.·A (to≃∘sucPerm*≡sucPerm∘to≃R n) p p₁ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  cong₂ _∙ₑ_ p p₁ ∙ respectsCompSucPerm _ _ 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃∘sucPerm*≡sucPerm∘to≃ : ∀ n → ∀ x →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     to≃ (suc n) (sucPerm* n x) ≡ sucPerm (to≃ n x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃∘sucPerm*≡sucPerm∘to≃ n = RelimProp.f (to≃∘sucPerm*≡sucPerm∘to≃R n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃PunchHeadInOutPerm≡rot≃ : ∀ n k →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    to≃ n (PunchHeadInOutPerm n k) ≡ rot≃ {n = n} k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃PunchHeadInOutPerm≡rot≃ (suc n) zero = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃PunchHeadInOutPerm≡rot≃ (suc (suc n)) (suc k) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  cong (_ ∙ₑ_) (to≃∘sucPerm*≡sucPerm∘to≃ (suc n) (PunchHeadInOutPerm (suc n) k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∙ cong sucPerm (to≃PunchHeadInOutPerm≡rot≃ (suc n) k))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- perSymSec : ∀ n → section (to≃ n) (from≃ n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- perSymSec zero b = equivEq =■
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- perSymSec (suc n) e =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   let  (e' , p) = unwindPermHead e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   in  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     cong₂ _∙ₑ_ (to≃∘sucPerm*≡sucPerm∘to≃ n (from≃ n e')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ∙ cong sucPerm (perSymSec n e'))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (to≃PunchHeadInOutPerm≡rot≃ (suc n) (fst e zero))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ∙ sym p


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- perSymRet : ∀ n → retract (to≃ n) (from≃ n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- perSymRetR-lem : ∀ n → (e f : _) → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    from≃ (suc n) e · from≃ (suc n) f ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (from≃ (suc n) (e ∙ₑ f))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- perSymRetR-lem n =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    GeneratedElimConstr'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (SymData (suc n) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (generatedSym n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (λ f → (cong (_· from≃ _ f) {!!} ∙ idl _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ∙ cong (from≃ (suc n)) (sym (compEquivIdEquiv f)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- perSymRetR : ∀ n → Relim (λ z → from≃ (suc n) (to≃ (suc n) z) ≡ z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Relim.isPropA (perSymRetR n) _ = trunc _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Relim.εA (perSymRetR n) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   idr _ ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      cong (sucPerm* n ∘ from≃ n) unwindPermId 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ∙ cong (sucPerm* n) (perSymRet (n) ε)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Relim.ηA (perSymRetR .one) (zero {zero}) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  cong₂ _·_ (idl ε) (idr _) ∙ idl _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Relim.ηA (perSymRetR .(suc (suc n))) (zero {suc n}) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  cong₂ _·_ (cong (_· ε) (cong {y = idEquiv _} (sucPerm* (suc (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ∘ sucPerm* (suc n) ∘ from≃ (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (equivEq refl)) ∙ {!!} ) (idr _) ∙ (idl _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Relim.ηA (perSymRetR .(suc (suc n))) (suc {suc n} k) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   idr _ ∙ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     cong {x = (from≃ (suc (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (fst (unwindPermHead (to≃ (suc (suc (suc n))) (η (suc k))))))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (sucPerm* _) (
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       cong (_· PunchHeadInOutPerm (suc _) (fst (adjTransposition k) zero))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (cong {x = (fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (unwindPermHead
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (fst (unwindPermHead (to≃ (suc (suc (suc n))) (η (suc k)))))))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             {y = (fst (unwindPermHead (to≃ (suc (suc n)) (η k))))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (sucPerm* (suc n) ∘ from≃ (suc n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (equivEq refl))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ∙ Relim.ηA (perSymRetR _) k)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Relim.·A (perSymRetR n) {x} {y} pX pY =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   sym (perSymRetR-lem n _ _) ∙ cong₂ _·_ pX pY
 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- perSymRet zero = Relim.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  (record { isPropA = λ _ → trunc _ _ ; εA = refl ; ηA = ⊥.rec ∘ ¬Fin0
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ; ·A = λ pX pY → sym (idl _) ∙ cong₂ _·_ pX pY  })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- perSymRet (suc n) = Relim.f (perSymRetR n)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- GroupIsoPermSymData : ∀ n → GroupIso (Permutation n)  (SymData n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (fst (GroupIsoPermSymData n)) = to≃ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (fst (GroupIsoPermSymData n)) = from≃ n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (fst (GroupIsoPermSymData n)) = perSymSec n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (fst (GroupIsoPermSymData n)) = perSymRet n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (GroupIsoPermSymData n) = to≃GH n
