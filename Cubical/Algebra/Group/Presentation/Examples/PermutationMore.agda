{-# OPTIONS --safe --lossy-unification #-} 
module Cubical.Algebra.Group.Presentation.Examples.PermutationMore where

open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything
-- open import Cubical.Foundations.Function
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Bool as 𝟚
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Data.Nat using (ℕ ; suc ; zero)
open import Cubical.Data.Bool using (false ; true) renaming (Bool to 𝟚) 
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sum

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties

open import Cubical.HITs.EilenbergMacLane1

open import Cubical.HITs.GroupoidTruncation as GT

open import Cubical.HITs.S1


open import Cubical.Algebra.Group.Presentation.RelIndex

open import Cubical.Algebra.Group.Presentation.Examples.Permutation

open import Cubical.Algebra.Group.Abelianization.Base
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Algebra.Group.Abelianization.Properties renaming (rec to recAb)

-- open Braid/Symmetric false public

open import Cubical.Data.Int hiding (_·_)

open import Cubical.Algebra.Group.Instances.Int

open import Cubical.Algebra.Group.Presentation.Abelianization

module _ (n : ℕ) where
 open Braid n public
 open PresentationAbelianization σ-r public
 open Pres G {IxR = _} relsAb public

𝟚→ℤ+ : 𝟚 → ℤ → ℤ
𝟚→ℤ+ false = predℤ
𝟚→ℤ+ true = sucℤ

𝟚→ℤ+-invo : ∀ b x → 𝟚→ℤ+ (𝟚.not b) (𝟚→ℤ+ b x) ≡ x
𝟚→ℤ+-invo false = sucPred
𝟚→ℤ+-invo true = predSuc

𝔹ₙ→ℤ : ∀ n → T (suc (suc n)) → ℤ   
𝔹ₙ→ℤ n = RecT.f (suc (suc n)) w
 where
 open RecT
 w : Pres.RecT _ _ _
 isSetA w = isSetℤ
 εA w = pos zero
 ∷A w b (σₖ x) = 𝟚→ℤ+ b
 ∷A w b (σₖₗ x x₁) = 𝟚→ℤ+ b ∘ 𝟚→ℤ+ b 
 inv∷A w b (σₖ x) = 𝟚→ℤ+-invo b 
 inv∷A w b (σₖₗ x x₁) y =
  cong (𝟚→ℤ+ (𝟚.not b)) (𝟚→ℤ+-invo b _) ∙ 𝟚→ℤ+-invo b _
 relA w (inr (comp-σ x x₁)) a = refl
 relA w (inr (comm-σ k l x)) a = refl
 relA w (inr (braid-σ x)) a = refl
 relA w (inl (σₖ x , σₖ x₁)) a = refl
 relA w (inl (σₖ x , σₖₗ x₁ x₂)) a = refl
 relA w (inl (σₖₗ x x₁ , σₖ x₂)) a = refl
 relA w (inl (σₖₗ x x₁ , σₖₗ x₂ x₃)) a = refl

ηsk≡ηk : ∀ n k k< → Path (T (suc (suc n)) )
       ((true , σₖ (k , <-weaken k<)) ∷ ε) ((true , σₖ (suc k , k<)) ∷ ε) 
ηsk≡ηk n k k< =
  ·CancelL
   ((true , G.σₖₗ (k , <-weaken k<) (suc k , k<)) ∷ ε)
    (head-comm-η _ _ _ _ ∙ sym (rel (inr (braid-σ (k , k<))) ε))
 where
 open GroupTheory (GroupT (suc (suc n)))

ηk≡η0' : ∀ n k k< → Path (T (suc (suc n)) )
       ((true , σₖ (k , k<)) ∷ ε) ((true , σₖ (zero , _)) ∷ ε) 
ηk≡η0' n zero k< = refl
ηk≡η0' n (suc k) k< = 
  sym (ηsk≡ηk n k k<) ∙ ηk≡η0' n k (<-weaken k<)

ηk≡η0 : ∀ b n k k< → Path (T (suc (suc n)) )
       ((b , σₖ (k , k<)) ∷ ε) ((b , σₖ (zero , _)) ∷ ε) 
ηk≡η0 false n k k< = cong (inv _) (ηk≡η0' n k k<)
ηk≡η0 true = ηk≡η0'


Ab𝔹ₙ : ℕ → Type
Ab𝔹ₙ = λ n → T (suc (suc n))

ℤ→𝔹ₙ : ∀ n → ℤ → T (suc (suc n))
ℤ→𝔹ₙ n (pos n₁) =
 ℕ.iter n₁ ((true , (σₖ (zero , _))) ∷_) ε
ℤ→𝔹ₙ n (negsuc n₁) =
 ℕ.iter n₁ ((false , (σₖ (zero , _))) ∷_) ((false , σₖ (zero , _)) ∷ ε)

sec𝔹ₙℤ : ∀ n → section (𝔹ₙ→ℤ n) (ℤ→𝔹ₙ n)
sec𝔹ₙℤ n (pos zero) = refl
sec𝔹ₙℤ n (pos (suc n₁)) = cong sucℤ (sec𝔹ₙℤ n (pos (n₁))) 
sec𝔹ₙℤ n (negsuc zero) = refl
sec𝔹ₙℤ n (negsuc (suc n₁)) = cong predℤ (sec𝔹ₙℤ n (negsuc n₁))

ret𝔹ₙℤ : ∀ n → retract (𝔹ₙ→ℤ n) (ℤ→𝔹ₙ n)
ret𝔹ₙℤ n = ElimPropT.f _ w
 where

 lem : ∀ b x y → ℤ→𝔹ₙ n (𝟚→ℤ+ b y) ≡
      (σ-r (suc (suc n)) PresentationAbelianization.·''
       ((b , σₖ (zero , tt)) ∷ ε))
      (ℤ→𝔹ₙ n y)
 lem false x (pos zero) = refl
 lem false x (pos (suc n)) = sym (inv∷ _ _ _)
 lem false x (negsuc n) = refl
 lem true x (pos n) = refl
 lem true x (negsuc zero) = sym (inv∷ _ _ _)
 lem true x (negsuc (suc n)) = sym (inv∷ _ _ _)

 lem'  : ∀ xs b x → ℤ→𝔹ₙ n (𝔹ₙ→ℤ n xs) ≡ xs → 
   ℤ→𝔹ₙ n (𝔹ₙ→ℤ n ((b , G.σₖ x) ∷ xs)) ≡ (b , G.σₖ x) ∷ xs
 lem' xs b x p =
     lem b x (𝔹ₙ→ℤ n xs)
   ∙ cong₂ (λ x → _·''_ (suc (suc n)) x)
  (sym (ηk≡η0 b n (fst x) (snd x))) p

 open ElimPropT
 w : ElimPropT _  _
 isPropA w _ = trunc _ _
 εA w = refl
 ∷A w {xs} b (σₖ x) = lem' xs b x
 
 ∷A w {xs} true (σₖₗ x x₁) p =
   (cong (ℤ→𝔹ₙ n ∘ 𝔹ₙ→ℤ n) (sym (rel (inr (comp-σ _ _)) xs)) ∙
     lem' _ _ _ (lem' _ _ _ p)) 
     ∙ rel (inr (comp-σ _ _)) xs 
 ∷A w {xs} false (σₖₗ x x₁) p =
      (cong (ℤ→𝔹ₙ n ∘ 𝔹ₙ→ℤ n) (sym (relInv _ (inr (comp-σ _ _)) xs)) ∙
     lem' _ _ _ (lem' _ _ _ p)) 
     ∙ relInv _ (inr (comp-σ _ _)) xs 

IsoAb𝔹ₙℤ : ∀ n → Iso (Ab𝔹ₙ n) ℤ
Iso.fun (IsoAb𝔹ₙℤ n) = 𝔹ₙ→ℤ n
Iso.inv (IsoAb𝔹ₙℤ n) = ℤ→𝔹ₙ n
Iso.rightInv (IsoAb𝔹ₙℤ n) = sec𝔹ₙℤ n
Iso.leftInv (IsoAb𝔹ₙℤ n) = ret𝔹ₙℤ n

-- Ghom : ∀ n → IsGroupHom (snd ℤGroup) (ℤ→𝔹ₙ n) (snd (GroupT (suc (suc n))))  
-- Ghom n = w
--  where
--  w' : ∀ x y → _
--  w' (pos zero) y = {!!}
--  w' (pos (suc n)) y =
--    {!!} ∙ cong ((true , G.σₖ (0 , tt)) ∷_) (w' (pos n) y) 
--  w' (negsuc n) y = {!!}

--  w : IsGroupHom _ _ _
--  IsGroupHom.pres· w = w'
  
--  IsGroupHom.pres1 w = refl
--  IsGroupHom.presinv w = {!!}

Ghom : ∀ n → IsGroupHom (snd (GroupT (suc (suc n)))) (𝔹ₙ→ℤ n) (snd ℤGroup)  
Ghom n = w
 where
 
 w : IsGroupHom _ _ _
 IsGroupHom.pres· w = ElimPropT.f (suc (suc n)) w'
  where
  open Pres.ElimPropT
  w' : ElimPropT (suc (suc n)) _
  isPropA w' _ = isPropΠ λ _ → isSetℤ _ _
  εA w' _ = pos0+ _
  ∷A w' false (Braid/Symmetric.σₖ x) x₁ x₂ =
    cong predℤ  (x₁ x₂) ∙ predℤ+ _ _
  ∷A w' true (Braid/Symmetric.σₖ x) x₁ x₂ =
    cong sucℤ  (x₁ x₂) ∙ sucℤ+ _ _
  ∷A w' {xs} false (σₖₗ x x₃) x₁ x₂ =
    cong (predℤ ∘ predℤ) (x₁ x₂)
     ∙∙ cong (predℤ) (predℤ+ _ _) 
     ∙∙ predℤ+ _ _
  ∷A w' true (σₖₗ x x₃) x₁ x₂ =
    cong (sucℤ ∘ sucℤ) (x₁ x₂)
     ∙∙ cong (sucℤ) (sucℤ+ _ _) 
     ∙∙ sucℤ+ _ _
  
 IsGroupHom.pres1 w = refl
 IsGroupHom.presinv w = ElimPropT.f (suc (suc n)) w'
  where
  open Pres.ElimPropT
  w' : ElimPropT (suc (suc n)) _
  isPropA w' _ = isSetℤ _ _
  εA w' = refl
  ∷A w' b x x₁ = {!!}
  -- ∷A w' true x x₁ = {!!}


-- Ab𝔹ₙ→S¹ : ∀ n → Ab𝑩ₙ (suc (suc n)) → ℤ   
-- Ab𝔹ₙ→S¹ n =
--  recAb _ isSetℤ
--    (𝔹ₙ→ℤ n)
--    λ a b c → {!!}
--    -- cong (𝔹ₙ→ℤ n a +_) {!!} --(+Comm (𝔹ₙ→ℤ n b) (𝔹ₙ→ℤ n c))
--   -- λ a b c → cong (cong (𝔹ₙ→S¹ n) a ∙_)
--   --   (comm-ΩS¹ (cong (𝔹ₙ→S¹ n) b) (cong (𝔹ₙ→S¹ n) c))


-- -- 𝔹ₙ→S¹ : ∀ n → 𝔹T (suc (suc n)) → S¹   
-- -- 𝔹ₙ→S¹ n = Rec𝔹T.f (suc (suc n)) w
-- --  where
-- --  open Rec𝔹T
-- --  w : Pres.Rec𝔹T _ _ _
-- --  isGroupoidA w = isGroupoidS¹
-- --  baseA w = base
-- --  loopA w (σₖ x) = loop
-- --  loopA w (σₖₗ x x₁) = loop ∙ loop
-- --  relSqA w (comp-σ k l) i j =
-- --    hcomp
-- --      (λ i' → λ { (j = i0) → base
-- --                ; (j = i1) → loop (i ∧ i')
-- --                ; (i = i0) → loop j })
-- --      (loop j)
-- --  relSqA w (comm-σ k l x) = refl
-- --  relSqA w (braid-σ x) i j = 
-- --    hcomp (λ k → λ { (i = i0) → loop j
-- --                    ; (i = i1) →
-- --                      (invSides-filler (S¹.loop) (sym (S¹.loop))) (~ k) j 

-- --                    })
-- --           ((invSides-filler (S¹.loop) (sym (S¹.loop))) (~ i) j )

-- -- S¹→𝔹ₙ : ∀ n → S¹ → 𝔹T (suc (suc n))   
-- -- S¹→𝔹ₙ n base = base
-- -- S¹→𝔹ₙ n (loop i) = loop (σₖ (zero , tt)) i


-- -- Ab𝔹ₙ→S¹ : ∀ n → Ab𝑩ₙ (suc (suc n)) → ΩS¹   
-- -- Ab𝔹ₙ→S¹ n =
-- --  recAb _ isSetΩS¹ (cong (𝔹ₙ→S¹ n))
-- --   λ a b c → cong (cong (𝔹ₙ→S¹ n) a ∙_)
-- --     (comm-ΩS¹ (cong (𝔹ₙ→S¹ n) b) (cong (𝔹ₙ→S¹ n) c))

-- -- S¹→Ab𝔹ₙ : ∀ n → ΩS¹ → Ab𝑩ₙ (suc (suc n))   
-- -- S¹→Ab𝔹ₙ n = Abelianization.η ∘ cong (S¹→𝔹ₙ n)

-- -- secS¹→Ab𝔹ₙ : ∀ n → section (Ab𝔹ₙ→S¹ n) (S¹→Ab𝔹ₙ n)
-- -- secS¹→Ab𝔹ₙ n b = {!!}

-- -- retS¹→Ab𝔹ₙ : ∀ n → retract (Ab𝔹ₙ→S¹ n) (S¹→Ab𝔹ₙ n)
-- -- retS¹→Ab𝔹ₙ n a = {!!}
