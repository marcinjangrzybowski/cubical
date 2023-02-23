{-# OPTIONS --safe #-}
module Cubical.Data.Nat.Order.PermutationMore where

open import Cubical.Data.Nat.Base as ℕ hiding (_·_)
open import Cubical.Data.Nat.Properties


-- open import Cubical.Data.Fin.Properties as FP
open import Cubical.Data.Empty as ⊥

open import Cubical.Functions.Involution

open import Cubical.Foundations.Everything
open import Cubical.Foundations.Univalence
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

import Cubical.Data.Nat.FinGenAut2 as A

import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.HITs.GroupoidQuotients as GQ
  renaming ([_] to [_]// ; RelimProp to  RelimProp// ; Rrec to Rrec//)


open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

-- open import Cubical.Algebra.Group.Generators

open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.SequentialColimit as SC

open import Cubical.Data.Nat.Order.Permutation

-- open import Cubical.Data.FinData.GTrun

open import Cubical.HITs.EilenbergMacLane1 renaming (elim to elimEM)

private
  variable
    ℓ : Level
    A : Type ℓ



-- EMΣ : ?

ℙrm : ℕ → Type
ℙrm n = EM₁ (Symmetric-Group (Fin n) (isSetFin {n}))

ℙrm' : ℕ → Type
ℙrm' n = EM₁ (PermG n)


h𝔽in : ∀ n → ℙrm n → hSet ℓ-zero
h𝔽in n = EMrec.f w
 where
  w : EMrec (Symmetric-Group (Fin n) (isSetFin {n})) isGroupoidHSet
  EMrec.b w = Fin n , isSetFin {n}
  EMrec.bloop w g = TypeOfHLevel≡ 2 (ua g)
  EMrec.bComp w g h =
     ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
        (compPath-filler (ua g) (ua h) ▷
          (sym (uaCompEquiv _ _)))



-- h𝔽in' : ∀ n → ℙrm' n → hSet ℓ-zero
-- h𝔽in' n = EMrec.f w
--  where
--   w : EMrec _ isGroupoidHSet
--   EMrec.b w = Fin n , isSetFin {n}
--   EMrec.bloop w g = TypeOfHLevel≡ 2
--     (ua (isoToEquiv (Iso.fun (fst (PermGIsoIso n)) g)))
--   EMrec.bComp w g h = 
--      ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
--         (compPath-filler
--           (ua (isoToEquiv (Iso.fun (fst (PermGIsoIso n)) g)))
--           (ua (isoToEquiv (Iso.fun (fst (PermGIsoIso n)) h))) ▷
--           ((sym (uaCompEquiv _ _) ∙
--             cong ua (equivEq {!!})))
--           )




𝔽in : ∀ n → ℙrm n → Type ℓ-zero
𝔽in  n = fst ∘ h𝔽in n


ism : ∀ n → Iso (Perm n) (Iso (Fin n) (Fin n))
ism n = (fst (PermGIsoIso n))


-- 𝔽in' : ∀ n → ℙrm' n → Type ℓ-zero
-- 𝔽in'  n = fst ∘ h𝔽in n ∘ gh→em₂→ _
--   (compGroupHom (_ , snd (PermGIsoIso n)) (_ , snd (SG-SI _ _)))

h𝔽in' : ∀ n → ℙrm' n → hSet ℓ-zero
h𝔽in' n = EMrec.f w
 where
  w : EMrec _ isGroupoidHSet
  EMrec.b w = Fin n , isSetFin {n}
  EMrec.bloop w g = TypeOfHLevel≡ 2 (ua
    (isoToEquiv ( (permuteIso n g))))
  EMrec.bComp w g h = 
     ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
        (compPath-filler (ua (isoToEquiv ((permuteIso n g))))
          (ua (isoToEquiv (permuteIso n h))) ▷
          
          ((sym (uaCompEquiv _ _)) ∙
            cong ua (equivEq (cong Iso.fun (permuteIso· n g h))))
          )



𝔽in' : ∀ n → ℙrm' n → Type ℓ-zero
𝔽in' n = fst ∘ h𝔽in' n


𝔽h : (A : Type ℓ) → ∀ n → ℙrm n → Type ℓ
𝔽h A n em = 𝔽in n em → A 

𝔽h' : (A : Type ℓ) → ∀ n → ℙrm' n → Type ℓ
𝔽h' A n em = 𝔽in' n em → A 


-- -- Iso-𝔽h-×^ : ∀ n → Iso (𝔽h A n embase) (A ×^ n) 
-- -- Iso-𝔽h-×^ n = {!!}


adjT×^'→ : ∀ {n} → ℕ →
             (A ×^ n) → (A ×^ n)
adjT×^'→ {n = zero} _ x = x
adjT×^'→ {n = suc zero} _ x = x
adjT×^'→ {n = suc (suc n)} zero (x , x' , xs) = (x' , x , xs)
adjT×^'→ {n = suc (suc n)} (suc k) (x , xs) =
   x , adjT×^'→ k xs

isInvo-adjT×^'→ : ∀ {n} → ∀ k → isInvolution (adjT×^'→ {A = A} {n} k) 
isInvo-adjT×^'→ {n = zero} k x = refl
isInvo-adjT×^'→ {n = suc zero} k x = refl
isInvo-adjT×^'→ {n = suc (suc n)} zero x = refl
isInvo-adjT×^'→ {n = suc (suc n)} (suc k) (x , xs) =
 cong (x ,_) (isInvo-adjT×^'→ k xs)


braid-adjT×^'→ : ∀ {n} → ∀ k →  suc (suc k) < n → ∀ v → 
  (adjT×^'→ {A = A} {n} k ∘ adjT×^'→ {A = A} {n} (suc k) ∘ adjT×^'→ {A = A} {n} (k)) v
  ≡ (adjT×^'→ {A = A} {n} (suc k) ∘ adjT×^'→ {A = A} {n} (k) ∘ adjT×^'→ {A = A} {n} (suc k)) v
braid-adjT×^'→ {n = suc (suc (suc n))} zero x _ = refl
braid-adjT×^'→ {n = suc (suc (suc (suc n)))} (suc k) x (v , vs) =
  cong (v ,_) (braid-adjT×^'→ k x vs)

-- adjT×^ : ∀ {n} → ℕ →
--   Iso (A ×^ n)
--       (A ×^ n)
-- adjT×^ {n} k =
--  involIso {f = adjT×^'→ {n} k} (isInvo-adjT×^'→ {n} k)


lawAdj : ∀ n k → (f : Fin n → A) → tabulate {n = n}
      (f ∘ adjT n k)
      ≡ adjT×^'→ (fst k) (tabulate f)
lawAdj (suc (suc n)) (zero , snd₁) f = refl
lawAdj (suc (suc n)) (suc k , k<) f =
  cong ((f (zero , _)) ,_) (lawAdj (suc n) (k , k<) (f ∘ sucF) )

lawAdj' : ∀ n k → (v : A ×^ n) →
                lookup v ∘ (adjT n k)
            ≡  lookup (adjT×^'→ {n = n} (fst k) v)
lawAdj' (suc (suc n)) (zero , k<) v =
  funExt (uncurry (cases (λ _ → refl)
    (cases (λ _ → refl) λ _ _ → refl)))
lawAdj' (suc (suc (suc n))) (suc k , k<) v =
  funExt (uncurry (cases (λ _ → refl)
     λ kk y → funExt⁻ (lawAdj' (suc (suc n)) (k , k<) (snd v)) (kk , y)) )

lawAdj-invo : ∀ n k → (f : Fin n → A) →
    Square
      (lawAdj n k (f ∘ adjT n k))
      (sym (isInvo-adjT×^'→ (fst k) (tabulate f)))
      (cong (tabulate ∘' (f ∘'_)) (funExt (isInvolution-adjT n k)))
      (cong′ (adjT×^'→ (fst k)) (lawAdj n k f))
 
lawAdj-invo (suc (suc n)) (zero , k<) f =
  congP (λ i → cong ((f (0 , tt)) ,_))
    (congP (λ i → cong ((f (1 , tt)) ,_))
      (congP (λ i → cong (tabulate ∘' (f ∘'_)))
       (isSet→isSet' (isSet→ (isSetFin {n = (suc (suc n))}))
         _ _ _ _)))
lawAdj-invo (suc (suc (suc n))) (suc k , k<) f =
   congP (λ i → cong ((f (0 , tt)) ,_))
     (lawAdj-invo (suc (suc n)) (k , k<) (f ∘ sucF))

lawAdj'-invo : ∀ n k → (v : A ×^ n) →
    Square
      (cong′ (_∘ adjT n k) (lawAdj' n k v)) 
      (sym (cong (lookup) (isInvo-adjT×^'→ (fst k) v)))      
      ( funExt (cong (lookup v) ∘ (isInvolution-adjT n k)))
      (lawAdj' n k (adjT×^'→ (fst k) v))

lawAdj'-invo (suc (suc n)) (zero , k<) v =
  congP (λ _ → cong′ uncurry)
    (refl A.sqP→ refl A.sqP→
      congP (λ _ → cong′ (curry ∘ (lookup (snd (snd v)) ∘_ )))
         (flipSquare ((isSet→ (isSetFin {n = n}))
            _ _ _ _)))
  
lawAdj'-invo (suc (suc (suc n))) (suc k , k<) v =
  congP (λ _ → cong′ uncurry)
    (refl A.sqP→
      congP (λ _ → cong′ curry)
        (lawAdj'-invo (suc (suc n)) (k , k<) (snd v)))


-- module _ (isSetA : isGroupoid A) where

--   pRel : ∀ n → Perm n → Rel (A ×^ n) (A ×^ n) ℓ
--   pRel = {!!}




-- permute→×^ : ∀ n → (p : Perm n) → 
--     Σ ((A ×^ n) → (A ×^ n)) λ f → 
--       (∀ v z z< → (lookup v ((z , z<)))
--           ≡ lookup (f v) (permuteF' n p (z , z<)) )
-- permute→×^ {A = A} n = Relim.f (w n)
--  where

--  open Relim

--  w : ∀ n → Relim {n = n}
--       λ p → Σ ((A ×^ n) → (A ×^ n)) λ f → 
--       (∀ v z z< → (lookup v ((z , z<)))
--           ≡ lookup (f v) (permuteF' n p (z , z<)) )
--  isSetA (w n) = {!!}
--  εA (w n) = idfun _ , λ _ _ _ → refl
--  fst (∷A (w n) k (X , _)) = adjT×^'→ (fst k) ∘ X
--  snd (∷A (w (suc (suc n))) (zero , k<) (X , XP)) v zero z< =
--      {!XP (v) 0 _!}
--  snd (∷A (w (suc (suc n))) (zero , k<) (X , XP)) v (suc z) z< = {!!}
 
--  snd (∷A (w (suc (suc (suc n)))) (suc k , k<) (X , XP)) v zero z< =
--    {!!}
--  snd (∷A (w (suc (suc (suc n)))) (suc k , k<) (X , XP)) v (suc z) z< = {!!}
--  invoA (w n) = {!!}
--  braidA (w n) = {!!}
--  commA (w n) = {!!}


-- permute→×^ : ∀ n → (p : Perm n) → 
--     Σ ((A ×^ n) → (A ×^ n)) λ f → 
--       (∀ v z z< → (lookup v (permuteF n p (z , z<)))
--           ≡ lookup (f v) (z , z<) )
-- permute→×^ {A = A} n = Relim.f (w n)
--  where

--  open Relim

--  w : ∀ n → Relim {n = n}
--       λ p → Σ ((A ×^ n) → (A ×^ n)) λ f → 
--       (∀ v z z< → (lookup v (permuteF n p (z , z<)))
--           ≡ lookup (f v) (z , z<) )
--  isSetA (w n) = {!!}
--  εA (w n) = idfun _ , λ _ _ _ → refl
--  fst (∷A (w n) k (X , _)) = (adjT×^'→ (fst k) ∘ X)
--  snd (∷A (w n) k (X , _)) = {!!}
--  -- snd (∷A (w (suc (suc n))) (zero , k<) (X , XP)) v zero z< =
--  --  XP (v) 1 _
--  -- snd (∷A (w (suc (suc n))) (zero , k<) (X , XP)) v (suc zero) z< =
--  --  XP (v) 0 _
--  -- snd (∷A (w (suc (suc n))) (zero , k<) (X , XP)) v (suc (suc z)) z< =
--  --  XP (v) (suc (suc z)) _
  
--  -- snd (∷A (w (suc (suc n))) (suc k , k<) (X , XP)) v z z< ={!!}
--  invoA (w n) = {!!}
--  braidA (w n) = {!!}
--  commA (w n) = {!!}


-- -- permute→×^ : ∀ n → (p : Perm n) → 
-- --     singl {A = (A ×^ n) → (A ×^ n)}
-- --       (λ v → tabulate (lookup v ∘ permuteF n p))
-- -- permute→×^ {A = A} n = Relim.f (w n)
-- --   where

-- --    open Relim

   
-- --    w : ∀ n → Relim {n = n}
-- --       (λ z → singl {A = (A ×^ n) → (A ×^ n)}
-- --           (λ v → tabulate {A = A} {n = n}
-- --            (lookup {n = n} v ∘ permuteF n z)))
-- --    isSetA (w n) _ = isOfHLevelPlus 2 (isContrSingl _)
-- --    εA (w n) = (idfun _) , (funExt (Iso.leftInv (Iso-×^-F→ n)))
-- --    fst (∷A (w n) k {xs} (X , XP)) = (adjT×^'→ (fst k) ∘ X)
-- --    snd (∷A (w n) k {xs} (X , XP)) =      
-- --       funExt
-- --         (λ v →
-- --          lawAdj n k (lookup v ∘ permuteF n xs))
-- --           ∙ cong′ (adjT×^'→ (fst k) ∘_) XP
        
-- --    invoA (w n) k {xs} (f , p') =
-- --      -- TODO ; simplify
-- --      ΣPathP
-- --      (funExt (λ v → isInvo-adjT×^'→ (fst k) (f v)) ,
-- --       ((cong′ (
-- --          (funExt
-- --         (λ v →
-- --          lawAdj n k _)) ∙_)
-- --           (cong-∙ (adjT×^'→ (fst k) ∘_) _ _) ∙
-- --            assoc _ _ _)
-- --             ◁ comm→PathP (pp ∙ assoc _ _ _)))
-- --      where

-- --       ppL : (v : A ×^ n) →
-- --          _
-- --       ppL v = PathP∙∙→compPathR
-- --         (flipSquare (lawAdj-invo {A = A} n k (lookup v ∘
-- --             permuteF n xs)))

-- --       pp1 = _
-- --       pp : _
-- --       pp = cong′ (_∙ p') (cong funExt (funExt (ppL))
-- --         ∙ doubleCompPath-elim
-- --            (funExt ((λ x i →
-- --             lawAdj n k ((λ x₁ → lookup x (permuteF n xs x₁))
-- --               ∘ adjT n k) i))) _ _)
-- --         ∙ sym (assoc pp1 _ _)
-- --         ∙ cong′ (pp1 ∙_)
-- --           (homotopyNatural
-- --                (λ a → cong (_∘' a) (funExt (isInvo-adjT×^'→ (fst k))))
-- --                 p') 
     
-- --    braidA (w n) = {!!}
-- --    commA (w n) = {!!}



-- -- permute→×^' : ∀ n → (p : Perm n) → 
-- --     Σ ((A ×^ n) → (A ×^ n))
-- --      λ f → ∀ v k k< →
-- --         (lookup v ((permuteF' n p) (k , k<)))
-- --            ≡ lookup (f v) (k , k<)
-- -- permute→×^' {A = A} n = Relim.f (w n)
-- --  where
-- --   open Relim



-- --   h∷ : ∀ n xs k → 
-- --      ∀ v  k' k'< →
-- --        ((lookup {n = n} v ∘ permuteF' n (k ∷ xs)) ( k' , k'<)) ≡
-- --        ((lookup (adjT×^'→ (fst k) v) ∘ permuteF' n xs) ( k' , k'<)) 
-- --   h∷ n xs k v k' k'< i = 
-- --     (lawAdj' {A = A} n k v i) (permuteF' n xs (k' , k'<))


-- --   -- h∷ : ∀ n xs k → 
-- --   --    ∀ v  k' k'< →
-- --   --      ((lookup {n = n} v ∘ permuteF' n (k ∷ xs)) ( k' , k'<)) ≡
-- --   --      ((lookup (adjT×^'→ (fst k) v) ∘ permuteF' n xs) ( k' , k'<)) 
-- --   -- h∷ n xs k v k' k'< i = 
-- --   --   (lawAdj' {A = A} n k v i) (permuteF' n xs (k' , k'<))

-- --   -- hh : ∀ n → (v : A ×^ (suc n)) (k : Fin n) (k₁ : ℕ) (k< : k₁ < (suc n)) →
-- --   --      (f : Fin (suc n) → Fin (suc n)) →
-- --   --      (g : A ×^ (suc n) → A ×^ (suc n))
-- --   --     (XP : (v : A ×^ (suc n)) (k₁ : ℕ) (k< : k₁ < (suc n)) →
-- --   --        lookup v (f (k₁ , k<)) ≡ lookup (g v) (k₁ , k<))
-- --   --      →   
-- --   --     lookup v (adjT (suc n) k (f (k₁ , k<))) ≡
-- --   --     lookup (g (adjT×^'→ (fst k) v)) (k₁ , k<)
      
-- --   -- hh (suc n) v (zero , k<) k₁ k₁< f₁ g XP =
-- --   --   {!XP (adjT×^'→ zero v) ? k₁ k₁<!}
  
-- --   -- hh n v (suc k , k<) k₁ k₁< f₁ g XP = {!!}

-- --   w : ∀ n → Relim {n = n} λ p → Σ ((A ×^ n) → (A ×^ n))
-- --      λ f → ∀ v k k< →
-- --         (lookup v ((permuteF' n p) (k , k<)))
-- --            ≡ lookup (f v) (k , k<)
-- --   isSetA (w n) = {!!}
-- --   εA (w n) = (idfun _) , λ _ _ _ → refl
-- --   fst (∷A (w n) k {xs} (X , _)) = X ∘ adjT×^'→ (fst k)
-- --   snd (∷A (w (suc (suc n))) (zero , k<) {xs} (X , XP)) v k₁ k<₁ = 
-- --     let XP' = XP (adjT×^'→ zero v) k₁ k<₁
-- --     in {!XP'!}
-- --   snd (∷A (w (suc (suc n))) (suc k , k<) {xs} (X , XP)) v k₁ k<₁ = {!!}
-- --     -- h∷ n xs k v k' k< ∙ XP (adjT×^'→ (fst k) v) k' k<
-- --   invoA (w n) k {xs} (X , XP) = {!!}
-- --    -- ΣPathP
-- --    --  ((funExt
-- --    --   (λ v → cong X (isInvo-adjT×^'→ (fst k) v))) ,
-- --    --    funExt λ v → funExt λ m → funExt λ m< → 
-- --    --        -- todo : simplify to  use less hcomps
-- --    --      sym (doubleCompPath-elim' _ _ _) ◁
-- --    --       λ i j →
-- --    --         hcomp
-- --    --          (λ l →
-- --    --            λ { (j = i0) →
-- --    --                  lawAdj'-invo n k v i (~ l) (permuteF' n xs (m , m<))
                   
-- --    --               ; (j = i1) → XP (isInvo-adjT×^'→ (fst k) v i ) m m< l
-- --    --               ; (i = i1) → invSides-filler
-- --    --                 (λ i →
-- --    --                   (lookup (isInvo-adjT×^'→ (fst k) v (~ i))
-- --    --             (permuteF' n xs (m , m<))))
-- --    --               (XP v m m<) (j) (~ l) 
-- --    --               })
-- --    --         (invSides-filler
-- --    --           (λ i → lookup (isInvo-adjT×^'→ (fst k) v i)
-- --    --             (permuteF' n xs (m , m<)))
-- --    --              (sym (h∷ n xs k (adjT×^'→ (fst k) v) m m<)) (~ i) j )   
-- --    --          ) 
-- --   braidA (w n) k k< {xs} (X , XP) = {!!}
-- --     -- ΣPathP (funExt (λ v → cong X (braid-adjT×^'→ k k< v))  ,
-- --     --  funExt₃ λ v k k< → {!!})
-- --      -- {!(? ∙ ( ? ∙ ?)) j!}
-- --   commA (w n) = {!!}



-- -- -- permute→×^' : ∀ n → (p : Perm n) → 
-- -- --     Σ ((A ×^ n) → (A ×^ n))
-- -- --      λ f → ∀ v k k< →
-- -- --         (lookup v ((permuteF' n p) (k , k<)))
-- -- --            ≡ lookup (f v) (k , k<)
-- -- -- permute→×^' {A = A} n = Relim.f (w n)
-- -- --  where
-- -- --   open Relim


-- -- --   h∷ : ∀ n xs k → 
-- -- --      ∀ v  k' k'< →
-- -- --        ((lookup {n = n} v ∘ permuteF' n (k ∷ xs)) ( k' , k'<)) ≡
-- -- --        ((lookup (adjT×^'→ (fst k) v) ∘ permuteF' n xs) ( k' , k'<)) 
-- -- --   h∷ n xs k v k' k'< i = 
-- -- --     (lawAdj' {A = A} n k v i) (permuteF' n xs (k' , k'<))


-- -- --   w : ∀ n → Relim {n = n} λ p → Σ ((A ×^ n) → (A ×^ n))
-- -- --      λ f → ∀ v k k< →
-- -- --         (lookup v ((permuteF' n p) (k , k<)))
-- -- --            ≡ lookup (f v) (k , k<)
-- -- --   isSetA (w n) = {!!}
-- -- --   εA (w n) = (idfun _) , λ _ _ _ → refl
-- -- --   fst (∷A (w n) k {xs} (X , _)) = X ∘ adjT×^'→ (fst k)
-- -- --   snd (∷A (w n) k {xs} (X , XP)) v k' k< =
-- -- --     h∷ n xs k v k' k< ∙ XP (adjT×^'→ (fst k) v) k' k<
-- -- --   invoA (w n) k {xs} (X , XP) = ΣPathP
-- -- --     ((funExt
-- -- --      (λ v → cong X (isInvo-adjT×^'→ (fst k) v))) ,
-- -- --       funExt λ v → funExt λ m → funExt λ m< → 
-- -- --           -- todo : simplify to  use less hcomps
-- -- --         sym (doubleCompPath-elim' _ _ _) ◁
-- -- --          λ i j →
-- -- --            hcomp
-- -- --             (λ l →
-- -- --               λ { (j = i0) →
-- -- --                     lawAdj'-invo n k v i (~ l) (permuteF' n xs (m , m<))
                   
-- -- --                  ; (j = i1) → XP (isInvo-adjT×^'→ (fst k) v i ) m m< l
-- -- --                  ; (i = i1) → invSides-filler
-- -- --                    (λ i →
-- -- --                      (lookup (isInvo-adjT×^'→ (fst k) v (~ i))
-- -- --                (permuteF' n xs (m , m<))))
-- -- --                  (XP v m m<) (j) (~ l) 
-- -- --                  })
-- -- --            (invSides-filler
-- -- --              (λ i → lookup (isInvo-adjT×^'→ (fst k) v i)
-- -- --                (permuteF' n xs (m , m<)))
-- -- --                 (sym (h∷ n xs k (adjT×^'→ (fst k) v) m m<)) (~ i) j )   
-- -- --             ) 
-- -- --   braidA (w n) k k< {xs} (X , XP) =
-- -- --     ΣPathP (funExt (λ v → cong X (braid-adjT×^'→ k k< v))  ,
-- -- --      funExt₃ λ v k k< → {!!})
-- -- --      -- {!(? ∙ ( ? ∙ ?)) j!}
-- -- --   commA (w n) = {!!}

-- -- -- -- 

-- -- -- -- (λ i → XP (adjT×^'→ (fst k) (adjT×^'→ (fst k) v)) m m< i)

-- -- -- -- lookup (funExt (λ v₁ i → X (isInvo-adjT×^'→ (fst k) v₁ i)) z v)
-- -- -- --          (m , m<)

-- -- -- -- (XP v m m<)


-- -- -- -- permute→×^' : ∀ n → (p : Perm n) → 
-- -- -- --     Σ ((A ×^ n) → (A ×^ n))
-- -- -- --      λ f → ∀ v →
-- -- -- --         (lookup v ∘ permuteF' n p)
-- -- -- --            ≡ lookup (f v)
-- -- -- -- permute→×^' {A = A} n = Relim.f (w n)
-- -- -- --  where

-- -- -- --   open Relim

-- -- -- --   h∷ : ∀ n xs k →
-- -- -- --      ∀ v → (lookup {n = n} v ∘ permuteF' n (k ∷ xs)) ≡
-- -- -- --        (lookup (adjT×^'→ (fst k) v) ∘ permuteF' n xs) 
-- -- -- --   h∷ n xs k v = cong′ (_∘' permuteF' n xs)
-- -- -- --       (lawAdj' n k v)


-- -- -- --   w : ∀ n → Relim {n = n} λ p → Σ ((A ×^ n) → (A ×^ n))
-- -- -- --      λ f → ∀ v →
-- -- -- --         (lookup v ∘ permuteF' n p)
-- -- -- --            ≡ lookup (f v)
-- -- -- --   isSetA (w n) = {!!}
-- -- -- --   εA (w n) = (idfun _) , λ _ → refl
-- -- -- --   fst (∷A (w n) k {xs} (X , _)) = X ∘ adjT×^'→ (fst k)
-- -- -- --   snd (∷A (w n) k {xs} (X , XP)) v =
-- -- -- --      h∷ n xs k v ∙ XP (adjT×^'→ (fst k) v)
    
-- -- -- --   invoA (w n) k {xs} (X , XP) = ΣPathP
-- -- -- --    ((funExt (λ v →
-- -- -- --        cong X (isInvo-adjT×^'→ (fst k) v))) ,
-- -- -- --      (funExt λ v →
-- -- -- --       let q = 
-- -- -- --                   ((λ i₁ a₁ → h∷ n (k ∷ xs) k v i₁ a₁) ∙
-- -- -- --                    (λ i₁ a₁ → h∷ n xs k (adjT×^'→ (fst k) v) i₁ a₁))
                  
-- -- -- --       in assoc _ _ _ ◁ 
-- -- -- --           comm→PathP {r = q ∙ _} ((
           
-- -- -- --           (cong′ (_∙ (XP v))
-- -- -- --             -- {x = λ i a → (lookup v ∘ permuteF' n (invo k xs i)) a}
-- -- -- --             -- {y = q ∙ {!!}}
-- -- -- --             {! !} 
-- -- -- --             ∙ sym (assoc _ _ _) ∙ 
-- -- -- --             cong′ (q ∙_)
-- -- -- --               (sym (homotopyNatural XP (isInvo-adjT×^'→ (fst k) v))))
-- -- -- --           ∙
-- -- -- --           assoc _ _ _))))

-- -- -- -- -- (λ i → lookup v ∘ permuteF' n (invo k xs i)) ∙ XP v 

-- -- -- --    -- where
-- -- -- --    --  q = {!!}

-- -- -- --     -- zz : ∀ v → 
-- -- -- --     --    {!!} ∙ XP v ≡ XP (adjT×^'→ (fst k) (adjT×^'→ (fst k) v))
-- -- -- --     --       ∙ (λ i →
-- -- -- --     --      lookup (funExt (λ v₁ i₁ → X (isInvo-adjT×^'→ (fst k) v₁ i₁)) i v))
-- -- -- --     -- zz v = sym (homotopyNatural
-- -- -- --     --   {f = {!!}} {g = {!!}}
-- -- -- --     --   XP
-- -- -- --     --   {x = {!!}} {y = {!!}} (isInvo-adjT×^'→ (fst k) v)

-- -- -- --     -- qq : ∀ v → {!!}
-- -- -- --     -- qq v = (homotopyNatural 
-- -- -- --     --               (λ a → cong (a ∘'_)
-- -- -- --     --                 {!(funExt λ a' → λ z → isInvo-adjT×^'→ (fst k) a' z)!} )
-- -- -- --     --                  (XP v))
-- -- -- --     -- zL : ∀ v → {!!}
-- -- -- --     -- zL v = assoc _ _ _ ∙
-- -- -- --     --   {!!}
-- -- -- --      -- cong′ (h∷ n (k ∷ xs) k v ∙_)
-- -- -- --      --  {!!}
-- -- -- --      --  ∙ {!!}
-- -- -- --   braidA (w n) = {!!}
-- -- -- --   commA (w n) = {!!}

-- -- -- -- -- permute→×^' : ∀ n → (p : Perm n) → 
-- -- -- -- --     singl {A = (A ×^ n) → (A ×^ n)}
-- -- -- -- --       (λ v → tabulate (lookup v ∘ permuteF' n p))
-- -- -- -- -- permute→×^' {A = A} n = Relim.f (w n)
-- -- -- -- --  where

-- -- -- -- --   open Relim

-- -- -- -- --   h∷ : ∀ n xs k →
-- -- -- -- --     (λ v → tabulate {A = A} (lookup v ∘ permuteF' n (k ∷ xs))) ≡
-- -- -- -- --      (λ x → tabulate (lookup (adjT×^'→ (fst k) x) ∘ permuteF' n xs)) 
-- -- -- -- --   h∷ n xs k = funExt
-- -- -- -- --        (λ v → 
-- -- -- -- --         cong′ (tabulate ∘' (_∘' (permuteF' n xs)))
-- -- -- -- --          (lawAdj' n k v))

-- -- -- -- --   w : ∀ n → Relim {n = n}
-- -- -- -- --      (λ z → singl {A = (A ×^ n) → (A ×^ n)}
-- -- -- -- --          (λ v → tabulate {A = A} {n = n}
-- -- -- -- --           (lookup {n = n} v ∘ permuteF' n z)))
-- -- -- -- --   isSetA (w n) _ = isOfHLevelPlus 2 (isContrSingl _)
-- -- -- -- --   εA (w n) = (idfun _) , (funExt (Iso.leftInv (Iso-×^-F→ n)))
-- -- -- -- --   fst (∷A (w n) k {xs} (X , XP)) = (X ∘ adjT×^'→ (fst k))
-- -- -- -- --   snd (∷A (w n) k {xs} (X , XP)) =  h∷ n xs k
-- -- -- -- --          ∙ cong′ (_∘ adjT×^'→ (fst k)) XP
-- -- -- -- --   invoA (w n) k {xs} (f , p') = 
-- -- -- -- --    ΣPathP
-- -- -- -- --     ((funExt (λ v →
-- -- -- -- --        cong f (isInvo-adjT×^'→ (fst k) v))) ,
-- -- -- -- --          (zzL ◁ (comm→PathP (
-- -- -- -- --            (cong (_∙ p')
-- -- -- -- --               {!!} ∙
-- -- -- -- --             sym (assoc _ _ p') ∙
-- -- -- -- --                cong′ (p'' ∙_)
-- -- -- -- --                  (((homotopyNatural 
-- -- -- -- --                   (λ a → cong (a ∘'_)
-- -- -- -- --                     (funExt λ a' → λ z → isInvo-adjT×^'→ (fst k) a' z) )
-- -- -- -- --                      p')))
-- -- -- -- --                  )
-- -- -- -- --                 ∙ assoc p'' _ _)) ))
-- -- -- -- --    where

-- -- -- -- --     p'' = (h∷ n (k ∷ xs) k)
-- -- -- -- --           ∙ cong′ (_∘ adjT×^'→ (fst k)) (h∷ n xs k) 

-- -- -- -- --     s'' : {!!}
-- -- -- -- --     s'' = {!!}

-- -- -- -- --     zzL : _
-- -- -- -- --     zzL = cong′ (h∷ n (k ∷ xs) k ∙_)
-- -- -- -- --       (cong-∙ (_∘ adjT×^'→ (fst k))
-- -- -- -- --         (h∷ n xs k) (cong′ (_∘ adjT×^'→ (fst k)) p'))
-- -- -- -- --       ∙ assoc _ _ _


-- -- -- -- --    --  ppL' : {!!}
-- -- -- -- --    --  ppL' = funExt λ v → PathP→comm
-- -- -- -- --    --     ( (  ( ( (lawAdj'-invo {A = A} n k)) v)))


-- -- -- -- --     --  -- -- ppL : ∀ v → _
-- -- -- -- --     --  -- -- ppL v = symP-fromGoal (PathP∙∙→compPathR (symP-fromGoal
-- -- -- -- --     --  -- --   ((lawAdj'-invo {A = A} n k v))))


-- -- -- -- --     --  -- zzP : {!!}
-- -- -- -- --     --  -- zzP = {!sym ppL'!}
-- -- -- -- --     --  --   ∙ {!!} 
-- -- -- -- --     --  --  -- ({!!}
-- -- -- -- --     --  --  --   ∙ cong₂ _∙_
-- -- -- -- --     --  --  --  (λ _ → (λ i x → p' (~ i) (adjT×^'→ (fst k) (adjT×^'→ (fst k) x))))
-- -- -- -- --     --  --  --  (cong funExt (funExt
-- -- -- -- --     --  --  --      (cong (sym ∘
-- -- -- -- --     --  --  --       cong (tabulate ∘' (_∘ permuteF' n xs))) ∘ ppL)))) ∙
-- -- -- -- --        -- sym (homotopyNatural 
-- -- -- -- --        --   (λ a → cong (a ∘'_)
-- -- -- -- --        --     (funExt λ a' → λ z → isInvo-adjT×^'→ (fst k) a' z) )
-- -- -- -- --        --      (sym p'))
      

-- -- -- -- --   braidA (w n) = {!!}
-- -- -- -- --   commA (w n) = {!!}



-- -- -- -- -- -- -- -- -- 𝕍lem : (A : Type ℓ) → ∀ n g
-- -- -- -- -- -- -- -- --    → PathP
-- -- -- -- -- -- -- -- --       (λ i →
-- -- -- -- -- -- -- -- --          ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) i ≡
-- -- -- -- -- -- -- -- --          ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) i)
-- -- -- -- -- -- -- -- --       (λ i → 𝔽h' A n (emloop g i))
-- -- -- -- -- -- -- -- --       (ua
-- -- -- -- -- -- -- -- --        ((λ x → tabulate (λ a → lookup x (Iso.fun (Iso.fun (ism n) g) a)))
-- -- -- -- -- -- -- -- --         ,
-- -- -- -- -- -- -- -- --         isoToIsEquiv
-- -- -- -- -- -- -- -- --         (compIso (Iso-×^-F→ n)
-- -- -- -- -- -- -- -- --          (compIso (invIso (domIso (Iso.fun (ism n) g)))
-- -- -- -- -- -- -- -- --           (invIso (Iso-×^-F→ n))))))
-- -- -- -- -- -- -- -- -- -- 𝕍lem A n = {!!}
-- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- --    z : ∀ n (g : Perm n) → (x : Fin n → A) →
-- -- -- -- -- -- -- -- -- --       {!!}
-- -- -- -- -- -- -- -- -- --    z zero g x = {!!}
-- -- -- -- -- -- -- -- -- --    z (suc n) g x = {!!}
-- -- -- -- -- -- -- -- -- --      -- cong₂ _,_ {!cong x ?!} {!!}

-- -- -- -- -- -- 𝔽-emloop : (A : Type ℓ) → ∀ n → (g : Perm n) →
-- -- -- -- -- --                cong (𝔽h' A n) (emloop g) ≡
-- -- -- -- -- --                  ua (
-- -- -- -- -- --                   preCompEquiv (substEquiv (𝔽in' n)
-- -- -- -- -- --                      (sym (emloop g)))) 
-- -- -- -- -- -- 𝔽-emloop A n g =
-- -- -- -- -- --  let zz = ((((funTypeTransp' (𝔽in' n) A (emloop g)))))
-- -- -- -- -- --      z =
-- -- -- -- -- --       isInjectiveTransport {p = cong (𝔽h' A n) (emloop g)}
-- -- -- -- -- --          {q = ua (
-- -- -- -- -- --            preCompEquiv ((substEquiv (𝔽in' n) (sym (emloop g)))))}
-- -- -- -- -- --          (funExt λ x → fromPathP (zz x) ∙
-- -- -- -- -- --            sym (uaβ
-- -- -- -- -- --              (preCompEquiv ((substEquiv (𝔽in' n) (sym (emloop g)))))
-- -- -- -- -- --              x))
           
-- -- -- -- -- --  in z


-- -- -- -- -- -- uaDomIso : ∀ {ℓ ℓ'} {A B : Type ℓ} (C : Type ℓ') → (e : Iso A B) →  
-- -- -- -- -- --      ua (isoToEquiv (domIso {C = C} e))
-- -- -- -- -- --        ≡ cong (λ X → X → C) (ua (isoToEquiv e))
-- -- -- -- -- -- uaDomIso C e =
-- -- -- -- -- --   invEq≡→equivFun≡ (invEquiv univalence)
-- -- -- -- -- --    (equivEq (funExt (λ x →
-- -- -- -- -- --      fromPathP (funTypeTransp' (idfun _) C ((ua (isoToEquiv e))) x)
-- -- -- -- -- --       ∙ funExt λ y → cong x (cong (Iso.inv e) (transportRefl y)))))


-- -- -- -- -- -- 𝔽-≡ : (A : Type ℓ) → ∀ n (g : Perm n) →
-- -- -- -- -- --       PathP (λ i → singl (𝔽h' A n (emloop g i)))
-- -- -- -- -- --       ((A ×^ n) , ua (isoToEquiv (invIso (Iso-×^-F→ n))))
-- -- -- -- -- --       ((A ×^ n) , ua (isoToEquiv (invIso (Iso-×^-F→ n))))
-- -- -- -- -- -- 𝔽-≡ A n g = 
-- -- -- -- -- --   let (e , p)  = permute→×^' {A = A} n g
      
-- -- -- -- -- --   in ΣPathP (ua (e , subst isEquiv p
-- -- -- -- -- --           (snd (isoToEquiv (Iso-×^-F→ n)
-- -- -- -- -- --              ∙ₑ preCompEquiv (isoToEquiv (invIso (permuteIso n g)))
-- -- -- -- -- --              ∙ₑ isoToEquiv (invIso (Iso-×^-F→ n))))) ,
-- -- -- -- -- --        flipSquare ( sym (uaDomIso A _) ◁
-- -- -- -- -- --          comm→PathP
-- -- -- -- -- --            (sym (uaCompEquiv _ _) ∙∙
-- -- -- -- -- --             cong ua (equivEq (cong (_∘ tabulate) (sym p)
-- -- -- -- -- --                ∙ funExt
-- -- -- -- -- --                 λ x →
-- -- -- -- -- --                  cong′ (tabulate ∘' (_∘' permuteF' n g))
-- -- -- -- -- --                   (Iso.rightInv (Iso-×^-F→ n) x  )))
-- -- -- -- -- --             ∙∙ uaCompEquiv _ _)))


    

-- -- -- -- -- -- 𝔽-sq-fst : (A : Type ℓ) → ∀ n → (g h : Perm n) → 
-- -- -- -- -- --   Square
-- -- -- -- -- --     (congP (λ _ → fst) (𝔽-≡ A n g))
-- -- -- -- -- --     (congP (λ _ → fst) (𝔽-≡ A n (g · h)))
-- -- -- -- -- --     refl
-- -- -- -- -- --     (congP (λ _ → fst) (𝔽-≡ A n h) )
-- -- -- -- -- -- 𝔽-sq-fst = {!!}

-- -- -- -- -- -- 𝕍 : (A : Type ℓ) → ∀ n em → singl (𝔽h' A n em)
-- -- -- -- -- -- 𝕍 A n = EMelim.f w
-- -- -- -- -- --  where
-- -- -- -- -- --   w : EMelim _
-- -- -- -- -- --                       (λ z → singl (𝔽h' A n z))
-- -- -- -- -- --   EMelim.isGrpB w _ = isOfHLevelPlus 3 (isContrSingl _)
-- -- -- -- -- --   EMelim.b w = (A ×^ n) , ua (isoToEquiv (invIso (Iso-×^-F→ n)))
-- -- -- -- -- --   EMelim.bPathP w = 𝔽-≡ A n
-- -- -- -- -- --   fst (EMelim.bSqP w g h i j) = 𝔽-sq-fst A n g h i j
-- -- -- -- -- --   snd (EMelim.bSqP w g h i j) k = {!!}

