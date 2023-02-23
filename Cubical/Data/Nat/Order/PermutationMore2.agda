{-# OPTIONS --safe #-}
module Cubical.Data.Nat.Order.PermutationMore2 where

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

open import Cubical.HITs.ListedFiniteSet.Base2

private
  variable
    ℓ : Level
    A : Type ℓ





-- EMΣ : ?

ℙrm : ℕ → Type
ℙrm n = EM₁ (Symmetric-Group (Fin n) (isSetFin {n}))

ℙrm' : ℕ → Type
ℙrm' n = EM₁ (PermG n)


-- h𝔽in : ∀ n → ℙrm n → hSet ℓ-zero
-- h𝔽in n = EMrec.f w
--  where
--   w : EMrec (Symmetric-Group (Fin n) (isSetFin {n})) isGroupoidHSet
--   EMrec.b w = Fin n , isSetFin {n}
--   EMrec.bloop w g = TypeOfHLevel≡ 2 (ua g)
--   EMrec.bComp w g h =
--      ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
--         λ i j →
--           Glue (ua {!ua !} i)
--             λ { (j = i0) → {!!}
--               ; (j = i1) → {!!}
--               }




-- 𝔽in : ∀ n → ℙrm n → Type ℓ-zero
-- 𝔽in  n = fst ∘ h𝔽in n


-- 𝔽h : (A : Type ℓ) → ∀ n → ℙrm n → Type ℓ
-- 𝔽h A n em = 𝔽in n em → A 





-- uaDom≃ : ∀ {ℓ ℓ'} {A B : Type ℓ} (C : Type ℓ') → (e : A ≃ B) →  
--      ua (preCompEquiv {C = C} (invEquiv e))
--        ≡ cong (λ X → X → C) (ua e)
-- uaDom≃ C e = {!!}
--   -- invEq≡→equivFun≡ (invEquiv univalence)
--   --  (equivEq (funExt (λ x →
--   --    fromPathP (funTypeTransp' (idfun _) C ((ua (isoToEquiv e))) x)
--   --     ∙ funExt λ y → cong x (cong (Iso.inv e) (transportRefl y)))))

-- 𝔽h* : (A : Type ℓ) → ∀ n → (p : ℙrm n) → singl (𝔽h A n p )
-- 𝔽h* A n = EMelim.f w
--  where
--  w : EMelim _ λ z → singl (𝔽h A n z)
--  EMelim.isGrpB w = {!!}
--  EMelim.b w = _ , refl
--  EMelim.bPathP w g = ΣPathP
--    ((ua (preCompEquiv {C = A} (invEquiv g))) ,
--      flipSquare (sym (uaDom≃ A g)))
--  EMelim.bSqP w = {!!}
 
-- 𝔽-≡ : (A : Type ℓ) → ∀ n (g : Fin n ≃ Fin n) →
--       PathP (λ i → singl (𝔽h A n (emloop g i)))
--       ((A ×^ n) , ua (isoToEquiv (invIso (Iso-×^-F→ n))))
--       ((A ×^ n) , ua (isoToEquiv (invIso (Iso-×^-F→ n))))
-- 𝔽-≡ A n g = ΣPathP
--     (ua ({!!} ∙ₑ preCompEquiv (invEquiv g) ∙ₑ {!Iso-×^-F→ n!})
--    , flipSquare (symP-fromGoal {!  uaDom≃ A g!}))
--  where
--  s : {!!}
--  s = (uaDomIso A {!!})

-- -- 𝕍 : (A : Type ℓ) → ∀ n em → singl (𝔽h A n em)
-- -- 𝕍 A n = EMelim.f w
-- --  where
-- --  w : EMelim _
-- --                      (λ z → singl (𝔽h A n z))
-- --  EMelim.isGrpB w _ = isOfHLevelPlus 3 (isContrSingl _)
-- --  EMelim.b w = (A ×^ n) , ua (isoToEquiv (invIso (Iso-×^-F→ n)))
-- --  EMelim.bPathP w = 𝔽-≡ A n
-- --  fst (EMelim.bSqP w g h i j) = 𝔽-sq-fst A n g h i j
-- --  snd (EMelim.bSqP w g h i j) k = {!!}

ism : ∀ n → Iso (Perm n) (Iso (Fin n) (Fin n))
ism n = (fst (PermGIsoIso n))


-- 𝔽in' : ∀ n → ℙrm' n → Type ℓ-zero
-- 𝔽in'  n = fst ∘ h𝔽in n ∘ gh→em₂→ _
--   (compGroupHom (_ , snd (PermGIsoIso n)) (_ , snd (SG-SI _ _)))



𝔽inSqSides : ∀ n → (g h : Perm n) → ∀ i j →
   Partial (j ∨ ~ j ∨ i ∨ ~ i)
           (Σ[ T ∈ Type ] T ≃ Fin n)
𝔽inSqSides n g h i j = 
          λ { (i = i0) → (ua (isoToEquiv (permuteIso n g))) j ,
                 permuteF n h
                  ∘ ua-ungluePathExt (isoToEquiv (permuteIso n g)) j
                ,
                isProp→PathP
                (λ j → isPropIsEquiv (permuteF n h
                  ∘ ua-ungluePathExt (isoToEquiv (permuteIso n g)) j))
                   ((isoToIsEquiv (compIso (permuteIso n g) (permuteIso n h))))
                   (unglueIsEquiv (Fin n) i1
                      (λ _ → Fin n , isoToEquiv (permuteIso n h))) j
           ; (i = i1) →
            (ua (isoToEquiv (permuteIso n (g · h)))) j ,
              ua-ungluePathExt (isoToEquiv (permuteIso n (g · h))) j ,
              isProp→PathP (λ j →
                  isPropIsEquiv (ua-ungluePathExt (isoToEquiv (permuteIso n (g · h))) j))
                  (isoToIsEquiv (permuteIso n (g · h)))
                  (unglueIsEquiv (Fin n) i1 (λ _ → Fin n , idEquiv (Fin n)))
                  j
           ; (j = i0) → Fin n , (cong isoToEquiv (permuteIso· n g h)) i
           ; (j = i1) → (ua (isoToEquiv (permuteIso n h))) i ,
                    unglueEquiv _ (i ∨ ~ i)
                      (λ { (i = i0) → (_ , (isoToEquiv (permuteIso n h)))
                          ; (i = i1) → (_ , idEquiv _) })
           }



h𝔽in' : ∀ n → ℙrm' n → hSet ℓ-zero
h𝔽in' n = EMrec.f w
 where
  w : EMrec _ isGroupoidHSet
  EMrec.b w = _ , isSetFin {n}
  EMrec.bloop w g = TypeOfHLevel≡ 2 (ua
    (isoToEquiv (permuteIso n g)))
  EMrec.bComp w g h =
    ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
      λ i j → Glue (Fin n) (𝔽inSqSides n g h i j)


𝔽in' : ∀ n → ℙrm' n → Type ℓ-zero
𝔽in' n = fst ∘ h𝔽in' n


h𝔽inSqUnglue : ∀ n → (g h : Perm n) →
    SquareP (λ i j → 𝔽in' n (emcomp g h i j) → (Fin n))
        (congP (λ _ → Iso.fun (permuteIso n h) ∘_)
          (ua-ungluePathExt _))
        (ua-ungluePathExt (isoToEquiv (permuteIso n ((snd (PermG n) GroupStr.· g) h))))
        (λ i → Iso.fun (permuteIso· n g h i))
        (ua-ungluePathExt _)
h𝔽inSqUnglue n g h i j = unglue _  {e = λ x → snd (𝔽inSqSides n g h i j x)}




-- 𝔽h : (A : Type ℓ) → ∀ n → ℙrm n → Type ℓ
-- 𝔽h A n em = 𝔽in n em → A 

𝔽h' : (A : Type ℓ) → ∀ n → ℙrm' n → Type ℓ
𝔽h' A n em = 𝔽in' n em → A 

-- -- -- Iso-𝔽h-×^ : ∀ n → Iso (𝔽h A n embase) (A ×^ n) 
-- -- -- Iso-𝔽h-×^ n = {!!}


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

adjT×^ : ∀ {n} → ℕ →
  Iso (A ×^ n)
      (A ×^ n)
adjT×^ {n} k =
 involIso {f = adjT×^'→ {n} k} (isInvo-adjT×^'→ {n} k)

comm-adjT×^'→ : ∀ {n} → ∀ k l → (k< : (suc k) < n) (l< : (suc l) < n) → 
  A.commT k l → ∀ v →  
  (adjT×^'→ {A = A} {n} l
    ∘ adjT×^'→ {A = A} {n} k ) v
  ≡ (adjT×^'→ {A = A} {n} k
    ∘ adjT×^'→ {A = A} {n} l ) v
comm-adjT×^'→ {n = suc (suc (suc (suc n)))} zero (suc (suc l)) k< l< x v = refl
comm-adjT×^'→ {n = suc (suc (suc (suc n)))} (suc k) (suc (suc l)) k< l< x (v , vs) =
   cong (v ,_) (comm-adjT×^'→
    {n = suc (suc (suc n))} k (suc l) k< l< x vs)


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


lawAdj'-braidDiag' : ∀ n k k< → (v : A ×^ n) → ∀ m m< →
  (lookup ((adjT×^'→ (suc k) ∘ adjT×^'→ k) v) ∘
       adjT n (k , <-weaken {n = n} k<))
      (m , m<)
      ≡
      (lookup ((adjT×^'→ k ∘ adjT×^'→ (suc k)) v) ∘ adjT n (suc k , k<))
      (m , m<)
lawAdj'-braidDiag' (suc (suc (suc n))) zero k< v =
  cases (λ _ → refl) (cases (λ _ → refl) (cases (λ _ → refl) λ _ _ → refl))  
lawAdj'-braidDiag' (suc (suc (suc (suc n)))) (suc k) k< v =
 cases (λ _ → refl) (lawAdj'-braidDiag' (suc (suc (suc n))) k k< (snd v))

lawAdj'-braidDiag : ∀ n k k< → (v : A ×^ n) → ∀ m m< →
  (lookup
       ((adjT×^'→ (suc k) ∘ adjT×^'→ k) (adjT×^'→ (suc k) (adjT×^'→ k v)))
       ∘ adjT n (k , <-weaken {n = n} k<))
      (m , m<)
      ≡
      (lookup
       ((adjT×^'→ k ∘ adjT×^'→ (suc k)) (adjT×^'→ (suc k) (adjT×^'→ k v)))
       ∘ adjT n (suc k , k<))
      (m , m<)
lawAdj'-braidDiag (suc (suc (suc n))) zero k< v =
  cases (λ _ → refl) (cases (λ _ → refl) (cases (λ _ → refl) λ _ _ → refl))  
lawAdj'-braidDiag (suc (suc (suc (suc n)))) (suc k) k< v =
 cases (λ _ → refl) (lawAdj'-braidDiag (suc (suc (suc n))) k k< (snd v))


lawAdj'-braidL' : ∀ n k k< → (v : A ×^ n) → ∀ m m<
  → 
    Square
      ((funExt⁻ (lawAdj' n (k , <-weaken {n = n} k<)
        ((adjT×^'→ (suc k) ∘ adjT×^'→ k) v)) (m , m<)))
      
      (funExt⁻ (lawAdj' n (suc k , k<) _) (m , m<))      
      (lawAdj'-braidDiag' n k k< v m m<)
      (λ i → lookup (braid-adjT×^'→ k k< v
       i) (m , m<))
lawAdj'-braidL' (suc (suc (suc n))) zero k< v =
  cases (λ _ → refl) (cases (λ _ → refl)
   (cases (λ _ → refl) λ _ _ → refl))
lawAdj'-braidL' (suc (suc (suc (suc n)))) (suc k) k< v =
  cases (λ _ → refl)
   (lawAdj'-braidL' (suc (suc (suc n))) k k< (snd v))

lawAdj'-braidR'-diag : ∀ n k (k< : suc (suc (suc k)) ≤ n)
 → (v : A ×^ n) → ∀ m m< m<' 
  → lookup (adjT×^'→ k v)
      ((A.sucFun (A.adjTransposition k) ∘ A.adjTransposition k) m , m<)
      ≡
      lookup (adjT×^'→ (suc k) v)
      (A.adjTransposition k (A.sucFun (A.adjTransposition k) m) , m<')
lawAdj'-braidR'-diag (suc (suc (suc n))) zero k< v =
  cases (λ _ _ → refl)
   (cases (λ _ _ → refl)
     (cases (λ _ _ → refl) λ m m< m<' i →
      lookup (snd (snd (snd v))) (m , isProp≤ {suc m} {n} m< m<' i)))

lawAdj'-braidR'-diag (suc (suc (suc n))) (suc k) k< v =
  cases (λ _ _ → refl)
   (lawAdj'-braidR'-diag (suc (suc (n))) (k) k< (snd v))

lawAdj'-braidR' : ∀ n k k< → (v : A ×^ n) → ∀ m m< m<'
  → 
    Square
      ((funExt⁻ (lawAdj' n (k , <-weaken {n = n} k<)
        _) (_ , m<)))
      
      (funExt⁻ (lawAdj' n (suc k , k<) _)
       (_ , m<'))
       (λ i → lookup {A = A} v
         (≡Fin {n = n} {_ , adjT< n k
             ((A.sucFun (A.adjTransposition k) ∘ A.adjTransposition k) m)
             (<-weaken {n = n} k<) m<}
             {_ , adjT< n (suc k)
          (A.adjTransposition k (A.sucFun (A.adjTransposition k) m)) k< m<'}
           (λ i → A.adjTranspositionBraid k i m) i))
      (lawAdj'-braidR'-diag n k k< v m m< m<')


-- lookup v (permuteF' n (braid k k< xs z) (k' , k'<))

lawAdj'-braidR' (suc (suc (suc n))) zero k< v =
  cases (λ _ _ → refl)
   (cases (λ _ _ → refl)
     (cases (λ _ _ → refl)
       λ m m< m<' →
         congP (λ _ → cong (lookup (snd (snd (snd v)))))
           (isSet→isSet' (isSetFin {n = n}) _ _ _ _)))


lawAdj'-braidR' (suc (suc (suc (suc n)))) (suc k) k< v =
  cases (λ _ _ → refl)
   (lawAdj'-braidR' (suc (suc (suc n))) (k) k< (snd v))

lawAdj'-braidL : ∀ n k k< → (v : A ×^ n) → ∀ m m<
  → 
    Square
      ((funExt⁻ (lawAdj' n (k , <-weaken {n = n} k<) _) (m , m<)))
      (funExt⁻ (lawAdj' n (suc k , k<) _) (m , m<))      
      (lawAdj'-braidDiag n k k< v m m<)
      (λ i → lookup (braid-adjT×^'→ k k< (adjT×^'→ (suc k) (adjT×^'→ k v))
       i) (m , m<))
lawAdj'-braidL (suc (suc (suc n))) zero k< v =
  cases (λ _ → refl) (cases (λ _ → refl)
   (cases (λ _ → refl) λ _ _ → refl))
lawAdj'-braidL (suc (suc (suc (suc n)))) (suc k) k< v =
  cases (λ _ → refl)
   (lawAdj'-braidL (suc (suc (suc n))) k k< (snd v))


lawAdj'-braidCenter : ∀ n k k< → (v : A ×^ n) → ∀ m m< m<' m<''
  → 
    Square
      (funExt⁻ (lawAdj' {A = A} n (suc k , m<'') _) _)
      (funExt⁻ (lawAdj' {A = A} n (k , m<') _) _)
      (lawAdj'-braidR'-diag n k k< v m _ _)
      (lawAdj'-braidDiag' n k k< v m m<)
lawAdj'-braidCenter (suc (suc (suc n))) zero k< v =
  cases (λ _  _ _ → refl) (cases (λ _  _ _ → refl)
   (cases (λ _ _ _ → refl) λ _ _ _ _ →
        congP (λ _ → cong (lookup (snd (snd (snd v)))))
           (isSet→isSet' (isSetFin {n = n}) _ _ _ _)))

lawAdj'-braidCenter (suc (suc (suc (suc n)))) (suc k) k< v =
  cases (λ _ _ _ → refl)
   (lawAdj'-braidCenter (suc (suc (suc n))) k k< (snd v))

lawAdj'-comm-Diag : ∀ n k l k< l< (z : A.commT k l) → (v : A ×^ n) → ∀ m m<
  → (lookup (adjT×^'→ k v) ∘ adjT n (l , l<)) (m , m<) ≡
      (lookup (adjT×^'→ l v) ∘ adjT n (k , k<)) (m , m<)
lawAdj'-comm-Diag (suc (suc (suc (suc n)))) zero (suc (suc l)) k< l< z v =
      cases (λ _ → refl)
     (cases (λ _ → refl)
       λ m m<
        → funExt⁻ (lawAdj' (suc (suc n)) (l , l<) (snd (snd v))) (m , m<) )

lawAdj'-comm-Diag (suc (suc (suc (suc n)))) (suc k) (suc (suc (suc l))) k< l< z v = cases (λ _ → refl)
  (lawAdj'-comm-Diag (suc (suc (suc n))) k (suc (suc l)) k< l< z (snd v))

lawAdj'-commR' : ∀ n k l k< l< z → (v : A ×^ n) → ∀ m m<
  
  → 
    Square 
      ((funExt⁻ (lawAdj' n (l , l<) _) (m , m<)))
      (funExt⁻ (lawAdj' n (k , k<) _) (m , m<))      
      (lawAdj'-comm-Diag n k l k< l< z v m m<)
      λ i → lookup (comm-adjT×^'→ k l k< l< z v i)
        (m , m<)
lawAdj'-commR' (suc (suc (suc (suc n)))) zero (suc (suc l)) k< l< z v =
  cases
    (λ _ → refl)
    (cases (λ _ → refl)
      λ m m< i j →
        lawAdj' (suc (suc n)) (l , l<) (snd (snd v)) (i ∨ j) (m , m<))
lawAdj'-commR' (suc (suc (suc (suc (suc n))))) (suc k) (suc (suc (suc l))) k< l< z v = cases (λ _ → refl)
       (lawAdj'-commR' (suc (suc (suc (suc n)))) k (suc (suc l)) k< l< z (snd v))

lawAdj'-commL' : ∀ n k l k< l< z → (v : A ×^ n) → ∀ m m< 
  → 
    Square 
      (funExt⁻ (lawAdj' n (k , k<) _) _)
      (funExt⁻ (lawAdj' n (l , l<) _) _)
      (cong′ (lookup v) (
            ≡Fin {n = n} --{k = _ , m<'} {_ , m<''}
             (sym (funExt⁻ (A.adjTranspositionComm k l z) m))))
      (lawAdj'-comm-Diag n k l k< l< z v m m<)
lawAdj'-commL' (suc (suc (suc (suc n)))) zero (suc (suc l)) k< l< z v =
  cases (λ _ → refl)
   (cases (λ _ → refl)
     λ m m< →  flipSquare (
     congP (λ _ → cong′ (lookup (snd (snd v))))
           (isSet→isSet' (isSetFin {n = (suc (suc n))})
             (cong (A.adjTransposition l m ,_) _)
             (cong (A.adjTransposition l m ,_) _)
             (cong (A.adjTransposition l m ,_) _)
             (cong (A.adjTransposition l m ,_) _)) ◁
       λ i j →
        (lawAdj' (suc (suc n)) (l , l<) (snd (snd v)) (i ∧ j) (m , m<))))
lawAdj'-commL' (suc (suc (suc (suc (suc n))))) (suc k) (suc (suc (suc l))) k< l< z v = cases (λ _ → refl)
  (lawAdj'-commL' (suc (suc (suc (suc n)))) k (suc (suc l)) k< l< z (snd v))

-- permute→×^ : ∀ n → (p : Perm n) → 
--     singl {A = (A ×^ n) → (A ×^ n)}
--       (λ v → tabulate (lookup v ∘ permuteF n p))
-- permute→×^ {A = A} n = Relim.f (w n)
--   where

--    open Relim

   
--    w : ∀ n → Relim {n = n}
--       (λ z → singl {A = (A ×^ n) → (A ×^ n)}
--           (λ v → tabulate {A = A} {n = n}
--            (lookup {n = n} v ∘ permuteF n z)))
--    isSetA (w n) _ = isOfHLevelPlus 2 (isContrSingl _)
--    εA (w n) = (idfun _) , (funExt (Iso.leftInv (Iso-×^-F→ n)))
--    fst (∷A (w n) k {xs} (X , XP)) = (adjT×^'→ (fst k) ∘ X)
--    snd (∷A (w n) k {xs} (X , XP)) =      
--       funExt
--         (λ v →
--          lawAdj n k (lookup v ∘ permuteF n xs))
--           ∙ cong′ (adjT×^'→ (fst k) ∘_) XP
        
--    invoA (w n) k {xs} (f , p') =
--      -- TODO ; simplify
--      ΣPathP
--      (funExt (λ v → isInvo-adjT×^'→ (fst k) (f v)) ,
--       ((cong′ (
--          (funExt
--         (λ v →
--          lawAdj n k _)) ∙_)
--           (cong-∙ (adjT×^'→ (fst k) ∘_) _ _) ∙
--            assoc _ _ _)
--             ◁ comm→PathP (pp ∙ assoc _ _ _)))
--      where

--       ppL : (v : A ×^ n) →
--          _
--       ppL v = PathP∙∙→compPathR
--         (flipSquare (lawAdj-invo {A = A} n k (lookup v ∘
--             permuteF n xs)))

--       pp1 = _
--       pp : _
--       pp = cong′ (_∙ p') (cong funExt (funExt (ppL))
--         ∙ doubleCompPath-elim
--            (funExt ((λ x i →
--             lawAdj n k ((λ x₁ → lookup x (permuteF n xs x₁))
--               ∘ adjT n k) i))) _ _)
--         ∙ sym (assoc pp1 _ _)
--         ∙ cong′ (pp1 ∙_)
--           (homotopyNatural
--                (λ a → cong (_∘' a) (funExt (isInvo-adjT×^'→ (fst k))))
--                 p') 
     
--    braidA (w n) = {!!}
--    commA (w n) = {!!}


singl≡ExtIso : ∀ n → (p : Perm n) →
  (f : (A ×^ n) → (A ×^ n)) →
   (∀ v k k< →
        (lookup v ((permuteF' n p) (k , k<)))
           ≡ lookup (f v) (k , k<)) ≃ ( tabulate ∘'
      (_∘ (permuteF' n p) )
      ∘' lookup  ≡ f)
singl≡ExtIso {ℓ} {A = A} n p f =
  (pathToEquiv
    ( cong′ {A = (A ×^ n) → Type ℓ} (λ X → ∀ x → X x)
    
        (funExt (λ x →
          (λ i →
            ((k : ℕ) (k< : suc k ≤ n) →
        (Iso.rightInv (Iso-×^-F→ n)) (lookup x ∘ permuteF' n p) (~ i)
       ((k , k<))
       ≡ lookup (f x) (k , k<)))
          ∙ (funExt₂Path) ∙
          ua (invEquiv (congEquiv
            (isoToEquiv (compIso (Iso-×^-F→ n) curryIso)))) 
          )))) ∙ₑ funExtEquiv 

permute→×^' : ∀ n → (p : Perm n) → 
    Σ ((A ×^ n) → (A ×^ n))
     λ f → ∀ v k k< →
        (lookup v ((permuteF' n p) (k , k<)))
           ≡ lookup (f v) (k , k<)
permute→×^' {A = A} n = Relim.f (w n)
 where
  open Relim


  h∷ : ∀ n xs k → 
     ∀ v  k' k'< →
       ((lookup {n = n} v ∘ permuteF' n (k ∷ xs)) ( k' , k'<)) ≡
       ((lookup (adjT×^'→ (fst k) v) ∘ permuteF' n xs) ( k' , k'<)) 
  h∷ n xs k v k' k'< i = 
    (lawAdj' {A = A} n k v i) (permuteF' n xs (k' , k'<))

  w : ∀ n → Relim {n = n} λ p → Σ ((A ×^ n) → (A ×^ n))
     λ f → ∀ v k k< →
        (lookup v ((permuteF' n p) (k , k<)))
           ≡ lookup (f v) (k , k<)
  isSetA (w n) p =
     isOfHLevelRetractFromIso
         2
         (Σ-cong-iso-snd (equivToIso ∘ singl≡ExtIso n p))
              (isOfHLevelPlus 2 (isContrSingl
         ( tabulate {A = A} {n = n} ∘ ((_∘ permuteF' n p ))
           ∘ lookup {A = A} {n = n})))
  εA (w n) = (idfun _) , λ _ _ _ → refl
  fst (∷A (w n) k {xs} (X , _)) = X ∘ adjT×^'→ (fst k)
  snd (∷A (w n) k {xs} (X , XP)) v k' k< =
    h∷ n xs k v k' k< ∙ XP (adjT×^'→ (fst k) v) k' k<
  invoA (w n) k {xs} (X , XP) = 
    ΣPathP
    ((funExt
     (λ v → cong X (isInvo-adjT×^'→ (fst k) v))) ,
      funExt λ v → funExt λ m → funExt λ m< → 
        sym (doubleCompPath-elim' _ _ _) ◁
         λ i j →
           hcomp
            (λ l →
              λ { (j = i0) →
                    lawAdj'-invo n k v i (~ l) (permuteF' n xs (m , m<))
                   
                 ; (j = i1) → XP (isInvo-adjT×^'→ (fst k) v i ) m m< l
                 ; (i = i1) → invSides-filler
                   (λ i →
                     (lookup (isInvo-adjT×^'→ (fst k) v (~ i))
               (permuteF' n xs (m , m<))))
                 (XP v m m<) (j) (~ l) 
                 })
           (invSides-filler
             (λ i → lookup (isInvo-adjT×^'→ (fst k) v i)
               (permuteF' n xs (m , m<)))
                (sym (h∷ n xs k (adjT×^'→ (fst k) v) m m<)) (~ i) j)) 
  braidA (w n) k k< {xs} (X , XP) =
    ΣPathP (funExt (λ v → cong X (braid-adjT×^'→ k k< v))  ,
     funExt₃ λ v k' k'< → 
       λ i →
          (lawAdj'-braidR' n k k< v _ _
             (adjT< n k _ (<-weaken {suc (suc k)} {n} k<)
                  (adjT< n (suc k) _
                    k<
                  (snd (permuteF' n xs (k' , k'<))))) i
             ∙ (lawAdj'-braidCenter n _ _ _ _ _ _ _ i)
             ∙ ( lawAdj'-braidL' n k k< v _ _ i )
            ∙ XP (braid-adjT×^'→ k k< v i) k' k'<))
  commA (w n) k l z {xs} (X , XP) =
    ΣPathP (funExt (cong X ∘ (comm-adjT×^'→ (fst k) (fst l) (snd k) (snd l) z))
     , λ i v k' k'< →
       (lawAdj'-commL' n (fst k) (fst l) (snd k) (snd l) z v _ _ i
       ∙ lawAdj'-commR' n (fst k) (fst l) (snd k) (snd l) z v _ _ i ∙
         XP (comm-adjT×^'→ (fst k) (fst l) (snd k) (snd l) z v i) k' k'<))




permute→×^'-≡ : ∀ n g → fst (permute→×^' {A = A} n g) ≡
    tabulate ∘ (( _∘ permuteF' n g)) ∘ lookup 
permute→×^'-≡ {A = A} n g =
     sym ((fst ((singl≡ExtIso n g) _)) (snd (permute→×^' {A = A} n g)))    

-- isEquiv-permute→×^' : ∀ n g → isEquiv (fst (permute→×^' {A = A} n g))
-- isEquiv-permute→×^' {A = A} n g =
--  let p = funExt λ x → 
--        let zz = funExt (uncurry ((snd (permute→×^' {A = A} n g)) x))
--        in isoFunInjective (Iso-×^-F→ n) _ _
--          ( Iso.rightInv (Iso-×^-F→ n) _ ∙  zz)

--  in subst isEquiv p
--           (snd (isoToEquiv (Iso-×^-F→ n)
--              ∙ₑ preCompEquiv (isoToEquiv (invIso (permuteIso n g)))
--              ∙ₑ isoToEquiv (invIso (Iso-×^-F→ n))))
-- -- 

isEquiv-permute→×^' : ∀ n g → isEquiv (fst (permute→×^' {A = A} n g))
isEquiv-permute→×^' {A = A} n = RelimProp.f (w n)
 where
 open Relim

 w : ∀ n → RelimProp {n = n} λ g → isEquiv (fst (permute→×^' {A = A} n g))
 RelimProp.isPropA (w n) _ = isPropIsEquiv _
 RelimProp.εA (w n) = idIsEquiv _
 RelimProp.∷A (w n) k x = snd (compEquiv (isoToEquiv (adjT×^ (fst k))) (_ , x))
 

-- module _ (isGroupoidA : isGroupoid A) where

--  𝔽-≡-lem : ∀ n (g : Perm n) →
--           PathP (λ j → ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j →
--                           ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j)
--                   (idfun _)
--                   (fst (permute→×^' n g))
--  𝔽-≡-lem n = Relim.f (w n)
--   where
--   open Relim

--   zz : ∀ j → ∀ n → ℕ → (ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j →
--                          ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j)
--                → (ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j →
--                          ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j)
--   zz j n k f =
--       (ua-gluePathExt (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j
--           ∘ Iso.fun (Iso-×^-F→ {A = A} n) ∘ adjT×^'→ k)
--      ∘ ua-ungluePathExt (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j

--   w : ∀ n → Relim {n = n} λ g →
--          PathP (λ j → ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j →
--                           ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j)
--                   (idfun _)
--                   (fst (permute→×^' n g))
--   isSetA (w n) = {!!}
--   εA (w n) j x = x
--   ∷A (w (suc (suc n))) (zero , k<) x j =
--     {!zz j (suc (suc n)) zero !}
--   ∷A (w (suc (suc n))) (suc k , k<) x = {!!}
--   invoA (w n) = {!!}
--   braidA (w n) = {!!}
--   commA (w n) = {!!}

--  --   {!!}
--  -- where
--  --  zz : PathP (λ j → ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j →
--  --                         ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j)
--  --                    {!!}
--  --                    {!!}
--  --  zz j = 
--  --         (ua-gluePathExt (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j
--  --          ∘ {!Iso.fgu(invIso (Iso-×^-F→ {A = A} n))!})
--  --     ∘ ua-ungluePathExt (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j

unglue-∷ : (A : Type ℓ) → ∀ n (g : Perm n) k →
  PathP
    (λ i → 𝔽in' n (emloop g i) → 𝔽in' n (emloop (k ∷ g) i))
    {!!}
    {!!}
    -- (adjT n k)
    -- (idfun _)
unglue-∷ A n = Relim.f {n = n} (w n)
 where
 open Relim

 w : ∀ n → Relim (λ (g : Perm n) → ∀ k
             → PathP
               (λ i → 𝔽in' n (emloop g i) → 𝔽in' n (emloop (k ∷ g) i))
               (adjT n k)
               (idfun _))
 w n = {!!}

  -- ua-gluePathExt ((isoToEquiv (permuteIso n (k ∷ g)))) i ∘
  --   ua-ungluePathExt (isoToEquiv (permuteIso n g)) i

𝔽-≡-lem : (A : Type ℓ) → ∀ n (g : Perm n) →
    PathP (λ i → (𝔽in' n (emloop g i) → A) → A ×^ n)
           (fst (permute→×^' {A = A} n g) ∘ tabulate)
           tabulate
𝔽-≡-lem A n = Relim.f {n = n} (w n)
 where
 open Relim

 w : ∀ n → Relim
      (λ z →
         PathP (λ i → (𝔽in' n (emloop z i) → A) → A ×^ n)
         (fst (permute→×^' n z) ∘ tabulate) tabulate)
 isSetA (w n) = {!!}
 εA (w n) i x = tabulate (x ∘ ua-gluePathExt (isoToEquiv (permuteIso n ε)) i)
 ∷A (w (suc (suc n))) (zero , k<) {xs} X = 
  let z = {!!}
  in {!!}
 ∷A (w (suc (suc (suc n)))) (suc k , k<) {xs} X = {!!}

-- {!adjT×^'→ (fst k) !}
 invoA (w n) = {!!}
 braidA (w n) = {!!}
 commA (w n) = {!!}
 
 -- isSetA w = {!!}
 -- εA w i = {!(ua-ungluePathExt (isoToEquiv (permuteIso n ε))) i!}
 -- ∷A w = {!!}
 -- invoA w = {!!}
 -- braidA w = {!!}
 -- commA w = {!!}


-- 𝔽-≡ : (A : Type ℓ) → ∀ n (g : Perm n) →
--       PathP (λ i → singl (𝔽h' A n (emloop g i)))
--       ((A ×^ n) , ua (isoToEquiv (invIso (Iso-×^-F→ n))))
--       ((A ×^ n) , ua (isoToEquiv (invIso (Iso-×^-F→ n))))
-- 𝔽-≡ A n g =
--   let (e , p')  = permute→×^' {A = A} n g
--       p = funExt λ x → 
--        let zz = funExt (uncurry (p' x))
--        in isoFunInjective (Iso-×^-F→ n) _ _
--          ( Iso.rightInv (Iso-×^-F→ n) _ ∙  zz)

--       g≃ : {!!}
--       g≃ = (_ , isEquiv-permute→×^' n g)

--       -- g⁻≃ : {!!}
--       -- g⁻≃ = (_ , isEquiv-permute→×^' {A = A} n (inv g))

--       pp : PathP (λ i → (𝔽in' n (emloop g i) → A) → A ×^ n)
--                  (fst (permute→×^' {A = A} n g) ∘ tabulate)
--                  tabulate
--       pp = cong (_∘ (tabulate)) (permute→×^'-≡ n g)
--                ◁ (λ i →    
           
--              λ a → tabulate
--                  (  (Iso.rightInv (Iso-×^-F→ {A = A} n))
--                     ((a ∘ ((ua-gluePathExt ((isoToEquiv (permuteIso n g)) ) i)))) i
--                         ∘ permuteF' n g  ))
--                   ▷ ( cong′ (tabulate ∘'_)
--                        (funExt  λ k → 
--                           cong (k ∘_) (funExt (Iso.rightInv (permuteIso n g)))  )  )

--   in ΣPathP (ua g≃  ,

--        λ i j →
--         Glue
--           (A ×^ n) {~ i ∨ i ∨ ~ j ∨ j}
--           λ {(i = i0) → ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j ,
--                        fst g≃  ∘
--                         (ua-ungluePathExt (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))))
--                           j
--                        --   fst (permute→×^' {A = A} n g) ∘
--                        --  ua-ungluePathExt
--                        --   (isoToEquiv (invIso (Iso-×^-F→ {A = A} n)))
--                        --   j
--                          --  ua-ungluePathExt
--                          -- (isoToEquiv (invIso (Iso-×^-F→ {A = A} n)))
--                          -- j ∘
--                          --   {!!}
--                        -- ua-ungluePathExt
--                        --   (isoToEquiv (invIso (Iso-×^-F→ {A = A} n)))
--                        --   j ∘ ?
--                          ,
--                        {!!}
--             ;(i = i1) → ua ((isoToEquiv (invIso (Iso-×^-F→ {A = A} n)))) j ,
--                           -- {!!}
--                          (ua-ungluePathExt (isoToEquiv (invIso (Iso-×^-F→ {A = A} n)))
--                              j ) 
--                          --   ∘ fst (permute→×^' {A = A} n (inv g)) ∘ ua-ungluePathExt
                         
--                          -- (isoToEquiv (invIso (Iso-×^-F→ {A = A} n)))
--                          -- j
                         
--                          ,
--                        {!!}
--             ;(j = i0) → (𝔽in' n (emloop g i) → A) ,
--                         pp i ,
--                        -- pp i ,
--                        {!!}
--             ;(j = i1) → ua g≃ i ,
--                        ua-ungluePathExt g≃ i
--                       -- ua-gluePathExt g⁻≃ i
--                       --  -- ∘ fst (permute→×^' {A = A} n (inv g))
--                       --  ∘ ua-ungluePathExt g≃ i
--                        ,
--                       {!!}
--              }

-- -------------

--        -- λ i j →
--        --  Glue
--        --    (ua (isoToEquiv (invIso (Iso-×^-F→ {A = A} n))) j) {i ∨ ~ i ∨ ~ j ∨ j}
--        --    λ {(i = i0) → ua (isoToEquiv (invIso (Iso-×^-F→ n))) j ,
--        --          idEquiv _
--        --      ;(i = i1) → ua (isoToEquiv (invIso (Iso-×^-F→ n))) j
--        --          , {! !}
--        --          , {!!}
--        --      ;(j = i0) → (𝔽in' n (emloop g i) → A) ,
--        --          (_∘ ua-gluePathExt (isoToEquiv (permuteIso n g)) i) 
--        --             ,
--        --         {!!}
--        --      ;(j = i1) → {!!} ,
--        --            {!!} 
--        --             ,
--        --         {!!}
--        --       }


-- ------------

--        -- λ i j →
--        --  Glue
--        --    (A ×^ n) {i ∨ ~ i ∨ ~ j}
--        --    λ {(i = i0) → ua (isoToEquiv (invIso (Iso-×^-F→ n))) j ,
                
--        --          fst (permute→×^' n g)
--        --           ∘ ua-ungluePathExt (isoToEquiv (invIso (Iso-×^-F→ n))) j
--        --         , {!!}
--        --      ;(i = i1) → ua (isoToEquiv (invIso (Iso-×^-F→ n))) j ,
--        --         ua-ungluePathExt (isoToEquiv (invIso (Iso-×^-F→ n))) j
--        --          , {!!}
--        --      ;(j = i0) → (𝔽in' n (emloop g i) → A) ,
--        --          {!!}
--        --          -- {!(Iso.fun (invIso (Iso-×^-F→ n)))!} ∘ (_∘ ua-gluePathExt (isoToEquiv (permuteIso n g)) i)
--        --             ,
--        --         {!!}
--        --       }
--        )





-- -- -- 𝔽-sq-fst : (A : Type ℓ) → (isGroupoid A) → ∀ n → (g h : Perm n) → 
-- -- --   Square
-- -- --     (congP (λ _ → fst) (𝔽-≡ A n g))
-- -- --     (congP (λ _ → fst) (𝔽-≡ A n (g · h)))
-- -- --     refl
-- -- --     (congP (λ _ → fst) (𝔽-≡ A n h) )
-- -- -- 𝔽-sq-fst {ℓ} A isGrpA n = Relim.f (w n)
-- -- --  where
-- -- --   open Relim

-- -- --   w∷ : ∀ n → I → (k : Σ ℕ (λ k₁ → suc k₁ < n)) {xs : Perm n} →
-- -- --       ((h : Perm n) →
-- -- --        Square (congP (λ _ → fst) (𝔽-≡ A n xs))
-- -- --        (congP (λ _ → fst) (𝔽-≡ A n (xs · h))) refl
-- -- --        (congP (λ _ → fst) (𝔽-≡ A n h))) →
-- -- --       (h : Perm n) → I → I → Type ℓ
-- -- --       -- Square (congP (λ _ → fst) (𝔽-≡ A n (k ∷ xs)))
-- -- --       -- (congP (λ _ → fst) (𝔽-≡ A n (k ∷ (xs · h)))) refl
-- -- --       -- (congP (λ _ → fst) (𝔽-≡ A n h))
-- -- --   w∷ n l k {xs} X h =
-- -- --     λ i j →
-- -- --           hfill
-- -- --            (λ l → λ {
-- -- --             (i = i0) → ua-CompFill'∙ₑ
-- -- --               ((isoToEquiv (adjT×^ {A = A} {n = n} (fst k))))
-- -- --               (_ , isEquiv-permute→×^' n (xs)) l j 
-- -- --            ;(i = i1) →
-- -- --                 ua-CompFill'∙ₑ
-- -- --               ((isoToEquiv (adjT×^ {A = A} {n = n} (fst k))))
-- -- --               (_ , isEquiv-permute→×^' n (xs · h)) l j
-- -- --            ;(j = i0) → 
-- -- --              (ua (isoToEquiv (adjT×^ {A = A} {n = n} (fst k))) (~ l)) --A ×^ n
-- -- --            ;(j = i1) → fst (𝔽-≡ A n h i)   --z i l
-- -- --              })
-- -- --               (inS (X h i j))
-- -- --               l
 
-- -- --   w : ∀ n → Relim {n = n}
-- -- --         λ g → (h : Perm n) → 
-- -- --             Square
-- -- --               (congP (λ _ → fst) (𝔽-≡ A n g))
-- -- --               (congP (λ _ → fst) (𝔽-≡ A n (g · h)))
-- -- --               (refl {x = A ×^ n})
-- -- --               (congP (λ _ → fst) (𝔽-≡ A n h))
-- -- --   isSetA (w n) x =
-- -- --     isSetΠ λ _ → isOfHLevelRetractFromIso 2
-- -- --       (invIso PathP→comm-Iso)
-- -- --       (isOfHLevel≡ 3
-- -- --         (isOfHLevel×^ n 3 isGrpA)
-- -- --         (isOfHLevel×^ n 3 isGrpA)
-- -- --         _ _)
    
-- -- --   εA (w n) h = ua-CompFill _ _ _
-- -- --   ∷A (w n) k {xs} X h i j = w∷ n i1 k {xs} X h i j
-- -- --   invoA (w n) k {xs} X l h i j = 
-- -- --     hcomp
-- -- --      (λ m →
-- -- --        λ {  (l = i1) → w∷ n (~ m) k {xs} X h i j
-- -- --            ;(i = i0) → i0Cu l (~ m) j 
-- -- --            ;(i = i1) →
-- -- --               let ff : ∀ l m →
-- -- --                        involPathSym {f = (adjT×^'→ {A = A} {n} (fst k))}
-- -- --                          (isInvo-adjT×^'→ (fst k)) l (~ m) → A ×^ n
-- -- --                   ff = λ l m → (fst (permute→×^' n (xs · h)) ∘
-- -- --                        (λ x →
-- -- --                          ua-unglue ((involEquiv
-- -- --                         {f = (adjT×^'→ {A = A} {n} (fst k))}
-- -- --                           (isInvo-adjT×^'→ (fst k)))) l
-- -- --                            (unglue (m ∨ ~ m) x))) 
-- -- --               in Glue (A ×^ n)
-- -- --                   (λ { (j = i0) →
-- -- --                      (involPathSym {f = (adjT×^'→ {A = A} {n} (fst k))}
-- -- --                     (isInvo-adjT×^'→ {n = n} (fst k)) l) (~ m) ,
-- -- --                      ff l m ,
-- -- --                      isProp→SquareP (λ l m →
-- -- --                          isPropIsEquiv (ff l m))
-- -- --                        refl
-- -- --                        (isProp→PathP
-- -- --                           (λ l → isPropIsEquiv (ff l i1))
-- -- --                             _ _)
-- -- --                        (isProp→PathP
-- -- --                           (λ m → isPropIsEquiv (ff i0 m))
-- -- --                             (isEquiv-permute→×^' n (k ∷ (xs · h)))
-- -- --                             (isEquiv-permute→×^' n (k ∷ k ∷ (xs · h))))
-- -- --                        (symP (isProp→PathP
-- -- --                          ((λ m → isPropIsEquiv (ff i1 (~ m))))
-- -- --                            (isEquiv-permute→×^' n (xs · h))
-- -- --                             (isEquiv-permute→×^' n (k ∷ (xs · h)))))
-- -- --                        l m
-- -- --                      ; (j = i1) → (_ , idEquiv _)
-- -- --                  })
-- -- --            ;(j = i0) →
-- -- --              involPathSym {f = (adjT×^'→ {A = A} {n} (fst k))}
-- -- --                (isInvo-adjT×^'→ {n = n} (fst k)) l (~ m)
               
-- -- --            ;(j = i1) → fst (𝔽-≡ A n h i)
-- -- --            ;(l = i0) →
-- -- --               (w∷ n (m) k {k ∷ xs}
-- -- --           (λ h i j → w∷ n i1 k {xs} X h i j) h i j)
             
-- -- --           })
-- -- --           (w∷ n i1 k {xs} X h i j)
       

-- -- --     where

-- -- --       i0CuP : SquareP
-- -- --            (λ l m → involPathSym {f = (adjT×^'→ {A = A} {n} (fst k))}
-- -- --              (isInvo-adjT×^'→ {A = A} {n = n} (fst k)) l m → (A ×^ n))
-- -- --             (λ m → fst (permute→×^' n (k ∷ xs)) ∘
-- -- --                ua-ungluePathExt
-- -- --                  ((isoToEquiv (adjT×^ {A = A} {n = n} (fst k)))) m)
-- -- --             (λ m → fst (permute→×^' n (xs)) ∘
-- -- --                ua-ungluePathExt
-- -- --                  ((isoToEquiv (adjT×^ {A = A} {n = n} (fst k)))) (~ m))
-- -- --             (cong (fst (permute→×^' n xs) ∘_)
-- -- --                (funExt (isInvo-adjT×^'→ {n = n} (fst k))))
-- -- --             (refl {x = fst (permute→×^' n (k ∷ xs)) ∘
-- -- --                          ua-ungluePathExt (isoToEquiv (adjT×^ (fst k))) i1})
-- -- --       i0CuP l m x =
-- -- --         let x' = unglue (m ∨ ~ m) x
-- -- --             x'' =  ua-unglue ((involEquiv
-- -- --                    {f = (adjT×^'→ {A = A} {n} (fst k))}
-- -- --                      (isInvo-adjT×^'→ (fst k)))) l x'
-- -- --         in fst (permute→×^' n (xs)) x''

-- -- --       i0Cu : PathP (λ l → Square
-- -- --                     ((congP (λ _ → fst) (𝔽-≡ A n (invo k xs l))))
-- -- --                     ((congP (λ _ → fst) (𝔽-≡ A n (k ∷ xs))))
                    
-- -- --                     (involPathSym {f = (adjT×^'→ {A = A} {n} (fst k))}
-- -- --                (isInvo-adjT×^'→ {n = n} (fst k)) l)
-- -- --                     refl)
-- -- --           (symP (ua-CompFill'∙ₑ
-- -- --               ((isoToEquiv (adjT×^ {A = A} {n = n} (fst k))))
-- -- --               (_ , isEquiv-permute→×^' n (k ∷ xs)))  )
-- -- --           ((ua-CompFill'∙ₑ
-- -- --               ((isoToEquiv (adjT×^ {A = A} {n = n} (fst k))))
-- -- --               (_ , isEquiv-permute→×^' n (xs))))
-- -- --       i0Cu l m j =
-- -- --        Glue (A ×^ n)
-- -- --          (λ { (j = i0) → (
-- -- --              (involPathSym {f = (adjT×^'→ {A = A} {n} (fst k))}
-- -- --                (isInvo-adjT×^'→ {n = n} (fst k)) l) m
-- -- --              , (i0CuP l m) ,
-- -- --                  isProp→SquareP
-- -- --                    (λ l m → isPropIsEquiv (i0CuP l m))
-- -- --                    (isProp→PathP (λ l → isPropIsEquiv (i0CuP l i0)) _ _)
-- -- --                    (refl)
-- -- --                    (symP ((isProp→PathP
-- -- --                       (λ m → isPropIsEquiv (i0CuP i0 (~ m)))
-- -- --                       (isEquiv-permute→×^' n (k ∷ xs))
-- -- --                       (snd ((isoToEquiv (adjT×^ {A = A} {n = n} (fst k)))
-- -- --                        ∙ₑ (_ , isEquiv-permute→×^' n (k ∷ xs)))))))
-- -- --                   (isProp→PathP
-- -- --                       (λ m → isPropIsEquiv (i0CuP i1 (m)))
-- -- --                       (isEquiv-permute→×^' n xs)
-- -- --                       (snd ((isoToEquiv (adjT×^ {A = A} {n = n} (fst k)))
-- -- --                        ∙ₑ (_ , isEquiv-permute→×^' n xs))))
-- -- --                      l m)
-- -- --             ; (j = i1) → (_ , idEquiv _)
-- -- --             })
      
-- -- --   braidA (w n) k k< x' = {!!}
-- -- --   commA (w n) k l z x' = {!!}


-- -- -- 𝔽-sq-snd : (A : Type ℓ)
-- -- --    → (isGroupoidA : isGroupoid A) → ∀ n → (g h : Perm n) → 
-- -- --   SquareP (λ i j → 𝔽h' A n (emcomp g h i j) ≡
-- -- --      𝔽-sq-fst A isGroupoidA n g h i j)
-- -- --     (congP (λ _ → snd) (𝔽-≡ A n g))
-- -- --     (congP (λ _ → snd) (𝔽-≡ A n (g · h)))
-- -- --     refl
-- -- --     (congP (λ _ → snd) (𝔽-≡ A n h) )
-- -- -- 𝔽-sq-snd {ℓ} A isGrpA n = RelimProp.f (w n)
-- -- --  where

-- -- --  open RelimProp

-- -- --  w : ∀ n → RelimProp {n = n}
-- -- --         λ g → (h : Perm n) → 
-- -- --   SquareP (λ i j → 𝔽h' A n (emcomp g h i j) ≡
-- -- --      𝔽-sq-fst A isGrpA n g h i j)
-- -- --     (congP (λ _ → snd) (𝔽-≡ A n g))
-- -- --     (congP (λ _ → snd) (𝔽-≡ A n (g · h)))
-- -- --     refl
-- -- --     (congP (λ _ → snd) (𝔽-≡ A n h) )
-- -- --  isPropA (w n) _ = isPropΠ λ _ →
-- -- --     {!!}
-- -- --  εA (w n) h i j = {!!}
-- -- --     -- Glue {!!}
-- -- --     --   {{!j ∨ ~ j ∨ i ∨ ~ i!}}
-- -- --     --   {!!}
-- -- --  ∷A (w n) = {!!}

-- -- -- -- -- ua-ungluePathExt∙ₑ : ∀ {ℓ} {A B C : Type ℓ} (e : A ≃ B) (f : B ≃ C)
-- -- -- -- --   → PathP (λ i → ua (e ∙ₑ f) i → ua (f) i)
-- -- -- -- --       (fst e) (idfun _)
-- -- -- -- -- ua-ungluePathExt∙ₑ {A = A} {B = B} {C = C} e f i x =
-- -- -- -- --    glue {A = C} {i ∨ ~ i}
-- -- -- -- --          (λ { (i = i0) → e .fst x
-- -- -- -- --             ; (i = i1) → x })
-- -- -- -- --          (ua-unglue (e ∙ₑ f) i x) --(ua-unglue (e ∙ₑ f) i x)


-- -- -- -- -- ua-ungluePathExt∙ₑ' : ∀ {ℓ} {A B C : Type ℓ} (e : A ≃ B) (f : B ≃ C)
-- -- -- -- --    → ∀ p
-- -- -- -- --   → PathP (λ i → ua (fst f ∘ fst e , p) i → ua (f) i)
-- -- -- -- --       (fst e) (idfun _)
-- -- -- -- -- ua-ungluePathExt∙ₑ' {A = A} {B = B} {C = C} e f p i x =
-- -- -- -- --    glue {A = C} {i ∨ ~ i}
-- -- -- -- --          (λ { (i = i0) → e .fst x
-- -- -- -- --             ; (i = i1) → x })
-- -- -- -- --          (ua-unglue (_ , p) i x) --(ua-unglue (e ∙ₑ f) i x)

-- -- -- -- -- -- ua-gluePathExt∙ₑ' : ∀ {ℓ} {A B C : Type ℓ} (e : A ≃ B) (f : B ≃ C)
-- -- -- -- -- --    → ∀ p
-- -- -- -- -- --   → PathP (λ i → ua (f) i → ua (fst f ∘ fst e , p) i)
-- -- -- -- -- --       (invEq e) (idfun _)
-- -- -- -- -- -- ua-gluePathExt∙ₑ' {A = A} {B = B} {C = C} e f p =
-- -- -- -- -- --    {!!} ◁ (λ i → ua-gluePathExt (fst f ∘ fst e , p) i ∘
-- -- -- -- -- --          invEq ((fst f ∘ fst e , p)) ∘ ua-ungluePathExt f i)
-- -- -- -- -- --      ▷ funExt (secEq (fst f ∘ fst e , p))
-- -- -- -- -- --    -- glue {A = C} {i ∨ ~ i}
-- -- -- -- -- --    --       (λ { (i = i0) → e .fst x
-- -- -- -- -- --    --          ; (i = i1) → x })
-- -- -- -- -- --    --       (ua-unglue (_ , p) i x) --(ua-unglue (e ∙ₑ f) i x)

-- -- -- -- -- -- ua-gluePathExtLem : {!!}
-- -- -- -- -- -- ua-gluePathExtLem = {!!}

-- -- -- -- -- -- ua-gluePathExt∙ₑ : ∀ {ℓ} {A B : Type ℓ}
-- -- -- -- -- --     (e : A → A)
-- -- -- -- -- --     (eInvol : isInvolution e)
-- -- -- -- -- --     (f : A ≃ B)
-- -- -- -- -- --   → PathP (λ i → ua (f) i → ua (involEquiv {f = e} eInvol ∙ₑ f) i)
-- -- -- -- -- --       (e) (idfun _)
-- -- -- -- -- --       -- (idfun _)  
-- -- -- -- -- -- ua-gluePathExt∙ₑ {A = A} {B = B} e eInvol f =
-- -- -- -- -- --     funExt (λ x → cong e (sym (retEq f x) ))
-- -- -- -- -- --       ◁ (λ i → 
-- -- -- -- -- --     ua-gluePathExt (involEquiv {f = e} eInvol ∙ₑ f) i
-- -- -- -- -- --       ∘' e ∘ invEq f ∘ ua-ungluePathExt f i)
-- -- -- -- -- --       ▷ funExt
-- -- -- -- -- --         λ x → secEq (involEquiv {f = e} eInvol ∙ₑ f) x
      
-- -- -- -- -- --    -- glue {A = B} {i ∨ ~ i}
-- -- -- -- -- --    --       (λ { (i = i0) → x
-- -- -- -- -- --    --          ; (i = i1) → {!f x!} })
-- -- -- -- -- --    --          (unglue  {!i ∨ ~ i!} x)
-- -- -- -- -- --          -- (ua-unglue (involEquiv {f = e} eInvol)
-- -- -- -- -- --          --   i {!!}) --(ua-unglue (e ∙ₑ f) i x)



-- -- -- -- -- -- -- -- --     -- Z : Square
-- -- -- -- -- -- -- -- --     --       (ua e)
-- -- -- -- -- -- -- -- --     --       (ua (e ∙ₑ f))
-- -- -- -- -- -- -- -- --     --       refl
-- -- -- -- -- -- -- -- --     --       (ua f)
-- -- -- -- -- -- -- -- --     -- Z i j =
-- -- -- -- -- -- -- -- --     --    Glue (ua f i)
-- -- -- -- -- -- -- -- --     --      (λ { (j = i0) → (A ,
-- -- -- -- -- -- -- -- --     --           ua-gluePathExt f i ∘ fst e ,
-- -- -- -- -- -- -- -- --     --           isProp→PathP (λ i → isPropIsEquiv
-- -- -- -- -- -- -- -- --     --             (ua-gluePathExt f i ∘ fst e))
-- -- -- -- -- -- -- -- --     --               (snd e)
-- -- -- -- -- -- -- -- --     --               (snd (e ∙ₑ f)) i
-- -- -- -- -- -- -- -- --     --         )
-- -- -- -- -- -- -- -- --     --         ; (j = i1) → (ua f i , idEquiv (ua f i)) })

-- -- -- -- 𝕍 : (A : Type ℓ) → (isGroupoid A) → ∀ n em → singl (𝔽h' A n em)
-- -- -- -- 𝕍 A isGroupoidA n = EMelim.f w
-- -- -- --  where
-- -- -- --   w : EMelim _
-- -- -- --                       (λ z → singl (𝔽h' A n z))
-- -- -- --   EMelim.isGrpB w _ = isOfHLevelPlus 3 (isContrSingl _)
-- -- -- --   EMelim.b w = (A ×^ n) , ua (isoToEquiv (invIso (Iso-×^-F→ n)))
-- -- -- --   EMelim.bPathP w = 𝔽-≡ A n
-- -- -- --   fst (EMelim.bSqP w g h i j) = 𝔽-sq-fst A isGroupoidA n g h i j
-- -- -- --   snd (EMelim.bSqP w g h i j) k = {!!}


-- -- -- -- -- -- module _ (A : Type ℓ) where


-- -- -- -- -- -- --  -- zzz : ∀ n g → 
-- -- -- -- -- -- --  --      ∀ i →
-- -- -- -- -- -- --  --         A →
-- -- -- -- -- -- --  --         fst (𝕍 A n (emloop g i)) →
-- -- -- -- -- -- --  --         fst
-- -- -- -- -- -- --  --         (𝕍 A (suc n)
-- -- -- -- -- -- --  --          (gh→em₂→ (Perm n , snd (PermG n)) (sucPerm , sucPermGH n)
-- -- -- -- -- -- --  --           (emloop g i)))
-- -- -- -- -- -- --  -- zzz n g i a =
-- -- -- -- -- -- --  --    ua-gluePathExt (fst (permute→×^' {A = A} (suc n) (sucPerm g) )
-- -- -- -- -- -- --  --         , isEquiv-permute→×^' (suc n) (sucPerm g) )
-- -- -- -- -- -- --  --         i ∘'
-- -- -- -- -- -- --  --     (a ,_)
-- -- -- -- -- -- --  --     ∘' ua-ungluePathExt (fst (permute→×^' {A = A} n g) ,
-- -- -- -- -- -- --  --       isEquiv-permute→×^' n g) i


-- -- -- -- -- --   open Relim

-- -- -- -- -- -- --   -- ww'* : ∀ n → ∀ (g : Perm n) →
-- -- -- -- -- -- --   --      Square
-- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- --   --        {!!}
-- -- -- -- -- -- --   -- ww'* = {!!}

-- -- -- -- -- --   ww'' : ∀ n → Relim {n = n} λ (g : Perm n) →
-- -- -- -- -- --            map-× (idfun A) (fst (permute→×^' n g)) ≡
-- -- -- -- -- --       fst (permute→×^' (suc n) (sucPerm g))
-- -- -- -- -- --           -- PathP
-- -- -- -- -- --           -- (λ i →
-- -- -- -- -- --           --    A × fst (𝔽-≡ A n g i) →
-- -- -- -- -- --           --   fst (𝔽-≡ A (suc n) (sucPerm g) i) )
-- -- -- -- -- --           --      (idfun _)
-- -- -- -- -- --           --      (idfun _)
-- -- -- -- -- --   isSetA (ww'' n) = {!!}
-- -- -- -- -- --   εA (ww'' n) = refl
-- -- -- -- -- --   ∷A (ww'' (suc n)) k X = 
-- -- -- -- -- --     λ i x → X i (fst x , adjT×^'→ (fst k) (snd x)) 
-- -- -- -- -- --   invoA (ww'' (suc n)) k X i j x = 
-- -- -- -- -- --      X j (fst x , isInvo-adjT×^'→ (fst k) (snd x) i)
-- -- -- -- -- --   braidA (ww'' (suc (suc (suc n)))) k k< X i j x = 
-- -- -- -- -- --      X j (fst x , braid-adjT×^'→ k k< (snd x) i)
-- -- -- -- -- --   commA (ww'' (suc (suc (suc n)))) k (suc l , l<) z X i j x = 
-- -- -- -- -- --     X j (fst x , comm-adjT×^'→ (fst k) (suc l) (snd k) l< z (snd x) (i))

-- -- -- -- -- --   ww''' : ∀ n → ∀ g →
-- -- -- -- -- --               Square
-- -- -- -- -- --              -- (ua ( (Σ-cong-equiv-snd
-- -- -- -- -- --              --     λ _ → (_ , isEquiv-permute→×^' n g))))
-- -- -- -- -- --              -- (λ i → A × (fst (𝔽-≡ A n g i)))
-- -- -- -- -- --              (ua (≃-× (idEquiv _) (_ , isEquiv-permute→×^' n g)))
-- -- -- -- -- --              (congP (λ _ → fst) (𝔽-≡ A (suc n) (sucPerm g)))
-- -- -- -- -- --              refl
-- -- -- -- -- --              refl
-- -- -- -- -- --   ww''' n g =
-- -- -- -- -- --     cong ua (equivEq (Relim.f (ww'' n) g))

-- -- -- -- -- --   ww* : ∀ n → ∀ (g : Perm n) →
-- -- -- -- -- --           PathP
-- -- -- -- -- --           (λ i →
-- -- -- -- -- --              (ua (≃-× (idEquiv _) (_ , isEquiv-permute→×^' n g))) i →
-- -- -- -- -- --              fst (𝔽-≡ A (suc n) (sucPerm g) i) )
-- -- -- -- -- --           (λ x → x) λ x → x
-- -- -- -- -- --   ww* n g = 
-- -- -- -- -- --    transport-fillerExt refl ◁ congP (λ _ → transport) (flipSquare (ww''' n g)) ▷
-- -- -- -- -- --      sym (transport-fillerExt refl)


-- -- -- -- -- --   ww'* : ∀ n → ∀ (g : Perm n) →
-- -- -- -- -- --           PathP
-- -- -- -- -- --           (λ i →
-- -- -- -- -- --              A →
-- -- -- -- -- --              fst (𝔽-≡ A n g i) →
-- -- -- -- -- --              fst (𝔽-≡ A (suc n) (sucPerm g) i) )
-- -- -- -- -- --           _,_ _,_
-- -- -- -- -- --   ww'* n g i a x = ww* n g i
-- -- -- -- -- --     (glue {A = A ×^ (suc n)} {i ∨ ~ i}
-- -- -- -- -- --       (λ { (i = i0) → _
-- -- -- -- -- --          ; (i = i1) → _
-- -- -- -- -- --          }) (a , ua-unglue (_ , isEquiv-permute→×^' n g) i x))



-- -- -- -- -- --   𝕍∷R : ∀ n → EMelim _ (λ (p : ℙrm' n) → A → fst (𝕍 A n p)
-- -- -- -- -- --                             → fst (𝕍 A (suc n)
-- -- -- -- -- --                               (gh→em₂→ _ (_ , sucPermGH _) p)))
-- -- -- -- -- --   EMelim.isGrpB (𝕍∷R n) = {!!}
-- -- -- -- -- --   EMelim.b (𝕍∷R n) = _,_
-- -- -- -- -- --   EMelim.bPathP (𝕍∷R n) = ww'* n

-- -- -- -- -- --   EMelim.bSqP (𝕍∷R n) g h = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  𝕍∷ : ∀ n → (p : ℙrm' n) → A → fst (𝕍 A n p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            → fst (𝕍 A (suc n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                              (gh→em₂→ _ (_ , sucPermGH _) p))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  𝕍∷ n = EMelim.f (𝕍∷R n)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- to𝕍R : RElim λ (x : FMSet2 A) → Σ _ (fst ∘ 𝕍 A (len2 x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- RElim.[]* to𝕍R = embase , tt*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- (to𝕍R RElim.∷* x) (e , xs) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --   -- (gh→em₂→ {!!} (_ , sucPermGH _) e ) , {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- RElim.comm* to𝕍R = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- RElim.comm-inv* to𝕍R = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- RElim.hexDiag* to𝕍R = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- RElim.hexU* to𝕍R = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- RElim.hexL* to𝕍R = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- RElim.trunc* to𝕍R = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- to𝕍 : (x : FMSet2 A) → Σ _ (fst ∘ 𝕍 A (len2 x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- to𝕍 = RElim.f to𝕍R
     


    
