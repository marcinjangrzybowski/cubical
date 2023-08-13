{-# OPTIONS --safe #-}
module Cubical.HITs.Permutation.Isos where

open import Cubical.Data.Nat.Base as ℕ hiding (_·_)
open import Cubical.Data.Nat.Properties


-- open import Cubical.Data.Fin.Properties as FP
open import Cubical.Data.Empty as ⊥

open import Cubical.Functions.Involution
open import Cubical.Functions.FunExtEquiv

open import Cubical.Foundations.Everything
-- open import Cubical.Data.Empty as ⊥
-- open import Cubical.Data.Nat as ℕ hiding (_·_)
-- open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Unit
open import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Sum as ⊎


open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Data.Nat.Order.Permutation
-- open import Cubical.Data.Nat.Order.RecursiveMoreEquiv

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

open import Cubical.Algebra.Group

open import Cubical.Algebra.SymmetricGroup

import Cubical.Functions.Logic as L

open import Cubical.Functions.Embedding

open import Cubical.Data.List as Li

import Cubical.Data.Nat.FinGenAut2 as A

import Cubical.HITs.PropositionalTruncation as Prop



open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

-- open import Cubical.Algebra.Group.Generators

open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.SequentialColimit as SC


-- open import Cubical.Data.FinData.GTrun

open import Cubical.HITs.EilenbergMacLane1 renaming (elim to elimEM)

open import Cubical.Relation.Binary

import Cubical.Homotopy.EilenbergMacLane.Properties as EMP

open import Cubical.Foundations.Equiv.HalfAdjoint

open import Cubical.HITs.Permutation.Base



-- predIso𝟚^ : ∀ n → (e : Iso (Bool ×^ (suc n)) (Bool ×^ (suc n)))
--                 → (∀ v → fst (Iso.fun e (false , v)) ≡ false)
--                 → (Iso (Bool ×^ n) (Bool ×^ n)) 
-- Iso.fun (predIso𝟚^ n e x) = predFun𝟚^ n (Iso.fun e)
-- Iso.inv (predIso𝟚^ n e x) = predFun𝟚^ n (Iso.inv e)
-- Iso.rightInv (predIso𝟚^ n e x) b =
--   let z = Iso.rightInv e (false , b)
--       zz : ∀ v → fst (Iso.inv e (false , v)) ≡ false
--       zz v = {!x (snd (Iso.inv e (false , v)))!}
--   in
--      -- cong (snd ∘ Iso.fun e)
--      --    (( sym zz ∙ {!!})
--      --      ∙ cong (Iso.inv e ∘ (_, b)) (x (snd (Iso.inv e (false , b)))))
--       {!!}
--         ∙ cong snd z
-- Iso.leftInv (predIso𝟚^ n e x) = {!!}

-- predIso𝟚^ : {!!}
-- predIso𝟚^ = {!!}


private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C : Type ℓ






isPermutationComp : ∀ n {f g} →
             ⟨ isPermutation n f
           L.⇒ isPermutation n g
           L.⇒ isPermutation n (compIso f g) ⟩    
isPermutationComp n {f} {g} p q x =
 let p₁ = fst ∘ p 
     p₂ = snd ∘ p
     q₁ = fst ∘ q
     q₂ = snd ∘ q
 in ((fst (q₁ (Iso.fun f x)) ∘ (fst (p₁ x)) )
   , snd (p₁ x) ∘ (snd (q₁ (Iso.fun f x))))
   , ((fst (q₂ (Iso.fun f x)) ∘ (fst (p₂ x)) )
   , snd (p₂ x) ∘ (snd (q₂ (Iso.fun f x))))

isPermutationSucIso : ∀ n {f} →
             ⟨ isPermutation n f
           L.⇒ isPermutation (suc n)
                (sucIso×^ n f) ⟩    
isPermutationSucIso n {f} p (false , xs) = p xs
isPermutationSucIso n {f} p (true , xs) =
  snd (p xs) , ((λ ()) , (λ ()))
  

isPermutationΣ-swap-01-Iso : ∀ n → ⟨ isPermutation (2 + n) Σ-swap-01-Iso ⟩
isPermutationΣ-swap-01-Iso n x =
  ((Fin×Snd∘adjT× _ zero x) ,
  Fin×Snd∘adjT× _ zero (adjT×^ zero x))
  , allFalse∘adjT× _ zero x ,
   allFalse∘adjT× _ zero (adjT×^ zero x) 

isPermutationRot×^Iso : ∀ n k → ⟨ isPermutation n (rot×^Iso n k) ⟩
isPermutationRot×^Iso (suc (suc n)) (suc k) =
  isPermutationComp (suc (suc n))
    {sucIso×^ (suc n) (rot×^Iso (suc n) k)} {Σ-swap-01-Iso}
    (isPermutationSucIso (suc n)
     {rot×^Iso (suc n) k} (isPermutationRot×^Iso (suc n) k))
    (isPermutationΣ-swap-01-Iso n)
isPermutationRot×^Iso (suc (suc n)) zero = isPermutationΣ-swap-01-Iso n
isPermutationRot×^Iso zero k x = ((λ ()) , (λ ())) , ((λ _ → tt*) , (λ _ → tt*))
isPermutationRot×^Iso (suc zero) k (false , _) =
  ((λ ()) , (λ ())) , (λ _ → tt*) , (λ _ → tt*)
isPermutationRot×^Iso (suc zero) k (true , _) =
  ((λ _ → tt*) , (λ _ → tt*)) , ((λ ()) , (λ ()))

rotPerm× : ∀ n → ℕ → Perm× n
rotPerm× n k =
  from𝟚×^Iso n
    (rot×^Iso n k)
    (isPermutationRot×^Iso n k)



PrePerm× : ∀ n → Type
PrePerm× n = Σ _ (fst ∘ isPermutation n)

fromPrePerm× : ∀ n → PrePerm× n → Perm× n
fromPrePerm× = uncurry ∘ from𝟚×^Iso

compPrePerm× : ∀ n → PrePerm× n → PrePerm× n → PrePerm× n
compPrePerm× n (e , p) (f , q) =
  compIso e f , isPermutationComp n {e} {f} p q

isPermutationInvIso : ∀ n {f} →
             ⟨ isPermutation n f
           L.⇒ isPermutation n (invIso f) ⟩    
isPermutationInvIso n {f} x =
  (λ ((a , a') , (b , b')) →
     (a' ∘ subst (fst ∘ Fin×Snd n) (sym (z.rightInv _)) ,
        subst (fst ∘ Fin×Snd n) (z.rightInv _) ∘ a) ,
       b' ∘ subst (fst ∘ allFalse n) (sym (z.rightInv _)) ,
       subst (fst ∘ allFalse n) (z.rightInv _) ∘ b) ∘ x ∘ z.inv
 where
 module z = Iso f

Σ≡PP× : ∀ n → {x y : PrePerm× n}
         → Iso.fun (fst x) ≡ Iso.fun (fst y)
         → Iso.inv (fst x) ≡ Iso.inv (fst y)
         → x ≡ y
Σ≡PP× n p q = Σ≡Prop (snd ∘ isPermutation n)
  (SetsIso≡
    (isOfHLevel×^ n 2 isSetBool)
    (isOfHLevel×^ n 2 isSetBool) p q)

GPrePerm× : ℕ → Group ℓ-zero
GPrePerm× n =
  makeGroup {G = PrePerm× n}
   (idIso , λ x → ((idfun _) , (idfun _)) , (idfun _) , (idfun _))
   (compPrePerm× n)
   (λ (f , p) → (invIso f , isPermutationInvIso n {f} p))
   (isSetΣ (isSet-SetsIso
     (isOfHLevel×^ n 2 isSetBool)
     (isOfHLevel×^ n 2 isSetBool))
     (isProp→isSet ∘ snd ∘ isPermutation n))
   (λ _ _ _ → Σ≡PP× n refl refl)
   (λ _ → Σ≡PP× n refl refl)
   (λ _ → Σ≡PP× n refl refl)
   (λ (x , _) → Σ≡PP× n (funExt (Iso.leftInv x))
                  (funExt (Iso.leftInv x)))
      (λ (x , _) → Σ≡PP× n (funExt (Iso.rightInv x))
                  (funExt (Iso.rightInv x)))

sucPrePerm× : ∀ n → PrePerm× n → PrePerm× (suc n)
sucPrePerm× n (f , p) =
  sucIso×^ n f , isPermutationSucIso n {f} p

module _ {n : ℕ} where
 module PP = GroupStr (snd (GPrePerm× n)) 

rotHlp×' : ∀ n → Bool ×^ n → PrePerm× (suc n)
rotHlp×' zero _ = PP.1g
rotHlp×' (suc n) (b , bs) =
  (sucPrePerm× (suc n) (rotHlp×' n bs)) PP.·
    (if b
   then Σ-swap-01-Iso , isPermutationΣ-swap-01-Iso n
   else PP.1g) 
    
rotHlp×RepeatFalse : ∀ n → rotHlp×' n (repeat n false) ≡ PP.1g
rotHlp×RepeatFalse zero = refl
rotHlp×RepeatFalse (suc n) =
  PP.·IdR _ ∙∙ cong (sucPrePerm× (suc n)) (rotHlp×RepeatFalse n)
   ∙∙ Σ≡PP× (suc (suc n))
     refl refl
   
fillUpToFstT : ∀ n → Bool ×^ n → Bool ×^ n 
fillUpToFstT zero _ = tt*
fillUpToFstT (suc n) (false , bs) = true , fillUpToFstT n bs
fillUpToFstT (suc n) (true , bs) = true , repeat n false

rotPrePerm× : ∀ n → Bool ×^ (suc n) → PrePerm× (suc n)
rotPrePerm× n (false , xs) = rotHlp×' n (fillUpToFstT n xs)
rotPrePerm× n (true , xs) = PP.1g
-- (rotHlp× n (fillUpToFstT (suc n) b))

rotPerm×* : ∀ n → Bool ×^ (suc n) → Perm× (suc n)
rotPerm×* n b = fromPrePerm× (suc n) (rotPrePerm× n b)

constAtF0 : ∀ n → (Iso (Bool ×^ n) (Bool ×^ n)) → hProp ℓ-zero
constAtF0 zero x = L.⊤
constAtF0 (suc n) x =
   (fst (Iso.fun x (true , repeat n false)) ≡ true) , isSetBool _ _

unwind𝟚^Iso : ∀ n → PrePerm× (suc n)
  → PrePerm× (suc n)
unwind𝟚^Iso n x =
  x PP.· rotPrePerm× n (Iso.fun (fst x) (true , repeat n false))


rotk[zero]≡k : ∀ n (k : Fin× (suc n))
  → (Iso.inv (fromPrePerm× (suc n) (rotPrePerm× n (fst k))) Fin×0)
    ≡ k

rotk[zero]≡k-lem : ∀ n bs → ⟨ Fin×Snd (suc n) bs ⟩  →
   Iso.inv
      (fromPrePerm× (suc (suc n)) (rotPrePerm× (suc n) (false , bs)))
      Fin×0
      ≡ sucFin× (Iso.inv (fromPrePerm× (suc n) (rotPrePerm× n bs)) Fin×0)

rotk[zero]≡k-lem n (false , bs) x =
  Σ≡Prop (snd ∘ Fin×Snd _)
   (cong′ (false ,_)
    refl)
rotk[zero]≡k-lem n (true , bs) x =
  Σ≡Prop (snd ∘ Fin×Snd _)
   (cong′ (false ,_)
    (funExt⁻ (cong (Iso.inv ∘ fst) (rotHlp×RepeatFalse n)) _))


rotk[zero]≡k zero ((true , snd₁) , _) = Fin×0= zero
rotk[zero]≡k (suc n) ((false , bs) , q) =
 let p = rotk[zero]≡k n (bs , q)
 in  rotk[zero]≡k-lem n bs  q ∙  cong sucFin× p
rotk[zero]≡k (suc n) ((true , bs) , _) = Fin×0= (suc n)

rotk[k]≡zero : ∀ n (k : Fin× (suc n))
  → (Iso.fun (fst (rotPrePerm× n (fst k))) (fst k))
    ≡ (true , repeat n false)
rotk[k]≡zero n k =
   let p = (rotk[zero]≡k n k)
   in cong′ (Iso.fun (fst (rotPrePerm× n (fst k))) ∘ fst) (sym p) ∙
       Iso.rightInv (fst (rotPrePerm× n (fst k))) (fst Fin×0)
     

constAtF0unwind : ∀ n x → ⟨ constAtF0 (suc n) (fst (unwind𝟚^Iso n x)) ⟩ 
constAtF0unwind n x =
  cong′ fst (
  rotk[k]≡zero n (Iso.fun (fromPrePerm× (suc n) x)
   Fin×0))

predPrePerm× : ∀ n (x : PrePerm× (suc n)) → ⟨ constAtF0 (suc n) (fst x) ⟩
                     → {!x!}
predPrePerm× = {!!}

-- rotPerm×' : ∀ n → ℕ → Perm× n
-- rotPerm×' n zero = idIso
-- rotPerm×' n (suc x) = rotPerm× n x

-- predFunFin×' : ∀ n → (Fin× (suc n) → Fin× (suc n))                   
--                    → Fin× n → Fin× n
-- predFunFin×' n f k = predFin× {a = k} (f (sucFin× k))


-- -- rotHlp×' : ∀ n → Bool ×^ n → Iso (A ×^ (suc n)) (A ×^ (suc n))
-- -- rotHlp×' zero _ x = {!x!}
-- -- rotHlp×' (suc n) (false , bs) = map-snd (rotHlp×' n bs) 
-- -- rotHlp×' (suc n) (true , bs) x₁ = {!swap!}

-- -- rotHlp× : ∀ n → Bool ×^ (suc n) → A ×^ (suc n) → A ×^ (suc n)
-- -- rotHlp× n (true , _) x = x
-- -- rotHlp× n (false , bs) xs = rotHlp×' n bs xs

-- -- -- predIsoFin× : ∀ n → (e : Perm× (suc n))
-- -- --                 → (∀ v isAllF → fst (fst (Iso.fun e ((true , v) , isAllF)))
-- -- --                         ≡ true)
-- -- --                 → (Perm× n) 
-- -- -- Iso.fun (predIsoFin× n e x) = predFunFin×' n (Iso.fun e)
-- -- -- Iso.inv (predIsoFin× n e x) = predFunFin×' n (Iso.inv e)
-- -- -- Iso.rightInv (predIsoFin× n e x) = {!!}
-- -- -- Iso.leftInv (predIsoFin× n e x) = {!!}

-- -- -- -- swapTest : ∀ n x →
-- -- -- --    ℕ→Fin× (suc (suc n)) (Fin×→ℕ (suc (suc n)) (swap-01 x)) ≡
-- -- -- --      swap-01 x
-- -- -- -- swapTest n x = {!!}

-- -- -- -- unwindIsoFin× : ∀ n → Iso (Perm× (suc n))
-- -- -- --                           ((Σ ℕ  λ k → (suc k < suc (suc n))) × (Perm× n))
-- -- -- -- Iso.fun (unwindIsoFin× n) e =
-- -- -- --   {!!} ,
-- -- -- --    (predIsoFin× n
-- -- -- --       (compIso e (rotPerm×' (suc n)
-- -- -- --         (Fin×→ℕ (suc n) (fst (Iso.fun e Fin×0)))))
-- -- -- --           {!!})  
-- -- -- -- Iso.inv (unwindIsoFin× n) = {!!}
-- -- -- -- Iso.rightInv (unwindIsoFin× n) = {!!}
-- -- -- -- Iso.leftInv (unwindIsoFin× n) = {!!}


-- -- -- -- -- rotℙ : ∀ n → (Σ ℕ  λ k → (suc k < suc n)) →
-- -- -- -- --          Path (ℙrm {true} n) 𝕡base 𝕡base
-- -- -- -- -- rotℙ n (zero , k<) = refl
-- -- -- -- -- rotℙ (suc (suc n)) (suc k , k<) = 
-- -- -- -- --   𝕡loop (zero , tt) ∙'
-- -- -- -- --     cong (sucℙrm (suc n)) (rotℙ (suc n) (k , k<))
-- -- -- -- -- rotℙ (suc zero) (suc zero , k<) = 𝕡loop (zero , k<)


-- -- -- -- -- toℙ≡bb : ∀ n → Iso (𝔽in n 𝕡base) (𝔽in n 𝕡base)
-- -- -- -- --                → Path (ℙrm {true} n) 𝕡base 𝕡base
-- -- -- -- -- toℙ≡bb zero _ = refl
-- -- -- -- -- toℙ≡bb (suc n) x =
-- -- -- -- --   let (k , x') = Iso.fun (unwindIsoFin× n) x
-- -- -- -- --   in cong (sucℙrm n) (toℙ≡bb n x') ∙ rotℙ _ k

-- -- -- -- -- rotFin×Iso : ∀ n → ℕ → Perm× n
-- -- -- -- -- rotFin×Iso = {!!}

-- -- -- -- -- sucFin×Iso : ∀ n → Perm× n → Perm× (suc n)
-- -- -- -- -- sucFin×Iso = {!!}


-- -- -- -- -- -- pathToIso-∙ : ∀ {ℓ} {A B C : Type ℓ} → (p : A ≡ B) (q : B ≡ C)
-- -- -- -- -- --          → pathToIso (p ∙ q) ≡ compIso (pathToIso p) (pathToIso q)
-- -- -- -- -- -- Iso.fun (pathToIso-∙ {A = A} p q i) z =
-- -- -- -- -- --   transp (λ j → q j) i0
-- -- -- -- -- --          (transp (λ i₁ → p i₁) i0 (transp (λ i₁ → A) i z))
-- -- -- -- -- -- Iso.inv (pathToIso-∙ {A = A} p q i) z =
-- -- -- -- -- --   transp (λ j → A) i
-- -- -- -- -- --          (transp (λ i₁ → p (~ i₁)) i0 (transp (λ i₁ → q (~ i₁)) i0 z))
-- -- -- -- -- -- Iso.rightInv (pathToIso-∙ {A = A} p q i) b j =
-- -- -- -- -- --   {!!}
-- -- -- -- -- -- Iso.leftInv (pathToIso-∙ p q i) = {!!}

-- -- -- -- -- toℙ≡bb-sec : ∀ n e → pathToIso (cong (𝔽in n) (toℙ≡bb n e)) ≡ e
-- -- -- -- -- Iso.fun (toℙ≡bb-sec zero e i) (_ , ())
-- -- -- -- -- Iso.inv (toℙ≡bb-sec zero e i) (_ , ())
-- -- -- -- -- Iso.rightInv (toℙ≡bb-sec zero e i) (_ , ())
-- -- -- -- -- Iso.leftInv (toℙ≡bb-sec zero e i) (_ , ())
-- -- -- -- -- toℙ≡bb-sec (suc n) e =
-- -- -- -- --   let (k , x') = Iso.fun (unwindIsoFin× n) e
-- -- -- -- --   in  cong pathToIso (cong-∙∙ (𝔽in (suc n))
-- -- -- -- --         (rotℙ _ k) (cong (sucℙrm n) (toℙ≡bb n x')) refl)
-- -- -- -- --            ∙
-- -- -- -- --              ({!!}
-- -- -- -- --              ≡⟨ {!!} ⟩
-- -- -- -- --               compIso (pathToIso (cong (𝔽in (suc n)) (rotℙ _ k)))
-- -- -- -- --                 (pathToIso
-- -- -- -- --                   (cong (𝔽in (suc n) ∘ sucℙrm n) (toℙ≡bb n x'))) 
-- -- -- -- --              ≡⟨ {!!} ⟩
-- -- -- -- --               {!!}
-- -- -- -- --              ≡⟨ {!!} ⟩
-- -- -- -- --              e ∎)

-- -- -- -- -- -- toℙ≡sqLem : ∀ n k e →
-- -- -- -- -- --             toℙ≡bb n (compIso e (F×adjTIso {n} (fst k)))
-- -- -- -- -- --                 ≡ toℙ≡bb n e ∙ 𝕡loop k
-- -- -- -- -- -- toℙ≡sqLem = {!!}


-- -- -- -- -- sucPrm-toℙ≡bb : ∀ n e →
-- -- -- -- --    cong (sucℙrm n) (toℙ≡bb n e)
-- -- -- -- --     ≡ toℙ≡bb (suc n) (sucFin×Iso n e)
-- -- -- -- -- sucPrm-toℙ≡bb zero e = {!!}
-- -- -- -- -- sucPrm-toℙ≡bb (suc n) e =
-- -- -- -- --  let (k , x') = Iso.fun (unwindIsoFin× n) e
-- -- -- -- --  in _
-- -- -- -- --       -- ≡⟨ cong-∙∙ (sucℙrm (suc n))
-- -- -- -- --       --   (rotℙ _ k) (cong (sucℙrm n) (toℙ≡bb n x')) refl ⟩
-- -- -- -- --       -- (cong (sucℙrm (suc n)) (rotℙ (suc n) k) ∙'
-- -- -- -- --       --   cong (sucℙrm (suc n)) (λ i → sucℙrm n (toℙ≡bb n x' i)))
-- -- -- -- --      ≡⟨ cong (cong (sucℙrm (suc n)) ∘ (rotℙ _ k ∙'_)) (sucPrm-toℙ≡bb n x') ⟩
-- -- -- -- --      _
-- -- -- -- --      -- ≡⟨ cong-∙∙ (sucℙrm (suc n)) (rotℙ (suc n) k)
-- -- -- -- --      --       (toℙ≡bb (suc n) (sucFin×Iso n x'))
-- -- -- -- --      --       refl ⟩
-- -- -- -- --      --  (cong (sucℙrm (suc n)) (rotℙ (suc n) k) ∙'
-- -- -- -- --      --    cong (sucℙrm (suc n)) (toℙ≡bb (suc n) (sucFin×Iso n x')))
-- -- -- -- --      ≡⟨ {!!} ⟩
-- -- -- -- --       {!!} ∎ 


-- -- -- -- -- unwindIsoFin×Inv : ∀ n e →
-- -- -- -- --      (sucFin×Iso n (snd (Iso.fun (unwindIsoFin× n) e)))
-- -- -- -- --        ≡ compIso (rotFin×Iso (suc n)
-- -- -- -- --         (fst (fst (Iso.fun (unwindIsoFin× n) e)))) e
-- -- -- -- -- unwindIsoFin×Inv = {!!}

-- -- -- -- -- sucFin×IsoComp : ∀ n e f →
-- -- -- -- --     compIso (sucFin×Iso n e) (sucFin×Iso n f)
-- -- -- -- --       ≡ sucFin×Iso n (compIso e f)
-- -- -- -- -- sucFin×IsoComp = {!!}

-- -- -- -- -- toℙ≡sq : ∀ n k e →
-- -- -- -- --             toℙ≡bb n (compIso e (F×adjTIso {n} (fst k)))
-- -- -- -- --                 ≡ toℙ≡bb n e ∙ 𝕡loop k
-- -- -- -- -- toℙ≡sq (suc (suc n)) (zero , k<) e = {!!}
-- -- -- -- -- toℙ≡sq (suc n) k*@(suc k , k<) e =
-- -- -- -- --  let (e0 , e') = Iso.fun (unwindIsoFin× n) e
-- -- -- -- --      -- e'P : ?
-- -- -- -- --      e'P = unwindIsoFin×Inv n e
-- -- -- -- --      (f0 , f') = Iso.fun (unwindIsoFin× n) (compIso e (F×adjTIso  (suc k)))
     
-- -- -- -- --      f'P = unwindIsoFin×Inv n (compIso e (F×adjTIso  (suc k)))
-- -- -- -- --  in   _
-- -- -- -- --       -- (rotℙ _ f0 ∙'
-- -- -- -- --       --    cong (sucℙrm n) (toℙ≡bb n f'))
-- -- -- -- --      ≡⟨ cong (rotℙ (suc n) f0 ∙'_) (sucPrm-toℙ≡bb n f') ⟩
-- -- -- -- --       {!!}
-- -- -- -- --      -- ≡⟨ {!!} ⟩
-- -- -- -- --      --  {!!}
-- -- -- -- --      ≡⟨ {!!} ⟩
-- -- -- -- --       _
-- -- -- -- --      ≡⟨ cong (rotℙ (suc n) e0 ∙_) (
-- -- -- -- --           cong (toℙ≡bb (suc n))
-- -- -- -- --             (cong₂ compIso (sym e'P) refl
-- -- -- -- --                ∙ sucFin×IsoComp n e' (F×adjTIso k))
-- -- -- -- --           ∙ sym (sucPrm-toℙ≡bb n _)) ⟩
-- -- -- -- --      --  {!!}
-- -- -- -- --      -- ≡⟨ {!e'P!} ⟩
-- -- -- -- --      --  {!!}
     
-- -- -- -- --      (rotℙ _ e0 ∙ cong (sucℙrm n) (toℙ≡bb n (compIso e' (F×adjTIso k))))
-- -- -- -- --      ≡⟨ cong (rotℙ _ e0 ∙_) (
-- -- -- -- --         cong (cong (sucℙrm n)) (toℙ≡sq n (k , k<) e')
-- -- -- -- --           ∙ cong-∙ (sucℙrm n) (toℙ≡bb n e') (𝕡loop (k , k<)) )  ⟩
-- -- -- -- --       (rotℙ _ e0 ∙
-- -- -- -- --          (cong (sucℙrm n) (toℙ≡bb n e') ∙ 𝕡loop k*))
-- -- -- -- --      ≡⟨ assoc _ _ _ ∙ sym (doubleCompPath-elim _ _ _)
-- -- -- -- --           ∙ split-leftright _ _ _ ⟩
-- -- -- -- --       toℙ≡bb (suc n) e ∙ 𝕡loop k* ∎ 
-- -- -- -- --      -- ({!!} ∙ sym (cong sym (doubleCompPath-elim _ _ _)))
-- -- -- -- --      --  ∙ split-leftright _ _ _

-- -- -- -- -- -- transportIsoR : ∀ {ℓ} {A B C : Type ℓ} → (p : B ≡ C) → ∀ e → 
-- -- -- -- -- --    transport (λ i → Iso A (p i)) e ≡ compIso e (pathToIso p)
-- -- -- -- -- -- transportIsoR {A = A} {B} {C} p e =
-- -- -- -- -- --   J {x = B}
-- -- -- -- -- --     (λ C p → transport (λ i → Iso A (p i)) e ≡ compIso e (pathToIso p))
-- -- -- -- -- --     (transportRefl _ ∙∙ sym (compIsoIdR e)
-- -- -- -- -- --       ∙∙ cong (compIso e) (sym pathToIso-refl)) p

-- -- -- -- -- -- rotℙ∙sucℙrm-lem : ∀ n k (p : 𝕡base ≡ 𝕡base) →
-- -- -- -- -- --   rotℙ (suc n) k ∙' cong (sucℙrm n) p ≡ refl {x = 𝕡base}
-- -- -- -- -- --    → (p ≡ refl) × (fst k ≡ zero)
-- -- -- -- -- -- rotℙ∙sucℙrm-lem n (zero , _) p x =
-- -- -- -- -- --   {! (cong sym (rUnit _)) ∙ x!} ,  refl
-- -- -- -- -- -- rotℙ∙sucℙrm-lem (suc n) (suc k , _) p x = {!n!}


-- -- -- -- -- -- pathToIso𝕡loop : ∀ n k →
-- -- -- -- -- --   (pathToIso (λ i → 𝔽in n (𝕡loop k (~ i)))) ≡
-- -- -- -- -- --      F×adjTIso (fst k)
-- -- -- -- -- -- pathToIso𝕡loop n k =
-- -- -- -- -- --  let z = funExt (λ x → Σ≡Prop (snd ∘ Fin×Snd n)
-- -- -- -- -- --        (funExt⁻ (transport-adjT×^≡ n (fst k)) (fst x)))
-- -- -- -- -- --  in SetsIso≡ (isSetFin× _) (isSetFin× _)
-- -- -- -- -- --      ((λ i' → transport (λ i → 𝔽in n (𝕡invol k i' (~ i)))) ∙ z)
-- -- -- -- -- --       z

-- -- -- -- -- -- p∙ploop≡q→p≡q∙ploop : ∀ n k {x} p q →
-- -- -- -- -- --    Path (Path (ℙrm {trunc = true} n) x 𝕡base) (p ∙ 𝕡loop k) q
-- -- -- -- -- --    → Path (x ≡ 𝕡base) p (q ∙ 𝕡loop k)
-- -- -- -- -- -- p∙ploop≡q→p≡q∙ploop n k p q s =
-- -- -- -- -- --    (rUnit p ∙ cong (p ∙_) (sym (lCancel (𝕡loop k))
-- -- -- -- -- --      ∙ cong (_∙ (𝕡loop k)) (sym (𝕡invol k))))
-- -- -- -- -- --     ∙∙ assoc _ _ _ ∙∙ cong (_∙ 𝕡loop k) s

-- -- -- -- -- -- toℙ≡ : ∀ n x → (Iso (𝔽in n 𝕡base) (𝔽in n x)) → (𝕡base ≡ x)
-- -- -- -- -- -- toℙ≡ n = R𝕡elimSet'.f {n = n} {true} (w {n}) 
-- -- -- -- -- --  where
-- -- -- -- -- --  open R𝕡elimSet'
-- -- -- -- -- --  w : ∀ {n} → R𝕡elimSet' λ x → (Iso (𝔽in n 𝕡base) (𝔽in n x)) → (𝕡base ≡ x)
-- -- -- -- -- --  isSetA w _ = isSetΠ λ _ → 𝕡squash _ _ _
-- -- -- -- -- --  abase w = toℙ≡bb _
-- -- -- -- -- --  aloop (w {n}) k = funTypePathP
-- -- -- -- -- --   _ _ _ _ (funExt
-- -- -- -- -- --     λ e → substInPathsL _ _ ∙ 
-- -- -- -- -- --       cong (λ x → toℙ≡bb n x ∙ 𝕡loop k)
-- -- -- -- -- --        (transportIsoR (λ i → (𝔽in n (𝕡loop k (~ i)))) e)
-- -- -- -- -- --         ∙ sym (p∙ploop≡q→p≡q∙ploop _ _ (toℙ≡bb n e) _
-- -- -- -- -- --          (sym (toℙ≡sq n k e) ∙
-- -- -- -- -- --           cong (toℙ≡bb n ∘ (compIso e)) (sym (pathToIso𝕡loop n k)))))

-- -- -- -- -- -- toℙ≡-idIso : ∀ n → (toℙ≡ n 𝕡base idIso) ≡ refl
-- -- -- -- -- -- toℙ≡-idIso zero = refl
-- -- -- -- -- -- toℙ≡-idIso (suc n) = {!!}

-- -- -- -- -- -- toP≡-refl : ∀ n (e : Iso (𝔽in n 𝕡base) (𝔽in n 𝕡base))
-- -- -- -- -- --               (p : toℙ≡ n 𝕡base e ≡ refl) →
-- -- -- -- -- --             idIso ≡ e
-- -- -- -- -- -- Iso.fun (toP≡-refl zero e p i) (_ , ()) 
-- -- -- -- -- -- Iso.inv (toP≡-refl zero e p i) (_ , ()) 
-- -- -- -- -- -- Iso.rightInv (toP≡-refl zero e p i) (_ , ()) 
-- -- -- -- -- -- Iso.leftInv (toP≡-refl zero e p i) (_ , ()) 

-- -- -- -- -- -- toP≡-refl (suc n) e p =
-- -- -- -- -- --   let (k , e') = Iso.fun (unwindIsoFin× n) e
-- -- -- -- -- --       (p' , k=0) = rotℙ∙sucℙrm-lem n k (toℙ≡ n 𝕡base e') p
-- -- -- -- -- --       q = toP≡-refl n e' p'
-- -- -- -- -- --   in sym (compIsoIdL idIso) ∙
-- -- -- -- -- --        cong₂ compIso {!cong rot!} {!q!} ∙ {!!}
-- -- -- -- -- -- isEquivToℙ≡ : ∀ n x → isEquiv' (toℙ≡ n x)
-- -- -- -- -- -- isEquivToℙ≡ n x =
-- -- -- -- -- --   J (λ x p → isContr (fiber (toℙ≡ n x) p))
-- -- -- -- -- --      ((idIso , toℙ≡-idIso n) ,
-- -- -- -- -- --       uncurry λ e p → Σ≡Prop (λ _ → 𝕡squash _ _ _ _ _)
-- -- -- -- -- --         (toP≡-refl n e p))


-- -- -- -- -- -- -- secIsoFin≡ : ∀ n x → section (λ x₁ → pathToIso (λ i → 𝔽in n (x₁ i))) (toℙ≡ n x)
-- -- -- -- -- -- -- secIsoFin≡ n = R𝕡elimProp.f ww
-- -- -- -- -- -- --  where
-- -- -- -- -- -- --  ww : R𝕡elimProp _
-- -- -- -- -- -- --  R𝕡elimProp.isPropA ww = {!!}
-- -- -- -- -- -- --  R𝕡elimProp.abase ww b = {!!}

-- -- -- -- -- -- -- retIsoFin≡ : ∀ n x → retract (λ x₁ → pathToIso (λ i → 𝔽in n (x₁ i))) (toℙ≡ n x)
-- -- -- -- -- -- -- retIsoFin≡ n x = J
-- -- -- -- -- -- --   (λ x p → toℙ≡ n x (pathToIso (cong (𝔽in n) p)) ≡ p)
-- -- -- -- -- -- --     (cong (toℙ≡ n 𝕡base) (pathToIso-refl)
-- -- -- -- -- -- --      ∙ {!!}) 

-- -- -- -- -- -- -- Iso𝔽in≡ : ∀ n x → Iso (𝕡base ≡ x) (Iso (𝔽in n 𝕡base) (𝔽in n x))
-- -- -- -- -- -- -- Iso.fun (Iso𝔽in≡ n x) = pathToIso ∘ cong (𝔽in n)
-- -- -- -- -- -- -- Iso.inv (Iso𝔽in≡ n x) = toℙ≡ n x
-- -- -- -- -- -- -- Iso.rightInv (Iso𝔽in≡ n x) = secIsoFin≡ n x
-- -- -- -- -- -- -- Iso.leftInv (Iso𝔽in≡ n x) = retIsoFin≡ n x 
-- -- -- -- -- -- -- -- Iso.fun (Iso𝔽in≡ n x y) = to𝔽Iso n x y
-- -- -- -- -- -- -- -- Iso.inv (Iso𝔽in≡ n x y) = toℙ≡ n x y 
-- -- -- -- -- -- -- -- Iso.rightInv (Iso𝔽in≡ n x y) = {!!}
-- -- -- -- -- -- -- -- Iso.leftInv (Iso𝔽in≡ n x y) = {!!}


-- -- -- -- -- -- -- -- to𝔽Iso : ∀ n x y → (x ≡ y) → (Iso (𝔽in n x) (𝔽in n y))
-- -- -- -- -- -- -- -- to𝔽Iso n x y = pathToIso ∘ cong (𝔽in n)

-- -- -- -- -- -- -- -- -- unwind-adjT : ∀ n e →
-- -- -- -- -- -- -- -- --       {!snd (Iso.fun (unwindIsoFin× n) (compIso ? e))!}
-- -- -- -- -- -- -- -- -- unwind-adjT = {!!}

-- -- -- -- -- -- -- -- toℙ≡bb : ∀ n → Iso (𝔽in n 𝕡base) (𝔽in n 𝕡base)
-- -- -- -- -- -- -- --                → Path (ℙrm {true} n) 𝕡base 𝕡base
-- -- -- -- -- -- -- -- toℙ≡bb zero _ = refl
-- -- -- -- -- -- -- -- toℙ≡bb (suc n) x =
-- -- -- -- -- -- -- --   let (k , x') = Iso.fun (unwindIsoFin× n) x
-- -- -- -- -- -- -- --   in rotℙ _ k ∙' cong (sucℙrm n) (toℙ≡bb n x')


-- -- -- -- -- -- -- -- toℙ≡loop : ∀ n (k : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- -- --       PathP
-- -- -- -- -- -- -- --       (λ i → Iso (𝔽in n 𝕡base)
-- -- -- -- -- -- -- --              (Σ (adjT×^≡ {A = Bool} {n = n} (fst k) i)
-- -- -- -- -- -- -- --                    (λ z → F×adjTP {n = n} (fst k) i z)) →
-- -- -- -- -- -- -- --         𝕡base {trunc = true}  ≡ 𝕡loop {n = n} k i)
-- -- -- -- -- -- -- --       (toℙ≡bb n) (toℙ≡bb n)
-- -- -- -- -- -- -- -- toℙ≡loop n k = toPathP
-- -- -- -- -- -- -- --   (funExt λ x → {!!})

-- -- -- -- -- -- -- -- -- funExtDep
-- -- -- -- -- -- -- -- --  λ {x₀} {x₁} p →
-- -- -- -- -- -- -- -- --    let p' = fromPathP p
-- -- -- -- -- -- -- -- --    in toPathP ({!!} ∙ cong (toℙ≡bb n) p')

-- -- -- -- -- -- -- -- toℙ≡ : ∀ n x y → (Iso (𝔽in n x) (𝔽in n y)) → (x ≡ y)
-- -- -- -- -- -- -- -- toℙ≡ n = R𝕡elimSet'.f {n = n} {true} (w {n}) 
-- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- --  open R𝕡elimSet'
-- -- -- -- -- -- -- --  w : ∀ {n} → R𝕡elimSet' (λ z → (y : ℙrm n) → Iso (𝔽in n z) (𝔽in n y) → z ≡ y)
-- -- -- -- -- -- -- --  isSetA w _ = isSetΠ2 λ _ _ → 𝕡squash _ _ _
-- -- -- -- -- -- -- --  abase (w {n}) = R𝕡elimSet'.f {n = n} ww
-- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- --   ww : R𝕡elimSet' (λ z → Iso (𝔽in n 𝕡base) (𝔽in n z) → 𝕡base ≡ z)
-- -- -- -- -- -- -- --   isSetA ww = {!!}
-- -- -- -- -- -- -- --   abase ww = toℙ≡bb _
-- -- -- -- -- -- -- --   aloop ww = toℙ≡loop _
 
-- -- -- -- -- -- -- --  aloop (w {n}) k = funExt (R𝕡elimProp.f {n = n} ww)
-- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- --   ww : R𝕡elimProp _
         
-- -- -- -- -- -- -- --   ww = {!!}

-- -- -- -- -- -- -- -- Iso𝔽in≡ : ∀ n x y → Iso (x ≡ y) (Iso (𝔽in n x) (𝔽in n y)) 
-- -- -- -- -- -- -- -- Iso.fun (Iso𝔽in≡ n x y) = to𝔽Iso n x y
-- -- -- -- -- -- -- -- Iso.inv (Iso𝔽in≡ n x y) = toℙ≡ n x y 
-- -- -- -- -- -- -- -- Iso.rightInv (Iso𝔽in≡ n x y) = {!!}
-- -- -- -- -- -- -- -- Iso.leftInv (Iso𝔽in≡ n x y) = {!!}
