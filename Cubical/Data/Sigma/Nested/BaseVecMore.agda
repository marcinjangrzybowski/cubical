

{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Sigma.Nested.BaseVecMore where

open import Cubical.Data.Nat

open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.Empty

open import Cubical.Foundations.Everything
open import Cubical.Foundations.CartesianKanOps


open import Cubical.HITs.NCube.IntervalPrim

open import Cubical.Data.Sigma.Nested.PathP

open import Cubical.HITs.NCube.BaseVec







NBoundary-Boundaryω-Isoω : ∀ {ℓ} → ∀ n → (A : NCube n → Type ℓ) →
                                Isoω (∀ x → A (boundaryInj x))
                                     (Boundaryω n (Ct[ n , A ]))





CylΣ-squashedTy : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ) →
                     (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
                     (c1 : (x : Vec Interval' n) → (A b∷ true) x) → 
                     Type ℓ
CylΣ-squashedTy n A c0 c1 = ∀ x → (PathCu A c0 c1) (boundaryInj x)

BdCylω-squashedTy : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ) →
                     (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
                     (c1 : (x : Vec Interval' n) → (A b∷ true) x) →  
                     ωType
BdCylω-squashedTy n A c0 c1 = Cylω-squashedTy n A (boundaryExpr n) c0 c1


CylΣ-squash : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ) →
                     (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
                     (c1 : (x : Vec Interval' n) → (A b∷ true) x) →
                     (PathP (λ i → ∀ x → (A i∷ i) (boundaryInj x))
                                    (c0 ∘ boundaryInj) 
                                    (c1 ∘ boundaryInj))
                     → CylΣ-squashedTy n A c0 c1
CylΣ-squash (suc n) A c0 c1 x z i = x i z


CylΣ-unsquash : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ) →
                     (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
                     (c1 : (x : Vec Interval' n) → (A b∷ true) x) 
                     → CylΣ-squashedTy n A c0 c1
                     → (PathP (λ i → ∀ x → (A i∷ i) (boundaryInj x))
                                    (c0 ∘ boundaryInj) 
                                    (c1 ∘ boundaryInj))
                     
CylΣ-unsquash n A c0 c1 x i z = x z i




BdCylω : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ) →
                     (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
                     (c1 : (x : Vec Interval' n) → (A b∷ true) x) → 
                     ωType 
BdCylω n A c0 c1 = Cylω n (Ct[ _ ,  A ]) (boundaryExpr n) ct[ _ , c0 ] ct[ _ , c1 ]

-- Partialⁿ-Sub (suc n) {A = Ct[ _ ,  A ]}
--                         {i = ↑Expr 1 (boundaryExpr n)}
--                         {j = (λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)}
--                         (mkCylEndsΣ n A c0 c1) 

BdCylω-squash : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ) →
                     (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
                     (c1 : (x : Vec Interval' n) → (A b∷ true) x) →
                     T[ BdCylω n A c0 c1 ]
                     → T[ BdCylω-squashedTy n A c0 c1 ] 
BdCylω-squash n A c0 c1 = Cylω-squash n A (boundaryExpr n) c0 c1
-- BdCylω-squash {ℓ} zero A c0 c1 x ()
-- -- Cylω-squash {ℓ} (suc zero) A c0 c1 x i = zz
-- --   where
-- --     zz : T[ Partialⁿ zero (boundaryExpr 1 i) (Ct[ 1 , PathCu A c0 c1 ] i) ]
-- --     zz (i = i0) = λ i₁ → outS (x i₁ i 1=1)
-- --     zz (i = i1) = λ i₁ → outS (x i₁ i 1=1)
    
-- BdCylω-squash {ℓ} (suc zero) A c0 c1 x i = zz
--    where
--      zz : _
--      zz (i = i1) = λ i₁ → outS (x i₁ i1 1=1)
--      zz (i = i0) = λ i₁ → outS (x i₁ i0 1=1)
-- BdCylω-squash {ℓ} (suc (suc n)) A c0 c1 x i i₁ = {!!}


  -- let zz : (i j : I) →
  --             T[ Partialⁿ-Sub n (mkCylEndsΣ (suc n) A c0 c1 j i) ]
  --     zz i j = x j i
  -- in {!zz!}



BdCylω-unsquash : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ) →
                     (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
                     (c1 : (x : Vec Interval' n) → (A b∷ true) x) →
                     T[ BdCylω-squashedTy n A c0 c1 ]
                     → T[ BdCylω n A c0 c1 ] 
BdCylω-unsquash n A c0 c1 = Cylω-unsquash n A (boundaryExpr n) c0 c1
-- BdCylω-unsquash zero A c0 c1 x i ()
-- BdCylω-unsquash (suc zero) A c0 c1 x i i₁ = {!!}

-- BdCylω-unsquash (suc (suc n)) A c0 c1 x i i₁ = {!!}

fromωCyl : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ) →
                     (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
                     (c1 : (x : Vec Interval' n) → (A b∷ true) x) →
                     T[ BdCylω n A c0 c1 ]
                     → T[ Boundaryω (suc n) Ct[ _ , A ] ]
fromωCyl {ℓ} n@zero A c0 c1 x = attachEndsToCylω n Ct[ _ , A ] (boundaryExpr n) ct[ zero , c0 ] ct[ zero , c1 ] x
fromωCyl {ℓ} n@(suc _) A c0 c1 x = attachEndsToCylω n Ct[ _ , A ] (boundaryExpr n) _ _ x



toωCyl : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ) → (e : Ie n)
                      (bdω : T[ Partialⁿ (suc n) (((λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∨ⁿ (↑Expr 1 e))) Ct[ _ , A ] ])
                     → T[ Cylω n (Ct[ _ , A ]) e
                            ct[ _ , ((Isoω.from (NCubeP-Isomω n (_))
                              (Partialⁿ-getLid n e false _ bdω))) ]
                            ct[ _ , ((Isoω.from (NCubeP-Isomω n (_))
                              (Partialⁿ-getLid n e true _ bdω))) ] ]

toωCyl zero A e bdω i i=1 = inS ((⊆I→⊆'I 1 (⊆I-∨2 {1} ((λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr)) (↑Expr 1 e) ) bdω) i i=1)
toωCyl (suc zero) A e bdω l l₁ i=1 = toωCyl zero (λ x → A (head x ∷ inside l₁ ∷ [])) (e l₁) ((λ i → bdω i  l₁)) l i=1
toωCyl (suc (suc n)) A e bdω l l₁ = (toωCyl (suc n) (λ c → A (head c ∷ inside  l₁ ∷ tail c)) (e  l₁) (λ i → bdω i  l₁)) l
 

toωCylBd : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ) →
                      (bdω : T[ Boundaryω (suc n) Ct[ _ , A ] ])
                     → T[ BdCylω n A
                            ((Isoω.from (NCubeP-Isomω n (_))
                              (Boundaryω-getLid n false (Ct[ _ , A ]) bdω)))
                            ((Isoω.from (NCubeP-Isomω n (_))
                              (Boundaryω-getLid n true (Ct[ _ , A ]) bdω))) ]

toωCylBd zero A bdω i ()
toωCylBd (suc n) A bdω = toωCyl (suc n) A (boundaryExpr (suc n)) bdω


--- inside related 




-- InsideCylω : ∀ {ℓ} → ∀ n →
--                       (A : NCube (suc n) → Type ℓ) → (e : Ie n) →
--                      (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
--                      (c1 : (x : Vec Interval' n) → (A b∷ true) x) → 
--                      T[ Cylω n Ct[ suc n , A ] e ct[ n , c0 ] ct[ n , c1 ] ]
--                     → ωType 
-- InsideCylω n A e c0 c1 cl =
--   Subⁿ (suc n) (((λ i → [ i ]Iexpr ∨ⁿ [ ~ i ]Iexpr) ∨ⁿ ↑Expr 1 e))
--     (attachEndsToCylω n Ct[ _ , A ] (e) ct[ _ , c0 ] ct[ _ , c1 ] cl)


-- InsideCylω-squashed : ∀ {ℓ} → ∀ n →
--                       (A : NCube (suc n) → Type ℓ) → (e : Ie n) →
--                      (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
--                      (c1 : (x : Vec Interval' n) → (A b∷ true) x) → 
--                     T[ Cylω-squashedTy n A e c0 c1  ]
--                     → ωType 
-- InsideCylω-squashed n A e x₀ x₁ cl = Subⁿ n e cl

-- Subⁿ-squash : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ)  → (e : Ie n) →
--                      (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
--                      (c1 : (x : Vec Interval' n) → (A b∷ true) x) →
--                      (cl : T[ Cylω n Ct[ suc n , A ] e ct[ n , c0 ] ct[ n , c1 ] ])
--                    → T[ InsideCylω n A e c0 c1 cl ]
--                    → T[ InsideCylω-squashed n A e c0 c1 (Cylω-squash n A e c0 c1 cl) ]
-- Subⁿ-squash = {!!}

-- Subⁿ-squash-Bd : ∀ {ℓ} → ∀ n → (A : NCube (suc n) → Type ℓ) →
--                      (c0 : (x : Vec Interval' n) → (A b∷ false) x) →
--                      (c1 : (x : Vec Interval' n) → (A b∷ true) x) →
--                      (cl : T[ BdCylω n A c0 c1 ])
--                    → T[ InsideCylω n A (boundaryExpr n) c0 c1 cl ]
--                    → T[ InsideCylω-squashed n A (boundaryExpr n) c0 c1 (BdCylω-squash n A c0 c1 cl) ]
-- Subⁿ-squash-Bd = {!!}

--

Isoω.to (NBoundary-Boundaryω-Isoω zero A) x ()
Isoω.toω (NBoundary-Boundaryω-Isoω zero A) t₀ t₁ x () i
Isoω.from (NBoundary-Boundaryω-Isoω zero A) x ()
Isoω.sec (NBoundary-Boundaryω-Isoω zero A) b i ()
Isoω.ret (NBoundary-Boundaryω-Isoω zero A) a () i

NBoundary-Boundaryω-Isoω (suc n) A = h

  where

    module bIso = Iso (NBoundaryP-rec-Iso {A = A}) 

    h : Isoω ((x : NBoundary (suc n)) → A (boundaryInj x))
               (Boundaryω (suc n) Ct[ suc n , A ])
    Isoω.to h bd =
      let ((e0 , e1) , cy) = bIso.fun bd
          w = Isoω.to (NBoundary-Boundaryω-Isoω n _) (CylΣ-squash n A e0 e1 cy)

      in fromωCyl n A e0 e1 (BdCylω-unsquash n A e0 e1 w)       

    
    Isoω.toω h bd = {!!}
      
    Isoω.from h bdω =
       let c0 : (x : NCube n) → A (inside (Bool→I false) ∷ x)
           c0 = (Isoω.from (NCubeP-Isomω n (_))
                   (Boundaryω-getLid n false (Ct[ _ , A ]) bdω))

           c1 : (x : NCube n) → A (inside (Bool→I true) ∷ x)
           c1 = (Isoω.from (NCubeP-Isomω n (_))
                    (Boundaryω-getLid n true (Ct[ _ , A ]) bdω))

           z = BdCylω-squash n A
                    c0 c1
                  (toωCylBd n A bdω)


           w = Isoω.from (NBoundary-Boundaryω-Isoω n _) z
       in bIso.inv ((c0 , c1) ,
                    CylΣ-unsquash n A
                    c0
                    c1
                    w)

    
    Isoω.sec h = {!!}
    Isoω.ret h = {!!}




Boundaryω-Boundary : ∀ n → T[ Boundaryω n Ct[ n , (λ _ → NBoundary n) ] ] 
Boundaryω-Boundary n = Isoω.to (NBoundary-Boundaryω-Isoω n (λ _ → NBoundary n)) (idfun _)




Iso-string : ∀ {ℓ} → (A : ℕ → ℕ → Type ℓ) → (∀ n m → Iso (A (suc n) m) (A n (suc m)))
                   → ∀ n → (Iso (A n zero) (A zero n))
Iso-string A x zero = idIso
Iso-string A x (suc n) = compIso (x n zero) (Iso-string (λ n m → A n (suc m)) (λ n' m' → x n' (suc m')) n)






module VecHelp {ℓ} {A : Type ℓ}  where
  assoc-vec-1 : ∀ n m → Iso (Vec A ((suc n) + m)) (Vec A (n + (suc m)))
  assoc-vec-1 zero m = idIso 

  Iso.fun (assoc-vec-1 (suc n) m) (x ∷ x₁) = x ∷ Iso.fun (assoc-vec-1 (n) m) x₁
  Iso.inv (assoc-vec-1 (suc n) m) (x ∷ x₁) = x ∷ Iso.inv (assoc-vec-1 (n) m) x₁
  Iso.rightInv (assoc-vec-1 (suc n) m) (x ∷ b) i = x ∷ Iso.rightInv (assoc-vec-1 (n) m) (b) i
  Iso.leftInv (assoc-vec-1 (suc n) m) (x ∷ a) i = x ∷ Iso.leftInv (assoc-vec-1 (n) m) (a) i

  split : ∀ {m n} → Vec A (m + n) → Vec A m × Vec A n 
  split {zero} x =  [] , x 
  split {suc m} (x ∷ x₁) = x ∷ fst (split x₁) , snd (split x₁)

  split-++-iso : ∀ {m n} → Iso (Vec A (m + n)) (Vec A m × Vec A n)
  Iso.fun split-++-iso = split
  Iso.inv split-++-iso = uncurry _++_
  Iso.rightInv (split-++-iso {zero}) ([] , snd₁) = refl
  Iso.rightInv (split-++-iso {suc m}) (x ∷ fst₁ , snd₁) i =
    let (vm , vn) = Iso.rightInv (split-++-iso {m}) (fst₁ , snd₁) i
     in x ∷ vm  , vn
  Iso.leftInv (split-++-iso {zero}) a = refl
  Iso.leftInv (split-++-iso {suc m}) (x ∷ a) i =
    x ∷ Iso.leftInv (split-++-iso {m}) a i
     

  swapFirstTwo : ∀ n → Iso (Vec A n) (Vec A n)
  swapFirstTwo zero = idIso
  swapFirstTwo (suc zero) = idIso
  Iso.fun (swapFirstTwo (suc (suc n))) (x ∷ x₁ ∷ x₂) = (x₁ ∷ x ∷ x₂) 
  Iso.inv (swapFirstTwo (suc (suc n))) (x ∷ x₁ ∷ x₂) = (x₁ ∷ x ∷ x₂)
  Iso.rightInv (swapFirstTwo (suc (suc n))) (x ∷ x₁ ∷ x₂) = refl
  Iso.leftInv (swapFirstTwo (suc (suc n))) (x ∷ x₁ ∷ x₂) = refl

  ∷-elim : ∀ {ℓ'} → ∀ {n} → (B : Vec A (suc n) → Type ℓ') → ∀ x → (B (head x ∷ tail x)) → B x 
  ∷-elim _ (x ∷ x₂) x₁ = x₁

  ∷-elim2 : ∀ {ℓ'} → ∀ {n} → (B : Vec A (suc (suc n)) → Type ℓ') → ∀ x → (B (head x ∷ head (tail x) ∷ tail (tail x))) → B x 
  ∷-elim2 _ (x ∷ x₂ ∷ x₃) x₁ = x₁


  rotateIso : ∀ n → Iso (Vec A n) (Vec A n)
  rotateIso zero = idIso
  rotateIso (suc zero) = idIso
  Iso.fun (rotateIso (suc (suc n))) = (λ x → head x ∷ Iso.fun (rotateIso (suc n)) (tail x)) ∘ (Iso.fun (swapFirstTwo (suc (suc n))))
  Iso.inv (rotateIso (suc (suc n))) = (Iso.inv (swapFirstTwo (suc (suc n)))) ∘ (λ x → head x ∷ Iso.inv (rotateIso (suc n)) (tail x))
  Iso.rightInv (rotateIso (suc (suc n))) b = {!!}    
  Iso.leftInv (rotateIso (suc (suc n))) (x ∷ x₁ ∷ a) = {!!}

  iso-first-× : ∀ {B B' C : Type ℓ} → Iso B B' → Iso (B × C) (B' × C) 
  Iso.fun (iso-first-× y) x = Iso.fun y (fst x) , snd x
  Iso.inv (iso-first-× y) x = Iso.inv y (fst x) , snd x
  Iso.rightInv (iso-first-× y) x = cong ( _, snd x) (Iso.rightInv y (fst x))
  Iso.leftInv (iso-first-× y) x = cong ( _, snd x) (Iso.leftInv y (fst x))

  assoc-vec-2 : ∀ n m → Iso (Vec A ((suc n) + m)) (Vec A (n + (suc m)))
  assoc-vec-2 n m =
     compIso split-++-iso (compIso (iso-first-× (rotateIso (suc n)))
       (compIso (invIso (split-++-iso)) (assoc-vec-1 n m)))


lem-assoc-vec-2 : ∀ {ℓ} → {A : Type₀} → ∀ n m → (B : Vec A (suc (n + m)) → Type ℓ) → (vn : Vec A n) → (vm : Vec A m) → ∀ a →
                  Iso ((B ∘ Iso.inv (VecHelp.assoc-vec-2 n m)) (vn ++ a ∷ vm))
                       (B ((a) ∷ (vn ++ vm)))
lem-assoc-vec-2 zero m B [] vm a = idIso
lem-assoc-vec-2 (suc zero) m B (x ∷ []) vm a = idIso

lem-assoc-vec-2 (suc (suc zero)) m B (x ∷ x₁ ∷ []) vm a = idIso

lem-assoc-vec-2 (suc (suc (suc n))) m B (x ∷ x₁ ∷ x₂ ∷ vn) vm a = 
   let z : {!!}
       z = lem-assoc-vec-2 (suc (suc n)) m (λ x₃ → B (head x₃ ∷ x ∷ tail x₃)) (x₁ ∷ x₂ ∷ vn) vm a
   in compIso {!!} z

SplitVecBdIns-Ty : ∀ {ℓ} → ∀ n m → (A : NCube (n + m) → Type ℓ) → Type ℓ 
SplitVecBdIns-Ty n m A = Σ (((bdN : NBoundary n) → (cuM : NCube m) → A (boundaryInj bdN ++ cuM)))
                           λ x → ∀ (cuM : NCube m) → InsideOfP {n = n} (λ v → A (v ++ cuM)) λ x₁ → x x₁ cuM

SplitVecBdIns-Ty' : ∀ {ℓ} → ∀ n m → (A : NCube (n + m) → Type ℓ) → Type ℓ 
SplitVecBdIns-Ty' n m A = (cuM : NCube m) → Σ (((bdN : NBoundary n) → A (boundaryInj bdN ++ cuM)))
                           λ x → InsideOfP {n = n} (λ v → A (v ++ cuM)) λ x₁ → x x₁

SplitVecBdIns-Ty-Iso-Ty' : ∀ {ℓ} → ∀ n m → (A : NCube (n + m) → Type ℓ) →
                                Iso
                                  (SplitVecBdIns-Ty n m A)
                                  (SplitVecBdIns-Ty' n m A)
Iso.fun (SplitVecBdIns-Ty-Iso-Ty' n m A) (bd , ins) cuM = (λ bdN → bd bdN cuM) , ins cuM
Iso.inv (SplitVecBdIns-Ty-Iso-Ty' n m A) x = (λ bdN cuM → fst (x cuM) bdN) , (λ cuM → snd (x cuM))
Iso.rightInv (SplitVecBdIns-Ty-Iso-Ty' n m A) b = funExt λ x → refl
Iso.leftInv (SplitVecBdIns-Ty-Iso-Ty' n m A) a = refl



hlp : ∀ {ℓ} {n} {m} {A : NCube (suc (suc (suc n)) + m) → Type ℓ}
        {bdN = bd : NBoundary (suc (suc n))} {i}
        {xs = cuM : Vec Interval' m} →
      A (inside i ∷ boundaryInj bd ++ cuM) →
      (A ∘ Iso.inv (VecHelp.assoc-vec-2 (suc (suc n)) m))
      (boundaryInj bd ++ inside i ∷ cuM)

hlp {ℓ} {zero} {m} {A} {bdN = lid false (end false ∷ [])} {i} {xs = cuM} x = x
hlp {ℓ} {zero} {m} {A} {bdN = lid false (end true ∷ [])} {i} {xs = cuM} x = x
hlp {ℓ} {zero} {m} {A} {bdN = lid false (inside i₁ ∷ [])} {i} {xs = cuM} x = x
hlp {ℓ} {zero} {m} {A} {bdN = lid true (end false ∷ [])} {i} {xs = cuM} x = x
hlp {ℓ} {zero} {m} {A} {bdN = lid true (end true ∷ [])} {i} {xs = cuM} x = x
hlp {ℓ} {zero} {m} {A} {bdN = lid true (inside i₁ ∷ [])} {i} {xs = cuM} x = x
hlp {ℓ} {zero} {m} {A} {bdN = cyl (lid false []) i₁} {i} {xs = cuM} x = x
hlp {ℓ} {zero} {m} {A} {bdN = cyl (lid true []) i₁} {i} {xs = cuM} x = x
hlp {ℓ} {suc n} {m} {A} {bdN = bd} {i} {xs = cuM} x = {!!}



SplitVecBdIns-step→Bd-rec : ∀ {ℓ} → ∀ n m → ∀ A
                        → (SplitVecBdIns-Ty {ℓ} (suc n) m A)
                        → (i : I) → SplitVecBdIns-Ty {ℓ} n m λ v → (A i∷ i) v

fst (SplitVecBdIns-step→Bd-rec zero m A (bd , ins) i) () cuM
snd (SplitVecBdIns-step→Bd-rec zero m A (bd , ins) i) cuM = ins cuM i
fst (SplitVecBdIns-step→Bd-rec (suc n) m A (bd , ins) i) bdN cuM = bd (cylEx i bdN) cuM
snd (SplitVecBdIns-step→Bd-rec (suc n) m A (bd , ins) i) cuM i₁ = ins cuM i i₁


SplitVecBdIns-step→Ins-rec : ∀ {ℓ} → ∀ n m → (A : NCube ((suc n) + m) → Type ℓ)
                        → ((i : I) → SplitVecBdIns-Ty {ℓ} n m λ v → (A i∷ i) v)
                        → (SplitVecBdIns-Ty {ℓ} n (suc m) (A ∘ ((Iso.inv (VecHelp.assoc-vec-2 n m)) )))

fst (SplitVecBdIns-step→Ins-rec zero m A x) () cuM
snd (SplitVecBdIns-step→Ins-rec zero m A x) (end false ∷ cuM) = snd (x i0) cuM
snd (SplitVecBdIns-step→Ins-rec zero m A x) (end true ∷ cuM) = snd (x i1) cuM
snd (SplitVecBdIns-step→Ins-rec zero m A x) (inside i ∷ cuM) = snd (x i) cuM

fst (SplitVecBdIns-step→Ins-rec (suc zero) m A x) (lid false []) (end false ∷ cuM) = fst (x i0) (lid false []) cuM
fst (SplitVecBdIns-step→Ins-rec (suc zero) m A x) (lid false []) (end true ∷ cuM) = fst (x i1) (lid false []) cuM
fst (SplitVecBdIns-step→Ins-rec (suc zero) m A x) (lid false []) (inside i ∷ cuM) = fst (x i) (lid false []) cuM
fst (SplitVecBdIns-step→Ins-rec (suc zero) m A x) (lid true []) (end false ∷ cuM) = fst (x i0) (lid true []) cuM
fst (SplitVecBdIns-step→Ins-rec (suc zero) m A x) (lid true []) (end true ∷ cuM) = fst (x i1) (lid true []) cuM
fst (SplitVecBdIns-step→Ins-rec (suc zero) m A x) (lid true []) (inside i ∷ cuM) = fst (x i) (lid true []) cuM
snd (SplitVecBdIns-step→Ins-rec (suc zero) m A x) (end false ∷ cuM) = {!!}
snd (SplitVecBdIns-step→Ins-rec (suc zero) m A x) (end true ∷ cuM) = {!!}

snd (SplitVecBdIns-step→Ins-rec (suc zero) m A x) (inside i ∷ cuM) = snd (x i) cuM


fst (SplitVecBdIns-step→Ins-rec (suc (suc n)) m A x) bdN (end false ∷ cuM) =
      Iso.inv (lem-assoc-vec-2 (suc (suc n)) m A (boundaryInj bdN) cuM (inside i0) ) (fst (x i0) bdN cuM)
fst (SplitVecBdIns-step→Ins-rec (suc (suc n)) m A x) bdN (end true ∷ cuM) =
   Iso.inv (lem-assoc-vec-2 (suc (suc n)) m A (boundaryInj bdN) cuM (inside i1) ) (fst (x i1) bdN cuM)
fst (SplitVecBdIns-step→Ins-rec (suc (suc n)) m A x) bdN (inside i ∷ cuM) =
   Iso.inv (lem-assoc-vec-2 (suc (suc n)) m A (boundaryInj bdN) cuM (inside i) ) (fst (x i) bdN cuM)
snd (SplitVecBdIns-step→Ins-rec (suc (suc n)) m A x) (end x₁ ∷ cuM) = {!!}
snd (SplitVecBdIns-step→Ins-rec (suc (suc n)) m A x) (inside i ∷ cuM) = {!snd (x i) cuM!}

   -- let zz : (i : I) → _
   --     zz i = 
   --            (SplitVecBdIns-step→Ins-rec (suc n) m
   --            (λ x₁ → A (head x₁ ∷ inside i ∷ tail x₁))
   --             λ i₁ → (λ bdN cuM → fst (x i₁) (cylEx i bdN)  cuM) ,
   --             λ cuM i₂ → snd (x i₁) cuM i i₂)

   -- in (λ bdN cuM → {!!}) , {!!}

     

   -- where
   --   zz : SplitVecBdIns-Ty' (suc (suc n)) (suc m)
   --          (λ x₁ → A (Iso.inv (VecHelp.assoc-vec-2 (suc (suc n)) m) x₁))
   --   fst (zz cuM) (lid x x₁) = {!!}
   --   fst (zz cuM) (cyl x i) = {!!}
   --   snd (zz (end false ∷ cuM)) i = {!!}
   --   snd (zz (end true ∷ cuM)) i = {!!}
   --   snd (zz (inside i₁ ∷ cuM)) i  = {!!}


SplitVecBdIns-step→ : ∀ {ℓ} → ∀ n m → ∀ A
                        → SplitVecBdIns-Ty {ℓ} (suc n) m A
                        → SplitVecBdIns-Ty n (suc m) (A ∘ (Iso.inv (VecHelp.assoc-vec-2 n m)))  
SplitVecBdIns-step→ n m A x = SplitVecBdIns-step→Ins-rec n m A (SplitVecBdIns-step→Bd-rec n m A x)
  

-- fst (SplitVecBdIns-step→ zero m A (fst₁ , snd₁)) () cuM
-- snd (SplitVecBdIns-step→ zero m A (fst₁ , snd₁)) (end false ∷ cuM) = snd₁ cuM i0
-- snd (SplitVecBdIns-step→ zero m A (fst₁ , snd₁)) (end true ∷ cuM) = snd₁ cuM i1
-- snd (SplitVecBdIns-step→ zero m A (fst₁ , snd₁)) (inside i ∷ cuM) = snd₁ cuM i
-- -- fst (SplitVecBdIns-step→ (suc zero) m A (fst₁ , snd₁)) bdN@(lid false []) (end false ∷ cuM) = snd₁ cuM i0 i0
-- -- fst (SplitVecBdIns-step→ (suc zero) m A (fst₁ , snd₁)) bdN@(lid false []) (end true ∷ cuM) = snd₁ cuM i1 i0
-- -- fst (SplitVecBdIns-step→ (suc zero) m A (fst₁ , snd₁)) bdN@(lid false []) (inside i ∷ cuM) = snd₁ cuM i i0
-- -- fst (SplitVecBdIns-step→ (suc zero) m A (fst₁ , snd₁)) bdN@(lid true []) (end false ∷ cuM) = snd₁ cuM i0 i1
-- -- fst (SplitVecBdIns-step→ (suc zero) m A (fst₁ , snd₁)) bdN@(lid true []) (end true ∷ cuM) = snd₁ cuM i1 i1
-- -- fst (SplitVecBdIns-step→ (suc zero) m A (fst₁ , snd₁)) bdN@(lid true []) (inside i ∷ cuM) = snd₁ cuM i i1

-- -- fst (SplitVecBdIns-step→ (suc (suc n)) m A (fst₁ , snd₁)) (lid x₁ x₂) (end x ∷ cuM) = {!!}
-- -- fst (SplitVecBdIns-step→ (suc (suc n)) m A (fst₁ , snd₁)) (cyl x₁ i) (end x ∷ cuM) = {!!}
-- -- fst (SplitVecBdIns-step→ (suc (suc n)) m A (fst₁ , snd₁)) (lid x x₁) (inside i ∷ cuM) = {!!}
-- -- fst (SplitVecBdIns-step→ (suc (suc n)) m A (fst₁ , snd₁)) (cyl x i₁) (inside i ∷ cuM) = {!!}

-- fst (SplitVecBdIns-step→ (suc zero) m A (fst₁ , snd₁)) (lid false []) (end false ∷ cuM) = fst₁ (cylEx i0 (lid false [])) cuM
-- fst (SplitVecBdIns-step→ (suc zero) m A (fst₁ , snd₁)) (lid true []) (end false ∷ cuM) = fst₁ (cylEx i0 (lid true [])) cuM
-- fst (SplitVecBdIns-step→ (suc zero) m A (fst₁ , snd₁)) (lid false []) (end true ∷ cuM) = fst₁ (cylEx i1 (lid false [])) cuM
-- fst (SplitVecBdIns-step→ (suc zero) m A (fst₁ , snd₁)) (lid true []) (end true ∷ cuM) = fst₁ (cylEx i1 (lid true [])) cuM
-- fst (SplitVecBdIns-step→ (suc zero) m A (fst₁ , snd₁)) (lid false []) (inside i ∷ cuM) = fst₁ (cylEx i (lid false [])) cuM
-- fst (SplitVecBdIns-step→ (suc zero) m A (fst₁ , snd₁)) (lid true []) (inside i ∷ cuM) = fst₁ (cylEx i (lid true [])) cuM

-- snd (SplitVecBdIns-step→ (suc zero) m A (fst₁ , snd₁)) (end false ∷ cuM) = snd₁ cuM i0
-- snd (SplitVecBdIns-step→ (suc zero) m A (fst₁ , snd₁)) (end true ∷ cuM) = snd₁ cuM i1
-- snd (SplitVecBdIns-step→ (suc zero) m A (fst₁ , snd₁)) (inside i ∷ cuM) = snd₁ cuM i

-- fst (SplitVecBdIns-step→ (suc (suc n)) m A x) bdN (end x₁ ∷ cuM) = {!!}
-- fst (SplitVecBdIns-step→ (suc (suc n)) m A (fst₁ , snd₁)) bd (inside i ∷ cuM) = {!(fst₁ (cyl bd i)  cuM)!}
-- snd (SplitVecBdIns-step→ (suc (suc n)) m A x) (end x₁ ∷ cuM) = {!!}
-- snd (SplitVecBdIns-step→ (suc (suc n)) m A (fst₁ , snd₁)) (inside i ∷ cuM) = {!snd₁ cuM i!}







-- -- Impos : ∀ n → NCube n → Type₀
-- -- Impos n x = Σ (NBoundary n) (λ bd → boundaryInj bd ≡ x)

-- -- impos : ∀ n → ∀ cu → Impos n cu
-- -- impos zero cu₁ = {!!}
-- -- impos (suc zero) (end false ∷ []) = (lid false []) , refl
-- -- impos (suc zero) (end true ∷ []) = lid false [] , λ i → inside i ∷ []
-- -- fst (impos (suc zero) (inside i ∷ [])) = (lid false []) 
-- -- snd (impos (suc zero) (inside i ∷ [])) = {!!}
-- -- impos (suc (suc n)) (x ∷ cu₁) = {!!}


-- -- appAtSnd : ∀ {ℓ} → ∀ n → (A : NCube (suc (suc n)) → Type ℓ)
-- --             → (bd : ∀ x → (A ∘ boundaryInj) x )
-- --               → InsideOfP A bd
-- --               → (i : I)
-- --               → InsideOfP (λ x → A (head x ∷ (inside i) ∷ tail x ))
-- --                            λ x → bd (cyl'' {!x!} {!!})
-- -- appAtSnd = {!!}



-- -- InsideOf→InsideOfω-L' : ∀ {ℓ} → ∀ {n} → {A : NCube (suc n) → Type ℓ}
-- --                      → (bd : ∀ x → (A ∘ boundaryInj) x )
-- --                      → InsideOfP {n = n}
-- --                         (PathCu A
-- --                           (fst (fst (Iso.fun (NBoundaryP-rec-Iso {A = A}) bd)))
-- --                           (snd (fst (Iso.fun (NBoundaryP-rec-Iso {A = A}) bd)))
-- --                             )
-- --                           (CylΣ-squash n A
-- --                               (fst (fst (Iso.fun (NBoundaryP-rec-Iso {A = A}) bd)))
-- --                               ((snd (fst (Iso.fun (NBoundaryP-rec-Iso {A = A}) bd))))
-- --                               ((snd (Iso.fun (NBoundaryP-rec-Iso {A = A}) bd))))
-- --                       → (Σ (Σ (NCube (suc n) → Type ℓ) (λ v → (x : NBoundary (suc n)) → v (boundaryInj x)))
-- --                           λ xx → InsideOfP {n = suc n} (fst xx) (snd xx))
-- -- InsideOf→InsideOfω-L' {n = zero} bd x = ({!!} , {!!}) , x
-- -- InsideOf→InsideOfω-L' {n = suc zero} bd x = ({!!} , {!!}) , x
-- -- InsideOf→InsideOfω-L' {n = suc (suc zero)} bd x = ({!!} , {!!}) , x

-- -- InsideOf→InsideOfω-L' {n = suc (suc (suc zero))} {A = A} bd x =
-- --    (A'
-- --    ,
-- --     Isoω.from (NBoundary-Boundaryω-Isoω (suc (suc (suc (suc zero)))) A') zz
-- --    ) , λ i i₁ i₂ i₃ → x i i₁ i₂ i₃

-- --    where
-- --      A' : NCube 4 → Type _
-- --      A' (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) = A (x₃ ∷ x ∷ x₁ ∷ x₂ ∷ [])

-- --      zz : T[ Boundaryω 4 Ct[ 4 , A' ] ]
-- --      zz i i₁ i₂ i₃ x =
-- --         (Isoω.to (NBoundary-Boundaryω-Isoω (suc (suc (suc (suc zero)))) A) bd) i₃ i i₁ i₂ x

-- -- InsideOf→InsideOfω-L' {n = suc (suc (suc (suc n)))} bd x = {!!} , {!!}


-- InsideOf→InsideOfω-L : ∀ {ℓ} → ∀ {n} → {A : NCube (suc n) → Type ℓ}
--                      → (bd : ∀ x → (A ∘ boundaryInj) x )
--                      → (ins : InsideOfP {n = suc n}  A bd)
--                      → InsideOfP {n = n}
--                         (PathCu A
--                           (fst (fst (Iso.fun (NBoundaryP-rec-Iso {A = A}) bd)))
--                           (snd (fst (Iso.fun (NBoundaryP-rec-Iso {A = A}) bd)))
--                           )
--                           (CylΣ-squash n A
--                               (fst (fst (Iso.fun (NBoundaryP-rec-Iso {A = A}) bd)))
--                               ((snd (fst (Iso.fun (NBoundaryP-rec-Iso {A = A}) bd))))
--                               ((snd (Iso.fun (NBoundaryP-rec-Iso {A = A}) bd))))
-- InsideOf→InsideOfω-L {ℓ} {zero} {A} bd ins = ins
-- InsideOf→InsideOfω-L {ℓ} {suc zero} {A} bd ins i i₁ = ins i₁ i
-- InsideOf→InsideOfω-L {ℓ} {suc (suc zero)} {A} bd ins i i₁ i₂ = ins i₂ i i₁
-- -- InsideOf→InsideOfω-L {ℓ} {suc (suc (suc zero))} {A} bd ins i i₁ i₂ i₃ = ins i₃ i i₁ i₂
-- -- InsideOf→InsideOfω-L {ℓ} {suc (suc (suc (suc zero)))} {A} bd ins i i₁ i₂ i₃ i₄ = ins i₄ i i₁ i₂ i₃
-- -- InsideOf→InsideOfω-L {ℓ} {suc (suc (suc (suc (suc n))))} {A} bd ins i i₁ = {!!}
-- InsideOf→InsideOfω-L {ℓ} {suc (suc (suc n))} {A} bd ins l l₁ = 
--   let z : PathP {!!} {!!} (InsideOf→InsideOfω-L (λ x → _) _)
--       z i = InsideOf→InsideOfω-L {ℓ} {suc (suc n)} {λ x → A (head x ∷ inside i ∷ tail x)}
--                         (λ x → (bd ∘ {!!}) (boundaryInj x)) (λ i₁ → ins i₁ i)

--       w : (i j : I) → PathP {!_!} _ _
--       w i j = InsideOf→InsideOfω-L {ℓ} {suc n} {A = λ x → A (inside i ∷ (inside j) ∷ x)} (bd ∘ cylEx i ∘ cylEx j) (ins i j)

--       w' : (i : I) → PathP {!_!} _ _
--       w' i = InsideOf→InsideOfω-L {ℓ} {suc (suc n)} {A = λ x → A (inside i ∷ x)} (bd ∘ cylEx i) (ins i)

--       ww : {!!}
--       ww = {!w' l  !}
--   in ww


--   -- let z : PathP (λ z →
--   --                   InsideOfP
--   --                   (PathCu (λ x → _)
--   --                    (fst (fst (Iso.fun NBoundaryP-rec-Iso (λ x → {!!}))))
--   --                    (snd (fst (Iso.fun NBoundaryP-rec-Iso (λ x → _))))
--   --                    i∷ z)
--   --                   (λ x →
--   --                      CylΣ-squash (suc n) (λ x₁ → _)
--   --                      (fst (fst (Iso.fun NBoundaryP-rec-Iso (λ x₁ → _))))
--   --                      (snd (fst (Iso.fun NBoundaryP-rec-Iso (λ x₁ → _))))
--   --                      (snd (Iso.fun NBoundaryP-rec-Iso (λ x₁ → _))) (cylEx z x)))

--   --                          ((insideOfP
--   --                           (λ x →
--   --                              CylΣ-squash (suc (suc n)) A
--   --                              (fst (fst (Iso.fun NBoundaryP-rec-Iso bd)))
--   --                              (snd (fst (Iso.fun NBoundaryP-rec-Iso bd)))
--   --                              (snd (Iso.fun NBoundaryP-rec-Iso bd)) (cylEx i (lid false x)))))

--   --                          (insideOfP
--   --                           (λ x →
--   --                              CylΣ-squash (suc (suc n)) A
--   --                              (fst (fst (Iso.fun NBoundaryP-rec-Iso bd)))
--   --                              (snd (fst (Iso.fun NBoundaryP-rec-Iso bd)))
--   --                              (snd (Iso.fun NBoundaryP-rec-Iso bd)) (cylEx i (lid true x))))
--   --     z i₁ = InsideOf→InsideOfω-L {ℓ} {suc n} {λ x → {!!}}
--   --          ((λ x i₂ → bd (cyl (cyl (cyl x i₁) i) i₂)))
--   --          (ins i) i₁
--   -- in z

-- InsideOf→InsideOfω-R : ∀ {ℓ} → ∀ {n} → {A : NCube (suc n) → Type ℓ}
--                      → (bd : ∀ x → (A ∘ boundaryInj) x )
--                      → T[ InsideOfω n (
--                             Isoω.to (NBoundary-Boundaryω-Isoω n
--                             (PathCu A
--                               (fst (fst (Iso.fun (NBoundaryP-rec-Iso {A = A}) bd)))
--                               (snd (fst (Iso.fun (NBoundaryP-rec-Iso {A = A}) bd)))
--                             )
--                             ) ((CylΣ-squash n A
--                               (fst (fst (Iso.fun (NBoundaryP-rec-Iso {A = A}) bd)))
--                               ((snd (fst (Iso.fun (NBoundaryP-rec-Iso {A = A}) bd))))
--                               ((snd (Iso.fun (NBoundaryP-rec-Iso {A = A}) bd)))))
--                              ) ]
--                      → T[ InsideOfω (suc n) (
--                             Isoω.to (NBoundary-Boundaryω-Isoω (suc n) A) bd
--                              ) ]

-- InsideOf→InsideOfω-R = {!!}


-- InsideOf→InsideOfω : ∀ {ℓ} → ∀ {n} → {A : NCube n → Type ℓ}
--                      → (bd : ∀ x → (A ∘ boundaryInj) x )
--                      → (InsideOfP A bd)
--                      → T[ InsideOfω n (
--                             Isoω.to (NBoundary-Boundaryω-Isoω n A) bd
--                              ) ]

-- InsideOf→InsideOfω {n = zero} bd x = inS x
-- InsideOf→InsideOfω {n = suc n} bd x =
--     InsideOf→InsideOfω-R {n = n} bd (InsideOf→InsideOfω {n = n}
--       _ (InsideOf→InsideOfω-L bd x))



-- -- InsideOf→InsideOfω {n = suc zero} {A = A} bd x i = inS (x i)

-- -- -- InsideOf→InsideOfω {n = suc (suc zero)} {A = A} bd x i i₁ = inS (x i i₁)
-- -- -- InsideOf→InsideOfω {n = suc (suc (suc zero))} {A = A} bd x i i₁ i₂ = inS (x i i₁ i₂)
-- -- -- InsideOf→InsideOfω {n = suc (suc (suc (suc n)))} {A = A} bd x i i₁ i₂ = {!!}

-- -- InsideOf→InsideOfω {n = (suc (suc n))} {A = A} bd x i = 
-- --  let z = InsideOf→InsideOfω {n = (suc n)} {A = A i∷ i} (bd ∘ cylEx i) (x i) 
-- --  in {!Subⁿ-squash-Bd (suc n) A!}
-- -- -- InsideOf→InsideOfω {n = suc (suc n)} bd x i = {!x!}



-- InsideOfω→InsideOf : ∀ {ℓ} → ∀ {n} → {A : NCube n → Type ℓ}
--                      → (bd : ∀ x → (A ∘ boundaryInj) x )
--                      → T[ InsideOfω n (Isoω.to (NBoundary-Boundaryω-Isoω n A) bd) ]
--                      → (InsideOfP A bd)
-- InsideOfω→InsideOf {n = zero} bd x = outS x
-- InsideOfω→InsideOf {n = suc n} {A = A} bd x i =
--    {!!}
-- -- -- InsideOfω→InsideOf {n = suc (suc zero)} {A = A} bd x i i₁ = outS (x i i₁)
-- -- -- InsideOfω→InsideOf {n = suc (suc (suc zero))} {A = A} bd x i i₁ i₂ = outS (x i i₁ i₂)
-- -- -- InsideOfω→InsideOf {n = suc (suc (suc (suc n)))} {A = A} bd x i i₁ = {!!}
-- -- InsideOfω→InsideOf {n = suc (suc n)} {A = A} bd x =
-- --   let z : (i : I) → {!!}
-- --       z i = Subⁿ-squash-Bd (suc n) A {!!} {!!} {!!} {!x i!}

-- -- --InsideOfω→InsideOf {n = suc n} {A = λ v → {!!}} (bd ∘ cylEx i) {!x i!}
  
-- --       w : PathP (λ i → InsideOfP (A i∷ i) (bd ∘ cylEx i))
-- --               ((λ i → insideOfP ((λ x₁ → bd (lid false x₁)) i∷ i)))
-- --                (λ i → insideOfP (λ x₁ → bd (lid true (inside i ∷ x₁))))
-- --       w j = {!!}

-- --       qq : (i : I) → InsideOfP (A i∷ i) (bd ∘ cylEx i)
-- --       qq = {!!}

  

-- -- -- hcompIns : ∀ {ℓ} → ∀ {n} → {A : NCube n → Type ℓ}
-- -- --            → (sides : I → (x : NBoundary n) → (A ∘ boundaryInj) x)
-- -- --            → InsideOfP A (sides i0)
-- -- --            → InsideOfP A (sides i1)
-- -- -- hcompIns {n = n} {A} sides x =
-- -- --   let z = hcompⁿ n (λ j → Isoω.to (NBoundary-Boundaryω-Isoω n A) (sides j)) (InsideOf→InsideOfω (sides i0) x)
-- -- --   in InsideOfω→InsideOf (sides i1) z


-- -- -- hfillIns : ∀ {ℓ} → ∀ {n} → {A : NCube n → Type ℓ}
-- -- --            → (sides : I → (x : NBoundary n) → (A ∘ boundaryInj) x)
-- -- --            → InsideOfP A (sides i0)
-- -- --            → (i : I) → InsideOfP A (sides i)
-- -- -- hfillIns {n = n} {A} sides x i =
-- -- --   let z = hfillⁿ n (λ j → Isoω.to (NBoundary-Boundaryω-Isoω n A) (sides j)) (InsideOf→InsideOfω (sides i0) x) i
-- -- --   in InsideOfω→InsideOf (sides i) z

-- -- -- hfillIns≡ : ∀ {ℓ} → ∀ {n} → {A : NCube n → Type ℓ}
-- -- --            → (sides : I → (x : NBoundary n) → (A ∘ boundaryInj) x)
-- -- --            → (x : InsideOfP A (sides i0))
-- -- --            → PathP (λ i → InsideOfP A (sides i)) x (hcompIns sides x)
-- -- -- hfillIns≡ {n = n} {A} sides x i = {!!}


-- -- -- hcomp-Iso' : ∀ {ℓ} → ∀ {n} → {A : NCube n → Type ℓ} →
-- -- --                 (sides : I → (x : NBoundary n) → (A ∘ boundaryInj) x)
-- -- --                 → Iso (InsideOfP A (sides i0))
-- -- --                       (InsideOfP A (sides i1))
-- -- -- Iso.fun (hcomp-Iso' sides) = hcompIns sides
-- -- -- Iso.inv (hcomp-Iso' sides) = hcompIns λ i → sides (~ i)
-- -- -- Iso.rightInv (hcomp-Iso' sides) b i = {!!}
-- -- -- Iso.leftInv (hcomp-Iso' sides) a i = {!hfillIns ? ?!}


-- -- -- hcomp-Iso : ∀ {ℓ} → ∀ {n} → {A : NCube n → Type ℓ} →
-- -- --                 Iso (∀ x → A x)
-- -- --                     (Σ _ (InsideOfP A) )
-- -- -- hcomp-Iso = {!!}
