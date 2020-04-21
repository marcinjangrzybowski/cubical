{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.NCube.CubeIn where


open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Prod
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.NCube.Base


NCubeIn : ∀ {ℓ} → (A : Type ℓ) → ℕ → Type ℓ  
NCubeIn A n = NCube n → A

NBorderIn : ∀ {ℓ} → (A : Type ℓ) → ℕ → Type ℓ  
NBorderIn A n = NBorder n → A 

InsideOf : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → NBorderIn A n → Type ℓ
InsideOf {A = A} {n = n} bd = Σ _ λ nci → nci ∘ boundaryMap ≡ bd 

nBorderEnd : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → Bool → NBorderIn A (suc n) → NBorderIn A n
nBorderEnd b bd = bd ∘ borderEndMap b

nBorderFaceBorder : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                     → ℕ → Bool
                     →  NBorderIn A (suc n)
                     →  NBorderIn A n
nBorderFaceBorder k b = _∘ (faceMap k b) ∘ boundaryMap 


nBorderEndsPath :  ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                     → (bd : NBorderIn A (suc n)) 
                     → nBorderEnd false bd ≡ nBorderEnd true bd 
nBorderEndsPath bd i = bd ∘ cylEx i

InsideOf-0 : ∀ {ℓ} → {A : Type ℓ} → ∀ {bd : NBorderIn A 0}  → A → InsideOf bd
fst (InsideOf-0 x) _ = x
snd (InsideOf-0 x) i ()

nBorderLid : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                     → (b : Bool) → (bd : NBorderIn A (suc n))
                     → InsideOf (nBorderEnd b bd)
fst (nBorderLid b bd) = bd ∘ lid b
snd (nBorderLid b bd) = refl

nBorderFace : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                     → (k : ℕ) → (b : Bool) → (bd : NBorderIn A (suc n))
                     → InsideOf (nBorderFaceBorder k b bd)
fst (nBorderFace k b bd) = bd ∘ (faceMap k b)
snd (nBorderFace k b bd) = refl



InsideOfP : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → NBorderIn A n → Type ℓ
InsideOfP {A = A} {n = zero} _ = A
InsideOfP {A = A} {n = suc n} bd =
             PathP
             (λ i → InsideOf ((nBorderEndsPath bd i)))
             (nBorderLid false bd)
             (nBorderLid true bd)




insideOfToP : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ∀ {bd : NBorderIn A n}
                 → InsideOf bd → InsideOfP bd
insideOfToP {n = zero} (c , _) = c _
insideOfToP {n = suc n} {bd = bd} (c , match) i =
     (((λ i₁ → λ x → match (~ i₁) (lid false x)))
       ∙∙ (λ j → (λ x → c (inside j , x)))
       ∙∙ (λ i₁ → λ x → match i₁ (lid true x))) i
      ,
      
      λ i₁ x → hcomp
         (λ k → λ {
            (i = i0) → (match (i₁ ∨ k) (lid false (boundaryMap x)))
          ; (i = i1) → (match (i₁ ∨ k) (lid true (boundaryMap x)))
          ; (i₁ = i1) → bd (cyl x i)
         })
        ((match i₁ (cyl x i)))


insideOfFromP : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ∀ {bd : NBorderIn A n}
                 → InsideOfP bd → InsideOf bd
insideOfFromP {n = zero} = InsideOf-0
fst (insideOfFromP {n = suc n} x) (end x₁ , x₂) = fst (x (Bool→I x₁)) x₂
fst (insideOfFromP {n = suc n} x) (inside i , x₂) = fst (x i) x₂
snd (insideOfFromP {n = suc n} {bd} x) i (lid false x₂) = bd (lid false x₂)
snd (insideOfFromP {n = suc n} {bd} x) i (lid true x₂) = bd (lid true x₂)
snd (insideOfFromP {n = suc n} x) i (cyl x₁ i₁) = snd (x i₁) i x₁


nBorderLidP : ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                     → (b : Bool) → (bd : NBorderIn A (suc n))
                     → InsideOfP (nBorderEnd b bd)
nBorderLidP b =  insideOfToP ∘ nBorderLid b




cutoff : ℕ → Type₀
cutoff (suc (suc (suc (suc (suc (suc n)))))) = ⊥
cutoff _ = Unit

cutoff-weak : ∀ {n} → cutoff (suc n) → cutoff n  
cutoff-weak {suc (suc (suc (suc (suc n))))} ()
cutoff-weak {zero} x = _
cutoff-weak {suc zero} x = _
cutoff-weak {suc (suc zero)} x = _
cutoff-weak {suc (suc (suc zero))} x = _
cutoff-weak {suc (suc (suc (suc zero)))} x = _

InsideOfP' : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → cutoff n → NBorderIn A n → Type ℓ


nBorderLidP' : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → (ctf : cutoff n)
                     → (s : Bool) → (bd : NBorderIn A (suc n))
                     → InsideOfP' ctf (λ x → bd (lid s (boundaryMap x)))

InsideOfP' {A = A} {n = zero} ctf _ = A
InsideOfP' {A = A} {n = suc n} ctf bd =
             PathP
             (λ i → InsideOfP' (cutoff-weak ctf) (nBorderEndsPath bd i))
             (nBorderLidP' (cutoff-weak ctf) false bd)
             (nBorderLidP' (cutoff-weak ctf) true  bd)

nBorderLidP' {n = zero} ctf s bd = bd (lid s _)
nBorderLidP' {n = suc zero} ctf s bd i = bd (lid s ((inside i) , _))
nBorderLidP' {n = suc (suc zero)} ctf s bd i i₁ = bd (lid s ((inside i) , (inside i₁) , _))
nBorderLidP' {n = suc (suc (suc zero))} ctf s bd i i₁ i₂ =
                                           bd (lid s ((inside i) , (inside i₁) , (inside i₂) , _))
nBorderLidP' {n = suc (suc (suc (suc zero)))} ctf s bd i i₁ i₂ i₃ =
                             bd (lid s ((inside i) , (inside i₁) , (inside i₂) ,  (inside i₃) , _))
nBorderLidP' {n = suc (suc (suc (suc (suc zero))))} ctf s bd i i₁ i₂ i₃ i₄ =
                 bd (lid s ((inside i) , (inside i₁) , (inside i₂) ,  (inside i₃) , (inside i₄) , _))






insideOfTo≡ :  ∀ {ℓ : Level} → {A : Type ℓ} → ∀ {bd : NBorderIn A 1}
                 → InsideOf bd →
                   _≡_ {A = Σ ((b : NCube 0) → A)
                     (λ nci → (Cubical.Data.Empty.elim {A = λ _ → A})
                             ≡ Cubical.Data.Empty.elim {A = λ _ → A} )}
                     (fst (nBorderLid false bd) , refl)
                     (fst (nBorderLid true bd) , refl)   
insideOfTo≡ x i = fst (insideOfToP x i) , refl
 

-- insideOfIso : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → ∀ {bd : NBorderIn A n}
--                  → Iso (InsideOf bd) (InsideOfP bd)
-- Iso.fun insideOfIso = insideOfToP
-- Iso.inv insideOfIso = insideOfFromP
-- Iso.rightInv (insideOfIso {n = zero}) b = refl
-- fst (Iso.rightInv (insideOfIso {n = suc n} {bd}) b i i₁) x =
--                doubleCompPath-filler
--                (λ _ → bd (lid false x))
--                (λ j → fst (b j) x ) 
--                (λ _ → bd (lid true x))
--                (~ i) i₁
               
-- snd (Iso.rightInv (insideOfIso {n = suc n}) b i i₁) i₂ x =
--    {!!}
-- fst (Iso.leftInv (insideOfIso {n = zero}) a i) _ = fst a _
-- snd (Iso.leftInv (insideOfIso {n = zero}) a i) i₁ ()
-- fst (Iso.leftInv (insideOfIso {n = suc n}) a i) (end x , x₁) = {!!}
-- fst (Iso.leftInv (insideOfIso {n = suc n}) a i) (inside i₁ , x₁) = {!!}
-- snd (Iso.leftInv (insideOfIso {n = suc n}) a i) = {!!}

asembleBorder :  ∀ {ℓ} → {A : Type ℓ} → ∀ {n}
                  → (ends : Bool → NCubeIn A n)
                  → PathP (λ x → NBorderIn A n)
                    (ends false ∘ boundaryMap)
                    (ends true ∘ boundaryMap)
                   → NBorderIn A (suc n)
asembleBorder ends x (lid x₁ x₂) = ends x₁ x₂
asembleBorder ends x (cyl x₁ i) = (x i) x₁

nCubeFromPath : ∀ {ℓ} → {A : Type ℓ} → ∀ {n} → (I → NCubeIn A n) → NCubeIn A (suc n)  
nCubeFromPath x (end x₁ , x₂) = x (Bool→I x₁) x₂ 
nCubeFromPath x (inside i , x₂) = x i x₂



makeSquareBorder :
   ∀ {ℓ} → {A : Type ℓ} →
   {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
   {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
   (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
    →  NBorderIn A 2
makeSquareBorder a₀₋ a₁₋ a₋₀ a₋₁ =
  asembleBorder
   (caseBool (nCubeFromPath λ x → λ _ → a₁₋ x) (nCubeFromPath λ x → λ _ → a₀₋ x))
   c
   
   where

   c : _
   c i (lid false x₁) = a₋₀ i
   c i (lid true x₁) = a₋₁ i
   c i (cyl () j)



Square' : ∀ {ℓ} → {A : Type ℓ} →  NBorderIn A 2 → Type ℓ
Square' bd =
     Square 
       (insideOfTo≡ (nBorderFace 0 false bd))
       (insideOfTo≡ (nBorderFace 0 true bd))
       (insideOfTo≡ (nBorderFace 1 false bd))
       (insideOfTo≡ (nBorderFace 1 true bd))



squareIso :
     ∀ {ℓ} → {A : Type ℓ} →
    {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
    {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
    (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
     → Iso
       (Square a₀₋ a₁₋ a₋₀ a₋₁)
       (InsideOfP (makeSquareBorder  a₀₋ a₁₋ a₋₀ a₋₁))
squareIso a₀₋ a₁₋ a₋₀ a₋₁ =
     iso fun inv rightInv leftInv
  where

     bd : _
     bd = (makeSquareBorder a₀₋ a₁₋ a₋₀ a₋₁)

     fun : _
     fst (fun x i) = nCubeFromPath (λ x₁ _ → (x i) x₁)
     snd (fun x i) _ (lid false x₂) =  a₋₀ i
     snd (fun x i) _ (lid true x₂) = a₋₁ i

     invFill : InsideOfP bd →
                   I → I → I → _
     invFill x z i j = 
        hfill (λ k → λ {
              (i = i0) → a₀₋ j  
            ; (i = i1) → a₁₋ j 
            ; (j = i0) → snd (x i) k (lid false _) 
            ; (j = i1) → snd (x i) k (lid true _)
              } )
            (inS (fst (x i) (inside j , _))) (~ z)
            
     inv : InsideOfP bd →
             Square a₀₋ a₁₋ a₋₀ a₋₁
     inv x i j = invFill x i0 i j

     z : _ → InsideOf bd
     z b = insideOfFromP b

     rightInv : _
     fst (rightInv x i i₁) (end false , x₁) = invFill x i i₁ i0
     fst (rightInv x i i₁) (end true , x₁) = invFill x i i₁ i1 
     
     snd (rightInv x i i₁) i₂ (lid false x₂) = (snd (z x)) ((i₂) ∨ (~ i)) (cyl (lid false _) i₁)
     snd (rightInv x i i₁) i₂ (lid true x₂) = (snd (z x)) ((i₂) ∨ (~ i)) (cyl (lid true _) i₁)

     fst (rightInv x i i₁) (inside i₂ , x₁) = invFill x i i₁ i₂
     
     leftInv : _
     leftInv a z i j =
            hcomp
             (λ k → λ {
                     (i = i0) → a i0 j
                   ; (i = i1) → a i1 j
                   ; (j = i0) → a i i0
                   ; (j = i1) → a i i1
                   ; (z = i1) → (a i j)
               })
             (a i j)


-- makeCubeBorder :
--    ∀ {ℓ} → {A : Type ℓ} →
--   {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
--   {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
--   {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
--   (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
--   {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
--   {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
--   {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
--   (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
--   {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
--   (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
--   {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
--   (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
--   (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
--   (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
--     →  NBorderIn A 3
-- makeCubeBorder  a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ = 
--   asembleBorder
--    (caseBool
--       (fst lid1)
--       (fst lid0)
--      )
--    ((snd lid0)
--     ∙∙
--     (λ i → makeSquareBorder  (a₋₀₋ i) (a₋₁₋ i) (a₋₋₀ i) ((a₋₋₁ i)))
--     ∙∙ sym (snd lid1))
   
--    where

--    lid0 : _
--    lid0 = (insideOfFromP (Iso.fun (squareIso _ _ _ _) a₀₋₋))


--    lid1 :  _
--    lid1 = (insideOfFromP (Iso.fun (squareIso _ _ _ _) a₁₋₋))

makeCubeBorder :
   ∀ {ℓ} → {A : Type ℓ} →
  {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
  {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
  {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
  (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
  {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
  {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
  {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
  (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
  {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
  (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
  {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
  (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
  (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
  (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
    →  NBorderIn A 3
makeCubeBorder  a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ = 
  asembleBorder
   (caseBool
      (fst lid1)
      (fst lid0)
     )
   ((snd lid0)
    ∙∙
    (λ i → makeSquareBorder  (a₋₀₋ i) (a₋₁₋ i) (a₋₋₀ i) ((a₋₋₁ i)))
    ∙∙ sym (snd lid1))
   
   where

   lid0 : _
   lid0 = (insideOfFromP (Iso.fun (squareIso _ _ _ _) a₀₋₋))


   lid1 :  _
   lid1 = (insideOfFromP (Iso.fun (squareIso _ _ _ _) a₁₋₋))


-- cubeIso :
--    ∀ {ℓ} → {A : Type ℓ} →
--   {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
--   {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
--   {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
--   (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
--   {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
--   {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
--   {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
--   (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
--   {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
--   (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
--   {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
--   (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
--   (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
--   (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
--      → Iso
--        (Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁)
--        (InsideOfP' _ (makeCubeBorder  a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁))
-- Iso.fun (cubeIso a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁) x = {!!}
-- Iso.inv (cubeIso a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁) = {!!}
-- Iso.rightInv (cubeIso a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁) = {!!}
-- Iso.leftInv (cubeIso a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁) = {!!}



-- -- cubeIso :
-- --    ∀ {ℓ} → {A : Type ℓ} →
-- --   {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
-- --   {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
-- --   {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
-- --   (a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁)
-- --   {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
-- --   {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
-- --   {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
-- --   (a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁)
-- --   {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
-- --   (a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁)
-- --   {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
-- --   (a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁)
-- --   (a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀)
-- --   (a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁)
-- --      → Iso
-- --        (Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁)
-- --        (InsideOfP (makeCubeBorder  a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁))
-- -- cubeIso a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ =     
-- --      iso fun inv rightInv leftInv
-- --   where

-- --      bd : _
-- --      bd = (makeCubeBorder  a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁)

-- --      fun : _     
-- --      fst (fun x i) (end false , x₂) = nCubeFromPath (λ x₁ _ → a₋₀₋ i x₁) x₂
-- --      fst (fun x i) (end true , x₂) = nCubeFromPath (λ x₁ _ → a₋₁₋ i x₁) x₂
-- --      fst (fun x i) (inside i₁ , x₂) = nCubeFromPath (λ x₁ _ → x i i₁ x₁) x₂
-- --      snd (fun x i) i₁ (lid false (end x₁ , x₂)) = {!!}
-- --      snd (fun x i) i₁ (lid false (inside i₂ , x₂)) = {!!}
-- --      snd (fun x i) i₁ (lid true (end x₁ , x₂)) = {!!}
-- --      snd (fun x i) i₁ (lid true (inside i₂ , x₂)) = {!!}
-- --      snd (fun x i) i₁ (cyl (lid false x₂) i₂) = {!!}
-- --      snd (fun x i) i₁ (cyl (lid true x₂) i₂) = {!!}
-- --        -- nCubeFromPath (λ x₁ _ → a₋₋₁ i i₂) ((end true) , {!_!})

-- --      invFill : InsideOfP bd →
-- --                  I → I → I → I → _              
-- --      invFill x z i j l = 
-- --         hfill (λ k → λ {
-- --               (i = i0) → a₀₋₋ j l  
-- --             ; (i = i1) → a₁₋₋ j l 
-- --             ; (j = i0) → {!!}
-- --             ; (j = i1) → {!!}
-- --             ; (l = i0) → {!!} 
-- --             ; (l = i1) → {!!}
-- --               } )
-- --             (inS (fst (x i) ((inside j) , ((inside l) , _)) )) (~ z)
            
-- --      inv : _
-- --      inv x i j l = invFill x i0 i j l

-- --      z : _ → InsideOf bd
-- --      z b = insideOfFromP b

-- --      rightInv : _
-- --      fst (rightInv x i i₁) (end false , (end false , _)) = invFill x i i₁ i0 i0
-- --      fst (rightInv x i i₁) (end false , (end true , _)) = invFill x i i₁ i0 i1
-- --      fst (rightInv x i i₁) (end false , (inside i₂ , _)) = invFill x i i₁ i0 i₂
-- --      fst (rightInv x i i₁) (end true , (end false , _)) = invFill x i i₁ i1 i0
-- --      fst (rightInv x i i₁) (end true , (end true , _)) = invFill x i i₁ i1 i1
-- --      fst (rightInv x i i₁) (end true , (inside i₂ , _)) = invFill x i i₁ i1 i₂
-- --      fst (rightInv x i i₁) (inside i₂ , (end false , x₁)) = invFill x i i₁ i₂ i0
-- --      fst (rightInv x i i₁) (inside i₂ , (end true , x₁)) = invFill x i i₁ i₂ i1
-- --      fst (rightInv x i i₁) (inside i₂ , (inside i₃ , _)) = invFill x i i₁ i₂ i₃
-- --      snd (rightInv x i i₁) = {!!}
     
-- --      leftInv : _
-- --      leftInv a z i j l =
-- --             hcomp
-- --              (λ k → λ {
-- --                      (i = i0) → a i0 j l
-- --                    ; (i = i1) → a i1 j l
-- --                    ; (j = i0) → a i i0 l
-- --                    ; (j = i1) → a i i1 l
-- --                    ; (l = i0) → a i j i0
-- --                    ; (l = i1) → a i j i1
-- --                    ; (z = i1) → (a i j l)
-- --                })
-- --              (a i j l)
