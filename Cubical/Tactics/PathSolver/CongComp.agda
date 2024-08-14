{-# OPTIONS --safe #-} 
module Cubical.Tactics.PathSolver.CongComp where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.List as L
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sigma


import Agda.Builtin.Reflection as R

open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Dimensions
open import Cubical.Tactics.Reflection.CuTerm


-- TODO : test this
normal𝑪ong* : R.Term → List CuTerm → (R.Term × List (List (SubFace × CuTerm) × CuTerm)) 
normal𝑪ong* t xs = h 200 0  t xs
 where
 h : ℕ → ℕ → R.Term → List CuTerm → (R.Term × List (List (SubFace × CuTerm) × CuTerm))
 h _ k t [] = t , []
 h fuel k t ((hco x y) ∷ xs) =
  let (t' , xs') = h fuel (suc k) t (xs)
  in t' , (x , y) ∷ xs'
 h fuel k t (cell' x x₁ ∷ xs) =
  let t' = replaceAtTrm k (liftVarsFrom (suc (k + length xs)) zero  x₁) t
  in h fuel k t' xs
 h _ k t (𝒄ong' x x₁ ∷ xs) = R.lit (R.string "imposible in normal𝑪ong*") , [] 

normal𝑪ong : R.Term → List CuTermNC → (R.Term × List (List (SubFace × CuTermNC) × CuTermNC)) 
normal𝑪ong t xs = h 200 0  t xs
 where
 h : ℕ → ℕ → R.Term → List CuTermNC → (R.Term × List (List (SubFace × CuTermNC) × CuTermNC)) 
 h _ k t [] = t , []
 h fuel k t ((hco x y) ∷ xs) =
  let (t' , xs') = h fuel (suc k) t (xs)
  in t' , (x , y) ∷ xs'
 h fuel k t (cell' x x₁ ∷ xs) =
  let t' = replaceAtTrm k (liftVarsFrom (suc (k + length xs)) zero  x₁) t
  in h fuel k t' xs
 h zero _ _ _ = R.lit (R.string "out of fuel in normal𝑪ong") , [] 

getSide : ∀ {A} → SubFace → List (SubFace × CuTerm' A Unit) → CuTerm' A Unit → CuTerm' A Unit
getSide {A = A}  sf l y = 
 Mb.rec
   ((let msf : SubFace × CuTerm' A Unit → Maybe (SubFace × CuTerm' A Unit)
         msf = λ (sf' , t) →
                map-Maybe
                 (λ sf'' → (injSF sf sf'') , cuEval (nothing  ∷ (injSF sf' sf'')) t)
                 (sf' sf∩ sf) 
         l' = L.catMaybes (L.map msf l)
         y' = (cuEval sf y)
     in cell (R.lit (R.string "todo in getSide")) )
       )
   ((λ (sf' , f) → f))
  (findBy (⊂⊃? ∘S (sf <sf>_) ∘S fst) l)



module appCongs where


 cuCong1 : R.Term → CuTermNC → CuTermNC 
 cuCong1L : R.Term → List (SubFace × CuTermNC) → List (SubFace × CuTermNC)
 cuCong1L t [] = []
 cuCong1L t ((sf , x) ∷ xs) =
  (sf , cuCong1 (liftVarsFrom 1 1 (subfaceCell (nothing ∷ sf) t)) x) ∷ cuCong1L t xs

 cuCong1 t (hco x x₁) = hco (cuCong1L t x) (cuCong1 t x₁)
 cuCong1 t (cell x₁) = cell (substTms [ x₁ ] t)
 
 congCus : ℕ → ℕ → R.Term → List (List (SubFace × CuTermNC) × CuTermNC) → CuTermNC
 congCus zero _ _ _ = cell (R.lit (R.string "out of fuel in congCus"))
 congCus (suc fuel) dim t ((x , y) ∷ []) = cuCong1 t (hco x y)
 congCus (suc fuel) dim t xs @(_ ∷ _ ∷ _) = --cell (R.lit (R.string "todo"))
   let lid = uncurry (congCus fuel dim) (normal𝑪ong t (L.map snd xs))
   in hco (L.map ff sfUnion)  lid
  where
  sfUnion = foldr (_++fe_ ∘S L.map fst ∘S fst) [] xs
  
  ff : SubFace → SubFace × CuTerm' ⊥ Unit
  ff sf = sf ,
   let ts = L.map (uncurry (getSide sf)) xs
   in uncurry (congCus fuel (suc (sfDim sf)))
       (normal𝑪ong (liftVarsFrom 1 (length xs)
        (subfaceCell ((repeat (length xs) nothing) ++ sf) t)) ts)

    
  -- cell (R.lit (R.string "todo"))
 congCus _ _ t [] = cell t

 appCongs : ℕ → ℕ → CuTerm → CuTermNC

 appCongsS : ℕ → List (SubFace × CuTerm) → List (SubFace × CuTermNC)
 appCongsS zero _ = [] 
 appCongsS _ [] = []   
 appCongsS (suc fuel) ((sf , x) ∷ xs) =
  (sf , appCongs fuel (suc (sfDim sf)) x) ∷ appCongsS fuel xs 
 
 appCongs zero _ _ = cell (R.lit (R.string "out of fuel in normal𝑪ong"))
 appCongs (suc fuel) dim (hco x x₁) =
   hco (appCongsS fuel x) (appCongs fuel dim x₁)
 appCongs _ dim  (cell' x x₁) = cell' x x₁
 appCongs (suc fuel) dim  (𝒄ong' x x₁) =
   uncurry (congCus fuel dim) (normal𝑪ong x (L.map (appCongs fuel dim) x₁))

appCongs : ℕ → CuTerm → CuTermNC
appCongs = appCongs.appCongs 100


module fillCongs where


 fillCongs : ℕ → ℕ → CuTerm → CuTermNC
 congFill : ℕ → ℕ → R.Term → List (List (SubFace × CuTerm) × CuTerm) → CuTermNC
 congFill fuel dim t xs =
   let lid = fillCongs fuel dim $ uncurry (𝒄ong)
                 (map-snd (L.map (uncurry hco)) (normal𝑪ong* t (L.map snd xs)))
   in hco (((repeat dim nothing ∷ʳ just false)  , f0) ∷
      L.map ff sfUnion)  lid --(L.map ff sfUnion)
  where
  sfUnion = foldr (_++fe_ ∘S L.map fst ∘S fst) [] xs
  
  ff : SubFace → SubFace × CuTermNC
  ff sf = sf ,
   let ts = L.map (uncurry (getSide sf)) xs
   in fillCongs fuel (suc (sfDim sf)) $ uncurry (𝒄ong)
                 (map-snd (L.map (uncurry hco)) (normal𝑪ong*
                  (liftVarsFrom 1 (length xs)
        (subfaceCell ((repeat (length xs) nothing) ++ sf) t)) ts)) 

--ToTerm.toTermFill' {Unit} {Unit} (defaultCtx dim)

  f0 : CuTermNC
  f0 = cell' _ (substTms (
        L.map (uncurry (ToTerm.toTermFill {Unit} {Unit} (defaultCtx dim)))
           xs
           ) (liftVarsFrom 1 (length xs) t))

-- (L.map ? (ToTerm.toTermFill' {⊥} {Unit} (defaultCtx dim)
--          ? ?))

 fillCongsS : ℕ → List (SubFace × CuTerm) → List (SubFace × CuTermNC)
  
 fillCongs fuel dim (hco x cu) =
   hco (fillCongsS fuel x) (fillCongs fuel dim cu)
 fillCongs fuel dim (cell x₁) = cell (liftVarsFrom 1 dim x₁)
 fillCongs zero dim (𝒄ong' x x₁) = cell (R.lit (R.string "out of fuel in fillCongs"))
 fillCongs (suc fuel) dim (𝒄ong' t []) = cell (liftVarsFrom 1 dim t)
      -- uncurry (congFill fuel dim) (normal𝑪ong* t xs)
 fillCongs (suc fuel) dim (𝒄ong' t xs) =
      uncurry (congFill fuel dim) (normal𝑪ong* t xs)
  

-- hco (L.map {!!} y')
--           {!!}
--       -- uncurry (congFill fuel dim) (normal𝑪ong x (L.map (fillCongs fuel dim) x₁))
 
 fillCongsS fuel [] = []
 fillCongsS fuel ((sf , x) ∷ xs) =
   (sf ∷ʳ nothing , fillCongs fuel (suc (sfDim sf)) x) ∷ fillCongsS fuel xs 


open fillCongs using (fillCongs) public
