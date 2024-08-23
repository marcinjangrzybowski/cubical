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
open import Agda.Builtin.String

open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Dimensions
open import Cubical.Tactics.Reflection.CuTerm
open import Cubical.Tactics.Reflection.Variables

-- TODO : test this
-- normal𝑪ong* : String → R.Term → List (Hco Unit Unit)→ (R.Term × List (Hco Unit Unit))
-- normal𝑪ong* = {!!}
-- -- normal𝑪ong* mark t xs = h 200 0  t xs
-- --  where
-- --  h : ℕ → ℕ → R.Term → List CuTerm → (R.Term × List (List (SubFace × CuTerm) × CuTerm))
-- --  h _ k t [] = t , []
-- --  h fuel k t ((hco x y) ∷ xs) =
-- --   let (t' , xs') = h fuel (suc k) t (xs)
-- --   in t' , (x , y) ∷ xs'
-- --  h fuel k t (cell' x x₁ ∷ xs) =
-- --   let t' = replaceAtTrm k (liftVarsFrom (suc (k + length xs)) zero  x₁) t
-- --   in h fuel k t' xs
-- --  -- h fuel k t (𝒄ong' x x₁ ∷ []) =
-- --  --   h fuel k ((replaceAtTrm zero x (liftVarsFrom (length x₁) 1 t))) x₁

-- --  h _ k t (𝒄ong' x x₁ ∷ xs) = R.lit (R.string $ "imposible in normal𝑪ong* " <> mark) , []

-- normal𝑪ong : R.Term → List (Hco ⊥ Unit) → (R.Term × List (List (SubFace × CuTermNC) × CuTermNC))
-- normal𝑪ong = {!!}
-- -- normal𝑪ong t xs = h 200 0  t xs
-- --  where
-- --  h : ℕ → ℕ → R.Term → List CuTermNC → (R.Term × List (List (SubFace × CuTermNC) × CuTermNC))
-- --  h _ k t [] = t , []
-- --  h fuel k t ((hco x y) ∷ xs) =
-- --   let (t' , xs') = h fuel (suc k) t (xs)
-- --   in t' , (x , y) ∷ xs'
-- --  h fuel k t (cell' x x₁ ∷ xs) =
-- --   let t' = replaceAtTrm k (liftVarsFrom (suc (k + length xs)) zero  x₁) t
-- --   in h fuel k t' xs
-- --  h zero _ _ _ = R.lit (R.string "out of fuel in normal𝑪ong") , []

getSide : ∀ {A} → SubFace → Hco A Unit → CuTerm' A Unit
getSide {A = A}  sf (hcodata l y) =
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

 appCongs : ℕ → ℕ → CuTerm → CuTermNC
 cuCong1 : R.Term → CuTermNC → CuTermNC
 cuCong1L : R.Term → List (SubFace × CuTermNC) → List (SubFace × CuTermNC)
 cuCong1L t [] = []
 cuCong1L t ((sf , x) ∷ xs) =
  (sf , cuCong1 (liftVarsFrom 1 1 (subfaceCell (nothing ∷ sf) t)) x) ∷ cuCong1L t xs

 cuCong1 t (hco x x₁) = hco (cuCong1L t x) (cuCong1 t x₁)
 cuCong1 t (cell x₁) = cell (substTms [ x₁ ] t)

 congCus : ℕ → ℕ → R.Term → List (Hco ⊥ Unit) → CuTermNC
 congCus zero _ _ _ = cell (R.lit (R.string "out of fuel in congCus"))
 congCus (suc fuel) dim t ((hcodata x y) ∷ []) = cuCong1 t (hco x y)
 congCus (suc fuel) dim t xs @(_ ∷ _ ∷ _) = --cell (R.lit (R.string "todo"))
   let lid = appCongs fuel dim (𝒄ongF t  (L.map (CuTermNC→CuTerm  ∘S Hco.bottom) xs))
                   --(normal𝑪ong t (L.map snd xs))
   in hco (L.map ff sfUnion)  lid
  where
  sfUnion = foldr (_++fe_ ∘S L.map fst ∘S Hco.sides) [] xs

  ff : SubFace → SubFace × CuTerm' ⊥ Unit
  ff sf = sf ,
   let ts = L.map (getSide sf) xs
   in appCongs fuel (suc (sfDim sf))
        (𝒄ongF
        (liftVarsFrom 1 (length xs)
        (subfaceCell ((repeat (length xs) nothing) ++ sf) t)) (L.map CuTermNC→CuTerm ts))


  -- cell (R.lit (R.string "todo"))
 congCus _ _ t [] = cell t


 
 appCongsS : ℕ → List (SubFace × CuTerm) → List (SubFace × CuTermNC)
 appCongsS zero _ = []
 appCongsS _ [] = []
 appCongsS (suc fuel) ((sf , x) ∷ xs) =
  (sf , appCongs fuel (suc (sfDim sf)) x) ∷ appCongsS fuel xs

 -- appCongsHco : ℕ → ℕ → Hco Unit Unit → Hco ⊥ Unit
 -- appCongsHco fuel dim (hcodata sides bottom) =
 --   hcodata (appCongsS fuel sides) {!!}

 appCongs zero _ _ = cell (R.lit (R.string "out of fuel in normal𝑪ong"))
 appCongs (suc fuel) dim (hco x x₁) =
   hco (appCongsS fuel x) (appCongs fuel dim x₁)
 appCongs _ dim  (cell' x x₁) = cell' x x₁
 appCongs (suc fuel) dim  (𝒄ong' x x₁) =
   congCus fuel dim x
     (L.map (λ (hcodata sides bottom) →
        hcodata (appCongsS fuel sides) (appCongs fuel dim bottom)) x₁)
   -- appCongs fuel dim ((𝒄ongF x (L.map (CuTermNC→CuTerm ∘S appCongs fuel dim ∘S  hco') x₁)))
   -- uncurry (congCus fuel dim) (normal𝑪ong x (L.map (appCongs fuel dim) x₁))
appCongs : ℕ → CuTerm → CuTermNC
appCongs = appCongs.appCongs 100


module fillCongs where


 fillCongs : ℕ → ℕ → CuTerm → CuTermNC
 congFill : ℕ → ℕ → R.Term → List (Hco Unit Unit) → CuTermNC
 congFill fuel dim t xs =
   let lid = fillCongs fuel dim $ 𝒄ongF t (L.map (Hco.bottom) xs)
   in hco (((repeat dim nothing ∷ʳ just false)  , f0) ∷
      L.map ff sfUnion)  lid 
  where
  sfUnion = foldr (_++fe_ ∘S L.map fst ∘S Hco.sides) [] xs

  ff : SubFace → SubFace × CuTermNC
  ff sf = sf ,
   let ts : List (CuTerm)
       ts = L.map ((getSide sf)) xs
   in fillCongs fuel (suc (sfDim sf)) $
           𝒄ongF  ((liftVarsFrom 1 (length xs)
                (subfaceCell ((repeat (length xs) nothing) ++ sf) t))) ts
          -- (map-snd (L.map (uncurry hco))
          --     {!!}
          --    (normal𝑪ong* "B"
          --                  ts)
          --       )

  f0 : CuTermNC
  f0 = cell' _ (substTms (
        L.map ((ToTerm.toTermFill {Unit} {Unit} (defaultCtx dim)))
           xs --xs
           ) (liftVarsFrom 1 (length xs) t))

 fillCongsS : ℕ → List (SubFace × CuTerm) → List (SubFace × CuTermNC)

 fillCongs fuel dim (hco x cu) =
   hco (fillCongsS fuel x) (fillCongs fuel dim cu)
 fillCongs fuel dim (cell x₁) = cell (liftVarsFrom 1 dim x₁)
 fillCongs zero dim (𝒄ong' x x₁) = cell (R.lit (R.string "out of fuel in fillCongs"))
 fillCongs (suc fuel) dim (𝒄ong' t []) = cell (liftVarsFrom 1 dim t)
      -- uncurry (congFill fuel dim) (normal𝑪ong* t xs)
 fillCongs (suc fuel) dim (𝒄ong' t xs) =
      uncurry (congFill fuel dim) (t , xs)
        --(normal𝑪ong* "C" t xs)

 fillCongsS fuel [] = []
 fillCongsS fuel ((sf , x) ∷ xs) =
   (sf ∷ʳ nothing , fillCongs fuel (suc (sfDim sf)) x) ∷ fillCongsS fuel xs


open fillCongs using (fillCongs) public
