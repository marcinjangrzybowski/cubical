{-# OPTIONS --safe -v testMarkVert:3 -v tactic:3 #-} 
-- -v 3 
module Cubical.Tactics.PathSolver.MonoidalSolver where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.List as L
open import Cubical.Data.Nat as ℕ

open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_ ; _<_ to _<ℕ_)

open import Cubical.Data.Sigma

open import Cubical.Reflection.Base renaming (v to 𝒗)
import Agda.Builtin.Reflection as R
open import Cubical.Tactics.PathSolver.Reflection
open import Cubical.Tactics.Reflection 
open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Cubical.Tactics.Reflection.Utilities

-- open import Cubical.Tactics.PathSolver.Base
open import Cubical.Tactics.PathSolver.CongComp

open import Cubical.Tactics.PathSolver.QuoteCubical 

open import Cubical.Tactics.PathSolver.Error
open import Cubical.Tactics.PathSolver.Dimensions
open import Cubical.Tactics.PathSolver.CuTerm
open import Cubical.Tactics.PathSolver.Reflection
open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.PathSolver.Degen
open import Cubical.Tactics.PathSolver.PathEval
import Cubical.Tactics.PathSolver.PathEval as PT

import Cubical.Tactics.PathSolver.ViaPrimPOr as ViaPrimPOr

private
  variable
    ℓ : Level
    A B : Type ℓ





PathTerm = R.Term ⊎ R.Term

record SquareTerm : Type where
 constructor squareTerm
 field
  term : R.Term


pattern 𝒓efl x = inl x
pattern 𝒑λ x = inr x

asPathTerm : R.Term → PathTerm
asPathTerm tm = 
  if (hasVar zero tm) then (𝒑λ tm) else (𝒓efl tm)

-- compPath'-filler, but composition is 'simplified' according to groupoid laws

-- (p : x ≡ y) → (q : y ≡ z) → (Σ (p∙q ∈ x ≡ z) (Square q p∙q p refl))

-- assumes that terms are already pre rpocessed : addNDimsToCtx 1 ∘S R.normalise ∘S pathApp


bfs' : PT.CTerm → R.TC R.Term
bfs' xs =  do
    let q = (PT.foldPath' (tail (PT.fill-flatten' xs)))
    hd ← Mb.rec (R.typeError [ "imposible tfct≡" ]ₑ )
           pure (listToMaybe (PT.fill-flatten' xs))
    -- addNDimsToCtx 2 $  R.typeError [ hd ]ₑ
    PT.fillHeadTrm hd q




_↙_ : PathTerm → PathTerm → R.TC (PathTerm × SquareTerm)
𝒓efl x ↙ q = q ,_ <$>  (squareTerm <$> bfs' (⊎.rec (idfun _) (idfun _) q))
𝒑λ x ↙ 𝒓efl y = 
  (𝒑λ (PT.wrapPaths x) ,_) <$> (squareTerm <$> (bfs' (PT.wrapFills x)) ) 
𝒑λ p ↙ 𝒑λ q = do
  pq-sq ← (PT.absorb 0 (PT.wrapPaths p) q)
  
  pq ← (PT.cTermEnd pq-sq) >>= Mb.rec
     ( 𝒓efl <$> (addNDimsToCtx 1 $ R.normalise
          (replaceVarWithCon (λ { zero → just (quote i0) ; _ → nothing }) p))) (pure ∘S 𝒑λ)
  -- addNDimsToCtx 1 $ R.typeError [ pq-sq ]ₑ
  pq ,_ <$> (squareTerm <$> bfs' pq-sq)
   
-- _ ↙ _ = R.typeError [ "testes" ]ₑ

macro
 ↙-test : R.Term → R.Term → R.Term → R.TC Unit
 ↙-test p q h = do
   p' ← asPathTerm <$> (addNDimsToCtx 1 ∘S R.normalise ∘S pathApp) p
   q' ← asPathTerm ∘S PT.wrapPaths <$> (addNDimsToCtx 1 ∘S R.normalise ∘S pathApp) q
   pq ← (SquareTerm.term ∘S snd) <$> p' ↙ q'
   R.unify pq h











flipOnFalse : Bool → R.Term → R.Term
flipOnFalse b t = if b then t else R.def (quote ~_) v[ t ] 



data 1DimView (A : Type ℓ) : Type ℓ where
 [_]1d : A → 1DimView A 
 [_∙∙1d_∙∙1d_]1d : 1DimView A → 1DimView A → 1DimView A → 1DimView A




map-1DimView : (f : A → B) → 1DimView A → 1DimView B
map-1DimView f [ x ]1d = [ f x ]1d
map-1DimView f [ x ∙∙1d x₁ ∙∙1d x₂ ]1d = [ (map-1DimView f x) ∙∙1d (map-1DimView f x₁) ∙∙1d (map-1DimView f x₂) ]1d



module _ {M : Functorω} {{_ : RawApplicative M}} {{_ : RawMonad M}} where 

 mapM-1DimView : (f : A → M B) → 1DimView A → M (1DimView B)
 mapM-1DimView f [ x ]1d = ⦇ [ f x ]1d ⦈
 mapM-1DimView f [ x ∙∙1d x₁ ∙∙1d x₂ ]1d =
   ⦇ [ (mapM-1DimView f x) ∙∙1d (mapM-1DimView f x₁) ∙∙1d (mapM-1DimView f x₂) ]1d ⦈


sym1DimView : 1DimView (A × R.Term) → 1DimView (A × R.Term)
sym1DimView [ (a , x) ]1d = [ (a , (invVar zero x)) ]1d
sym1DimView [ x ∙∙1d x₁ ∙∙1d x₂ ]1d =
  [ (sym1DimView x₂) ∙∙1d (sym1DimView x₁) ∙∙1d (sym1DimView x) ]1d

module _ (a : A) where
 to1DimView :  CuTerm' ⊥ A → Maybe (1DimView (A × R.Term)) 

 to1DimView (hco (((just b) ∷ [] , fc) ∷ ((just b') ∷ [] , fc') ∷ []) x₁) =
   (do x₁ ← to1DimView x₁
       f ← to1DimView fc 
       f' ← to1DimView fc'
       let f0 = if b then f' else f
       let f1 = if b then f else f' 
       just [ sym1DimView f0 ∙∙1d x₁ ∙∙1d f1 ]1d)


 to1DimView (cell' x x₁) = just [ (x , x₁) ]1d
 to1DimView _ = nothing


1dvEnd : 1DimView (A × R.Term) → R.TC PathTerm 
1dvEnd y@([ (_ , x) ]1d) = 𝒓efl <$> (addNDimsToCtx 1 $ R.normalise
          (replaceVarWithCon (λ { zero → just (quote i1) ; _ → nothing }) x))
1dvEnd y@([ x ∙∙1d x₁ ∙∙1d x₂ ]1d) = 1dvEnd x₂



fill1DV' : 1DimView (Maybe (R.Term × R.Term) × PathTerm) → PathTerm →  R.TC (R.Term × PathTerm)
fill1DV' [ nothing , p ]1d q = do
  (q , squareTerm s) ← p ↙ q
  pure (s , q)
fill1DV' [ just (_ , ud≡) , p ]1d q = do
  (q , squareTerm s) ← p ↙ q
  pure (R.def (quote comp₋₀) (s v∷ v[ vlam "𝓳" $ vlam "𝓲" ud≡ ])  , q)
fill1DV' [ p₀ ∙∙1d p₁ ∙∙1d p₂ ]1d q = do
  (s₂ , q) ← fill1DV' p₂ q
  (s₁ , q) ← fill1DV' p₁ q
  (s₀ , q) ← fill1DV' p₀ q  
  pure (R.def (quote _∙∙■_∙∙■_) (s₀ v∷ s₁ v∷ v[ s₂ ]) , q )

fill1DV : 1DimView (A × R.Term) → R.TC (R.Term × PathTerm)
fill1DV x = 
  
  1dvEnd x >>= (fill1DV' (map-1DimView (λ (_ , pt) → nothing ,  asPathTerm pt) x))



quote1D : Maybe R.Type → R.Term → R.TC ((Maybe R.Term) × 1DimView (Maybe (R.Term × R.Term) × R.Term))
quote1D mbty t = do
  cu ← extractCuTermFromPath mbty t
  te ← ppCT 1 100 cu
  let cu' = appCongs 1 cu
  congPa ← pure (ToTerm.toTerm (defaultCtx 2) (fillCongs 100 1 cu))
  -- R.typeError te
  let mbCongPa = if (hasVar 1 congPa) then just congPa else nothing 
  Mb.rec (R.typeError [ "imposible in simplifyPath" ]ₑ)
               (λ (x , y) → x ,_ <$> mapM-1DimView (UndegenCell.mbUndegen' 1 ∘S snd) y)
               (map-Maybe  (mbCongPa ,_) (to1DimView _ cu'))



simplifyFillTerm : Maybe R.Type → R.Term → R.TC R.Term
simplifyFillTerm mbTy t = do
  (_ , 1dv) ← quote1D  mbTy t
  (s , _) ← fill1DV 1dv
  pure s
  -- (R.typeError $ [ s ]ₑ)



macro
 simplifyFill : R.Term → R.Term → R.TC Unit
 simplifyFill t h = do
   sq ← simplifyFillTerm nothing t
   R.unify sq h
     -- <|> (R.typeError $ [ sq ]ₑ)

 simplifyPath : R.Term → R.Term → R.TC Unit
 simplifyPath t h = do   
   sq ← simplifyFillTerm nothing t
   R.unify (R.def (quote ◪→≡) v[ sq ]) h

stepSq : R.Type → R.Term → Maybe PathTerm →  R.TC (R.Term × PathTerm)
stepSq A p mbQ = do
  (mbCong≡ , 1dt) ← quote1D (just A) $ vlam "𝒾" p
  
  q ← Mb.rec (1dvEnd 1dt) pure mbQ  
  (s , q') ←  fill1DV' (map-1DimView (map-snd asPathTerm) 1dt ) q

  let s' = Mb.rec s
            (λ c≡ → R.def (quote comp₋₀) (s v∷ v[ vlam "𝓳" $ vlam "𝓲" c≡ ]))
            mbCong≡
  pure $ s' , q'                 

macro
 
 solvePaths : R.Term → R.TC Unit
 solvePaths h = R.withReduceDefs (false , [ quote ua ]) do   
  hTy ← R.inferType h >>= wait-for-term >>= R.normalise

  bdTM@(A , fcs) ← matchNCube hTy
  let dim = length fcs
  -- mbEquation' bdTM
  flip (Mb.rec (R.typeError [ "not equation" ]ₑ)) (mbEquation bdTM)
    λ (lhs , rhs) → do

       (lhsSq , _) ← stepSq A lhs nothing
       (rhsSq , _) ← stepSq A rhs nothing

       let solution = R.def (quote ◪→◪→≡) (lhsSq v∷ v[ rhsSq ])
       
       R.unify solution h <|> R.typeError [ solution ]ₑ

 

 solveSquare : R.Term → R.TC Unit
 solveSquare h = R.withReduceDefs (false , [ quote ua ]) do   
  hTy ← R.inferType h >>= wait-for-term >>= R.normalise
  bdTM@(A , ((a₀₋ , a₁₋) , (a₋₀ , a₋₁))) ← (matchSquare <$> matchNCube hTy) >>=
     Mb.rec (R.typeError [ "not a square" ]ₑ) pure
  (a₁₋' , p₁₀) ← stepSq A a₁₋ nothing
  (a₋₁' , p₀₁) ← stepSq A a₋₁ nothing
  (a₀₋' , _) ← stepSq A a₀₋ (just p₀₁)
  (a₋₀' , _) ← stepSq A a₋₀ (just p₁₀)

  let solution = R.def (quote ◪mkSq)
        (a₀₋' v∷ a₁₋' v∷ a₋₀' v∷ a₋₁' v∷ [])

  R.unify solution h  <|> R.typeError [ solution ]ₑ

 
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

