{-

This module implements a solver capable of handling squares, which are boundaries built of one-dimensional faces. At this stage, it does not support higher-dimensional cubes.

**Simplified One-Dimensional View**:
  - Represents compositions involving only one interval variable.
  - Defined using the specialized `1DimView` type.
  - Equipped with instances of both `RawMonad` and `RawApplicative`.
  - Simplifies the manipulation and normalization of paths within the solver
    (compared to more general, arbitrary dimensional CuTerm representation)

### Solver steps:

1. **Identifying Boundaries**:
   - The solver begins by identifying the boundary of a square term.

2. **Quoting into Specialized Representation**:
   - The boundary terms are quoted into a specialized one-dimensional representation using the `quote1D` function.

3. **Applying Generalized `cong-∙`**:
   - (if necessary) Uses the  `fillCongs` functions from the `CongComp` module to "push to the bottom" all application of functions (bring all the composiitons to the "top")

4. **Filler Construction**:
   - Constructs fillers for each face using the `_↙_` operator from the `PathEval` module.
   - Relies on the aspects of the free monoidal groupoid structure as implemented in `PathEval`.

5. **Assembling the Final Square**:
   - The final square term is assembled using the `◪mkSq` lemma from `Path.agda`.

-}

{-# OPTIONS --safe #-}
module Cubical.Tactics.PathSolver.MonoidalSolver2.MonoidalSolver where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path

open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.List as L
open import Cubical.Data.Nat


open import Cubical.Data.Sigma

open import Cubical.Reflection.Base renaming (v to 𝒗)
open import Cubical.Reflection.Sugar
import Agda.Builtin.Reflection as R

open import Cubical.Tactics.Reflection

open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Variables

open import Cubical.Tactics.PathSolver.CongComp

open import Cubical.Tactics.Reflection.QuoteCubical
open import Cubical.Tactics.Reflection.Error
open import Cubical.Tactics.Reflection.Dimensions
open import Cubical.Tactics.Reflection.CuTerm

open import Cubical.Tactics.PathSolver.Degen
open import Cubical.Tactics.PathSolver.MonoidalSolver2.PathEval
open import Cubical.Tactics.PathSolver.Path

private
  variable
    ℓ : Level
    A B : Type ℓ





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



1DimView→List : 1DimView A → List A
1DimView→List [ x ]1d = [ x ]
1DimView→List [ x ∙∙1d x₁ ∙∙1d x₂ ]1d =
  1DimView→List x ++ 1DimView→List x₁ ++ 1DimView→List x₂


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
  -- R.typeError [ t ]ₑ
  cu ← extractCuTermFromPath mbty t
  -- te ← ppCT 1 100 cu
  -- R.typeError te
  let cu' = appCongs 1 cu
  congPa ← pure (ToTerm.toTerm (defaultCtx 2) (fillCongs 100 1 cu))
  let mbCongPa = if (hasVar 1 congPa) then just congPa else nothing
  Mb.rec (R.typeError [ "imposible in simplifyPath" ]ₑ)
               (λ (x , y) → x ,_ <$> mapM-1DimView (UndegenCell.mbUndegen' 1 ∘S snd) y)
               (map-Maybe  (mbCongPa ,_) (to1DimView _ cu'))




module Specialised {ℓ} {A : Type ℓ} (unquoteInA : R.Term → R.TC A)
   (smartComp : A → List A → List A × R.Term) (symA : A → A)
   (unqt[A] : List A → R.Term) where 

 show1DimViewLeaf : (Maybe (R.Term × R.Term) × R.Term) → R.TC (List R.ErrorPart)
 show1DimViewLeaf (mbtms , t) =
   unquoteInA t >>= ((R.quoteTC >=> R.normalise) >=> (pure ∘ [_]ₑ))
  -- pure [ t ]ₑ
   -- pure ((Mb.rec [ "notihng on fst" ]ₑ (λ (x , y) → x ∷ₑ " , " ∷ₑ [ y ]ₑ  ) mbtms
   --    ++nl [ t ]ₑ))
 
 show1DimView : 1DimView (Maybe (R.Term × R.Term) × R.Term) → R.TC (List R.ErrorPart)
 show1DimView [ x ]1d = show1DimViewLeaf x
 show1DimView [ x ∙∙1d x₁ ∙∙1d x₂ ]1d = do
  y ← show1DimView x
  y₁ ← show1DimView x₁
  y₂ ← show1DimView x₂
  pure ([ "[ " ]ₑ ++nl y ++nl [ "∙∙1d" ]ₑ ++nl y₁ ++nl [ "∙∙1d" ]ₑ ++nl y₂ ++nl [ "]1d" ]ₑ)

 macro
  quote1Dinto : R.Term → R.Term → R.Term → R.TC Unit
  quote1Dinto ty tm' h = do
    tm ← wait-for-term tm'
    (mbtm , q1d) ← quote1D (just ty) tm
    y ← mapM-1DimView (unquoteInA ∘ snd) q1d >>= R.quoteTC
    -- q1dV ← show1DimView q1d
    -- addNDimsToCtx 1 $
    --   R.typeError
    --    --  (Mb.rec [ "notihng on fst" ]ₑ ([_] ∘ R.termErr) mbtm
    --    -- ++nl
    --    q1dV
    --    -- )
    R.unify y h

 -- module Solver  where

 solvedSq' : L.List A → 1DimView A →  (L.List A × R.Term) 
 solvedSq' x [ x₁ ]1d = smartComp x₁ x


 solvedSq' l [ x₁ ∙∙1d x₂ ∙∙1d x₃ ]1d = 
  let (l' , s) = solvedSq' l x₁
      (l'' , s') = solvedSq' l' x₂
      (l''' , s'') = solvedSq' l''  x₃
  in l''' , R.def (quote _∙∙■_∙∙■_) (s v∷ s' v∷ v[ s'' ]) 

 solvedSq : 1DimView A → R.Term 
 solvedSq = snd ∘ solvedSq' L.[]

 symA-1d : 1DimView A → 1DimView A 
 symA-1d [ x ]1d = [ symA x ]1d
 symA-1d [ x ∙∙1d x₁ ∙∙1d x₂ ]1d =
   [ symA-1d x₂ ∙∙1d symA-1d x₁ ∙∙1d symA-1d x ]1d


 stepSqOnlyCong : R.Type → R.Term
   → R.TC (R.Term)
 stepSqOnlyCong A p = do

   (mbCong≡ , 1dt'') ← quote1D (just A) $ vlam "𝒾" p
   
   -- q ← Mb.rec (1dvEnd 1dt) pure mbQ
   -- let (q' , s) = solvedSq' mbQ asA
     -- fill1DV' (map-1DimView (map-snd asPathTerm) 1dt ) q

   pure $ Mb.rec (R.def (quote refl) [])
             (λ c≡ →
                 vlam "𝓳" $ vlam "𝓲" (invVar 1 c≡)
               --  R.def
               -- (if dir then (quote comp₋₀) else
               --    (quote comp₋₀'))
               --  ( ((s v∷ v[ vlam "𝓳" $ vlam "𝓲" c≡ ]))
               --     )
                   )
             mbCong≡


 stepSq : Bool → Bool → R.Type → R.Term → List A
   → R.TC ((R.Term × List A) × Maybe R.Term)
 stepSq withHole dir A p mbQ = do

   (mbCong≡ , 1dt'') ← quote1D (just A) $ vlam "𝒾" p
   let 1dt' = map-1DimView snd 1dt''   
   asA' ← mapM-1DimView (unquoteInA) 1dt'
   let asA = if dir then asA' else (symA-1d asA')
   
   -- q ← Mb.rec (1dvEnd 1dt) pure mbQ
   let (q' , s) = solvedSq' mbQ asA
     -- fill1DV' (map-1DimView (map-snd asPathTerm) 1dt ) q

   let s' = Mb.rec s
             (λ c≡ → R.def
               (if dir then (quote comp₋₀) else
                  (quote comp₋₀'))
                ( ((s v∷ v[ vlam "𝓳" $ vlam "𝓲" c≡ ]))
                   ))
             mbCong≡
   pure ((s' , q') ,
      (if withHole
       then just R.unknown
            -- (Mb.rec
            --   ((R.def
            --    (quote comp₋₀'*)
            --     (s v∷ R.def (quote refl) L.[] v∷ v[ R.unknown ]
            --        )))
            --  (λ c≡ → R.def
            --    (if dir then (quote comp₋₀) else
            --       (quote comp₋₀'*))
            --     ( ((s v∷ (vlam "𝓳" $ vlam "𝓲" c≡) v∷ v[ R.unknown ]))
            --        ))
            --  mbCong≡)
          
       else nothing))
   -- pure $ s' , q'


-- (λ c≡ → R.def
--                (if dir then (quote comp₋₀) else
--                   (if withHole then (quote comp₋₀'*) else (quote comp₋₀')))
--                 ( ((s v∷ v[ vlam "𝓳" $ vlam "𝓲" c≡ ])
--                    L.++ (if withHole then v[ R.unknown ] else L.[]))
--                    ))

 macro

  solveCongs : R.Term → R.TC Unit
  solveCongs h = do
     R.debugPrint "sp" 0 $ [ "solvePaths - start :\n\n" ]ₑ
     hTy ← R.inferType h >>= wait-for-term >>= R.normalise
     R.debugPrint "sp" 0 $ [ "solvePaths - got ty :\n\n" ]ₑ ++ₑ [ hTy ]ₑ
     bdTM@(A , ((a₀₋ , a₁₋) , (a₋₀ , a₋₁))) ← (matchSquare <$> matchNCube hTy) >>=
        Mb.rec (R.typeError [ "not a square" ]ₑ) pure

     -- cuBdEPs ← renderCuBoundaryTypeTerm {!bdTM!} 
     -- R.debugPrint "sp" 0 $ [ "solvePaths - square matched.. :\n\n" ]ₑ
     --   ++ cuBdEPs
     (p-a₀₋) ← stepSqOnlyCong A a₀₋
     (p-a₁₋) ← stepSqOnlyCong A a₁₋
     (p-a₋₀) ← stepSqOnlyCong A a₋₀
     (p-a₋₁) ← stepSqOnlyCong A a₋₁

     -- R.typeError $ mapₑ (p-a₀₋ ∷ p-a₁₋ ∷ p-a₋₀ ∷ p-a₋₁ ∷ [])

     let sol = R.def (quote CompSquares.compSquares)
            (R.unknown v∷ p-a₀₋ v∷
              p-a₁₋ v∷ p-a₋₀
                 v∷ p-a₋₁ v∷ [])

     R.unify sol h <|> R.typeError [ sol ]ₑ

     -- R.debugPrint "sp" 0 $ [ "solvePaths - step 1 - start :\n" ]ₑ
     -- ((s , p) , _) ← stepSq false true A a₀₋ []
     -- R.debugPrint "sp" 0 $ [ "solvePaths - step 2 - start :\n" ]ₑ
     -- ((s' , p') , _) ← stepSq false true A a₋₁ p
     -- R.debugPrint "sp" 0 $ [ "solvePaths - step 3 - start :\n" ]ₑ
     -- ((s'' , p'') , _)  ← stepSq false false A a₁₋ p'
     -- R.debugPrint "sp" 0 $ [ "solvePaths - step 4 - start :\n" ]ₑ
     -- ((s''' , p''') , just s*) ← stepSq true false A a₋₀ p''
     --     where  _ → R.typeError [ "imposible" ]ₑ
     -- if (Dec→Bool (discreteℕ (length p''') zero))
     --  then (do
     --    let solution = R.def (quote ◪mkSq')
     --          (s v∷ s' v∷ s'' v∷ s''' v∷ [])
     --    R.debugPrint "sp" 0 $ [ "solvePaths - unify solution - start :\n" ]ₑ
     --      ++ₑ [ solution ]ₑ
     --    R.unify solution h <|> R.typeError [ solution ]ₑ)
     --  else R.typeError [ unqt[A] p''' ]ₑ
     --    -- R.unify
     --    --  (R.def (quote ◪mkSq') (s v∷ s' v∷ s'' v∷ s* v∷ []))
     --    --  h


  solvePaths : R.Term → R.TC Unit
  solvePaths h = do
   R.debugPrint "sp" 0 $ [ "solvePaths - start :\n\n" ]ₑ
   hTy ← R.inferType h >>= wait-for-term >>= R.normalise
   R.debugPrint "sp" 0 $ [ "solvePaths - got ty :\n\n" ]ₑ ++ₑ [ hTy ]ₑ
   bdTM@(A , ((a₀₋ , a₁₋) , (a₋₀ , a₋₁))) ← (matchSquare <$> matchNCube hTy) >>=
      Mb.rec (R.typeError [ "not a square" ]ₑ) pure

   -- cuBdEPs ← renderCuBoundaryTypeTerm {!bdTM!} 
   -- R.debugPrint "sp" 0 $ [ "solvePaths - square matched.. :\n\n" ]ₑ
   --   ++ cuBdEPs
   -- (a₁₋' , p₁₀) ← stepSq A a₁₋ nothing
   -- (a₋₁' , p₀₁) ← stepSq A a₋₁ nothing
   -- (a₀₋' , _) ← stepSq A a₀₋ (just p₀₁)
   -- (a₋₀' , _) ← stepSq A a₋₀ (just p₁₀)
   R.debugPrint "sp" 0 $ [ "solvePaths - step 1 - start :\n" ]ₑ
   ((s , p) , _) ← stepSq false true A a₀₋ []
   R.debugPrint "sp" 0 $ [ "solvePaths - step 2 - start :\n" ]ₑ
   ((s' , p') , _) ← stepSq false true A a₋₁ p
   R.debugPrint "sp" 0 $ [ "solvePaths - step 3 - start :\n" ]ₑ
   ((s'' , p'') , _)  ← stepSq false false A a₁₋ p'
   R.debugPrint "sp" 0 $ [ "solvePaths - step 4 - start :\n" ]ₑ
   ((s''' , p''') , just s*) ← stepSq true false A a₋₀ p''
       where  _ → R.typeError [ "imposible" ]ₑ
   if (Dec→Bool (discreteℕ (length p''') zero))
    then (do
      let solution = R.def (quote ◪mkSq')
            (s v∷ s' v∷ s'' v∷ s''' v∷ [])
      R.debugPrint "sp" 0 $ [ "solvePaths - unify solution - start :\n" ]ₑ
        ++ₑ [ solution ]ₑ
      R.unify solution h <|> R.typeError [ solution ]ₑ)
    else R.typeError [ unqt[A] p''' ]ₑ
      -- R.unify
      --  (R.def (quote ◪mkSq') (s v∷ s' v∷ s'' v∷ s* v∷ []))
      --  h

-- 

  solvePathsH : R.Term → R.TC Unit
  solvePathsH h = do
   hTy ← R.inferType h >>= wait-for-term >>= R.normalise
   bdTM@(A , ((a₀₋ , a₁₋) , (a₋₀ , a₋₁))) ← (matchSquare <$> matchNCube hTy) >>=
      Mb.rec (R.typeError [ "not a square" ]ₑ) pure
   -- (a₁₋' , p₁₀) ← stepSq A a₁₋ nothing
   -- (a₋₁' , p₀₁) ← stepSq A a₋₁ nothing
   -- (a₀₋' , _) ← stepSq A a₀₋ (just p₀₁)
   -- (a₋₀' , _) ← stepSq A a₋₀ (just p₁₀)
   ((s , p) , _) ← stepSq false true A a₀₋ []
   ((s' , p') , _) ← stepSq false true A a₋₁ p
   ((s'' , p'') , _)  ← stepSq false false A a₁₋ p'
   ((s''' , p''') , _) ← stepSq false false A a₋₀ p''


   let solution = R.def (quote ◪mkSq')
         (s v∷ s' v∷ s'' v∷ R.unknown v∷ [])

   R.unify solution h <|> R.typeError [ solution ]ₑ


-- simplifyFillTerm : Maybe R.Type → R.Term → R.TC R.Term
-- simplifyFillTerm mbTy t = do
--   (mbCong≡ , 1dv) ← quote1D  mbTy t
--   (s , _) ← fill1DV 1dv
--   pure (Mb.rec s
--             (λ c≡ → R.def (quote comp₋₀) (s v∷ v[ vlam "𝓳" $ vlam "𝓲" c≡ ]))
--             mbCong≡)
--   -- (R.typeError $ [ s ]ₑ)


-- _$sp_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → A → B
-- f $sp a = f a

-- $sp₂ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → (A → B → C) → A → B → C
-- $sp₂ f a b = f a b


-- macro
--  simplifyFill : R.Term → R.Term → R.TC Unit
--  simplifyFill t h = do
--    sq ← simplifyFillTerm nothing t
--    R.unify sq h

--  simplifyPath : R.Term → R.Term → R.TC Unit
--  simplifyPath t h = R.withReduceDefs (false , quote _$sp_ ∷ [ quote ua ]) do
--    sq ← simplifyFillTerm nothing t
--    R.unify (R.def (quote ◪→≡) v[ sq ]) h

-- stepSq : R.Type → R.Term → Maybe PathTerm →  R.TC (R.Term × PathTerm)
-- stepSq A p mbQ = do
--   (mbCong≡ , 1dt) ← quote1D (just A) $ vlam "𝒾" p

--   q ← Mb.rec (1dvEnd 1dt) pure mbQ
--   (s , q') ←  fill1DV' (map-1DimView (map-snd asPathTerm) 1dt ) q

--   let s' = Mb.rec s
--             (λ c≡ → R.def (quote comp₋₀) (s v∷ v[ vlam "𝓳" $ vlam "𝓲" c≡ ]))
--             mbCong≡
--   pure $ s' , q'


-- macro


--  solvePaths : R.Term → R.TC Unit
--  solvePaths h = R.withReduceDefs (false , quote $sp₂ ∷ quote _$sp_ ∷ [ quote ua ]) do
--   hTy ← R.inferType h >>= wait-for-term >>= R.normalise
--   bdTM@(A , ((a₀₋ , a₁₋) , (a₋₀ , a₋₁))) ← (matchSquare <$> matchNCube hTy) >>=
--      Mb.rec (R.typeError [ "not a square" ]ₑ) pure
--   (a₁₋' , p₁₀) ← stepSq A a₁₋ nothing
--   (a₋₁' , p₀₁) ← stepSq A a₋₁ nothing
--   (a₀₋' , _) ← stepSq A a₀₋ (just p₀₁)
--   (a₋₀' , _) ← stepSq A a₋₀ (just p₁₀)

--   let solution = R.def (quote ◪mkSq)
--         (a₀₋' v∷ a₁₋' v∷ a₋₀' v∷ a₋₁' v∷ [])

--   R.unify solution h <|> R.typeError [ solution ]ₑ

--  solvePathsHole : R.Term → R.TC Unit
--  solvePathsHole h = R.withReduceDefs (false , quote $sp₂ ∷ quote _$sp_ ∷ [ quote ua ]) do
--   hTy ← R.inferType h >>= wait-for-term >>= R.normalise
--   bdTM@(A , ((a₀₋ , a₁₋) , (a₋₀ , a₋₁))) ← (matchSquare <$> matchNCube hTy) >>=
--      Mb.rec (R.typeError [ "not a square" ]ₑ) pure
--   (a₁₋' , p₁₀) ← stepSq A a₁₋ nothing
--   (a₋₁' , p₀₁) ← stepSq A a₋₁ nothing
--   (a₀₋' , _) ← stepSq A a₀₋ (just p₀₁)
--   -- (a₋₀' , _) ← stepSq A a₋₀ (just p₁₀)

--   let solution = R.def (quote ◪mkSq)
--         (a₀₋' v∷ a₁₋' v∷ R.unknown v∷ a₋₁' v∷ [])

--   R.unify solution h <|> R.typeError [ solution ]ₑ

