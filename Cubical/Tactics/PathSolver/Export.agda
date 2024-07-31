{-# OPTIONS --allow-exec #-} 
-- -v extractCuTermTest:4  -v checkHcomp:5 
module Cubical.Tactics.PathSolver.Export where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Relation.Nullary

open import Cubical.Data.Bool hiding (True ; False) renaming (true to True ; false to False)
open import Cubical.Data.Empty
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe as Mb renaming (just to Just ; nothing to Nothing) 
open import Cubical.Data.List as L
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Order.Recursive as ℕOR

open import Cubical.Reflection.Base renaming (v to 𝒗)
import Agda.Builtin.Reflection as R
import Agda.Builtin.Reflection.External as RT
open import Cubical.Tactics.PathSolver.Reflection
open import Cubical.Tactics.Reflection 
open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Cubical.Tactics.Reflection.Utilities

import Cubical.Tactics.PathSolver.Base as PSB
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_ ; _<_ to _<ℕ_)

import Cubical.Tactics.PathSolver.QuoteCubical as QC
import Cubical.Tactics.PathSolver.Examples as E

private
  variable
    ℓ : Level
    A : Type ℓ
    x y z w v : A


qNormalise : A → R.TC A
qNormalise = (R.withNormalisation True ∘S R.quoteTC) >=> R.unquoteTC 


tut : ℕ → (ℕ → ℕ) → List ℕ
tut zero f = []
tut (suc k) f = f zero ∷ tut k (f ∘ suc)

utu : ℕ → List ℕ → (ℕ → ℕ)
utu max l k = L.lookupAlways k l k

tabulateUpToTC : ℕ → (ℕ → ℕ) → R.TC (ℕ → ℕ)
tabulateUpToTC max f = do
  l ← qNormalise (tut max f)
  pure $ utu max l


module Set where
 data Set (A : Type) : Type where
  fromList : List A → Set A

 toList : Set A → List A
 toList (fromList x) = x

module Map where
 data Map (K V : Type) : Type where
  fromList : List (K × V) → Map K V


 toList : ∀ {K V} → Map K V → List (K × V)
 toList (fromList xs) = xs

 mapKeys : ∀ {K V} → (K → K) → Map K V → Map K V
 mapKeys x (fromList x₁) = fromList (L.map (map-fst x) x₁)

-- data IExpr = IExpr (Set.Set ( Set.Set (Int , Bool)))
--   deriving (Eq , Show , Read)

data IExpr' : Type where
 IExpr : Set.Set (Set.Set (ℕ × Bool)) → IExpr'

reindexIExpr' : (ℕ → ℕ) → IExpr' → IExpr'
reindexIExpr' f (IExpr x) =
 IExpr (Set.fromList (L.map (Set.fromList ∘S L.map (map-fst f) ∘S Set.toList) (Set.toList x)))

-- data VarIndex = VarIndex Int | SomeDef String
--   deriving (Eq , Show, Ord , Read)

data OExpr : Type
data ClExpr' : Type
data CellExpr' : Type

data VarIndex' : Type where
 VarIndex : ℕ → VarIndex'
 SomeDef : String → VarIndex'


SF =  (Map.Map ℕ Bool)

Partial' = Map.Map SF OExpr



data ConstExpr' : Type where
 ConstExpr : String → ConstExpr'

data OExpr where
    HComp : (Maybe String) → Partial' → ClExpr' → OExpr
    Cell : CellExpr' → OExpr
    ConstE : ConstExpr' → OExpr
    CHole : ℕ → OExpr
    Appl : ClExpr' → List ClExpr' → OExpr  

data ClExpr' where 
 ClExpr : ℕ → (Map.Map (Map.Map ℕ Bool) OExpr) → ClExpr'

data CellExpr' where
 CellExpr : VarIndex' → List IExpr' → CellExpr'

data Visualisation' : Type where 
    Visualisation : (Maybe String) →
      ClExpr' → (List (String × (String × Maybe (List String)))) → Visualisation'  



fromSubFace : PSB.SubFace → Map.Map ℕ Bool
fromSubFace x = Map.fromList (fsb x)
 where
 fsb : PSB.SubFace → List (ℕ × Bool)
 fsb [] = []
 fsb (Nothing ∷ xs) = L.map (map-fst suc) (fsb xs)
 fsb (Just x ∷ xs) = (zero , x) ∷ L.map (map-fst suc) (fsb xs)
  -- Mb.rec [] ([_] ∘S (zero ,_)) x ++ L.map (map-fst suc) (fsb xs)

toSubFace : ℕ → Map.Map ℕ Bool → PSB.SubFace 
toSubFace dim (Map.fromList x) =
  foldr (λ (k , b) → replaceAt k (Just b)) (repeat dim Nothing) x  


-- module permCE where



--  permCE : ℕ → (ℕ → ℕ) → ClExpr' → R.TC ClExpr'
--  permOE : ℕ → (ℕ → ℕ) → ℕ → OExpr → R.TC OExpr

--  permCE zero _ _ = R.typeError [ "out of fuel in permCE" ]ₑ
--  permCE (suc fuel) prm (ClExpr dim (Map.fromList x)) = 
--    ⦇ ClExpr ⦇ dim ⦈ (Map.fromList <$>
--      (mapM (λ (sf , x) → do
--           let sf' = (toSubFace dim sf)
--           let d = dim ∸ (length (Map.toList sf))
--           let prm' = (PSB.permuteVars.intoFace
--                         (PSB.permuteVars.permute prm sf'))
--                           ∘S prm ∘S (PSB.permuteVars.fromFace sf')
--           -- let pm = PSB.permuteVars.sfPerm sf' prm 
--           ⦇ ⦇ (fromSubFace (PSB.permuteVars.permute prm sf')) ⦈
--               , (permOE fuel prm' d x) ⦈
--           ) x)) ⦈

 
--  permOE zero _ _ _ = R.typeError [ "out of fuel in permOE" ]ₑ
--  permOE (suc fuel) prm dim (HComp x (Map.fromList x₁) x₂) =
--     ⦇ HComp ⦇ x ⦈
--        (Map.fromList <$>
--           (mapM (λ (sf , x) → do
--               let sf' = (toSubFace dim sf)
--               let d = dim ∸ (length (Map.toList sf))
--               let pm = PSB.permuteVars.sfPerm sf' prm 
--               ⦇ ⦇ (fromSubFace (PSB.permuteVars.permute prm sf')) ⦈
--                   , (permOE fuel pm (suc d) x) ⦈
--               ) x₁))
--        (permCE (suc fuel) prm x₂) ⦈
--  permOE (suc fuel) prm dim (Cell (CellExpr x x₁)) =
--     ⦇ Cell ⦇ CellExpr (⦇ x ⦈) (mapM (λ x₂ → ⦇ ((reindexIExpr' prm x₂)) ⦈) x₁) ⦈ ⦈
--  permOE (suc fuel) prm dim (ConstE x) = R.typeError [ "todo in permOE - ConstE" ]ₑ
--  permOE (suc fuel) prm dim (CHole x) = pure (CHole x)
--  permOE (suc fuel) prm dim (Appl x x₁) = R.typeError [ "todo in permOE - Appl" ]ₑ


-- -- permOE = permCE.permOE 100

module fixCE where


 permSide : ℕ → ℕ → ℕ
 permSide dim zero = predℕ dim
 permSide dim (suc k) =
   if (suc k) <ℕ dim then k else (suc k)


 -- fixCE : ℕ → ClExpr' → R.TC ClExpr'
 -- fixOE : ℕ → ℕ → OExpr → R.TC OExpr
 
 -- fixCE zero _ = R.typeError [ "out of fuel in fixCE" ]ₑ
 -- fixCE (suc fuel) (ClExpr dim (Map.fromList x)) =
 --   ⦇ ClExpr ⦇ dim ⦈ (Map.fromList <$>
 --     (mapM (λ (sf , x) → ⦇ ⦇ sf ⦈ , (fixOE fuel (dim ∸ (length (Map.toList sf))) x) ⦈) x)) ⦈

 -- fixOE zero _ _ = R.typeError [ "out of fuel in fixOE" ]ₑ
 -- fixOE (suc fuel) dim (HComp x x₁ x₂) =
 --   ⦇ HComp ⦇ x ⦈
 --       (⦇ Map.fromList
 --         (mapM
 --           (λ (sf , c) → do
 --              let d = dim ∸ (length (Map.toList sf))
 --              c' ← fixOE fuel (suc d) c
 --              let pm = permSide (suc d) 
 --              ⦇ ⦇ sf ⦈ , (permCE.permOE 100 pm (suc d) c') ⦈)
 --           (Map.toList x₁)) ⦈)
 --       (fixCE (suc fuel) x₂) ⦈
 -- fixOE (suc fuel) dim (Cell x) = ⦇ (Cell x) ⦈
 -- fixOE (suc fuel) dim (ConstE x) = R.typeError [ "todo in fixOE - ConstE" ]ₑ
 -- fixOE (suc fuel) dim (CHole x) = ⦇ (CHole x) ⦈
 -- fixOE (suc fuel) dim (Appl x x₁) = R.typeError [ "todo in fixOE - Appl" ]ₑ


module permCE2 where



 permCE : ℕ → (ℕ → ℕ) → ClExpr' → R.TC ClExpr'
 permOE : ℕ → (ℕ → ℕ) → ℕ → OExpr → R.TC OExpr

 permCE zero _ _ = R.typeError [ "out of fuel in permCE" ]ₑ
 permCE (suc fuel) prm (ClExpr dim (Map.fromList x)) = 
   ⦇ ClExpr ⦇ dim ⦈ (Map.fromList <$>
     (mapM (λ (sf , x) → do
          let sf' = (toSubFace dim sf)
          let d = dim ∸ (length (Map.toList sf))
          let prm' = (PSB.permuteVars.intoFace
                        (PSB.permuteVars.permute prm sf'))
                          ∘S prm ∘S (PSB.permuteVars.fromFace sf')
          -- let pm = PSB.permuteVars.sfPerm sf' prm 
          ⦇ qNormalise (fromSubFace (PSB.permuteVars.permute prm sf'))
              , (permOE fuel prm' d x) ⦈
          ) x)) ⦈

 
 permOE zero _ _ _ = R.typeError [ "out of fuel in permOE" ]ₑ
 permOE (suc fuel) prm dim (HComp x (Map.fromList x₁) x₂) =
    ⦇ HComp ⦇ x ⦈
       (Map.fromList <$>
          (mapM (λ (sf , x) → do
              let sf' = (toSubFace dim sf)
              let d = dim ∸ (length (Map.toList sf))
              pm ← tabulateUpToTC dim (PSB.permuteVars.sfPerm sf' prm ∘S fixCE.permSide (suc d))
              let sf* = Map.mapKeys prm sf
              ⦇ (qNormalise sf*)
                    --(fromSubFace (PSB.permuteVars.permute prm sf'))
                    
                  , (permOE fuel pm (suc d) x) ⦈
              ) x₁))
       (permCE (suc fuel) prm x₂) ⦈
 permOE (suc fuel) prm dim (Cell (CellExpr x x₁)) =
    ⦇ Cell ⦇ CellExpr (⦇ x ⦈) (mapM (λ x₂ → qNormalise ((reindexIExpr' prm x₂)) ) x₁) ⦈ ⦈
 permOE (suc fuel) prm dim (ConstE x) = R.typeError [ "todo in permOE - ConstE" ]ₑ
 permOE (suc fuel) prm dim (CHole x) = pure (CHole x)
 permOE (suc fuel) prm dim (Appl x x₁) = R.typeError [ "todo in permOE - Appl" ]ₑ



fixCE = permCE2.permCE 100 (idfun ℕ)




-- toCellExpr

toIExpr : PSB.IExpr → IExpr'
toIExpr = IExpr ∘S Set.fromList ∘S L.map (Set.fromList ∘S L.map λ (x , y) → y , x) 

toProperIExpr : PSB.IExpr → R.TC IExpr'
toProperIExpr [] = R.typeError [ "not a proper IExpr i0" ]ₑ
toProperIExpr ([] ∷ []) = R.typeError [ "not a proper IExpr i1" ]ₑ
toProperIExpr x = ⦇ (toIExpr x) ⦈

toProperIExprMb : PSB.IExpr → Maybe IExpr'
toProperIExprMb [] = Nothing
toProperIExprMb ([] ∷ []) = Nothing
toProperIExprMb x = Just (toIExpr x)



toCellExpr' : ℕ → R.Term → R.TC OExpr
toCellExpr' dim (R.var k xs) = do
    ixesMbs ← PSB.addNDimsToCtx dim $ mapM toIE xs
    let mbIexs = fromAllMaybes ixesMbs 
    Cell <$> Mb.rec (PSB.addNDimsToCtx dim $
              do c' ← R.normalise
                       (R.var k xs)
                 hlpRed c')
      (λ iexs → pure $ (CellExpr (VarIndex k) iexs))
      mbIexs    -- pure $ Cell (CellExpr (VarIndex k) iexs) 

 where
 -- getVarIndex : R.Term → VarIndex'
 -- getVarIndex = {!!}

 hlpRed : R.Term → R.TC CellExpr'
 hlpRed (R.var k' xs') = do
    iexs ← mapM ((PSB.extractIExpr >=> toProperIExpr) ∘S unArg) xs'
    pure (CellExpr (VarIndex k') iexs)
 hlpRed _ = R.typeError [ "todo in  toCellExpr' - 1" ]ₑ
 
 toIE : R.Arg R.Term → R.TC (Maybe IExpr')
 toIE (R.arg _ x') = do
    x ← R.normalise x'
    toProperIExprMb <$> PSB.extractIExpr x  
toCellExpr' dim _ = R.typeError [ "todo in  toCellExpr' - 2" ]ₑ


toOExpr : ℕ → ℕ → PSB.CuTerm → R.TC OExpr


toClExpr : ℕ → ℕ → PSB.CuTerm → R.TC ClExpr'

toPartial' : ℕ → ℕ → List (PSB.SubFace × PSB.CuTerm) → R.TC Partial'

toClExpr fuel dim x =
  ⦇ ClExpr
      ⦇ dim ⦈
      ⦇ Map.fromList
           (mapM (λ sf → do
               x' ←  --PSB.normaliseCells (PSB.sfDim sf)
                     pure (PSB.cuEval sf x)
               ⦇ ⦇ (fromSubFace sf) ⦈ ,
                            (toOExpr fuel (PSB.sfDim sf)
                              (x')) ⦈)
             (PSB.allSubFacesOfDim dim)) ⦈ ⦈

toOExpr zero x₁ x₂ = R.typeError [ "out of fuel in toOExpr" ]ₑ
toOExpr (suc x) dim (PSB.hco x₂ x₃) =
  ⦇ HComp
      ⦇ Nothing ⦈
      (toPartial' x dim x₂)
      (toClExpr x dim x₃) ⦈
toOExpr (suc x) dim (PSB.cell x₃) = toCellExpr' dim x₃
toOExpr (suc x) dim (PSB.𝒄ong' x₂ x₃) = ⦇ CHole ⦇ zero ⦈ ⦈

toPartial' zero dim xs = R.typeError [ "out of fuel in toPartial'" ]ₑ
toPartial' (suc fuel) dim xs =
  Map.fromList <$> mapM
    (λ sf → do
        oe ← Mb.rec (R.typeError [ "imposible in toPartial'" ]ₑ)
                (pure) (PSB.pickSFfromPartial sf xs)
        ⦇ ⦇ (fromSubFace sf) ⦈ ,
         toOExpr fuel (suc (PSB.sfDim sf)) oe ⦈)
    (PSB.withAllIncluded dim (L.map fst xs))


module _ (dim : ℕ) where
 macro
  quoteAsCLExpr : R.Term → R.Term → R.TC Unit
  quoteAsCLExpr t h = do
    y ← QC.extractCuTerm dim t >>= qNormalise
    R.debugPrint "testMarkVert" 0 $ [ "extracted" ]ₑ
    -- R.typeError [ "yy" ]ₑ -- >>= fixCE
    y0 ← toClExpr 100 dim y >>= qNormalise
    R.debugPrint "testMarkVert" 0 $ [ "cl expr done" ]ₑ
    y'preQuote ← ( fixCE y0 )
    R.debugPrint "testMarkVert" 0 $ [ "cl expr fixed" ]ₑ
    y'preNorm ← R.withNormalisation True
      ((R.quoteTC {A = ClExpr'} y'preQuote))
    R.debugPrint "testMarkVert" 0 $ [ "cl expr quotend" ]ₑ
    y' ← pure y'preNorm --R.normalise y'preNorm 
    R.debugPrint "testMarkVert" 0 $ [ "cl expr normalised" ]ₑ
    -- y'' ← R.formatErrorParts [ y' ]ₑ
    R.typeError [ y' ]ₑ    
    -- R.unify y' h

-- printClExpr : ℕ → PSB.CuTerm → R.TC Unit
-- printClExpr dim y0 = do
--    y ← PSB.vizOrient dim y0
--    y' ← toClExpr 100 dim y >>= ((R.quoteTC {A = ClExpr'} >=> R.normalise)) 
--    -- y'' ← R.formatErrorParts [ y' ]ₑ
--    R.typeError [ y' ]ₑ


-- module PentaJJ1viz {x : A} (p : x ≡ y) (q : y ≡ z) (~r : w ≡ z) (r' r : z ≡ w) (s : w ≡ v) where


--  ex1ClExpr : ClExpr'
--  ex1ClExpr = quoteAsCLExpr (suc (suc zero)) (λ (i j : I) → E.PentaJJ1.P≡Q p q ~r r' r s i j)

-- -- macro
-- --   teeTest : R.Term → R.TC Unit
-- --   teeTest hole = do
-- --     (exitCode , (stdOut , stdErr)) ← RT.execTC "tee" [ "/Users/marcin/agdaTeeTest.txt" ] "abcdeXX"
-- --     R.unify hole (R.lit (R.string stdOut))

-- -- saveString : String → String → R.TC Unit
-- -- saveString f x = do
-- --     (exitCode , (stdOut , stdErr)) ← RT.execTC "tee" [ f ] x
-- --     pure _


-- module assocJ1 {x : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) where


--  assocExpr : ClExpr'
--  assocExpr = quoteAsCLExpr (suc (suc zero)) (λ (i j : I) → (cong sym (assoc (sym r) (sym q) (sym p))) i j)


-- -- module PentaJ1 {x : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (s : w ≡ v) where


-- --  pLHS = -- cong (p ∙_) (assoc q r s) ∙∙ assoc p (q ∙ r) s ∙∙ cong (_∙ s) (assoc p q r)
-- --         assoc p q (r ∙ s) ∙ assoc (p ∙ q) r s

-- --  LHSClExpr : ClExpr'
-- --  LHSClExpr = quoteAsCLExpr (suc (suc zero)) (λ (i j : I) → pLHS i j)

-- --  -- pentaClExpr : ClExpr'
-- --  -- pentaClExpr = quoteAsCLExpr (suc (suc (suc zero))) (λ (i j k : I) →
-- --  --   pentagonIdentity p q r s i j k)



-- -- -- -- module PentaJ1 {x : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (s : w ≡ v) where


-- -- -- --  pLHS = assoc p q (r ∙ s) ∙ assoc (p ∙ q) r s

-- -- -- --  LHSClExpr : ClExpr'
-- -- -- --  LHSClExpr = quoteAsCLExpr (suc (suc zero)) (λ (i j : I) → pLHS i j)



-- -- -- -- -- -- module penta-test {x : A}  (p : x ≡ y) (q : y ≡ z)  (r : z ≡ w) where

-- -- -- -- -- --  -- P Q : x ≡ v
-- -- -- -- -- --  -- P = {!p ∙ q ∙ r' ∙ sym!}
-- -- -- -- -- --  -- Q = {!!}





-- -- -- -- -- --  -- 5LHSi  : _
-- -- -- -- -- --  -- 5LHSi = cong (p ∙_) (assoc q r s) ∙∙ assoc p (q ∙ r) s ∙∙ cong (_∙ s) (assoc p q r)



-- -- -- -- -- --  -- 5LHS : Unit
-- -- -- -- -- --  -- 5LHS = {!extractCuTermTest (suc (suc zero)) λ (i j : I) → (assoc q r s) i j   !}


-- -- -- -- -- --  -- _ : I → I → A
-- -- -- -- -- --  -- _ = {!getCuTerm (suc (suc zero))
-- -- -- -- -- --  --                     (λ (i j : I) → 5LHSi i j)!}

-- -- -- -- -- --  -- assocClExpr : ClExpr'
-- -- -- -- -- --  -- assocClExpr = quoteAsCLExpr (suc (suc zero)) (λ (i j : I) → assoc p q r i j)



-- -- -- -- -- -- -- someViz : Visualisation'
-- -- -- -- -- -- -- someViz =
-- -- -- -- -- -- --  Visualisation (just "abc")
-- -- -- -- -- -- --    (ClExpr 3 (Map.fromList (((Map.fromList (((1 , False))
-- -- -- -- -- -- --      ∷ (2 , False) ∷ [])) , {!!}) ∷ ({!!} , {!!}) ∷ (Map.fromList {!!} , {!!}) ∷ [])))
-- -- -- -- -- -- --    {!!}



-- -- -- -- -- -- -- data ClExpr = ClExpr Int (Map.Map (Map.Map Int Bool) OExpr)
-- -- -- -- -- -- --   deriving (Eq , Show , Read)

-- -- -- -- -- -- -- data ConstExpr = ConstExpr String 
-- -- -- -- -- -- --   deriving (Eq , Show , Read)

-- -- -- -- -- -- -- data CellExpr = CellExpr VarIndex [IExpr]
-- -- -- -- -- -- --   deriving (Eq , Show , Read)

-- -- -- -- -- -- -- data OExpr =
-- -- -- -- -- -- --     HComp (Maybe String) Partial ClExpr
-- -- -- -- -- -- --   | Cell CellExpr
-- -- -- -- -- -- --   | ConstE ConstExpr
-- -- -- -- -- -- --   | CHole Int
-- -- -- -- -- -- --   | Appl ClExpr [ClExpr]  
-- -- -- -- -- -- --   deriving (Eq , Show , Read)


-- -- -- -- -- -- -- data Visualisation =
-- -- -- -- -- -- --     Visualisation (Maybe String) ClExpr ([ (String,(String,Maybe [String]))])  
-- -- -- -- -- -- --  deriving (Show,Read)
