{-# OPTIONS --safe  #-} 
-- -v extractCuTermTest:4  -v checkHcomp:5 -v getCuCaseφ:5
module Cubical.Tactics.PathSolver.Simplify where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Relation.Nullary

open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.List as L
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sigma

open import Cubical.Reflection.Base renaming (v to 𝒗)
import Agda.Builtin.Reflection as R
open import Cubical.Tactics.PathSolver.Reflection
open import Cubical.Tactics.Reflection 
open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Cubical.Tactics.Reflection.Utilities

open import Cubical.Tactics.PathSolver.Base

-- open import Cubical.Tactics.PathSolver.NSolverInfer

private
  variable
    ℓ : Level
    A : Type ℓ
    x y z w v : A

withAppliedDims : ℕ → (R.Term → R.TC R.Term) → (R.Term → R.TC R.Term)
withAppliedDims dim f t = do
  let tL = appNDimsI dim (liftVars.rv dim 0 t)
  vlamⁿ dim <$> addNDimsToCtx dim (f tL)

cuReduce : ℕ → R.Term → R.TC R.Term
cuReduce dim = withAppliedDims dim R.reduce

cuNormalise : ℕ → R.Term → R.TC R.Term
cuNormalise dim = withAppliedDims dim R.normalise

-- module CuSurvivalTests where


--  module _ (dim : ℕ) where
--   macro
--    survTest : R.Term → R.Term → R.Term → R.TC Unit
--    survTest A t _ = do
--      -- t ← cuReduce dim t
--      -- t ← withAppliedDims dim (λ t → R.withNormalisation true $ R.checkType t
--      --      (liftVars.rv dim 0 A)
--      --    ) t
     
--      -- t ← R.normalise t
--      t ← cuReduce dim t
--      R.typeError [ t ]ₑ


--  module Testing where
--   module dcpf-test {x : A} (q : y ≡ z) (p : Path A x y)  (r : z ≡ w) where

--    UU : I → I → A
--    UU = λ i j → doubleCompPath-filler p q r i j

--    UU' : I → I → A
--    UU' = λ i j → UU i j



--    dcpf-cuCaseTest : Unit
--    dcpf-cuCaseTest = {!survTest (suc (suc zero)) A (UU') !}








-- open InferByData


defsToReduce : List R.Name
defsToReduce =
  --   quote getSF2
  -- ∷ quote getSF1
    quote repeat
  ∷ quote offsetR
  ∷ quote hcomp
  ∷ quote fromCu
  ∷ quote $i
  ∷ quote $≡
  ∷ quote inS
  ∷ quote outS
  ∷ []
-- normaliseIfNotHcomp : R.Term → R.TC R.Term
-- normaliseIfNotHcomp = {!!}

-- (R.withReduceDefs (true , defsToReduce ) $

-- module CuCaseTesting where

-- --  module dcpf-test {x : A} (q : y ≡ z) (p : Path A x y)  (r : z ≡ w) where

-- --   UU : I → I → A
-- --   UU i j = doubleCompPath-filler p q r i j



-- --   dcpf-cuCaseTest : Unit
-- --   dcpf-cuCaseTest = {!getCuCaseTest (suc (suc zero)) A (λ (i j : I) → doubleCompPath-filler p q r i j) !}
  
--  module penta-test {x : A} (q : y ≡ z) (p : Path A x y)  (r : z ≡ w) (s : w ≡ v)  where



--   5LHS : Unit
--   5LHS = {!getCuCaseTest (suc (suc zero)) A (λ (i j : I) → (assoc p q (r ∙ s) ∙ assoc (p ∙ q) r s) i j) !}

--   5RHS : Unit
--   5RHS = {!getCuCaseTest 2 (cong (p ∙_) (assoc q r s) ∙∙ assoc p (q ∙ r) s ∙∙ cong (_∙ s) (assoc p q r)) !} 



-- doubleCompPath-fillerFlipped : {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
--                       → Square _ _ _ _
-- doubleCompPath-fillerFlipped p q r = flipSquare $ doubleCompPath-filler p q r
  

-- h-TmTy : ℕ → FExpr → R.Term → R.Term → R.TC (R.Term × R.Type)
-- h-TmTy 1 φ tφ t = pure (R.con (quote case-hcomp1) (repeat 3 (varg R.unknown)) ,
--                       R.def (quote Hcomp1) (vlamⁿ (suc zero) tφ v∷ v[ t ]))
-- h-TmTy 2 φ tφ t =
--    let dcpf-trm = R.def (quote doubleCompPath-fillerFlipped) ((repeat 3 (varg R.unknown)))
--        fc-args =
--           L.map (λ sf → if sf ⊂? φ then varg R.unknown else varg dcpf-trm)
--                   (((nothing ∷ just false ∷ [])) ∷ ((nothing ∷ just true ∷ []))
--                    ∷ ((just false ∷ nothing ∷  [])) ∷ [ just true ∷ nothing ∷  [] ])
--    in pure (R.con (quote case-hcomp2) ((varg R.unknown) ∷ fc-args) ,
--                       R.def (quote Hcomp2) (vlamⁿ (suc (suc zero)) tφ v∷ v[ t ]))
-- h-TmTy _ _ _ _ = R.typeError [ "not implemented in h-TmTy" ]ₑ



toℕTerm : ℕ → R.Term
toℕTerm zero = R.con (quote zero) []
toℕTerm (suc x) = R.con (quote suc) v[ toℕTerm x ]


-- data EvalPoint : Type where
--  cuCase checkHcomp :  


module _ where


 evalOp : R.Term → R.TC R.Term
 evalOp = R.reduce


 getCuCase' : R.Term → R.TC (Maybe ((R.Term × R.Term × R.Term × R.Term) × IExpr))
 getCuCase' (R.def (quote hcomp) ( _ h∷ A h∷ φTm h∷ fcs v∷ v[ cap ])) = do
   -- R.debugPrint "getCuCaseφ" 4 $ "getCuCase' φ :" ∷ₑ [ φTm ]ₑ  
   (just ∘ ((A , φTm , fcs , cap) ,_))  <$> extractIExpr φTm
 getCuCase' _ = pure nothing


 getCuCase : R.Term → R.TC (Maybe ((R.Term × R.Term × R.Term × R.Term) × IExpr))
 getCuCase x = evalOp x >>= ( getCuCase')

 module _ (dim : ℕ) where
  macro
   getCuCaseTest : R.Term → R.Term → R.Term → R.TC Unit
   getCuCaseTest A t h = do
    -- tmDim ← R.quoteTC dim
    -- t ← R.checkType t (R.def (quote I^_⟶_) (tmDim v∷ v[ A ]))
    -- t ← R.reduce t >>= wait-for-term
    -- R.typeError ( [ "input: \n" ]ₑ ++ [ t ]ₑ)
    addNDimsToCtx dim (getCuCase (appNDimsI dim (liftVars.rv dim 0 t))) >>=
     Mb.rec (R.typeError [ "cell" ]ₑ) (λ e → do
        R.typeError (niceAtomList (L.map SubFace→Term (I→F (snd e)))))



  


 extractCuArg : ℕ → ℕ → R.Term → R.TC CuArg


 try𝒄ong : ℕ → ℕ → R.Term → R.TC (Maybe (TermHead × List (R.Arg CuArg)))

 checkHcomp : ℕ → ℕ → R.Term → R.Term → R.Term → R.Term → FExpr → R.TC CuTerm  
 -- extractSubFace : ℕ → ℕ → SubFace →  R.Type → R.Term → R.TC CuTerm
 extractCuTerm' : ℕ → ℕ → R.Term → R.TC CuTerm

 checkHcomp zero _ _ _ _ _ _ = R.typeError [ "checkHcomp FAIL : max depth" ]ₑ
 checkHcomp (suc m) dim A φTm fcs lid φ = do
   -- R.debugPrint "checkHcomp" 4 $ "checkHcomp" ∷ₑ [] --[ chckedHcomp ]ₑ
   -- R.debugPrint "checkHcomp" 4 $ "fcs = " ∷ₑ [  vlamⁿ dim fcs ]ₑ --[ chckedHcomp ]ₑ
   -- R.debugPrint "checkHcomp" 4 $ "lid = " ∷ₑ [  vlamⁿ dim lid ]ₑ --[ chckedHcomp ]ₑ
   -- R.typeError [ vlamⁿ dim fcs ]ₑ
   -- (mapM (λ sf → do
   --         let tmB = (R.def (quote $PI) (liftVars A v∷ (liftVars fcs) v∷ v[ R.var 0 [] ] )) 
   --             sfbo = vlamⁿ (suc (sfDim sf)) (subfaceApp (nothing ∷ sf) tmB)
   --         -- R.debugPrint "checkHcomp" 4 $ (L.map (λ _ → R.strErr "X")  sf)
   --         R.debugPrint "checkHcomp" 4 $ (L.map (R.strErr ∘S Mb.rec ("_") (if_then "1" else "0"  ))  sf)
   --         -- ⦇ ⦇ sf ⦈ , (extractCuTerm' m (suc (sfDim sf)) sfbo) ⦈
   --         ) --extractSubFace d sf A (subfaceApp sf sides)
   --         (φ))
   ⦇ hco
      (mapM (λ sf → do
           let tmA = subfaceRepl sf fcs
               Atm = subfaceRepl sf A
               -- tmA' = replaceVarWithCon (λ { zero → just (quote i0) ; _ → nothing }) fcs 
               tmB = (R.def (quote $PI) ((liftVars Atm) v∷ ((liftVars tmA))
                       v∷ v[ R.var zero [] ] )) 
               sfbo = vlamⁿ (suc (sfDim sf)) tmB
           -- R.debugPrint "checkHcomp" 4 $ "tmA = " ∷ₑ [  vlamⁿ (sfDim sf) tmA ]ₑ --[ chckedHcomp ]ₑ
           -- -- R.debugPrint "checkHcomp" 4 $ "tmA' = " ∷ₑ [  vlamⁿ 1 tmA' ]ₑ --[ chckedHcomp ]ₑ
           -- R.debugPrint "checkHcomp" 4 $ "tmB = " ∷ₑ [  vlamⁿ (suc (sfDim sf)) tmB ]ₑ --[ chckedHcomp ]ₑ
           -- R.debugPrint "checkHcomp" 4 $ "fc = " ∷ₑ [  sfbo ]ₑ --[ chckedHcomp ]ₑ
           -- R.debugPrint "checkHcomp" 4 $ "fcTy = " ∷ₑ [  (tmI^ (suc (sfDim sf)) ⟶ liftVars Atm) ]ₑ
           -- -- sfboN ← R.withNormalisation true $
           -- --         R.checkType sfbo (tmI^ (suc (sfDim sf)) ⟶ liftVars Atm)-- >>= wait-for-term
           -- R.debugPrint "checkHcomp" 4 $ "fcN = " ∷ₑ [  sfboN ]ₑ --[ chckedHcomp ]ₑ
           -- R.typeError (L.map (λ _ → R.strErr "X")  sf)
           ⦇ ⦇ sf ⦈ , (extractCuTerm' m (suc (sfDim sf)) sfbo) ⦈
           ) --extractSubFace d sf A (subfaceApp sf sides)
           (φ))
      (pure (vlamⁿ dim lid) >>= evalOp >>= extractCuTerm' m dim) ⦈ 




 try𝒄ong zero _ _ = R.typeError [ "extractCuTerm FAIL : max depth" ]ₑ

 try𝒄ong (suc m) dim t = do
   -- addNDimsToCtx dim $ R.debugPrint "try𝒄ong" 20 ("try𝒄ong: \n " ∷ₑ [ t ]ₑ)
   Mb.rec (pure nothing) (uncurry (_<$>_ ∘S map-Maybe ∘S _,_) ∘S map-snd tryCuArgs) (match𝒄 t) 
   -- pure nothing

  where
  match𝒄 : R.Term → Maybe (TermHead × List (R.Arg R.Term))
  match𝒄 (R.var x args) = just (var (x ∸ dim) , args)
  match𝒄 (R.con c args) = just (con c , args)
  match𝒄 (R.def f args) = just (def f , args )
  match𝒄 _ = nothing 

 -- try𝒄 : R.Term → Maybe (TermHead × List (R.Arg CuArg))
 --  try𝒄 (R.var x args) = just (var (x ∸ dim) , {!L.map (mapArg ?)!})
 --  try𝒄 (R.con c args) = just (con c , {!!})
 --  try𝒄 (R.def f args) = just (def f , {!!} )
 --  try𝒄 _ = nothing 

  tryCuArgs : List (R.Arg R.Term) →
              R.TC (Maybe (List (R.Arg CuArg)))
  tryCuArgs = ((λ l → if foldr (_and_ ∘S isLeafCuArg ∘S unArg) true l then nothing else just l) <$>_)
    ∘S mapM (mapArgM (extractCuArg m dim)) 

 -- extractSubFace zero _ _ _  _ = R.typeError [ "extractSubFace FAIL : max depth" ]ₑ
 -- extractSubFace (suc m) dim sf A sides = {!!}

  --  (R.extendContext "𝒙" (varg (R.def (quote I) [])) $ do
  -- side ← wait-for-term  (R.def (quote $PI) (liftVars A v∷ (liftVars sides) v∷ v[ R.var 0 [] ] ))


 -- tryNormalise : R.Term → R.TC R.Term
 -- tryNormalise t = R.withReduceDefs (true , defsToReduce ) $ R.normalise t <|> pure t

 extractCuTerm' zero _ _ = R.typeError [ "extractCuTerm FAIL : max depth" ]ₑ
 extractCuTerm' (suc m) dim t = do
   -- t ← R.normalise t'
   -- R.debugPrint "checkHcomp" 0 $ "extractCuTerm : \n" ∷ₑ  [ t ]ₑ
   addNDimsToCtx dim (getCuCase (appNDimsI dim (liftVars.rv dim 0 t))) >>=
    Mb.rec ( (pure t )
             >>= λ tt → --R.debugPrint "checkHcomp" 4 ("cell: \n " ∷ₑ [ tt ]ₑ) >>
               ( (addNDimsToCtx dim $ evalOp (appNDimsI dim (liftVars.rv dim 0 tt)))
                 >>= try𝒄ong m dim ) >>= pure ∘S Mb.rec (cell tt) (uncurry 𝒄ong) 
               )
           λ ((A , φTm , fcs , cap) , φ) → (checkHcomp m dim A φTm fcs cap (L.map (offsetR nothing dim) (I→F φ)))
              -- <|> R.typeError [ "some checkHcomp fail: " ]ₑ ++  [ t ]ₑ)

 extractCuArg zero dim t = R.typeError [ "extractCuTerm FAIL : max depth" ]ₑ
 extractCuArg (suc m) dim t =
   (iArg <$> (addNDimsToCtx dim $ extractIExpr t))
   <|>
   (tArg <$> (extractCuTerm' m dim (vlamⁿ dim t)))


   
   
  

module _ (dim : ℕ) where
 macro
  extractCuTermTest : R.Term → R.Term → R.TC Unit
  extractCuTermTest t _ = do
   cu ← (extractCuTerm' 100 dim t)
   te ← ppCT dim 100 cu
   R.typeError $  te ++ₑ []
   --[ toTerm dim cu ]ₑ

  getCuTerm : R.Term → R.Term → R.TC Unit
  getCuTerm t hole = do
   cu ← (extractCuTerm' 100 dim t)
   R.unify (toTerm dim cu) hole



module App𝑪ongs where

 is𝑪ongFreeFA : List (R.Arg CuArg) → Bool
 is𝑪ongFreeFA [] = true
 is𝑪ongFreeFA (R.arg i (iArg x) ∷ xs) = is𝑪ongFreeFA xs
 is𝑪ongFreeFA (R.arg i (tArg x) ∷ xs) = is𝑪ongFree x and is𝑪ongFreeFA xs
 
 app𝑪ongsTail : List (SubFace × CuTerm) → List (SubFace × CuTerm)

 app𝑪ongsA : ℕ → List (R.Arg CuArg) → List (R.Arg CuArg)
 
 app𝑪ongs : ℕ → CuTerm → CuTerm
 app𝑪ongs dim (hco x x₁) = hco (app𝑪ongsTail x) (app𝑪ongs dim x₁)
 app𝑪ongs _ (cell x) = cell x
 app𝑪ongs dim (𝒄ong th tl) =
  if is𝑪ongFreeFA tl
  then h tl 
  else 𝒄ong th (app𝑪ongsA dim tl)

  where
  h : List (R.Arg CuArg) → CuTerm
  h [] = cell (R.lit (R.string "imposible"))
  h (R.arg i (iArg x) ∷ []) = cell (R.lit (R.string "todo - App𝑪ongs - iArg"))
  h (R.arg i (tArg x) ∷ []) =
        -- mapCuTerm (λ _ → R.unknown) dim x
    mapCuTerm (λ d → TermHead→Term (liftTermHead d th) ∘S [_] ∘S R.arg i) dim x
  h (x ∷ x₁ ∷ x₂) = cell (R.lit (R.string "todo - App𝑪ongs"))
  
 app𝑪ongsTail [] = []
 app𝑪ongsTail ((sf , x) ∷ xs) = 
    (sf , app𝑪ongs (suc (sfDim sf)) x) ∷ app𝑪ongsTail xs

 app𝑪ongsA _ [] = []
 app𝑪ongsA dim (R.arg i (iArg x) ∷ xs) = R.arg i (iArg x) ∷ app𝑪ongsA dim xs
 app𝑪ongsA dim (R.arg i (tArg x) ∷ xs) = R.arg i (tArg (app𝑪ongs dim x)) ∷ app𝑪ongsA dim xs
 -- app𝑪ongsA (R.arg i _ ∷ _) = --[ R.arg i $ tArg $ cell (R.lit (R.string "todo")) ]
 --    R.arg i (tArg (app𝑪ongs x)) ∷ app𝑪ongsA xs




module _ (dim : ℕ) where
 macro
   extractCuTermTestCong : R.Term → R.Term → R.TC Unit
   extractCuTermTestCong t _ = do
    cu ← (extractCuTerm' 100 dim t)
    te ← ppCTn false dim 100 cu
    te' ← ppCTn true dim 100 (App𝑪ongs.app𝑪ongs dim cu)
    
    R.typeError $ te
       -- ++ "\n\n-------\n" ∷ₑ [ toTerm dim cu ]ₑ
       ++ [ "\n\n-------\n appCong: \n" ]ₑ ++ te'
       ++ "\n\n-------\nappCong:\n" ∷ₑ [ toTerm dim (App𝑪ongs.app𝑪ongs dim cu) ]ₑ


-- module ExtractTesting where

--  module cong-test {x : A}
--             {B C : Type ℓ}
--             (f f' : A → B)
--           (g : B → B → C)
--           (p p' : Path A x y) (q q' : y ≡ z)   (r : z ≡ w) where

--   cong1 : I → I → B
--   cong1 i j = cong-∙ f p q i j

--   cong1-test : Unit
--   cong1-test = {!extractCuTermTestCong (suc (suc zero))
--          (λ (i j : I) → cong-∙ f p q i j) !}

--   cong2-test : Unit
--   cong2-test = {!extractCuTermTestCong (suc zero)
--          (λ (i : I) → cong₂ g (cong f (p ∙' q)) (cong f' (p' ∙ q')) i) !}


--   cong1-test' : cong-∙ f p q ≡
--                     getCuTerm (suc (suc zero))
--                       (λ (i j : I) → cong-∙ f p q i j)
--   cong1-test' = refl



 -- module dcpf-test {x : A} (q : y ≡ z) (p : Path A x y)  (r : z ≡ w) where

 --  dcpf-cuCaseTest : Unit
 --  dcpf-cuCaseTest = {!extractCuTermTest (suc (suc zero)) (λ (i j : I) → doubleCompPath-filler p q r i j)!}


 --  codim1 : I → I → A 
 --  codim1 i j = hcomp
 --        h
 --       (q (i ∧ j))
 --    where
 --    h : _
 --    h = (λ k → λ { (i = i0) → p (~ k)
 --                ; (j = i0) → p (~ k)
 --                ; (i = i1)(j = i1) → r k
 --          })


-- --   codim1-test : Unit
-- --   codim1-test = {!extractCuTermTest (suc (suc zero)) codim1!}

-- --   codim2-test : Unit
-- --   codim2-test = {!extractCuTermTest (suc (suc zero)) (λ (i j : I) → (p ∙ q) (i ∨ ~ j))!}


-- --  module SimpleTest (x : A) where

-- --   sqId : (x : A) → Square (λ _ → x) (λ _ → x) (λ _ → x) (λ _ → x)
-- --   sqId x i j = hcomp {φ = i ∨ ~ i ∨ j ∨ ~ j} (λ _ _ → x) x

-- --   U : Square (λ _ → x) (λ _ → x) (λ _ → x) (λ _ → x)
-- --   U = (λ i i₁ → sqId (sqId x i i₁) i i₁)

-- --   Ui : I → I → A
-- --   Ui = λ i i₁ → sqId (sqId x i i₁) i i₁

-- --   testU : Unit
-- --   testU = {! extractCuTermTest (suc (suc zero)) Ui!}

-- --   testCube : Cube
-- --       U (λ _ _ → x)
-- --      (λ _ _ → x) (λ _ _ → x) (λ _ _ → x) (λ _ _ → x)
-- --   testCube z i j = foldConstⁿ 2 (λ i j → I i j) z i j




 -- module penta-test {x : A}  (p : Path A x y) (q : y ≡ z)  (r r' : z ≡ w) (s : w ≡ v)  where

  -- P Q : x ≡ v
  -- P = {!p ∙ q ∙ r' ∙ sym!}
  -- Q = {!!}


  -- 5LHSi  : _
  -- 5LHSi = cong (p ∙_) (assoc q r s) ∙∙ assoc p (q ∙ r) s ∙∙ cong (_∙ s) (assoc p q r)
  
  
  -- 5LHS : Unit
  -- 5LHS = {!extractCuTermTest (suc (suc zero)) (λ (i j : I) → 5LHSi i j)  !}

  -- DCPFi : _
  -- DCPFi = doubleCompPath-filler p q r

  -- DCPF : Unit
  -- DCPF = {!extractCuTermTest (suc (suc zero)) (λ (i j : I) → DCPFi i j)  !}



-- --   -- reflX = refl {x = x}


-- --   -- 5RHS : Unit
-- --   -- 5RHS = {!extractCuTermTest (suc (suc zero))
-- --   --       (λ (i j : I) →
-- --   --        (cong (p ∙_) (assoc q r s) ∙∙ assoc p (q ∙ r) s ∙∙ cong (_∙ s) (assoc p q r)) i j) !} 


-- --   -- simpleTest : I → I → A
-- --   -- simpleTest i j =
-- --   --   hcomp h 
      
-- --   --     (q (i ∨ j))
-- --   --   where
-- --   --   h = (λ z → λ
-- --   --        { (i = i0) (j = i0) → p (~ z)
-- --   --        ; (i = i1) → r z
-- --   --        ; (i = i0) (j = i1) → r' z
-- --   --        })
         
-- --   -- fromCuTest fromCuTest' : I → I → A
-- --   -- fromCuTest = {!extractCuTermTest  (suc (suc zero))
-- --   --       (λ (i j : I) → simpleTest i j )!}

-- --   -- fromCuTest' = {!!}

-- --   -- 5RHSfromCuRefl : I → I → A
-- --   -- 5RHSfromCuRefl = {!getCuTerm (suc (suc zero))
-- --   --       (λ (i j : I) →
-- --   --        (cong (reflX ∙_) (assoc reflX reflX reflX) ∙∙ assoc reflX (reflX ∙ reflX) reflX ∙∙ cong (_∙ reflX) (assoc reflX reflX reflX)) i j)!}



-- --   -- 5RHSfromCu : I → I → A
-- --   -- 5RHSfromCu = {!getCuTerm (suc (suc zero))
-- --   --       (λ (i j : I) →
-- --   --        (cong (p ∙_) (assoc q r s) ∙∙ assoc p (q ∙ r) s ∙∙ cong (_∙ s) (assoc p q r)) i j)!}
  
-- --   -- 5RHSrefl : (cong (p ∙_) (assoc q r s) ∙∙ assoc p (q ∙ r) s ∙∙ cong (_∙ s) (assoc p q r))
-- --   --              ≡
-- --   --             (getCuTerm (suc (suc zero))
-- --   --              (λ (i j : I) →
-- --   --              (cong (p ∙_) (assoc q r s)
-- --   --                ∙∙ assoc p (q ∙ r) s
-- --   --                  ∙∙ cong (_∙ s) (assoc p q r)) i j))
-- --   -- 5RHSrefl = refl  

module FoldCongⁿ where



  foldCong : ℕ → List TermHead → CuCtx → CuTerm → CuTerm
  foldCongFill : ℕ → List TermHead → CuCtx 
       → List (SubFace × CuTerm) → CuTerm → List (SubFace × CuTerm)

  foldCongFill zero ths ctx _ _ =
    [ ([] , cell (R.lit (R.string "FoldCongⁿ fail - run out of magic number"))) ]
  foldCongFill (suc m) [] ctx xs cu = []
  foldCongFill (suc m) ths@(_ ∷ _) ctx xs cu = 
    let sfI0 = repeat (length (freeVars ctx) ∸ 1) nothing ∷ʳ just false
        ctx' = take (length ctx ∸ 1) ctx ∷ʳ ("" , just false) 
        fl =
             global2local ctx' $
            R.def (quote hcomp-congI')
                   (R.unknown
                    v∷ 
                       (vlam "a"
                           (foldl (λ x th → TermHead→Term
                              (liftTermHead (1 + length ( ctx)) th)
                              v[ x ]) (𝒗 0) ths)
                           )
                    v∷ ( (vlam "𝒛F" ((ToTerm.toSides ctx xs))))
                    v∷ (( R.def (quote inS)
                          v[(ToTerm.toTerm ctx cu) ] ))
                    v∷ [] )
    in  [(sfI0 , cell (vlamⁿ (length (freeVars ctx')) fl))]

  foldCong zero _ _ _ = cell (R.lit (R.string "FoldCongⁿ fail - run out of magic number")) 
  foldCong (suc m) ths ctx (hco x cu) = 
     hco (foldCongFill m ths ctx x cu ++
        L.map (λ (sf , ct) → 
             sf , (foldCong m ths (("𝒛" , nothing) ∷ applyFaceConstraints sf ctx) ct))
               x)
      (foldCong (suc m) ths ctx cu)
  foldCong (suc m) ths ctx (𝒄ong th v[ tArg x ]) =
    foldCong (suc m) (th ∷ ths) ctx x
  foldCong (suc m) ths ctx (𝒄ong x _) =
    cell (R.lit (R.string "FoldCongⁿ fail - not implemented"))
    
  foldCong (suc m) ths ctx (cell x) = cell $
     (mapTermUnderDims (length (freeVars ctx))
       (λ x → foldl (λ x th → TermHead→Term
            (liftTermHead (length $ freeVars ctx) th)
            v[ x ]) x ths)) x




  module _ (dim : ℕ) where
   macro
    congHcompⁿ : R.Term → R.Term → R.TC Unit
    congHcompⁿ t hole = do

      cu ← extractCuTerm' 100 dim t
      let cuLifted = cuTermInsLift 1 cu
          ctx = (defaultCtx dim ++ [ ( "𝑖" , nothing) ])
          pCu = foldCong 100 [] ctx cuLifted
          pTerm = vlamⁿ ((length ctx)) (ToTerm.toTerm ctx pCu) 
      R.unify pTerm hole
      -- R.typeError [ pTerm ]ₑ

open FoldCongⁿ using (congHcompⁿ)

module CongSolveTest where

 module T0 {x : A} {B : Type ℓ} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) --(s : w ≡ v)
            (f : A → B) where

  lhs rhs : f x ≡ f w
  lhs = cong f (p ∙∙ q ∙∙ r)
  rhs = cong f p ∙∙ cong f q ∙∙ cong f r

  eq1 : Square {A = B}
          lhs
          rhs
          refl
          refl


  eq1 = congHcompⁿ (suc zero) (λ (i : I) → lhs i) 


 module T1 {x : A} {B C : Type ℓ} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (s : w ≡ v)
            (f : A → B) (g : B → C) where

  lhs rhs mid : g (f x) ≡ g (f v)
  lhs = cong g (cong f p) ∙∙ cong (g ∘ f) (q ∙ r) ∙∙ cong g (cong f s)
  rhs = cong g (cong f p ∙∙ cong f q ∙ cong f r ∙∙ cong f s)

  mid = cong (g ∘ f) p ∙∙ cong (g ∘ f) q ∙ cong (g ∘ f) r ∙∙ cong (g ∘ f) s

  lhs≡rhs : lhs ≡ rhs  
  lhs≡rhs = (congHcompⁿ (suc zero) λ (i : I) → lhs i) ∙
     (sym (congHcompⁿ (suc zero) λ (i : I) → rhs i))


  testCu1 : Cube
             (λ i j → f (doubleCompPath-filler p q r i j))
             (λ i j → doubleCompPath-filler (cong f p) (cong f q) (cong f r) i j)
             refl (congHcompⁿ (suc zero) (λ (i : I) → f ((p ∙∙ q ∙∙ r) i)))
             refl refl
  testCu1 =
     congHcompⁿ (suc (suc zero))
       (λ (i j : I) → f (doubleCompPath-filler p q r i j))

  CU2 : Square
          (cong g (cong f q))
          (cong g (cong f p ∙∙ cong f q ∙∙ cong f (r ∙ s)  ))
          (cong g (cong f (sym p)))
          (cong g (cong f (r ∙ s)))
  CU2 i j =
    g (doubleCompPath-filler (cong f p) (cong f q)
        (cong f (r ∙ s)) i j)



  testCu2 : Path (I → I → C)
             (λ i j → CU2 i j)
             _ 

  testCu2 =

     congHcompⁿ (suc (suc zero))
       (λ (i j : I) → CU2 i j)

  testCu2cu : Cube
       CU2
       (doubleCompPath-filler
         (cong (g ∘ f) p)
         (cong (g ∘ f) q)
         ((cong (g ∘ f) r) ∙ (cong (g ∘ f) s)))
       refl ((congHcompⁿ (suc zero)
         (λ (i : I) → CU2 i1 i)))
       refl ((congHcompⁿ (suc zero)
         (λ (i : I) → CU2 i i1)))
       
  testCu2cu =

     congHcompⁿ (suc (suc zero))
       (λ (i j : I) → CU2 i j)


module CongAssoc {B : Type ℓ} {x : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (f : A → B) where

 assocCuTest : Cube  (cong (cong f) (assoc p q r))
                     (assoc (cong f p) (cong f q) (cong f r))
                     _ _
                     refl refl
 assocCuTest = 
     congHcompⁿ (suc (suc zero))
       (λ (i j : I) → (cong (cong f) (assoc p q r)) i j)



module FoldConstⁿ where

 module _ (endTerm : Bool) where
  foldStep : ℕ → CuTerm → CuTerm
  foldStepL : List (SubFace × CuTerm) → List (SubFace × CuTerm)
  foldStepL [] = []
  foldStepL ((sf , x) ∷ xs) =
    (sf , foldStep (suc (sfDim sf)) x) ∷ foldStepL xs


  foldStep k h@(hco x cu) =
    if (almostLeafQ h)
    then
       (if endTerm
        then cu
        else (hco ((repeat (k ∸ 1) nothing ++ [ just true ] ,
                cu) ∷ x) cu))
    else hco (foldStepL x)
           (foldStep k cu)
  foldStep k (cell x) = cell x
  foldStep k (𝒄ong h l) = 𝒄ong h l -- this shoudl be imposible for refl!,
      -- it should threw some error ideallly




 module _ n where


  redStepTerm : CuTerm → (R.Term × (CuTerm × CuTerm))
  redStepTerm cu =
    let cuLifted = cuTermInsLift 1 cu
        pTerm = foldStep false (suc n) cuLifted
    in (toTerm (suc n) pTerm , (pTerm , foldStep true n cu))



  pathCus : ℕ → CuTerm → List (R.Term × (CuTerm × CuTerm))
  pathCus zero cu = []
  pathCus (suc k) cu =
   if cellQ cu
   then []
   else 
    let (tm , (cu* , cu')) = redStepTerm cu
    in (tm , (cu* , cu')) ∷ pathCus k cu' 


  pathTerms' : ℕ → CuTerm → List R.Term
  pathTerms' k = L.map (fst) ∘S pathCus k
  -- pathTerms' zero cu = []
  -- pathTerms' (suc k) cu =
  --  if cellQ cu
  --  then []
  --  else 
  --   let (tm , cu') = redStepTerm cu
  --   in vlamⁿ (suc n) tm ∷ pathTerms' k cu' 


  macro
   foldConstⁿ : R.Term → R.Term → R.TC Unit
   foldConstⁿ t' hole = do
     t ← wait-for-term t'
     cu ← extractCuTerm' 100 n t

     -- addNDimsToCtx n $ ((ppCT 100 cu) >>= R.typeError)
     let pTrm = (foldR∙ (pathTerms' 100 cu))

     -- -- print consecutive CuTerms
     -- addNDimsToCtx' "𝒋" 1 $ addNDimsToCtx n $ concatMapM ((ppCT 100 >=& (_++ [ "\n------\n " ]ₑ)))
     --   (map (fst ∘ snd) (pathCus 100 cu)) >>= R.typeError

     -- R.typeError [ pTrm ]ₑ
     R.unify pTrm hole

   simplifyReflⁿ : R.Term → R.TC Unit
   simplifyReflⁿ hole = do
    
    (A' , (t0' , t1')) ← R.inferType hole >>= wait-for-term >>= (get-boundaryWithDom ) >>= Mb.rec
     (R.typeError [ R.strErr "unable to get boundary" ])
     pure

    let t = vlamⁿ n $ appNDims≡ n (liftVars.rv n 0 t0')
    t ← wait-for-term t
    cu ← extractCuTerm' 100 n t
    let pTrm = (foldR∙ (pathTerms' 100 cu))
    -- R.typeError [ pTrm ]ₑ
    R.unify pTrm hole
    -- foldConstⁿ {!!} hole 

open FoldConstⁿ using (foldConstⁿ ; simplifyReflⁿ) public


module SimpleTest (x : A) where

 sqId : (x : A) → Square (λ _ → x) (λ _ → x) (λ _ → x) (λ _ → x)
 sqId x i j = hcomp {φ = i ∨ ~ i ∨ j ∨ ~ j} (λ _ _ → x) x

 U : Square (λ _ → x) (λ _ → x) (λ _ → x) (λ _ → x)
 U = (λ i i₁ → sqId (sqId x i i₁) i i₁)


 testSimplify : Cube
    U (λ _ _ → x)
    (λ _ _ → x) (λ _ _ → x) (λ _ _ → x) (λ _ _ → x)

 
 testSimplify = simplifyReflⁿ (suc (suc zero))

module SimpleTest2D (x : A) where


 U : Square (λ _ → x) (refl ∙∙ (refl ∙ refl) ∙∙ refl)  (λ _ → x) (λ _ → x)
 U = rUnit refl ∙ rUnit (refl ∙ refl)


 testSimplify' : Path (I → I → A) (λ i j → U i j) λ _ _ → x
 testSimplify' = foldConstⁿ (suc (suc zero)) λ (i j : I) → U i j

 ttSide : Square (refl ∙∙ refl ∙ refl ∙∙ refl) (λ _ → x)
      refl refl --(refl ∙∙ refl ∙∙ refl) (refl ∙∙ refl ∙∙ refl)
 ttSide = foldConstⁿ (suc zero) (λ (i : I) → U i1 i)

 testSimplify : Cube
    U  (λ _ _ → x)
     {refl ∙∙ refl ∙∙ refl}
     {refl ∙∙ refl ∙∙ refl} 
    (flipSquare (refl {x = refl ∙∙ refl ∙∙ refl})) --(λ i i₁ → testSimplify' i i0 i₁)
    {refl ∙∙ refl ∙∙ refl}
    {refl ∙∙ refl ∙∙ refl}
    
    -- (λ i i₁ → x)
     --(foldConstⁿ (suc zero) λ (i : I) → U i1 i)
     (λ i i₁ → testSimplify' i i1 i₁)
     -- (flipSquare {!!})
     (flipSquare (refl {x = refl ∙∙ refl ∙∙ refl}))
     (flipSquare (refl {x = refl ∙∙ refl ∙∙ refl}))
     -- (λ i i₁ → testSimplify' i i₁ i0)
     -- (λ i i₁ → testSimplify' i i₁ i1)
    -- (λ _ → (λ _ → x) ∙∙ (λ _ → x) ∙∙ (λ _ → x))

 
 testSimplify i j k = testSimplify' i j k
   -- foldConstⁿ (suc (suc zero)) λ (i j : I) → U i j


-- module PentaJ {x : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (s : w ≡ v) where


--  pentagonTy = assoc p q (r ∙ s) ∙ assoc (p ∙ q) r s
--              ≡ cong (p ∙_) (assoc q r s) ∙∙ assoc p (q ∙ r) s ∙∙ cong (_∙ s) (assoc p q r)



-- pJ : ∀ {x : A} (p : x ≡ y) (q : y ≡ z)
--           (r : z ≡ w) (s : w ≡ v) → PentaJ.pentagonTy p q r s

-- pJ {x = x} =
--     J (λ y p → ∀ q r s → PentaJ.pentagonTy p q r s)
--    (J (λ z q → ∀ r s → PentaJ.pentagonTy refl q r s)
--    (J (λ w r → ∀ s → PentaJ.pentagonTy refl refl r s)
--    (J (λ v s → PentaJ.pentagonTy refl refl refl s)
--     (cong flipSquare
--          (flipSquareP (CompSquares.compSquaresPath→Cube
--             refl
--             (flipSquare (assoc refl refl (refl ∙ refl) ∙ assoc (refl ∙ refl) refl refl))
--             (flipSquare
--               (cong (refl ∙_) (assoc refl refl refl) ∙∙
--                 assoc refl (refl ∙ refl) refl ∙∙ cong (_∙ refl) (assoc refl refl refl)))
--             (λ i _ → (refl {x = x} ∙ refl ∙ refl ∙ refl) i)
--             (λ i _ → ((((λ _ → x) ∙ (λ _ → x)) ∙ (λ _ → x)) ∙ (λ _ → x)) i)
--             refl
--             (simplifyReflⁿ (suc (suc zero)))
--             ))))))
