{-# OPTIONS --safe -v 3  #-} 

module Cubical.Tactics.PathSolver.Coherence where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Relation.Nullary

open import Cubical.Algebra.Group.Free

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

open import Cubical.Tactics.PathSolver.Simplify

private
  variable
    ℓ : Level
    A B : Type ℓ
    x y z w v : A

open NormalForm ℕ
open Discrete discreteℕ

Vert : Type
Vert = List Bool


_[·]_ : [𝟚× ℕ ] → [𝟚× ℕ ] → [𝟚× ℕ ]
xs [·] ys = foldr η· ys xs


mb~ : Bool → ℕ → R.Term
mb~ b k = if b then (vlam "𝓲~" $ R.var (suc k) v[ 𝒗 0 ]) else
   (vlam "𝓲~" $ R.var (suc k) v[ R.def (quote ~_) v[ 𝒗 0 ] ])

∙tmSides : ∀ (ϕ : I) → A → (I → A) → I → Partial (~ ϕ ∨ ϕ) A
∙tmSides ϕ p q i (ϕ = i0) = p
∙tmSides ϕ p q i (ϕ = i1) = q i

 
-- ∙tm : R.Term → Bool → ℕ → R.Term
-- ∙tm t b k =
--    R.def (quote hcomp)
--      (R.def (quote ∙tmSides) (𝒗 0 v∷ t v∷ v[ mb~ b (suc k) ]) 
--       v∷ v[ t ])

-- [𝟚×ℕ]→PathTerm' : [𝟚× ℕ ] → Maybe R.Term
-- [𝟚×ℕ]→PathTerm' [] = nothing
-- [𝟚×ℕ]→PathTerm' ((b , k) ∷ []) = just $ ∙tm
--    (R.def (quote $i) (vlam "ra" (R.var (suc (suc k)) v[ 𝒗 0 ]) v∷ v[ endTerm (not b) ])) b k  
-- [𝟚×ℕ]→PathTerm' ((b , k) ∷ xs) =
--    map-Maybe (λ t → ∙tm t b k) ([𝟚×ℕ]→PathTerm' xs)

-- [𝟚×ℕ]→PathTerm : [𝟚× ℕ ] → Maybe R.Term
-- [𝟚×ℕ]→PathTerm = map-Maybe (vlam "i") ∘ [𝟚×ℕ]→PathTerm'

[𝟚×ℕ]→PathTerm : [𝟚× ℕ ] → R.Term
[𝟚×ℕ]→PathTerm [] = Rrefl
[𝟚×ℕ]→PathTerm ((b , k) ∷ []) = R∙ (vlam "ri" (R.var (suc k) v[ endTerm (not b) ]))
          (if b then 𝒗 k else Rsym (𝒗 k))
[𝟚×ℕ]→PathTerm ((b , k) ∷ xs) = R∙ ([𝟚×ℕ]→PathTerm xs) (if b then 𝒗 k else Rsym (𝒗 k))

[𝟚×ℕ]→FillTerm : (Bool × ℕ) → [𝟚× ℕ ] → R.Term
[𝟚×ℕ]→FillTerm (b , k) [] =
    R.def (quote compPath-filler) ((vlam "ri" (R.var (suc k) v[ endTerm (not b) ]))
         v∷ v[ if b then 𝒗 k else Rsym (𝒗 k) ])
[𝟚×ℕ]→FillTerm (b , k) xs =
  R.def (quote compPath-filler) ([𝟚×ℕ]→PathTerm xs v∷ v[ if b then 𝒗 k else Rsym (𝒗 k) ])


--    -- map-Maybe (λ t → ∙tm t b k) ([𝟚×ℕ]→PathTerm xs)



module [𝟚×ℕ]→PathTerm-test where

 module _ (l : [𝟚× ℕ ]) where
  macro
   [𝟚×ℕ]→PathTerm-test : R.Term → R.TC Unit
   [𝟚×ℕ]→PathTerm-test h = do
     let tm = [𝟚×ℕ]→PathTerm l
     -- R.typeError [ tm ]ₑ
     R.unify tm h


 module T1 {x : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (s : w ≡ v) where

  t1[] : [𝟚× ℕ ]
  t1[] = (false , 3) ∷ (false , 2) ∷
         (false , 1) ∷
         [ false , 0 ]   
  
  t1 : v ≡ x
  t1 = [𝟚×ℕ]→PathTerm-test t1[]

tryCastAsNoCongS :  (List (SubFace × CuTerm)) → R.TC (List (SubFace × CuTerm' ⊥ Unit))


tryCastAsNoCong : CuTerm → R.TC (CuTerm' ⊥ Unit)
tryCastAsNoCong (hco x x₁) = 
    ⦇ hco (tryCastAsNoCongS x) (tryCastAsNoCong x₁) ⦈
tryCastAsNoCong (cell x) = pure $ cell' _ x
tryCastAsNoCong (𝒄ong' x x₁) =
 R.typeError $ [ "tryCastAsNoCong failed " ]ₑ


tryCastAsNoCongS [] = ⦇ [] ⦈
tryCastAsNoCongS ((sf , x) ∷ xs) =
  ⦇ (⦇ ⦇ sf ⦈ , (tryCastAsNoCong x) ⦈) ∷ (tryCastAsNoCongS xs) ⦈


foldCells : (A → B → B) → CuTerm' ⊥ A → B → B
foldCells {A = A} {B = B} f = fc
 where
 fcs : List (SubFace × CuTerm' ⊥ A) → B → B
 
 fc : CuTerm' ⊥ A → B → B
 fc (hco x x₂) b = fc x₂ (fcs x b)
 fc (cell' x x₂) b = f x b

 fcs [] b = b
 fcs ((_ , x) ∷ x₂) b = fcs x₂ (fc x b)


visitCellsM : (A → R.TC Unit) → CuTerm' ⊥ A → R.TC Unit
visitCellsM {A = A} f = vc
 where

 vcs : List (SubFace × CuTerm' ⊥ A) → R.TC Unit

 vc : CuTerm' ⊥ A → R.TC Unit
 vc (hco x x₁) = vc x₁ >> vcs x >> pure _
 vc (cell' x x₁) = f x

 vcs [] = pure _
 vcs ((_ , x) ∷ xs) = vc x >> vcs xs
 
data CellVerts : Type where
  cv0 : [𝟚× ℕ ] → [𝟚× ℕ ] → CellVerts
  cvN : CellVerts → CellVerts → CellVerts


mapCellVerts : (f : [𝟚× ℕ ] → [𝟚× ℕ ]) → CellVerts → CellVerts
mapCellVerts f (cv0 x x₁) = cv0 (f x) (f x₁)
mapCellVerts f (cvN x x₁) = cvN (mapCellVerts f x) (mapCellVerts f x₁)

cellVert : CellVerts → Vert → R.TC [𝟚× ℕ ] 
cellVert (cv0 x x₂) (false ∷ []) = pure x
cellVert (cv0 x x₂) (true ∷ []) = pure x₂
cellVert (cvN x x₂) (false ∷ x₃) = cellVert x x₃
cellVert (cvN x x₂) (true ∷ x₃) = cellVert x₂ x₃
cellVert _ _ =  R.typeError $ [ "cellVert failed " ]ₑ

matchAtomPa : R.Term → R.TC (Maybe (Bool × ℕ))
matchAtomPa (R.var x []) = ⦇ nothing ⦈
matchAtomPa (R.var x v[ R.var zero [] ]) = ⦇ just (⦇ (true , x) ⦈) ⦈
matchAtomPa (R.var x v[ R.def (quote ~_) v[ R.var zero [] ] ]) =
   ⦇ just (⦇ (false , x) ⦈) ⦈
matchAtomPa t = R.typeError $ "unexpected in matchAtomPA : " ∷ₑ [ t ]ₑ

getAtomPa : R.Term → R.TC [𝟚× ℕ ]
getAtomPa t = addNDimsToCtx 1 $ do
  let t' = liftVars t
  tn ← R.normalise (appNDimsI 1 t')
  Mb.rec [] [_] <$> matchAtomPa tn

print[𝟚×] :  [𝟚× ℕ ] → List R.ErrorPart
print[𝟚×] x = join (L.map (λ (b , v)
            → ",(" ∷ₑ (if b then "T," else "F,") ∷ₑ [ v ] ++ₑ [ ") " ]ₑ ) x)

CellVerts→List : CellVerts → List (Vert × [𝟚× ℕ ])
CellVerts→List (cv0 x x₁) = ([ false ] , x) ∷ [ [ true ] , x₁ ] 
CellVerts→List (cvN x x₁) = 
  L.map (map-fst (false ∷_)) (CellVerts→List x)
   ++ L.map (map-fst (true ∷_)) (CellVerts→List x₁)

listToMaybe : List A → Maybe A
listToMaybe [] = nothing
listToMaybe (x ∷ _) = just x

allEqual? : Discrete A → List A → Bool
allEqual? _≟_ (x ∷ (y ∷ xs)) = Dec→Bool (x ≟ y) and allEqual? _≟_ (y ∷ xs)
allEqual? _≟_ _ = true

findBy : (A → Bool) → List A → Maybe A
findBy t [] = nothing
findBy t (x ∷ xs) = if t x then just x else findBy t xs

cellVertsHead : CellVerts → Maybe (Bool × ℕ) × [𝟚× ℕ ]  
cellVertsHead cv =
 let l = L.map (snd) $ CellVerts→List cv
     lM = L.map (length) l
     
     
 in if (allEqual? discreteℕ lM) then nothing , Mb.fromMaybe [] (listToMaybe l) else
     let maxL = foldr max 0 lM
     in Mb.rec (nothing , []) (λ x → listToMaybe x , tail x) (findBy (λ x → Dec→Bool $ discreteℕ (length x) maxL ) l)
          
printCellVerts : CellVerts → List (R.ErrorPart)
printCellVerts = (join ∘ L.map
   (λ (v , x) →  L.map (if_then "□" else "◼") v ++ₑ print[𝟚×] x ++ₑ [ "\n" ]ₑ)) ∘ CellVerts→List 

module GetAtomPaTests where

 macro
  getAtomPaTest : R.Term → R.Term → R.TC Unit
  getAtomPaTest t _ = do
    x ← L.map (map-snd predℕ) <$> getAtomPa t
    R.typeError ("got :" ∷ₑ print[𝟚×] x)

 -- module _ (p : x ≡ y) (q : y ≡ z) where
 --  getAtomPaTest1 : Unit
 --  getAtomPaTest1 = {!getAtomPaTest (λ (i : I) → (p ∙ q) i)!}




getTermVerts : ℕ → R.Term → R.TC CellVerts
getTermVerts zero x₁ = R.typeError [ "imposible - getTermsVerts" ]ₑ
getTermVerts (suc zero) t = do
  p ← getAtomPa t
  pure (cv0 [] p)
getTermVerts (suc (suc zero)) t = do
  p0i ← getAtomPa (subfaceCell (nothing ∷ [ just false ]) t)
  pi0 ← getAtomPa (subfaceCell (just false ∷ [ nothing ]) t)
  p1i ← getAtomPa (subfaceCell (nothing ∷ [ just true ]) t)
  pure $ cvN (cv0 [] pi0 ) (cv0 p0i (p1i [·] pi0) )
getTermVerts (suc (suc (suc x))) x₁ =
  R.typeError [ "not impemented - getTermsVerts" ]ₑ

module GetTermVertsTests where

 module _ (dim : ℕ) where
  macro
   getTermVertsTest : R.Term → R.Term → R.TC Unit
   getTermVertsTest t h = do
    r ← getTermVerts dim t
    r' ← R.quoteTC r
    R.unify r' h

 -- module _ (p : x ≡ y) (q : y ≡ z) where
 --  getTermVertsTest1 : CellVerts
 --  getTermVertsTest1 = {!getTermVertsTest (suc (suc zero)) (λ (i j : I) → p (~ j  ∧ i))!}




Edge : Type
Edge = SubFace

-- getEdge : Edge → CuTerm' ⊥ CellVerts → [𝟚× ℕ ]
-- getEdge = {!!}

getVert : ℕ → Vert → CuTerm' ⊥ ((Maybe IExpr) × CellVerts) → R.TC [𝟚× ℕ ] 
getVert zero v (hco xs _) =  R.typeError [ "ran out of magic in getVert" ]ₑ
getVert (suc m) v (hco xs _) = do
  (sf , x) ← Mb.rec (R.typeError [ "imposible getVert" ]ₑ) pure
              $ findBy ((L.map just v ⊂?_) ∘ [_] ∘ fst) xs
  let v' : Vert
      v' = (L.map (snd) $ (filter ((λ { nothing → true ; _ → false }) ∘S fst)
                (zipWith _,_ sf v)))
  getVert m (true ∷ v') x  
getVert _ x (cell' (_ , x₁) _) = cellVert x₁ x
  -- -- R.debugPrint "" 3 ( [ "cellVert: " ]ₑ ++ₑ print[𝟚×] l)                
  -- pure l


getIArg : ℕ → R.Term → R.TC (Maybe IExpr)
getIArg dim t = addNDimsToCtx dim $ do
  (R.normalise $ appNDimsI dim (liftVars.rv dim 0 t)) >>= h

 where
 h : R.Term → R.TC (Maybe IExpr)
 h (R.var x []) = ⦇ nothing ⦈
 h (R.var x v[ a ]) = just <$> extractIExpr a
 h t = R.typeError $ "unexpected in getIArg :" ∷ₑ [ t ]ₑ 
markVert : ℕ → ℕ → [𝟚× ℕ ] → (CuTerm' ⊥ Unit) → R.TC (CuTerm' ⊥ ((Maybe IExpr) × CellVerts))

getPaThruPartial : ℕ → Vert → List (SubFace × CuTerm' ⊥ Unit) → R.TC [𝟚× ℕ ]
getPaThruPartial m v xs = do
  (sf , x) ← Mb.rec (R.typeError [ "imposible gptp" ]ₑ) pure
              $ findBy ((L.map just v ⊂?_) ∘ [_] ∘ fst) xs
  let v' : Vert
      v' = (L.map (snd) $ (filter ((λ { nothing → true ; _ → false }) ∘S fst)
                (zipWith _,_ sf v)))
  xs' ← markVert m (suc (sfDim sf)) [] x                
  p0 ← getVert m (false ∷ v') xs'
  p1 ← getVert m (true ∷ v') xs'
  pure $ p1 [·] (invLi p0)

markVert zero dim w (hco x cu) = R.typeError [ "ran out of magic in markVert" ]ₑ
markVert (suc m) dim w (hco x cu) = do
  -- markedVerts ← mapM (λ (sf , x) → ⦇ ⦇ sf ⦈ , markVert m (suc (sfDim sf)) [] x ⦈) x
  paToLid ← invLi <$> (getPaThruPartial m (repeat dim false) x)
  markedCu ← markVert m dim (paToLid [·] w) cu
  fixedVerts ← mapM (λ (sf , x) → do
                 vv ← (getVert m (L.map (Mb.fromMaybe false) sf) markedCu)
                 ⦇ ⦇ sf ⦈ , markVert m (suc (sfDim sf)) vv x ⦈) x
  pure $ hco fixedVerts markedCu
markVert _ dim w (cell x) =
  ⦇ cell'
     ⦇ (getIArg dim x) , mapCellVerts (_[·] w) <$> getTermVerts dim x ⦈
     (⦇ x ⦈)
     ⦈


getMaxWordLen : CuTerm' ⊥ ((Maybe IExpr) × CellVerts) → ℕ
getMaxWordLen x = foldCells (flip (foldl max)  ∘ L.map (length ∘ snd) ∘ CellVerts→List ∘ snd) x zero 

flipOnFalse : Bool → R.Term → R.Term
flipOnFalse b t = if b then t else R.def (quote ~_) v[ t ] 

module MakeFoldTerm (t0 : R.Term) where

 -- ilSF : ℕ → SubFace → SubFace

 -- ilSF _ [] = []
 -- ilSF zero xs@(_ ∷ _) = repeat k nothing ++ xs
 -- ilSF (suc n) (x ∷ xs) = x ∷ ilSF n xs

 cellTerm : ℕ → (Maybe IExpr) × (Maybe (Bool × ℕ) × [𝟚× ℕ ]) → R.Term → R.Term 
 cellTerm dim (mbi , nothing , []) t = vlam "ii" (liftVars t)
 cellTerm dim (mbi , nothing , tl@(_ ∷ _)) t = --R.unknown
    vlam "ii" (vlamⁿ dim (R.def (quote $≡) (liftVars.rv dim 0 ([𝟚×ℕ]→PathTerm tl) v∷
       v[ R.def (quote ~_) v[ 𝒗 dim ] ])))
 cellTerm dim (just ie , just x , tl) t = --vlamⁿ 1 (liftVars.rv 1 0 t)
   
    vlam "ii" (vlamⁿ (dim) (R.def (quote $≡)
         (R.def (quote $≡) (liftVars.rv dim 0 ([𝟚×ℕ]→FillTerm x tl) v∷
            v[ flipOnFalse (fst x) (IExpr→Term ie) ]) v∷
       v[ R.def (quote ~_) v[ 𝒗 dim ] ])))
 cellTerm _ _ _ = R.lit (R.string ("unexpected in MakeFoldTerm.cellTerm"))
   -- let (zz , yy) = cellVertsHead cv
   -- in Mb.rec (vlam "ii" (liftVars $ [𝟚×ℕ]→PathTerm yy)) {!!} zz
 

 ctils : List (SubFace × (CuTerm' ⊥ ((Maybe IExpr) × CellVerts))) → List (SubFace × CuTerm)
 
 ctil : ℕ → (CuTerm' ⊥ ((Maybe IExpr) × CellVerts)) → CuTerm
 ctil dim (hco x c) =
   hco ((repeat dim nothing ++ [ just true ] , cell (vlamⁿ (suc dim) (liftVars.rv (suc dim) 0 t0)))
            ∷ ctils x)
          (ctil dim c)
 ctil dim (cell' cv x) = cell' tt $ cellTerm dim (map-snd cellVertsHead cv) x
 -- cell $
 --   let (zz , yy) = cellVertsHead cv
 --   in Mb.rec (vlam "ii" (liftVars $ [𝟚×ℕ]→PathTerm yy)) {!!} zz
   
   -- cell $ vlamⁿ k (liftVars.rv k 0 x)
 -- ctil (𝒄ong h l) = 𝒄ong h (ctila l)

 ctils [] = []
 ctils ((sf , x) ∷ xs) = 
   (sf ++ [ nothing ] , ctil (suc (sfDim sf)) x) ∷ ctils xs


makeFoldTerm : R.Term → ℕ → (CuTerm' ⊥ ((Maybe IExpr) × CellVerts)) → CuTerm
makeFoldTerm = MakeFoldTerm.ctil


module TestMarkVert where


 module _ (dim : ℕ) where
  macro
   testMarkVert : R.Term → R.Term → R.TC Unit
   testMarkVert t h = do
     cu ← extractCuTerm' 100 dim t
     cu' ← tryCastAsNoCong cu <|> R.typeError [ "failed to cast to no cong" ]ₑ
     mv ← markVert 100 dim [] cu'     
     visitCellsM (λ (mbIx , cv) → do
       Mb.rec (R.debugPrint "testMarkVert" 3 [ "noIExpr" ]ₑ)
               (R.debugPrint "testMarkVert" 3 ∘ [_]ₑ ∘ vlamⁿ dim ∘  IExpr→Term) mbIx
       ((R.debugPrint "testMarkVert" 3 ∘ ("cellMarks : \n" ∷ₑ_) ∘ printCellVerts) cv)  ) mv
     R.debugPrint "testMarkVert" 3 $ "max word: " ∷ₑ [ (getMaxWordLen mv ) ]ₑ
     
     R.typeError $ [ "ok" ]ₑ

  macro
   mkEqTerm : R.Term → R.Term → R.Term → R.TC Unit
   mkEqTerm t0 t h = do
     cu ← extractCuTerm' 100 dim t
     cu' ← tryCastAsNoCong cu <|> R.typeError [ "failed to cast to no cong" ]ₑ
     mv ← markVert 100 dim [] cu'     
     -- visitCellsM (λ (mbIx , cv) → do
     --   Mb.rec (pure _) (R.debugPrint "testMarkVert" 3 ∘ [_]ₑ ∘ vlamⁿ dim ∘  IExpr→Term) mbIx
     --   ((R.debugPrint "testMarkVert" 3 ∘ ("cellMarks : \n" ∷ₑ_) ∘ printCellVerts) cv)  ) mv
     -- R.debugPrint "testMarkVert" 3 $ "max word: " ∷ₑ [ (getMaxWordLen mv ) ]ₑ
     
     -- R.typeError $ [ "ok" ]ₑ
     let cu = makeFoldTerm t0 dim mv
     -- te ← ppCTn false dim 100 cu
    
     -- R.typeError $ [ toTerm (suc dim) (cu) ]ₑ


     R.unify (toTerm (suc dim) (cu)) h

   simplifyPaⁿ : R.Term → R.Term → R.TC Unit
   simplifyPaⁿ t0 hole = do
    
    (A' , (t0' , t1')) ← R.inferType hole >>= wait-for-term >>= (get-boundaryWithDom ) >>= Mb.rec
     (R.typeError [ R.strErr "unable to get boundary" ]) pure

    let t = vlamⁿ dim $ appNDims≡ dim (liftVars.rv dim 0 t0')
    t ← R.normalise t >>= wait-for-term

    R.typeError $ [ t ]ₑ

 --    cu ← extractCuTerm' 100 dim t
 --    cu' ← tryCastAsNoCong cu <|> R.typeError [ "failed to cast to no cong" ]ₑ
 --    mv ← markVert 100 dim [] cu'     
 --    -- visitCellsM (λ (mbIx , cv) → do
 --    --   Mb.rec (pure _) (R.debugPrint "testMarkVert" 3 ∘ [_]ₑ ∘ vlamⁿ dim ∘  IExpr→Term) mbIx
 --    --   ((R.debugPrint "testMarkVert" 3 ∘ ("cellMarks : \n" ∷ₑ_) ∘ printCellVerts) cv)  ) mv
 --    -- R.debugPrint "testMarkVert" 3 $ "max word: " ∷ₑ [ (getMaxWordLen mv ) ]ₑ

 --    -- R.typeError $ [ "ok" ]ₑ
 --    let cu = makeFoldTerm t0 dim mv
 --    -- te ← ppCTn false dim 100 cu

 --    -- R.typeError $ [ toTerm (suc dim) (cu) ]ₑ


 --    R.unify (toTerm (suc dim) (cu)) hole



 -- -- module Assoc1 {x : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (s : w ≡ v)where


 --  pLHS = assoc p q (r ∙ s) 
 --  rLHS = assoc p q (r ∙ s) 

 --  pentagonTy = pLHS ≡ rLHS

 --  pentagonComp : Square (λ _ → v) (λ _ → v) (λ _ → v) (λ _ → v)
 --  pentagonComp =
 --     CompSquares.compSquares
 --       (λ _ _ → x) (flipSquare pLHS) (flipSquare rLHS)
 --         (λ i _ → (p ∙ q ∙ r ∙ s) i)
 --         λ i _ → (((p ∙ q) ∙ r ∙ s)) i

 --  pentagonComp' : Square (λ _ → v) (λ _ → v) (λ _ → v) (λ _ → v)
 --  pentagonComp' =
 --     CompSquares.compSquares
 --       (λ _ _ → v) (flipSquare
 --                     (assoc (λ _ → v) (λ _ → v) ((λ _ → v) ∙ (λ _ → v)) ))
 --                      (flipSquare
 --                        (assoc (λ _ → v) (λ _ → v)
 --                          ((λ _ → v) ∙ (λ _ → v))))
 --         (λ i _ → ((λ _ → v) ∙ (λ _ → v) ∙ (λ _ → v) ∙ (λ _ → v)) i)
 --         λ i _ → ((((λ _ → v) ∙ (λ _ → v)) ∙ (λ _ → v) ∙ (λ _ → v))) i



 --  inferTestPenta : Unit
 --  inferTestPenta = {!extractCuTermTest (suc (suc zero))
 --       (λ (i j : I) → pentagonComp i j) !}

 -- --  testMarkVertPenta : Unit
 -- --  testMarkVertPenta = {!testMarkVert (suc (suc zero))
 -- --       (λ (i j : I) → pentagonComp i j) !}

 -- --  testEqVertPenta : pentagonComp ≡ pentagonComp'
 -- --  testEqVertPenta =
 -- --    mkEqTerm (suc (suc zero))
 -- --       (λ (i j : I) → pentagonComp i j) 

 -- --  testEqVertPenta'' : pentagonComp' ≡ refl {x = λ _ → v}
 -- --  testEqVertPenta'' = {!simplifyReflⁿ (suc (suc zero))!}
  
 -- --  testEqVertPenta' : pentagonComp ≡ refl
 -- --  testEqVertPenta' = testEqVertPenta ∙ λ i i₁ i₂ → {!!}
  
 -- --  -- tyHlp : {!!}
 -- --  -- tyHlp = CompSquares.compSquaresPath→Cube
 -- --  --   {!!} {!!} pLHS {!pRHS!} {!!} {!!} {!!}


 module PentaJ1 {x : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (s : w ≡ v) where


  pLHS = assoc p q (r ∙ s) ∙ assoc (p ∙ q) r s
  rLHS = cong (p ∙_) (assoc q r s) ∙∙ assoc p (q ∙ r) s ∙∙ cong (_∙ s) (assoc p q r)

  pentagonTy = pLHS ≡ rLHS



  pentagonComp : Square (λ _ → v) (λ _ → v) (λ _ → v) (λ _ → v)
  pentagonComp =
     CompSquares.compSquares
       (λ _ _ → x) (flipSquare pLHS) (flipSquare rLHS)
         (λ i _ → (p ∙ q ∙ r ∙ s) i)
         λ i _ → (((p ∙ q) ∙ r) ∙ s) i

 module PentaJJ1 {x : A} (p : x ≡ y) (q : y ≡ z) (r' r : z ≡ w) (s : w ≡ v) where

   P Q : x ≡ v
   P = refl ∙ (p ∙' q ∙ r' ∙ (sym r' ∙ (r ∙ s)))
   Q = p ∙ (q ∙ refl ∙ r ∙ s ∙ sym s) ∙ s


--    PC RC : I → I → A
--    PC = mkEqTerm (suc zero) x (λ (i : I) → P i)
--    RC = mkEqTerm (suc zero) x (λ (i : I) → Q i)


--    P≡Q : P ≡ Q
--    P≡Q i j =
--        hcomp (λ z → primPOr (~ i) (i ∨ j ∨ ~ j )
--       (λ _ → PC (~ z) j)
--         (λ _ → RC (~ z) j))
--         x


-- --   -- ppj : PentaJ1.pentagonComp p q r s ≡ refl
-- --   -- ppj = mkEqTerm (suc (suc zero))
-- --   --            v (λ (i j : I) → PentaJ1.pentagonComp p q r s i j) 

-- --   open PentaJ1 p q r s

-- --   PC RC : I → I → I → A
-- --   PC = mkEqTerm (suc (suc zero)) x (λ (i j : I) → pLHS i j)
-- --   RC = mkEqTerm (suc (suc zero)) x (λ (i j : I) → rLHS i j)


-- --   pent : assoc p q (r ∙ s) ∙ assoc (p ∙ q) r s
-- --            ≡
-- --           cong (p ∙_) (assoc q r s) ∙∙ assoc p (q ∙ r) s ∙∙ cong (_∙ s) (assoc p q r)
-- --   pent i j k =
-- --     hcomp (λ z → primPOr (~ i) (i ∨ j ∨ ~ j ∨ k ∨ ~ k)
-- --       (λ _ → PC (~ z) j k)
-- --       (λ _ → RC (~ z) j k))
-- --       x

-- --   -- PC' RC' : I → I → I → I → A
-- --   -- PC' = mkEqTerm (suc (suc (suc zero))) x (λ (i j k : I) → pent i j k)
-- --   -- RC' = mkEqTerm (suc (suc (suc zero))) x (λ (i j k : I) → pentagonIdentity p q r s i j k)


-- --   -- pent≡pentagonIdentity : {!pent ≡!}
-- --   -- pent≡pentagonIdentity = {!!}

-- -- --   -- pent : assoc p q (r ∙ s) ∙ assoc (p ∙ q) r s
-- -- --   --          ≡
-- -- --   --         cong (p ∙_) (assoc q r s) ∙∙ assoc p (q ∙ r) s ∙∙ cong (_∙ s) (assoc p q r)
-- -- --   -- pent i j k =
-- -- --   --   -- hcomp (λ z →
-- -- --   --   --         λ { (i = i0) → mkEqTerm (suc (suc zero))
-- -- --   --   --                          x (λ (i j : I) → pLHS i j) j k z
-- -- --   --   --           ; (i = i1) → mkEqTerm (suc (suc zero))
-- -- --   --   --                          x (λ (i j : I) → rLHS i j) j k z
-- -- --   --   --           ; (j = i0) → {!!}
-- -- --   --   --           ; (j = i1) → {!!}
-- -- --   --   --           ; (k = i0) → {!!}
-- -- --   --   --           ; (k = i1) → {!!}
-- -- --   --   --           })
-- -- --   --   --      ?


-- -- -- -- (congP (λ _ → flipSquare)
-- -- -- --            (flipSquareP (CompSquares.compSquaresPath→Cube _ _ _ _ _ _
-- -- -- --            (mkEqTerm (suc (suc zero)) v (λ (i j : I) → PentaJ1.pentagonComp p q r s i j))
-- -- -- --           -- (simplifyPaⁿ (suc (suc zero)) (λ (i j : I) → PentaJ1.pentagonComp p q r s i j)
-- -- -- --           --    v --(λ (i j : I) → PentaJ1.pentagonComp p q r s i j)
-- -- -- --           --    )
-- -- -- --              )))

-- -- -- --   pent' : assoc p q (r ∙ s) ∙ assoc (p ∙ q) r s
-- -- -- --            ≡
-- -- -- --           cong (p ∙_) (assoc q r s) ∙∙ assoc p (q ∙ r) s ∙∙ cong (_∙ s) (assoc p q r)
-- -- -- --   pent' = cancel→pathsEq ww

-- -- -- --    where
-- -- -- --    ww : Cube {!!} (refl {x = {!!}}) refl refl refl refl
-- -- -- --    ww = {!!}


-- -- --   --      (mkEqTerm (suc (suc zero)) x
-- -- --   --     λ (i j : I) →
-- -- --   --      ((assoc p q (r ∙ s) ∙ assoc (p ∙ q) r s)
-- -- --   --         ∙
-- -- --   --         sym (cong (p ∙_) (assoc q r s) ∙∙ assoc p (q ∙ r) s ∙∙ cong (_∙ s) (assoc p q r)))
-- -- --   --         i j
-- -- --   --         )
-- -- --   -- -- -- (congP (λ _ → flipSquare)
-- -- --   -- -- --          (flipSquareP (CompSquares.compSquaresPath→Cube _ _ _ _ _ _
-- -- --   -- -- --          (mkEqTerm (suc (suc zero)) v (λ (i j : I) → PentaJ1.pentagonComp p q r s i j))
-- -- --   -- -- --         -- (simplifyPaⁿ (suc (suc zero)) (λ (i j : I) → PentaJ1.pentagonComp p q r s i j)
-- -- --   -- -- --         --    v --(λ (i j : I) → PentaJ1.pentagonComp p q r s i j)
-- -- --   -- -- --         --    )
-- -- --   -- -- --            )))



-- -- --   -- -- -- pent≡pentagonIdentity : pent ≡ pentagonIdentity p q r s
-- -- --   -- -- -- pent≡pentagonIdentity = {!!}

-- -- --   -- -- -- -- ppj' : (PentaJ1.pentagonComp (refl {x = v}) refl refl refl) ≡ refl
-- -- --   -- -- -- -- ppj' = simplifyReflⁿ (suc (suc zero))

-- -- --   -- -- -- -- inferTestPenta : Unit
-- -- --   -- -- -- -- inferTestPenta = {!extractCuTermTest (suc (suc zero))
-- -- --   -- -- -- --      (λ (i j : I) → pentagonComp i j) !}

-- -- --   -- -- -- -- testMarkVertPenta : Unit
-- -- --   -- -- -- -- testMarkVertPenta = {!testMarkVert (suc (suc zero))
-- -- --   -- -- -- --      (λ (i j : I) → pentagonComp i j) !}


-- -- --   -- -- -- -- -- tyHlp : {!!}
-- -- --   -- -- -- -- -- tyHlp = CompSquares.compSquaresPath→Cube
-- -- --   -- -- -- -- --   {!!} {!!} pLHS {!pRHS!} {!!} {!!} {!!}
