{-# OPTIONS --safe -v testMarkVert:3 -v tactic:3 #-} 
-- -v 3 
module Cubical.Tactics.PathSolver.Coherence where


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

open import Cubical.Data.Sigma.Base

open import Cubical.Reflection.Base renaming (v to 𝒗)
import Agda.Builtin.Reflection as R
open import Cubical.Tactics.PathSolver.Reflection
open import Cubical.Tactics.Reflection 
open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Cubical.Tactics.Reflection.Utilities

-- open import Cubical.Tactics.PathSolver.Base
open import Cubical.Tactics.PathSolver.CongComp

open import Cubical.Tactics.PathSolver.QuoteCubical renaming (normaliseWithType to normaliseWithType')

open import Cubical.Tactics.PathSolver.Error
open import Cubical.Tactics.PathSolver.Dimensions
open import Cubical.Tactics.PathSolver.CuTerm
open import Cubical.Tactics.PathSolver.Reflection
open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.PathSolver.Degen

import Cubical.Tactics.PathSolver.ViaPrimPOr as ViaPrimPOr

private
  variable
    ℓ : Level
    A B : Type ℓ

-- open NormalForm ℕ --using ([𝟚×_])
-- open NormalFrom.Discrete ℕ discreteℕ using (η·)

-- normaliseWithType : R.Type → R.Term → R.TC R.Term
-- normaliseWithType _ = R.normalise

normaliseWithType : String → R.Type → R.Term → R.TC R.Term
normaliseWithType s ty tm = do
  -- R.debugPrint "" 3 $ s <> " nwt: " ∷ₑ [ ty ]ₑ 
  normaliseWithType' ty tm


[𝟚×Term] : Type
[𝟚×Term] = List (Bool × R.Term)

Vert : Type
Vert = List Bool


𝒏[_] : A  → R.TC A
𝒏[_] = pure --R.quoteTC >=> (R.normalise >=> R.unquoteTC)
-- module IsRedex? where

--  tm : R.Term → R.Term → Bool
--  tm x x' with mbTermHead x | mbTermHead x'
--  ... | just (h , xs) | just (h' , xs') =
--    {!_≟th_!}
--  ... | _ | _ = false



isRedex? : (Bool × R.Term) → (Bool × R.Term) → R.TC Bool
isRedex? (b , x) (b' , x') = 
 if (b ⊕ b')
 then 
   (((addNDimsToCtx 1 $ R.unify x x')>> pure true)
     <|> pure false) 
 else (pure false)
 
η· : Bool × R.Term → [𝟚×Term] → R.TC [𝟚×Term]
η· x [] = ⦇ [ ⦇ x ⦈ ] ⦈
η· x (y ∷ xs) = do
 b ← isRedex? x y
 pure $ if b then xs else (x ∷ y ∷ xs)

_[·]_ : [𝟚×Term] → [𝟚×Term] → R.TC [𝟚×Term]
xs [·] ys = foldrM η· ys xs

invLi : [𝟚×Term] → [𝟚×Term]
invLi = L.map (λ (x , y) → not x , y)  ∘S rev



asPath : R.Term → R.TC (Maybe (Bool × R.Term))
asPath tm = addNDimsToCtx 1 do
  -- fi ← findInterval 1 <$> R.normalise tm
  fi ← Mb.rec (pure nothing) (λ x → just <$> R.normalise x) $ findInterval 1 tm
  
  Mb.rec (⦇ nothing ⦈) (zz') fi

 where
 zz : R.Term → R.TC (R.Term ⊎.⊎ Maybe (Bool × R.Term))
 zz (R.var zero []) = pure $ pure $ just (true , tm) 
 zz (R.def (quote ~_) v[ R.var zero [] ]) = pure $ pure (just (false , invVar zero tm))
 zz (R.con _ _) = pure $ pure nothing
 zz (R.def (quote ~_) v[ R.var (suc k) [] ]) =
  R.typeError ([ "imposible in asPath : ~ : " ]ₑ ++ₑ [ k ]ₑ)
 zz tmI = pure (inl tmI)

 zz' : R.Term → R.TC (Maybe (Bool × R.Term))
 zz' = zz >=>
   ⊎.rec (((extractIExprM >=& normIExpr) >=& IExpr→Term) >=>
     (zz >=> ⊎.rec (λ tmI →
       R.typeError ([ "imposible in asPath: " ]ₑ ++ₑ [ tm ]ₑ ++ₑ [ "\n\n" ]ₑ ++ₑ [ tmI ]ₑ))
       (pure))) pure

 



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
  cv0 : [𝟚×Term] → [𝟚×Term] → CellVerts
  cvN : CellVerts → CellVerts → CellVerts


mapCellVerts : (f : [𝟚×Term] → [𝟚×Term]) → CellVerts → CellVerts
mapCellVerts f (cv0 x x₁) = cv0 (f x) (f x₁)
mapCellVerts f (cvN x x₁) = cvN (mapCellVerts f x) (mapCellVerts f x₁)

mapCellVertsM : (f : [𝟚×Term] → R.TC [𝟚×Term]) → CellVerts → R.TC CellVerts
mapCellVertsM f (cv0 x x₁) = ⦇ cv0 (f x) (f x₁) ⦈
mapCellVertsM f (cvN x x₁) = ⦇ cvN (mapCellVertsM f x) (mapCellVertsM f x₁) ⦈


cellVert : CellVerts → Vert → R.TC [𝟚×Term] 
cellVert (cv0 x x₂) (false ∷ []) = pure x
cellVert (cv0 x x₂) (true ∷ []) = pure x₂
cellVert (cvN x x₂) (false ∷ x₃) = cellVert x x₃
cellVert (cvN x x₂) (true ∷ x₃) = cellVert x₂ x₃
cellVert _ _ =  R.typeError $ [ "cellVert failed " ]ₑ

matchAtomPa : R.Term → R.TC (Maybe (Bool × ℕ))
matchAtomPa (R.var x []) = ⦇ nothing ⦈
matchAtomPa (R.var (suc x) v[ R.var zero [] ]) = ⦇ just (⦇ (true , x) ⦈) ⦈
matchAtomPa (R.var (suc x) v[ R.def (quote ~_) v[ R.var zero [] ] ]) =
   ⦇ just (⦇ (false , x) ⦈) ⦈
matchAtomPa t = R.typeError $ "unexpected in matchAtomPA : " ∷ₑ [ t ]ₑ




getAtomPa : R.Term → R.TC [𝟚×Term]
getAtomPa = (maybeToList <$>_) ∘S asPath

-- addNDimsToCtx 1 do 
--   tn ← R.normalise t --<|> (addNDimsToCtx dim $ R.typeError ([ "here :" ]ₑ ++ₑ [ t ]ₑ))
--   pure $ Mb.rec [] [_] (if (hasVar zero tn) then  (just tn) else nothing) 

print[𝟚×] :  [𝟚×Term] → List R.ErrorPart
print[𝟚×] = 
  join ∘S (L.map (λ (b , t)
            → ", (" ∷ₑ  vlam "𝕚" t  ∷ₑ [ ")" <> (if b then "" else "⁻¹") ]ₑ ))

CellVerts→List : CellVerts → List (Vert × [𝟚×Term])
CellVerts→List (cv0 x x₁) = ([ false ] , x) ∷ [ [ true ] , x₁ ] 
CellVerts→List (cvN x x₁) = 
  L.map (λ (x , y) →  (false ∷ x) , y) (CellVerts→List x)
   ++ L.map ((λ (x , y) → true ∷ x , y)) (CellVerts→List x₁)


allEqual? : Discrete A → List A → Bool
allEqual? _≟_ (x ∷ (y ∷ xs)) = Dec→Bool (x ≟ y) and allEqual? _≟_ (y ∷ xs)
allEqual? _≟_ _ = true


cellVertsHead : CellVerts → Maybe (Bool × R.Term) × [𝟚×Term]  
cellVertsHead cv = 
 let l = L.map (snd) $ CellVerts→List cv
     lM = L.map (length) l
     
     
 in if (allEqual? discreteℕ lM) then nothing , Mb.fromMaybe [] (listToMaybe l) else
     let maxL = foldr max 0 lM
     in Mb.rec (nothing , []) (λ x → listToMaybe x , tail x) (findBy (λ x → Dec→Bool $ discreteℕ (length x) maxL ) l)
          
printCellVerts : CellVerts → List (R.ErrorPart)
printCellVerts = (join ∘ L.map
   (λ (v , x) →  L.map (if_then "□" else "◼") v ++ₑ print[𝟚×] x ++ₑ [ "\n" ]ₑ)) ∘ CellVerts→List 

-- module GetAtomPaTests where

--  macro
--   getAtomPaTest : R.Term → R.Term → R.TC Unit
--   getAtomPaTest t _ = do
--     x ← L.map (map-snd predℕ) <$> getAtomPa t
--     R.typeError ("got :" ∷ₑ print[𝟚×] x)

 -- module _ (p : x ≡ y) (q : y ≡ z) where
 --  getAtomPaTest1 : Unit
 --  getAtomPaTest1 = {!getAtomPaTest (λ (i : I) → (p ∙ q) i)!}



module _ (ty : R.Type) where
 getTermVerts : ℕ → R.Term → R.TC CellVerts
 getTermVerts zero x₁ = R.typeError [ "imposible - getTermsVerts" ]ₑ
 getTermVerts (suc zero) t = do
   p ← getAtomPa  t
   pure (cv0 [] p)
 -- getTermVerts (suc (suc zero)) t = do
 --   p0i ← getAtomPa (subfaceCell (nothing ∷ [ just false ]) t)
 --   pi0 ← getAtomPa (subfaceCell (just false ∷ [ nothing ]) t)
 --   p1i ← getAtomPa (subfaceCell (nothing ∷ [ just true ]) t)
 --   p1i[·]pi0 ← p1i [·] pi0
 --   pure $ cvN (cv0 [] pi0 ) (cv0 p0i p1i[·]pi0)

 getTermVerts (suc n) t = do
   gtv0 ← getTermVerts n (subfaceCell (just false ∷ repeat n nothing) t)
   gtv1 ← getTermVerts n (subfaceCell (just true ∷ repeat n nothing) t)
   -- pi0 ← getAtomPa (subfaceCell (just false ∷ [ nothing ]) t)
   -- pi1 ← getAtomPa (subfaceCell (just true ∷ [ nothing ]) t)
   p0i ← getAtomPa (subfaceCell (nothing ∷ repeat n (just false)) t)

   -- pi1[·]p0i ← pi1 [·] p0i
   cvN gtv0 <$> (mapCellVertsM (_[·] p0i) gtv1)

-- getTermVerts (suc (suc (suc x))) x₁ =
--   R.typeError [ "not impemented - getTermsVerts" ]ₑ

-- module GetTermVertsTests where

--  module _ (dim : ℕ) where
--   macro
--    getTermVertsTest : R.Term → R.Term → R.TC Unit
--    getTermVertsTest t h = do
--     r ← getTermVerts dim t
--     r' ← R.quoteTC r
--     R.unify r' h

 -- module _ (p : x ≡ y) (q : y ≡ z) where
 --  getTermVertsTest1 : CellVerts
 --  getTermVertsTest1 = {!getTermVertsTest (suc (suc zero)) (λ (i j : I) → p (~ j  ∧ i))!}



getVert : ℕ → Vert → CuTerm' ⊥ (Maybe (R.Term × R.Term) × ((Maybe IExpr) × CellVerts)) → R.TC [𝟚×Term] 
getVert zero v (hco xs _) =  R.typeError [ "ran out of magic in getVert" ]ₑ
getVert (suc m) v (hco xs _) = do
  (sf , x) ← Mb.rec (R.typeError [ "imposible getVert" ]ₑ) pure
              $ findBy ((L.map just v ⊂?_) ∘ [_] ∘ fst) xs
  let v' : Vert
      v' = (L.map (snd) $ (filter ((λ { nothing → true ; _ → false }) ∘S fst)
                (zipWith _,_ sf v)))
  getVert m (true ∷ v') x  
getVert _ x (cell' (_ , (_ , x₁)) _) = cellVert x₁ x
  -- -- R.debugPrint "" 3 ( [ "cellVert: " ]ₑ ++ₑ print[𝟚×] l)                
  -- pure l

module _ (ty : R.Type) where
 -- getIArg : ℕ → R.Term → R.TC (Maybe IExpr)
 -- getIArg dim t = addNDimsToCtx dim $ do
 --   (normaliseWithType (lift)  $ t) >>= h

 --  where
 --  h : R.Term → R.TC (Maybe IExpr)
 --  h (R.var x []) = ⦇ nothing ⦈
 --  h (R.var x v[ a ]) = just <$> extractIExprM a
 --  h t = R.typeError $ "unexpected in getIArg :" ∷ₑ [ t ]ₑ

 markVert : ℕ → ℕ → [𝟚×Term] → (CuTerm' ⊥ Unit) → R.TC (CuTerm' ⊥ (Maybe (R.Term × R.Term) × ((Maybe IExpr) × CellVerts)))

 getPaThruPartial : ℕ → Vert → List (SubFace × CuTerm' ⊥ Unit) → R.TC [𝟚×Term]
 getPaThruPartial m v xs = do
   (sf , x) ← Mb.rec (R.typeError [ "imposible gptp" ]ₑ) pure
               $ findBy ((L.map just v ⊂?_) ∘ [_] ∘ fst) xs
   let v' : Vert
       v' = (L.map (snd) $ (filter ((λ { nothing → true ; _ → false }) ∘S fst)
                 (zipWith _,_ sf v)))
   xs' ← markVert m (suc (sfDim sf)) [] x                
   p0 ← getVert m (false ∷ v') xs'
   p1 ← getVert m (true ∷ v') xs'
   p1 [·] (invLi p0)

 markVert zero dim w (hco x cu) = R.typeError [ "ran out of magic in markVert" ]ₑ
 markVert (suc m) dim w (hco x cu) = do
   -- markedVerts ← mapM (λ (sf , x) → ⦇ ⦇ sf ⦈ , markVert m (suc (sfDim sf)) [] x ⦈) x
   paToLid ← invLi <$> (getPaThruPartial m (repeat dim false) x)
   paToLid[·]w ← paToLid [·] w
   markedCu ← markVert m dim (paToLid[·]w) cu
   fixedVerts ← mapM (λ (sf , x) → do
                  vv ← (getVert m (L.map (Mb.fromMaybe false) sf) markedCu)
                  ⦇ ⦇ sf ⦈ , markVert m (suc (sfDim sf)) vv x ⦈) x
   pure $ hco fixedVerts markedCu
 markVert m dim w (cell x') = do
   (mbX , x) ← UndegenCell.mbUndegen dim x'
   -- R.debugPrint "testMarkVert" 0 $ "mv" ∷ₑ [ m ]ₑ
   zz ← getTermVerts ty dim x >>= 𝒏[_]
   -- ia ← getIArg dim x <|>
   --        R.typeError (printCellVerts zz)
   ia ← Mb.rec (⦇ nothing ⦈) ((extractIExprM >=> 𝒏[_]) >=& just) (findInterval dim x) 

   zzT ← R.quoteTC zz
   iaT ← R.quoteTC ia

   R.debugPrint "testMarkVert" 3 $ ("markVert : \n" ∷ₑ zzT ∷ₑ "\n" ∷ₑ [ iaT  ]ₑ)       
   ⦇ cell'
      ⦇ ⦇ mbX ⦈ , ⦇ ⦇ ia ⦈ , mapCellVertsM (_[·] w) zz ⦈ ⦈
      ⦇ x ⦈
      ⦈ 


getMaxWordLen : CuTerm' ⊥ ((Maybe IExpr) × CellVerts) → ℕ
getMaxWordLen x = foldCells (flip (foldl max)  ∘ L.map (length ∘ snd) ∘ CellVerts→List ∘ snd) x zero 

flipOnFalse : Bool → R.Term → R.Term
flipOnFalse b t = if b then t else R.def (quote ~_) v[ t ] 






[𝟚×ℕ]→PathTerm : [𝟚×Term] → R.Term
[𝟚×ℕ]→PathTerm [] = Rrefl
[𝟚×ℕ]→PathTerm ((b , tm) ∷ []) =
   ViaPrimPOr.R∙ (vlam "_" (liftVars (subfaceCell [ just (not b) ] tm)))
      (vlam "𝕚'" (if b then tm else (invVar zero tm))) --(if b then tm else Rsym tm)
[𝟚×ℕ]→PathTerm ((b , tm) ∷ xs) = ViaPrimPOr.R∙ ([𝟚×ℕ]→PathTerm xs)
      (vlam "𝕚'" (if b then tm else (invVar zero tm))) 

[𝟚×ℕ]→FillTerm : Bool × R.Term → [𝟚×Term] → R.Term
[𝟚×ℕ]→FillTerm (b , tm) [] =
    R.def (quote ViaPrimPOr.compPath-filler) ((vlam "_" (liftVars (subfaceCell [ just (not b) ] tm)))
         v∷ v[ (vlam "𝕚'" (if b then tm else (invVar zero tm))) ])
[𝟚×ℕ]→FillTerm (b , tm) xs =
  R.def (quote ViaPrimPOr.compPath-filler) ([𝟚×ℕ]→PathTerm xs v∷
    v[ (vlam "𝕚'" (if b then tm else (invVar zero tm))) ])

module MakeFoldTerm (t0 : R.Term) where


 cellTerm : ℕ → (Maybe IExpr) × ((Maybe (Bool × R.Term) × [𝟚×Term])) → R.Term → R.Term
 -- cellTerm = {!!}
 cellTerm dim (mbi , nothing , []) t = (liftVars t)
 cellTerm dim (mbi , nothing , tl@(_ ∷ _)) _ = --R.unknown
    R.def (quote $≡) (liftVarsFrom (suc dim) 0 ([𝟚×ℕ]→PathTerm tl) v∷
       v[ R.def (quote ~_) v[ 𝒗 dim ] ])
 cellTerm dim (just ie , just (b , tm) , tl) _ = --vlamⁿ 1 (liftVarsFrom 1 0 t)
   
    R.def (quote $≡)
         ((R.def (quote $≡) (liftVarsFrom (suc dim) 0 ([𝟚×ℕ]→FillTerm (b , tm) tl) v∷
            -- v[ (IExpr→Term ie) ]) v∷
            v[ flipOnFalse (b) (IExpr→Term ie) ]) v∷
       v[ R.def (quote ~_) v[ 𝒗 dim ] ]))
 cellTerm _  _ _ = R.lit (R.string ("unexpected in MakeFoldTerm.cellTerm"))
   -- let (zz , yy) = cellVertsHead cv
   -- in Mb.rec (vlam "ii" (liftVars $ [𝟚×ℕ]→PathTerm yy)) {!!} zz
 

 ctils : List (SubFace × (CuTerm' ⊥ (Maybe (R.Term × R.Term) × ((Maybe IExpr) × CellVerts)))) →
    R.TC (List (SubFace × CuTerm))
 
 ctil : ℕ → (CuTerm' ⊥ (Maybe (R.Term × R.Term) × ((Maybe IExpr) × CellVerts))) → R.TC CuTerm
 ctil dim (hco x c) =
   ⦇ hco ⦇ pure (repeat dim nothing ++ [ just true ] , cell ((liftVarsFrom (suc dim) 0 t0)))
            ∷
            ctils x ⦈
          (ctil dim c) ⦈
 ctil dim (cell' (mbt , cv) x) = cell' tt <$>
    let ct = (cellTerm dim  (fst cv , cellVertsHead (snd cv)) x)
    in Mb.rec
         (pure ct)
         (λ tmUDG →
            UndegenCell.undegenCell dim tmUDG ct) mbt
 -- cell $
 --   let (zz , yy) = cellVertsHead cv
 --   in Mb.rec (vlam "ii" (liftVars $ [𝟚×ℕ]→PathTerm yy)) {!!} zz
   
   -- cell $ vlamⁿ k (liftVarsFrom k 0 x)
 -- ctil (𝒄ong h l) = 𝒄ong h (ctila l)

 ctils [] = ⦇ [] ⦈
 ctils ((sf , x) ∷ xs) = 
   ⦇ ⦇ pure (sf ++ [ nothing ]) , ctil (suc (sfDim sf)) x ⦈ ∷ ctils xs ⦈


makeFoldTerm : R.Term → ℕ → (CuTerm' ⊥ (Maybe (R.Term × R.Term) × ((Maybe IExpr) × CellVerts))) → R.TC CuTerm
makeFoldTerm = MakeFoldTerm.ctil


mkFoldTerm : R.Type → ℕ → R.Term → R.TC (R.Term)
mkFoldTerm ty dim t = do

  t0 ← normaliseWithType "mkFoldTerm" ty
            (subfaceCell (repeat dim (just false)) t)
  cu ← quoteCuTerm (just ty) dim t -- >>= 𝒏[_]
  cu' ← tryCastAsNoCong cu <|> R.typeError [ "failed to cast to no cong" ]ₑ -- (>>= 𝒏[_])

  mv ← markVert ty 100 dim [] cu'
  (ToTerm.toTerm (defaultCtx (suc dim)))   <$> makeFoldTerm t0 dim mv

-- mkFoldTermUD : ℕ → R.Term → R.TC (R.Term × R.Term)
-- mkFoldTermUD dim t = do

--   t0 ← R.normalise
--             (subfaceCell (repeat dim (just false)) t)
--   cuD ← quoteCuTerm dim t
--   cu ← undegenCub true dim cuD
--   degP ← toTerm (suc dim) <$> undegenCub false dim cuD
--   cu' ← tryCastAsNoCong cu <|> R.typeError [ "failed to cast to no cong" ]ₑ

--   mv ← markVert 100 dim [] cu'
--   pure (degP , ((ToTerm.toTerm (defaultCtx (suc dim)))   $ makeFoldTerm t0 dim mv))


mkAppFillTerm : R.Type → ℕ → R.Term → R.TC (R.Term × R.Term)
mkAppFillTerm ty dim t = do
    t0 ← normaliseWithType "mkAppFillTerm" ty
              (subfaceCell (repeat dim (just false)) t)
    R.debugPrint "testMarkVert" 0 $ [ "mkAppFillTerm - quoteCuTerm " ]ₑ       
    cu ← (quoteCuTerm (just ty) dim t)
    -- R.typeError $ [ "ok**" ]ₑ
    let cu' = appCongs dim cu
    -- te' ← ppCT dim 100 cu'
    -- R.typeError $ te'
    R.debugPrint "testMarkVert" 0 $ [ "mkAppFillTerm - markVert" ]ₑ       
    mv ← markVert ty 100 dim [] cu'
    
    R.debugPrint "testMarkVert" 0 $ [ "mkAppFillTerm - toTerm grpPa " ]ₑ       
    grpPa ←
      -- addNDimsToCtx (suc dim) $ R.normalise $
       (ToTerm.toTerm (defaultCtx (suc dim))) <$> makeFoldTerm t0 dim mv
       
    R.debugPrint "testMarkVert" 0 $ [ "mkAppFillTerm - toTerm congPa " ]ₑ               
    congPa ← --addNDimsToCtx (suc dim) $ R.normalise
              pure (ToTerm.toTerm (defaultCtx (suc dim)) (fillCongs 100 dim cu))
    -- R.typeError $ [ "ok**" ]ₑ
    pure (congPa , grpPa)  


-- -- onlyMkFoldTerm : ℕ → R.Term → R.TC R.Term
-- -- onlyMkFoldTerm dim t = do

-- --   t0 ← R.normalise
-- --             (subfaceCell (repeat dim (just false)) t)
-- --   cu ← quoteCuTerm dim t
-- --   cu' ← tryCastAsNoCong cu <|> R.typeError [ "failed to cast to no cong" ]ₑ

-- --   mv ← markVert 100 dim [] cu'
-- --   pure ((ToTerm.toTerm (defaultCtx (suc dim)))   $ makeFoldTerm t0 dim mv)


fullFExpr : ℕ → IExpr
fullFExpr dim =
 join $ L.map (λ k → [ (false , k) ] ∷ [ [ (true , k) ] ]) ((range dim))


-- por3 : ∀ i j k → A → A → A → Partial (i ∨ j ∨ k) A
-- por3 i j k x x₁ x₂ =
--  primPOr i {!j!}
--          {!!} {!!}



mkSolutionTerm' : ℕ → R.Term → R.Term → R.Term → R.Term
mkSolutionTerm' dim lhsP rhsP lid =
 let 
     sides = vlam "𝒛" $ R.def (quote primPOr)
             ( (liftVars $ IExpr→Term [ [ (false , dim) ] ])
               v∷ (liftVars $ (IExpr→Term (tail $ fullFExpr (suc dim))))
             v∷ (vlam "o" (liftVars $ invVar zero $ (rotVars dim (liftVarsFrom 1 (suc dim) lhsP))))
          v∷ v[ (vlam "o" (liftVars $ invVar zero $ (rotVars dim (liftVarsFrom 1 (suc dim) rhsP)))) ])
 in R.def (quote hcomp) (sides v∷ v[ lid ])


mkSolutionTerm : ℕ → R.Term → R.Term → R.Term
mkSolutionTerm dim lhsP rhsP =
  mkSolutionTerm' dim lhsP rhsP
   (subfaceCellNoDrop ((repeat dim nothing) ∷ʳ just true) lhsP)

mkSolutionTerm2 : ℕ → (R.Term × R.Term) → (R.Term × R.Term) → R.Term
mkSolutionTerm2 dim (lhsP , lhsP') (rhsP , rhsP') =
  mkSolutionTerm' dim lhsP rhsP
   (mkSolutionTerm dim lhsP' rhsP')





module _ (dim : ℕ) where
 -- macro
 --  testMarkVert : R.Term → R.Term → R.TC Unit
 --  testMarkVert t h = do
 --    cu ← extractCuTerm dim t
 --    cu' ← tryCastAsNoCong cu <|> R.typeError [ "failed to cast to no cong" ]ₑ
 --    mv ← markVert 100 dim [] cu'     
 --    addNDimsToCtx 1 $ visitCellsM (λ (mbIx , cv) → do
 --      Mb.rec (R.debugPrint "testMarkVert" 3 [ "noIExpr" ]ₑ)
 --              (R.debugPrint "testMarkVert" 3 ∘ [_]ₑ ∘ vlamⁿ dim ∘  IExpr→Term) mbIx
 --      ((R.debugPrint "testMarkVert" 3 ∘ ("cellMarks : \n" ∷ₑ_) ∘ printCellVerts) cv)  ) mv
 --    R.debugPrint "testMarkVert" 3 $ "max word: " ∷ₑ [ (getMaxWordLen mv ) ]ₑ

 --    R.typeError $ [ "ok" ]ₑ


  mkEqTerm : R.Type → R.Term → R.Term → R.TC Unit
  mkEqTerm ty t h = do
    t0 ← normaliseWithType "mkEqTerm" ty
           (subfaceCell (repeat dim (just false)) (appNDimsI dim (liftVarsFrom dim 0 t)))  
    cu ← extractCuTerm (just ty) dim t
    cu' ← tryCastAsNoCong cu <|> R.typeError [ "failed to cast to no cong" ]ₑ

    mv ← markVert ty 100 dim [] cu'
    -- R.typeError $ [ "ok" ]ₑ
    -- -- visitCellsM (λ (mbIx , cv) → do
    -- --   Mb.rec (pure _) (R.debugPrint "testMarkVert" 3 ∘ [_]ₑ ∘ vlamⁿ dim ∘  IExpr→Term) mbIx
    -- --   ((R.debugPrint "testMarkVert" 3 ∘ ("cellMarks : \n" ∷ₑ_) ∘ printCellVerts) cv)  ) mv
    -- -- R.debugPrint "testMarkVert" 3 $ "max word: " ∷ₑ [ (getMaxWordLen mv ) ]ₑ

    -- R.typeError $ [ "ok" ]ₑ
    cu ← makeFoldTerm t0 dim mv
    -- te ← ppCTn false dim 100 cu
    -- R.typeError $ [ toTerm (suc dim) (cu) ]ₑ
    R.unify (toTerm (suc dim) (cu)) h
     --  <|>
     -- (R.typeError $ "check :" ∷ₑ [ toTerm (suc dim) (cu) ]ₑ)


macro
 -- solvePathsUD : R.Term → R.TC Unit
 -- solvePathsUD h = do
 --  hTy ← R.inferType h >>= wait-for-term >>= R.normalise

 --  bdTM@(A , fcs) ← matchNCube hTy
 --  let dim = length fcs
 --  -- mbEquation' bdTM
 --  flip (Mb.rec (R.typeError [ "not equation" ]ₑ)) (mbEquation bdTM)
 --    λ (lhs , rhs) → do
 --       (udLHS , lhsFold) ← mkFoldTermUD (predℕ dim) lhs
       
 --       (udRHS , rhsFold) ← mkFoldTermUD (predℕ dim) rhs
       
 --       let solutionMid = vlamⁿ dim $ (mkSolutionTerm (predℕ dim) lhsFold rhsFold)
 --       let solution = R.def (quote _∙∙_∙∙_)
 --            (udLHS v∷ solutionMid v∷ v[ R.def (quote sym) (v[ udRHS ]) ])
 --       R.unify solution h --<|> R.typeError [ solution ]ₑ


 solvePaths : R.Term → R.TC Unit
 solvePaths h = R.withReduceDefs (false , [ quote ua ]) do
  hTy ← R.inferType h >>= wait-for-term >>= R.normalise

  bdTM@(A , fcs) ← matchNCube hTy
  let dim = length fcs
  -- mbEquation' bdTM
  flip (Mb.rec (R.typeError [ "not equation" ]ₑ)) (mbEquation bdTM)
    λ (lhs , rhs) → do
       (lhsFold) ← mkFoldTerm A (predℕ dim) lhs
       
       (rhsFold) ← mkFoldTerm A (predℕ dim) rhs
       
       solution ← (normaliseWithType "" hTy $ vlamⁿ dim $ (mkSolutionTerm (predℕ dim) lhsFold rhsFold))
                     -- >>= makeAuxiliaryDef "solvePathsSolution" hTy
       
       R.unify solution h <|> R.typeError [ solution ]ₑ


 solvePaths' : R.Term → R.TC Unit
 solvePaths' h = do
  hTy ← R.inferType h >>= wait-for-term >>= R.normalise
  R.debugPrint "solvePaths'" 0 $ [ "solvePaths' - start" ]ₑ
  bd' ← matchNCube hTy
  R.debugPrint "solvePaths'" 0 $ [ "solvePaths' - matchNCube done" ]ₑ
  bdTM@(A , fcs) ← nCubeToEq bd'
  R.debugPrint "solvePaths'" 0 $ [ "solvePaths' - nCubeToEq done" ]ₑ
  let dim = length fcs
  -- mbEquation' bdTM
  flip (Mb.rec (R.typeError [ "not equation" ]ₑ)) (mbEquation bdTM)
    λ (lhs , rhs) → do
       (lhsFold) ← mkFoldTerm A (predℕ dim) lhs
       R.debugPrint "solvePaths'" 0 $ [ "solvePaths' - lhsFold done" ]ₑ
       (rhsFold) ← mkFoldTerm A (predℕ dim) rhs
       R.debugPrint "solvePaths'" 0 $ [ "solvePaths' - rhsFold done" ]ₑ
       let solution' = vlamⁿ dim $ (mkSolutionTerm (predℕ dim) lhsFold rhsFold)
           solution = R.def (quote _▷_) (nCubeToEqPath bd' v∷ v[ solution' ])
       R.debugPrint "solvePaths'" 0 $ [ "solvePaths' - nCubeToEqPath done" ]ₑ
       R.unify solution h --<|> R.typeError [ solution ]ₑ


 solvePathsC : R.Term → R.TC Unit
 solvePathsC h = do
  hTy ← R.inferType h >>= wait-for-term >>= R.normalise
  R.debugPrint "testMarkVert" 0 $ [ "solvePathsC - start" ]ₑ
  bdTM@(A , fcs) ← matchNCube hTy
  let dim = length fcs
  R.debugPrint "testMarkVert" 0 $ [ "solvePathsC - dim : " ]ₑ ++ [ dim ]ₑ
  flip (Mb.rec (R.typeError [ "not equation" ]ₑ)) (mbEquation bdTM)
    λ (lhs , rhs) → do
       R.debugPrint "testMarkVert" 0 $ [ "solvePathsC - mkAppFillTerm LHS start " ]ₑ       
       lhsP ← mkAppFillTerm A (predℕ dim) lhs
       R.debugPrint "testMarkVert" 0 $ [ "solvePathsC - mkAppFillTerm RHS start " ]ₑ       
       rhsP ← mkAppFillTerm A (predℕ dim) rhs

       let solution = --mkSolutionTerm (predℕ dim) (snd lhsP) (snd rhsP)
              (mkSolutionTerm2 (predℕ dim) lhsP rhsP)
       R.debugPrint "testMarkVert" 0 $ [ "solvePathsC - unify " ]ₑ               
       -- R.typeError [ solution ]ₑ
       R.unify (vlamⁿ dim $ solution) h <|>
          (addNDimsToCtx dim $ do
             solN ← R.normalise solution
             R.typeError [ solN ]ₑ)

 solvePathsCfromTy : R.Term → R.Term → R.TC Unit
 solvePathsCfromTy ty h = do
  hTy ← R.normalise ty

  bdTM@(A , fcs) ← matchNCube hTy
  let dim = length fcs
  flip (Mb.rec (R.typeError [ "not equation" ]ₑ)) (mbEquation bdTM)
    λ (lhs , rhs) → do

       lhsP ← mkAppFillTerm A (predℕ dim) lhs
       rhsP ← mkAppFillTerm A (predℕ dim) rhs
       -- R.typeError [ "ok" ]ₑ
       let solution = --mkSolutionTerm (predℕ dim) (snd lhsP) (snd rhsP)
              (mkSolutionTerm2 (predℕ dim) lhsP rhsP)

       -- R.typeError [ solution ]ₑ
       R.unify (vlamⁿ dim $ solution) h <|>
          (addNDimsToCtx dim $ do
             solN ← R.reduce solution
             R.typeError [ vlamⁿ dim $ solN ]ₑ)
