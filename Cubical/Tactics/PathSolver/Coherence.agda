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

open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_ ; _<_ to _<ℕ_)
open import Agda.Builtin.String
open import Agda.Builtin.Char

open import Cubical.Data.Sigma.Base

open import Cubical.Reflection.Base renaming (v to 𝒗)
import Agda.Builtin.Reflection as R
open import Cubical.Tactics.PathSolver.Reflection
open import Cubical.Tactics.Reflection 

open import Cubical.Tactics.Reflection.Utilities

-- open import Cubical.Tactics.PathSolver.Base
open import Cubical.Tactics.PathSolver.CongComp

open import Cubical.Tactics.PathSolver.QuoteCubical renaming (normaliseWithType to normaliseWithType')

open import Cubical.Tactics.Reflection.Error
open import Cubical.Tactics.PathSolver.Dimensions
open import Cubical.Tactics.PathSolver.CuTerm
open import Cubical.Tactics.PathSolver.Reflection
open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.PathSolver.Degen


private
  variable
    ℓ : Level
    A B : Type ℓ

normaliseWithType : String → R.Type → R.Term → R.TC R.Term
normaliseWithType s ty tm = do
  -- R.debugPrint "" 3 $ s <> " nwt: " ∷ₑ [ ty ]ₑ 
  normaliseWithType' ty tm


[𝟚×Term] : Type
[𝟚×Term] = List (Bool × R.Term)

Vert : Type
Vert = List Bool


𝒏[_] : A  → R.TC A
𝒏[_] = pure


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




getAtomPa : R.Term → R.TC [𝟚×Term]
getAtomPa = (maybeToList <$>_) ∘S asPath

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


          
printCellVerts : CellVerts → List (R.ErrorPart)
printCellVerts = (join ∘ L.map
   (λ (v , x) →  L.map (if_then "□" else "◼") v ++ₑ print[𝟚×] x ++ₑ [ "\n" ]ₑ)) ∘ CellVerts→List 



module _ (ty : R.Type) where
 getTermVerts : ℕ → R.Term → R.TC CellVerts
 getTermVerts zero x₁ = R.typeError [ "imposible - getTermsVerts" ]ₑ
 getTermVerts (suc zero) t = do
   p ← getAtomPa  t
   pure (cv0 [] p)

 getTermVerts (suc n) t = do
   gtv0 ← getTermVerts n (subfaceCell (just false ∷ repeat n nothing) t)
   gtv1 ← getTermVerts n (subfaceCell (just true ∷ repeat n nothing) t)

   p0i ← getAtomPa (subfaceCell (nothing ∷ repeat n (just false)) t)

   cvN gtv0 <$> (mapCellVertsM (_[·] p0i) gtv1)

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


foldBdTermWithCuInput' =
  let T = (CuTerm' ⊥ Unit × Maybe R.Term)
  in List (T × T)


foldBdTermWithCuInput =
  let T = (CuTerm' ⊥ (Maybe (R.Term × R.Term) × ((Maybe IExpr) × CellVerts)) × Maybe R.Term)
  in List (T × T)



module _ (ty : R.Type) where

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

 markVertSnd : ℕ → ℕ → [𝟚×Term] → ((CuTerm' ⊥ Unit) × A)
   → R.TC (CuTerm' ⊥ (Maybe (R.Term × R.Term) × ((Maybe IExpr) × CellVerts)) × A)
 markVertSnd n m tms (x , y) = ⦇ markVert n m tms x , ⦇ y ⦈ ⦈

 markVertBd : foldBdTermWithCuInput'
    → R.TC foldBdTermWithCuInput
 markVertBd [] = R.typeError [ "markVertBd undefined" ]ₑ
 markVertBd (_ ∷ []) = R.typeError [ "markVertBd undefined" ]ₑ 
 markVertBd xs = do
   let dim = predℕ (length xs)
       v0 = repeat dim false
   fcs0 ← mapM (markVertSnd 100 dim [] ∘S fst) xs
   fcs0₀ ← Mb.rec (R.typeError [ "imposible" ]ₑ)
              (λ y → mapM (λ k → (getVert 100 (replaceAt k true v0)) (fst y))  (range dim))
             (lookup fcs0 0)
   fcs0₁ ← Mb.rec (R.typeError [ "imposible" ]ₑ)
     (getVert 100 (replaceAt (predℕ dim) true v0) ∘S fst) (lookup fcs0 1)
   
   fcs1 ← mapM (idfun _)
           (zipWith (markVertSnd 100 dim) (fcs0₁ ∷ fcs0₀) (snd <$> xs)) 
   pure (zipWith _,_ fcs0 fcs1)



flipOnFalse : Bool → R.Term → R.Term
flipOnFalse b t = if b then t else R.def (quote ~_) v[ t ] 






[𝟚×ℕ]→PathTerm : [𝟚×Term] → R.Term
[𝟚×ℕ]→PathTerm [] = Rrefl
[𝟚×ℕ]→PathTerm ((b , tm) ∷ []) =
   R∙ (vlam "_" (liftVars (subfaceCell [ just (not b) ] tm)))
      (vlam "𝕚'" (if b then tm else (invVar zero tm))) --(if b then tm else Rsym tm)
[𝟚×ℕ]→PathTerm ((b , tm) ∷ xs) = R∙ ([𝟚×ℕ]→PathTerm xs)
      (vlam "𝕚'" (if b then tm else (invVar zero tm))) 

[𝟚×ℕ]→FillTerm : Bool × R.Term → [𝟚×Term] → R.Term
[𝟚×ℕ]→FillTerm (b , tm) [] =
    R.def (quote compPath-filler) ((vlam "_" (liftVars (subfaceCell [ just (not b) ] tm)))
         v∷ v[ (vlam "𝕚'" (if b then tm else (invVar zero tm))) ])
[𝟚×ℕ]→FillTerm (b , tm) xs =
  R.def (quote compPath-filler) ([𝟚×ℕ]→PathTerm xs v∷
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
 

 ctils : List (SubFace × (CuTerm' ⊥ (Maybe (R.Term × R.Term) × ((Maybe IExpr) × CellVerts)))) →
    R.TC (List (SubFace × CuTerm))
 
 ctil : ℕ → (CuTerm' ⊥ (Maybe (R.Term × R.Term) × ((Maybe IExpr) × CellVerts))) → R.TC CuTerm
 ctil dim (hco x c) =
   ⦇ hco ⦇ pure (repeat dim nothing ++ [ just true ] , cell ((t0)))
            ∷
            ctils x ⦈
          (ctil dim c) ⦈
 ctil dim (cell' (mbt , cv) x) = cell' tt <$>
    let ct = (cellTerm dim  (fst cv , cellVertsHead (snd cv)) x)
    in Mb.rec
         (pure ct)
         (λ tmUDG →
            UndegenCell.undegenCell dim tmUDG ct) mbt

  where
  cellVertsHead : CellVerts → Maybe (Bool × R.Term) × [𝟚×Term]  
  cellVertsHead cv = 
    let l = L.map (snd) $ CellVerts→List cv
        lM = L.map (length) l


    in if (allEqual? discreteℕ lM) then nothing , Mb.fromMaybe [] (listToMaybe l) else
        let maxL = foldr max 0 lM
        in Mb.rec (nothing , []) (λ x → listToMaybe x , tail x) (findBy (λ x → Dec→Bool $ discreteℕ (length x) maxL ) l)


 ctils [] = ⦇ [] ⦈
 ctils ((sf , x) ∷ xs) = 
   ⦇ ⦇ pure (sf ++ [ nothing ]) , ctil (suc (sfDim sf)) x ⦈ ∷ ctils xs ⦈




foldBdTerm : R.Type → R.Term → foldBdTermWithCuInput
              → R.TC R.Term
foldBdTerm _ _ [] = R.typeError [ "foldBdTerm undefined for 0 dim" ]ₑ
foldBdTerm ty f0 xs = do
  let dim = length xs
      needsCongFill = any? (L.map (λ { ((_ , nothing) , (_ , nothing) ) → false ; _ → true} ) xs)
  t0 ← liftVarsFrom dim zero <$> normaliseWithType "mkFoldTerm" ty
            (subfaceCell (repeat (predℕ dim) (just false)) f0) 
  toTerm {A = Unit} dim <$>
   ⦇ hco
    (mapM (idfun _) $ join $ zipWith
      (λ k (cu0 , cu1) →
       let sf0 = replaceAt k (just false) (repeat dim nothing)
           sf1 = replaceAt k (just true) (repeat dim nothing)
           prmV = invVar 0 ∘S remapVars (λ k →
                     if (k <ℕ dim) then (if (k =ℕ (predℕ dim)) then zero else suc k)
                         else k)
                     
           fc : SubFace →
                  (CuTerm' ⊥ (Maybe (R.Term × R.Term) × Maybe IExpr × CellVerts) ×
                    Maybe R.Term) →
                  List _
           fc sf cu =
            let cuTm' = ((prmV ∘S ToTerm.toTerm (defaultCtx dim)) <$>
                            MakeFoldTerm.ctil t0 (predℕ dim) (fst cu))
                cuTm = ⦇ cell cuTm' ⦈
            in [ ((sf ,_)) <$>
               (if (not needsCongFill)
                then cuTm
                else do
                 cpa ←  cell <$>
                         (Mb.rec (subfaceCellNoDrop (just true ∷ repeat (predℕ dim) nothing) <$> cuTm')
                              (λ pa → pure $  (prmV pa)) (snd cu))
                 ⦇ hco
                   (pure ( (just true ∷ repeat (predℕ dim) nothing , cpa)
                       ∷ [ just false ∷ repeat (predℕ dim) nothing ,
                             cell t0 ]))
                   cuTm ⦈) ]

       in fc sf0 cu0 ++ fc sf1 cu1)
      (range dim) xs )
    ⦇ cell ⦇ t0 ⦈ ⦈ ⦈

doNotReduceInPathSolver = [ quote ua ]



toNoCons : ℕ → CuTerm → R.TC (CuTerm' ⊥ Unit × Maybe R.Term)
toNoCons dim cu =
 Mb.rec
  (do ptm ← addNDimsToCtx (suc dim) $ R.normalise $ (ToTerm.toTerm (defaultCtx (suc dim)) (fillCongs 100 dim cu))
      pure $ appCongs dim cu , just ptm)
  (λ x → ⦇ ⦇ x ⦈ , ⦇ nothing ⦈ ⦈)
  (tryCastAsNoCong cu)

macro

 solvePaths : R.Term → R.TC Unit
 solvePaths h = R.withReduceDefs (false , doNotReduceInPathSolver) do
  hTy ← R.inferType h >>= wait-for-term >>= R.normalise
  R.debugPrint "solvePaths'" 0 $ [ "solvePaths' - start" ]ₑ
  bdTM@(A , fcs) ← matchNCube hTy
  R.debugPrint "solvePaths'" 0 $ [ "solvePaths' - matchNCube done" ]ₑ
  let dim = length fcs

  (t0 , _) ← Mb.rec (R.typeError [ "imposible in solvePaths''" ]ₑ) pure (lookup fcs zero)

  cuFcs ← (quoteBd bdTM >>= mapM
    (λ (cu0 , cu1) → ⦇ toNoCons (predℕ dim) cu0 , toNoCons (predℕ dim) cu1 ⦈)) <|>
      R.typeError [ "quoteBd - failed" ]ₑ
  
  solution ← markVertBd A cuFcs >>= foldBdTerm A t0
  R.unify solution h --<|> R.typeError ("unify - failed:" ∷nl [ solution ]ₑ )
  
