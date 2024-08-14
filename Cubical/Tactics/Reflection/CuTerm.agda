{-# OPTIONS --safe  #-} 

module Cubical.Tactics.Reflection.CuTerm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.List as L
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Nat
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_ ; _<_ to _<ℕ_)


import Agda.Builtin.Reflection as R
open import Agda.Builtin.String

open import Cubical.Tactics.Reflection.Dimensions
open import Cubical.Tactics.Reflection.Error

open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.Reflection.Utilities

open import Cubical.Reflection.Base renaming (v to 𝒗)
open import Cubical.Reflection.Sugar

private
  variable
    ℓ : Level
    A B : Type ℓ
    
data CuTerm' (CongGuard : Type) (A : Type ℓ) : Type ℓ

data CuArg' (CongGuard : Type) (A : Type ℓ) : Type ℓ where
 iArg : IExpr → CuArg' CongGuard A
 tArg : CuTerm' CongGuard A → CuArg' CongGuard A

data CuTerm' CongGuard A where
 hco : List (SubFace × CuTerm' CongGuard A) → CuTerm' CongGuard A → CuTerm' CongGuard A
 cell' : A → R.Term → CuTerm' CongGuard A
 𝒄ong' : {cg : CongGuard} → R.Term → List ((CuTerm' CongGuard A)) → CuTerm' CongGuard A

pattern
 cell x = cell' tt x
-- pattern
--  hco x y = hco' tt x y

pattern
 𝒄ong th tl = 𝒄ong' {cg = tt} th tl

CuTerm = CuTerm' Unit Unit

CuTermNC = CuTerm' ⊥ Unit 


 
isCell : CuTerm → Bool
isCell (cell x) = true
isCell _ = false


is𝑪ongFreeF : List (SubFace × CuTerm) → Bool

is𝑪ongFree : CuTerm → Bool 
is𝑪ongFree (hco x x₁) = is𝑪ongFreeF x and is𝑪ongFree x₁
is𝑪ongFree (cell x) = true
is𝑪ongFree (𝒄ong x x₁) = false

is𝑪ongFreeF [] = true
is𝑪ongFreeF ((_ , x) ∷ xs) = is𝑪ongFree x and is𝑪ongFreeF xs


cellQ : CuTerm → Bool
cellQ (cell x) = true
cellQ _ = false

almostLeafQ : CuTerm → Bool
almostLeafQ (hco x (hco x₁ x₂)) = false
almostLeafQ (hco x (cell x₁)) =
  foldr (_and_ ∘S cellQ ∘S snd) true x
almostLeafQ _ = false



module prettyPrinter {A B : Type} (cellTermRender : CuCtx → R.Term →  R.TC (List R.ErrorPart)) (dim : ℕ) where

 renderSubFaceExp : SubFace → R.TC String 
 renderSubFaceExp sf = R.normalise (SubFace→Term sf) >>= renderTerm

  
 renderSubFacePattern : CuCtx → SubFace → String 
 renderSubFacePattern ctx sf =
   foldl _<>_ "" (L.map
       ((λ (b , k) → let k' = L.lookupAlways "‼"
                                   (freeVars ctx) k
                     in "(" <> k' <> "=" <> (if b then "1" else "0") <> ")"))
      (subFaceConstraints sf))
   -- (mapM (λ (b , k) → do k' ← renderTerm (R.var k [])
   --                       pure $ "(" <> k' <> "=" <> (if b then "1" else "0") <> ")")
   -- ∘S subFaceConstraints) >=& foldl _<>_ ""

 ppCT'' : CuCtx → ℕ → CuTerm' A B → R.TC (List R.ErrorPart)
 -- ppCArg : CuCtx → ℕ → CuArg → R.TC (List R.ErrorPart)
  
 ppCT'' _ zero _ = R.typeError [ "pPCT FAIL" ]ₑ
 ppCT'' ctx (suc d) (hco x x₁) = do
   let l = length ctx ∸ dim
   indN ← foldr max zero <$> (
              (mapM ((((pure ∘ (renderSubFacePattern ctx)) >=& stringLength)) ∘S fst ) x))

   let newDimVar = (mkNiceVar' "𝒛" l)
   rest ← (L.intersperse (R.strErr "\n") ∘S L.join)  <$> mapM
         (λ (sf , cu) → do



            -- R.extendContext "zz" (varg (R.def (quote I) [])) $
            ( do
               let sfTm = renderSubFacePattern ctx sf 
               -- R.extendContext newDimVar (varg (R.def (quote I) [])) $         
               (do sfTm' ← inCuCtx' (("z" , nothing) ∷ ctx) $ R.formatErrorParts [ liftVars (SubFace→TermInCtx ctx sf) ]ₑ
                   cu' ← (ppCT'' ((newDimVar , nothing) ∷ applyFaceConstraints sf ctx) d cu)
                   cu'' ← R.formatErrorParts cu'
                   let cu''' = indent' false ' ' 2 cu''
                   pure (offsetStrR indN sfTm  ∷ₑ
                             -- "/" ∷ₑ sfTm' ∷ₑ
                             " → " ∷ₑ [ cu''' ]ₑ))) >>=
                      (R.formatErrorParts >=& [_]ₑ)) x
   lid ← indent '│' 1 <$> (ppCT'' ctx d x₁ >>= R.formatErrorParts)
   rest' ← indent '║' 2 <$> R.formatErrorParts rest
   pure $ (R.strErr ("\n𝒉𝒄𝒐𝒎𝒑 λ " <> newDimVar <> "\n")) ∷
                   (rest' ∷ₑ "\n├─────────── \n" ∷ₑ
                   lid ∷ₑ [ "\n└─────────── "]ₑ)
  
 ppCT'' ctx _ (cell' _ x) = do
  ctr ← cellTermRender ctx x >>=
             --inCuCtx ctx ∘
             R.formatErrorParts
  pure [ ctr ]ₑ
 ppCT'' ctx (suc d) (𝒄ong' h t) = do
  rT ← mapM (argRndr >=> R.formatErrorParts) t
  rHead ← inCuCtx ctx $ addNDimsToCtx' "𝒙" (length t) $ renderTerm h
  pure  $ [ rHead <> indent ' ' 2 (foldr (_<>_  ∘S ("\n" <>_)) "" rT)]ₑ 

  where
  argRndr :  CuTerm' A B → R.TC _
  argRndr x =
      ((λ s → [ "(" ]ₑ ++ s ++ [ ")" ]ₑ) <$> (ppCT'' ctx d x))
  
 ppCT' :  ℕ → CuTerm' A B → R.TC (List R.ErrorPart)
 ppCT' = ppCT'' (defaultCtx dim)


ppCTn : {A B : Type} → Bool →  ℕ → ℕ → CuTerm' A B → R.TC (List R.ErrorPart)
ppCTn b =
  prettyPrinter.ppCT' (λ ctx x →
        do inCuCtx ctx $ do
            nt ← (if b then R.normalise else R.reduce) x
            x'' ← R.formatErrorParts [ nt ]ₑ
            pure [ R.strErr x'' ]) 


ppCT : {A B : Type} → ℕ → ℕ → CuTerm' A B  → R.TC (List R.ErrorPart)
ppCT = ppCTn true


ppCTs : {A B : Type} → ℕ → ℕ → CuTerm' A B  → R.TC (List R.ErrorPart)
ppCTs = prettyPrinter.ppCT' (λ _ x → pure [ R.strErr "■" ]) 



constPartial : A → ∀ φ → Partial φ A
constPartial a φ 1=1 = a

module ToTerm {A B : Type} where

 toTerm : CuCtx → CuTerm' A B → R.Term
 toTermFill toTermFill' : CuCtx → List (SubFace × CuTerm' A B) → CuTerm' A B → R.Term


 toTermA : CuCtx → List (CuTerm' A B) → List (R.Term)


 mkSFTrm : CuCtx → SubFace × CuTerm' A B → R.Term 
 mkSFTrm ctx (sf , cu) =
   R.def (quote constPartial)
    (toTerm (("𝒛" , nothing) ∷ applyFaceConstraints sf ctx) cu v∷
       v[ liftVars (SubFace→TermInCtx ctx sf) ])
 
 toSides : CuCtx → List (SubFace × CuTerm' A B) → R.Term
 toSides ctx [] = R.pat-lam [] []
 toSides ctx (x ∷ []) = mkSFTrm ctx x

 

 toSides ctx ((sf , cu) ∷ xs@(_ ∷ _)) =
   R.def (quote primPOr)
     (liftVars (SubFace→TermInCtx ctx sf) v∷ R.unknown v∷
        (mkSFTrm ctx (sf , cu)) v∷ v[ toSides ctx xs ])

 toTermA ctx [] = []
 toTermA ctx (x ∷ xs) =
    (toTerm ctx x) ∷  toTermA ctx xs 

 toTerm ctx (hco x x₁) =
   R.def (quote hcomp)
     (vlam "𝒛" (toSides ctx x) v∷ v[ toTerm ctx x₁ ])
 toTerm ctx (cell' _ x) = 
   liftWhere (L.map ((λ { (just _) → true ; _ → false }) ∘S snd ) ctx) x

 toTerm ctx (𝒄ong' h t) =
  let h' = liftWhere (repeat (length t) false ++ L.map ((λ { (just _) → true ; _ → false }) ∘S snd ) ctx) h
  in substTms (toTermA ctx t) h'

 toTermFill ctx x x₁ =
   R.def (quote hfill)
     (liftVars (vlam "𝒛" (toSides ctx x)) v∷
       R.def (quote inS) v[ liftVars (toTerm ctx x₁) ] v∷ v[ 𝒗 zero ])

 toTermFill' ctx x x₁ =
   R.def (quote hfill)
     (liftVarsFrom 1 (length ctx) (vlam "𝒛" (toSides ctx x)) v∷
       R.def (quote inS) v[ liftVarsFrom 1 (length ctx) (toTerm ctx x₁) ] v∷ v[ 𝒗 (length ctx) ]) 

toTerm : {A B : Type} → ℕ → CuTerm' A B → R.Term
toTerm dim = vlamⁿ dim ∘ (ToTerm.toTerm (defaultCtx dim)) 



module cuEval {A : Type} {b : B} where

 cuEval : ℕ → SubFace → CuTerm' A B → CuTerm' A B
 cuEvalL : ℕ → SubFace → List (CuTerm' A B) → List (CuTerm' A B)
 
 cuEvalL _ sf [] = []
 cuEvalL fuel sf (x ∷ l) = cuEval fuel sf x ∷ cuEvalL fuel sf l
 cuEval zero _ _ = cell' b (R.lit (R.string "out of fuel in cuEval"))
 cuEval (suc fuel) sf (hco l y) =
  let sSf = findBy (⊂⊃? ∘S (sf <sf>_) ∘S fst) l
  in h sSf

  where
  msf : SubFace × CuTerm' A B → Maybe (SubFace × CuTerm' A B)
  msf (sf' , t) =
    map-Maybe
     (λ sf'' → (injSF sf sf'') , cuEval fuel (nothing ∷ (injSF sf' sf'')) t)
     (sf' sf∩ sf) 
    
  h :  Maybe (SubFace × CuTerm' A B) → CuTerm' A B
  h (just (_ , x)) = cuEval fuel (just true ∷ repeat (sfDim sf) nothing) x
  h nothing =
    Mb.rec
      (let l' = L.catMaybes (L.map msf l)
       in hco l' (cuEval fuel sf y))
      (λ (sf' , f) → cuEval fuel (just true ∷ (injSF sf' sf)) f)
      (findBy (sf ⊂?_ ∘S [_] ∘S fst) l)



 cuEval fuel sf (cell'  x x₁) = cell' x (subfaceCell sf x₁)
 cuEval fuel sf (𝒄ong' {cg = cg} h tl) =
   let h' = subfaceCell (repeat (length tl)  nothing ++ sf) h
    in 𝒄ong' {cg = cg} h' (cuEvalL fuel  sf tl)

cuEval : {A : Type} {B : Type ℓ} {b : B} → SubFace → CuTerm' A B → CuTerm' A B
cuEval {b = b} = cuEval.cuEval {b = b} 100 



pickSFfromPartial' : A → SubFace → List (SubFace × CuTerm' B A) → Maybe (CuTerm' B A)
pickSFfromPartial' a sf l =
  let sSf = findBy (sf ⊂?_ ∘S [_] ∘S fst) l
  in map-Maybe (λ (sf' , f) → cuEval {b = a} (nothing ∷ (injSF sf' sf)) f) sSf

pickSFfromPartial : SubFace → List (SubFace × CuTerm) → Maybe (CuTerm)
pickSFfromPartial = pickSFfromPartial' _





module normaliseCells where

 
 nc : ℕ → ℕ → (CuTerm' A B) → R.TC (CuTerm' A B)
 nc zero _ _ = R.typeError [ "out of fuel in normaliceCells" ]ₑ
 nc (suc fuel) dim (hco x x₁) =
   ⦇ hco
       (mapM (λ (sf , x) → ⦇ ⦇ sf ⦈ , ( nc fuel (suc (sfDim sf)) x) ⦈ ) x)
       (nc (suc fuel) dim x₁) ⦈
 nc (suc fuel) dim (cell' x x₁) =
   cell' x <$> (addNDimsToCtx dim $ R.normalise x₁)
 nc (suc fuel) dim (𝒄ong' {cg = cg} x x₁) =
   𝒄ong' {cg = cg} x <$> mapM (nc fuel dim) x₁

normaliseCells : ℕ → CuTerm' A B → R.TC (CuTerm' _ _)
normaliseCells = normaliseCells.nc 100

cuEvalN : SubFace → (CuTerm' A Unit) → R.TC (CuTerm' A Unit)
cuEvalN sf = normaliseCells (sfDim sf) ∘S cuEval sf


mostNestedCap : CuTermNC → R.Term 
mostNestedCap (hco x x₁) = mostNestedCap x₁
mostNestedCap (cell' x x₁) = x₁


-- this can be trusted, only if we sure that term already typechecks!

allCellsConstant? : ℕ → CuTerm' A B → Bool
allCellsConstant? dim x = h dim x 
 where
 h : ℕ → CuTerm' _ _  → Bool
 hs : List (SubFace × CuTerm' _ _)  → Bool

 h dim (hco x₁ x₂) = h dim x₂ and hs x₁
  
 h dim (cell' x₁ x₂) = not (hasVarBy (_<ℕ dim) x₂)
 h dim (𝒄ong' x₁ x₂) = false

 hs [] = true
 hs ((sf , x) ∷ xs) = (h (suc (sfDim sf)) x) and hs xs
 
module permuteVars where

 permute : (ℕ → ℕ) → SubFace → SubFace
 permute f sf = foldr (λ k → replaceAt (f k) (lookupAlways nothing sf k)) sf (range (length sf))

 intoFace fromFace : SubFace → ℕ → ℕ
 intoFace [] k = k
 intoFace (nothing ∷ sf) zero = zero
 intoFace (nothing ∷ sf) (suc k) = suc (intoFace sf k)
 intoFace (just x ∷ sf) k = intoFace sf (predℕ k)
 fromFace [] k = k
 fromFace (nothing ∷ xs) zero = zero
 fromFace (nothing ∷ xs) (suc k) = suc (fromFace xs k)
 fromFace (just x ∷ xs) k = suc (fromFace xs k)
 
 sfPerm : SubFace → (ℕ → ℕ) → (ℕ → ℕ)
 sfPerm sf f k =
  if k =ℕ sfDim sf
  then k
  else intoFace (permute f sf) (f (fromFace sf k))
 
 nc : ℕ → (ℕ → ℕ) →  ℕ → CuTerm → R.TC CuTerm 
 nc zero _ _ _ = R.typeError [ "out of fuel in permuteVars" ]ₑ
 nc (suc fuel) prm dim (hco x x₁) = do
   
   ⦇ hco
      (mapM (λ (sf , c) → ⦇ ⦇ (permute prm sf) ⦈ , (nc fuel (sfPerm sf prm) (suc (sfDim sf)) c) ⦈) x)
      (nc (suc fuel) prm dim x₁) ⦈
 nc (suc fuel) prm _ (cell x) =
  pure $ cell (remapVars prm x)
 nc (suc fuel) _ _ (𝒄ong' x x₁) = R.typeError [ "TODO in permuteVars" ]ₑ


permuteVars = permuteVars.nc 100


CuBoundary' : ∀ A B → Type ℓ
CuBoundary' A B = List (CuTerm' A B × CuTerm' A B)

CuBoundary = CuBoundary' Unit Unit


tryCastAsNoCongS :  (List (SubFace × CuTerm)) → Maybe (List (SubFace × CuTerm' ⊥ Unit))


tryCastAsNoCong : CuTerm → Maybe (CuTerm' ⊥ Unit)
tryCastAsNoCong (hco x x₁) = 
    ⦇ hco (tryCastAsNoCongS x) (tryCastAsNoCong x₁) ⦈
tryCastAsNoCong (cell x) = pure $ cell' _ x
tryCastAsNoCong (𝒄ong' x x₁) = nothing


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



module codeGen {A B : Type} (normaliseCells : Bool)  (dim : ℕ) where

 renderSubFaceExp : SubFace → R.TC String 
 renderSubFaceExp sf = R.normalise (SubFace→Term sf) >>= renderTerm

  
 renderSubFacePattern : CuCtx → SubFace → String 
 renderSubFacePattern ctx sf =
   foldl _<>_ "" (L.map
       ((λ (b , k) → let k' = L.lookupAlways "‼"
                                   (freeVars ctx) k
                     in "(" <> k' <> " = " <> (if b then "i1" else "i0") <> ")"))
      (subFaceConstraints sf))

 ppCT'' : CuCtx → ℕ → CuTerm' A B → R.TC (List R.ErrorPart)
 -- ppCArg : CuCtx → ℕ → CuArg → R.TC (List R.ErrorPart)
  
 ppCT'' _ zero _ = R.typeError [ "pPCT FAIL" ]ₑ
 ppCT'' ctx (suc d) (hco x x₁) = do
   let l = length ctx ∸ dim
   indN ← foldr max zero <$> (
              (mapM ((((pure ∘ (renderSubFacePattern ctx)) >=& stringLength)) ∘S fst ) x))

   let newDimVar = (mkNiceVar' "𝒛" l)
   rest ← (L.intersperse (R.strErr "\n;") ∘S L.join)  <$> mapM
         (λ (sf , cu) → do



            -- R.extendContext "zz" (varg (R.def (quote I) [])) $
            ( do
               let sfTm = renderSubFacePattern ctx sf 
               -- R.extendContext newDimVar (varg (R.def (quote I) [])) $         
               (do sfTm' ← inCuCtx' (("z" , nothing) ∷ ctx) $ R.formatErrorParts [ liftVars (SubFace→TermInCtx ctx sf) ]ₑ
                   cu' ← (ppCT'' ((newDimVar , nothing) ∷ applyFaceConstraints sf ctx) d cu)
                   cu'' ← R.formatErrorParts cu'
                   let cu''' = indent' false ' ' 2 cu''
                   pure (offsetStrR indN sfTm  ∷ₑ
                             -- "/" ∷ₑ sfTm' ∷ₑ
                             " → " ∷ₑ [ cu''' ]ₑ))) >>=
                      (R.formatErrorParts >=& [_]ₑ)) x
   lid ← indent ' ' 1 <$> (ppCT'' ctx d x₁ >>= R.formatErrorParts)
   rest' ← indent ' ' 2 <$> R.formatErrorParts rest
   pure $ (R.strErr ("\nhcomp (λ " <> newDimVar <> " → λ { \n")) ∷
                   (rest' ∷ₑ "\n    }) \n" ∷ₑ
                   "(" ∷ₑ lid ∷ₑ ")" ∷ₑ [ "\n "]ₑ)
  
 ppCT'' ctx _ (cell' _ x) = do
  ctr ← inCuCtx ctx $ do
            nt ← (if normaliseCells then R.normalise else pure) x
            x'' ← R.formatErrorParts [ nt ]ₑ
            pure [ R.strErr (x'') ]
     -- cellTermRender ctx x >>=
     --         --inCuCtx ctx ∘
     --         R.formatErrorParts
  pure ctr 
 ppCT'' ctx (suc d) (𝒄ong' h t) = do
  rT ← (L.map (λ (k , s) → R.strErr ("\n    " <> mkNiceVar' "𝒙" k <> " = " <> s ))
            ∘S zipWithIndex) <$> (mapM (argRndr >=> (R.formatErrorParts >=& indent' false ' ' 6)) t)
  rHead ← inCuCtx ctx $ addNDimsToCtx' "𝒙" (length t) $ renderTerm h
  pure  $ "\nlet " ∷ₑ rT ++ "\nin " ∷ₑ [ rHead ]ₑ 

  where
  argRndr :  CuTerm' A B → R.TC _
  argRndr x = (((λ s → [ "(" ]ₑ ++ s ++ [ ")" ]ₑ) <$> (ppCT'' ctx d x)))
  
 ppCT' :  ℕ → CuTerm' A B → R.TC (List R.ErrorPart)
 ppCT' = ppCT'' (defaultCtx dim)



genAbstr : ℕ → String
genAbstr dim = "λ" <> 
 (L.foldl _<>_ "" $ L.map (λ k →  (" " <> mkNiceVar' "𝓲" k)) (rev (range dim))) <> " → "
 
codeGen : {A B : Type} (normaliseCells₁ : Bool) (dim : ℕ) →
            ℕ → CuTerm' A B → R.TC String
codeGen nc dim fuel cu = ((genAbstr dim <>_) ∘S (indent' false ' ' 6)) <$>
  (codeGen.ppCT' nc dim fuel cu >>= R.formatErrorParts)
