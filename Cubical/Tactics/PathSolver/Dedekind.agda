{-# OPTIONS --allow-exec  #-} 
module Cubical.Tactics.PathSolver.Dedekind where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude


open import Cubical.Data.Bool
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.List as L
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Order.Recursive as ℕOR
open import Cubical.Data.Empty

open import Cubical.Reflection.Base renaming (v to 𝒗)
open import Cubical.Reflection.Sugar
import Agda.Builtin.Reflection as R
open import Agda.Builtin.Reflection.External
open import Agda.Builtin.String
open import Agda.Builtin.Char

open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.Reflection.Utilities

open import Cubical.Tactics.PathSolver.Reflection
open import Cubical.Tactics.Reflection.Error

open import Cubical.Tactics.Reflection.Dimensions
open import Cubical.Tactics.Reflection.CuTerm

open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_ ; _<_ to _<ℕ_)
open import Cubical.Tactics.Reflection.QuoteCubical



strConcat = L.foldl _<>_ ""

module dedekindCodeGen {A B : Type} (normaliseCells : Bool)  (dim : ℕ) where

 renderSubFaceExp : SubFace → R.TC String 
 renderSubFaceExp sf = R.normalise (SubFace→Term sf) >>= renderTerm

  
 renderSubFacePattern : CuCtx → SubFace → String 
 renderSubFacePattern ctx sf =
   foldl _<>_ "" (L.map
       ((λ (b , k) → let k' = L.lookupAlways "‼"
                                   (freeVars ctx) k
                     in "" <> k' <> " = " <> (if b then "1" else "0") <> ""))
      (subFaceConstraints sf))

 ppCT'' : CuCtx → ℕ → CuTerm' A B → R.TC (List R.ErrorPart)
 -- ppCArg : CuCtx → ℕ → CuArg → R.TC (List R.ErrorPart)
  
 ppCT'' _ zero _ = R.typeError [ "pPCT FAIL" ]ₑ
 ppCT'' ctx (suc d) (hco x x₁) = do
   let l = length ctx ∸ dim
   indN ← foldr max zero <$> (
              (mapM ((((pure ∘ (renderSubFacePattern ctx)) >=& stringLength)) ∘S fst ) x))

   let newDimVar = (mkNiceVar' "𝒛" l)
   rest ← (L.intersperse (R.strErr " | ") ∘S L.join)  <$> mapM
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
                             " -> " ∷ₑ [ cu''' ]ₑ))) >>=
                      (R.formatErrorParts >=& [_]ₑ)) x
   lid ← indent ' ' 1 <$> (ppCT'' ctx d x₁ >>= R.formatErrorParts)
   rest' ← indent ' ' 2 <$> R.formatErrorParts rest
   pure $ (R.strErr ("\n hcomp (" <> newDimVar <> ")") ∷
                     "[" <> rest' <> "]" ∷ₑ
                   "" ∷ₑ lid ∷ₑ "" ∷ₑ [ "\n "]ₑ)
  
 ppCT'' ctx _ (cell' _ x) = do
       ctr ← inCuCtx ctx $ do
                 nt ← (if normaliseCells then R.normalise else pure) x
                 -- x'' ← R.formatErrorParts [ nt ]ₑ
                 termRndr nt
       pure ctr

  
    where
     renameConnections : String → String
     renameConnections =
           primStringFromList
        ∘S ( _>>= h )
        ∘S primStringToList
       where
       h : Char → List Char
       h '∨' = primStringToList "\\/"
       h '∧' = primStringToList "/\\"
       h x = [ x ]
       
     termRndr : R.Term → R.TC (List R.ErrorPart)
     termRndr (R.var x []) = [_]ₑ <$> renderTerm (R.var x [])
     termRndr (R.var x args) = do
        hd ← renderTerm (R.var x [])
        tl ← mapM ((renderTerm >=& renameConnections) ∘S unArg) args
        pure [ hd <> "(" <> strConcat (intersperse "," tl) <> ")"]ₑ 
     termRndr _ = R.typeError [ "todo in termRndr in Dedekind.agda" ]ₑ 
 ppCT'' ctx (suc d) (𝒄ong' h t) = pure [ "𝒄ong' - TODO" ]ₑ

 -- <> indent ' ' 2 (foldr (_<>_  ∘S ("\n" <>_)) "" rT)

  where
  argRndr :  CuTerm' A B → R.TC _
  argRndr x = (((λ s → [ "(" ]ₑ ++ s ++ [ ")" ]ₑ) <$> (ppCT'' ctx d x)))
  
 



asDedekindExpr : CuCtx  → CuTerm' ⊥ Unit → R.TC String
asDedekindExpr ctx cu = dedekindCodeGen.ppCT'' true (length ctx) ctx 100 cu >>= R.formatErrorParts


liftedTele : R.Telescope → R.Telescope
liftedTele [] = []
liftedTele (x ∷ xs) = L.map (map-snd (mapArg liftVars)) (x ∷ liftedTele xs)

asDedekindBd : CuBoundary' ⊥ Unit → R.TC String
asDedekindBd xs = do
  fcs ← strConcat ∘S intersperse " | " <$> (mapM h $ (zipWithIndex xs >>=
          λ (k , (cu0 , cu1)) → ((k , false) , cu0) ∷ [ (k , true) , cu1 ]))
  pure $ "(" <> ( strConcat $ intersperse " "  (fst <$> (cc)))
   <> ")[" <>
     fcs
     <> "]"

 where

  vr = mkNiceVar' "𝓲"

  cc : CuCtx
  cc = (_, nothing) ∘S vr ∘S fst <$>  (zipWithIndex xs)

  h : Σ (ℕ × Bool) (λ v → CuTerm' ⊥ Unit) → R.TC String
  h ((k , b) , cu) = 
   ((mkNiceVar' "𝓲" k <> " = " <> (if b then "1" else "0") <> " -> ") <>_) <$>
      (asDedekindExpr (rev (dropAt k cc)) cu)


asDedekindCtx : R.Telescope → R.TC String
asDedekindCtx = (mapM asDedekindCtxEntry >=& (strConcat ∘S rev ∘S catMaybes)) ∘S liftedTele

 where
  asDedekindCtxEntry : String × (R.Arg R.Type) → R.TC (Maybe String)
  asDedekindCtxEntry (s , R.arg _ (R.agda-sort _)) = pure nothing
  asDedekindCtxEntry (s , R.arg _ (R.def (quote Level) _)) = pure nothing
  asDedekindCtxEntry (s , R.arg i ty) = do
   -- (just ∘S (("\n" <> s <> "\n") <>_)) <$> (R.quoteTC ty >>= R.normalise >>= renderTerm) 
   ty' ← R.normalise ty
   nbd ← matchNCube ty' >>= quoteBdNC
   tyStr ← asDedekindBd nbd
   pure $ just $  s <> " : " <> tyStr <> "\n"


renderDedekindProblem : CuBoundary' ⊥ Unit → R.TC String
renderDedekindProblem bd = do
 ctx ← R.getContext >>= asDedekindCtx
 goal ← asDedekindBd bd
 pure $ ctx <> "---\n? : " <> goal


macro
 renderDedekindProblemM : R.Term → R.TC Unit
 renderDedekindProblemM h = do
   goal' ← R.inferType h >>= wait-for-type >>= R.normalise
   s ← matchNCube goal' >>= quoteBdNC >>= renderDedekindProblem
   R.typeError [ s ]ₑ


 ded! : R.Term → R.TC Unit
 ded! h = do
   goal' ← R.inferType h >>= wait-for-type >>= R.normalise
   dedInput ← matchNCube goal' >>= quoteBdNC >>= renderDedekindProblem
   (_ , (dedOutput , dedError)) ← execTC "dedekind-std" [] dedInput
   s ← R.checkFromStringTC dedOutput goal' <|>
      (R.typeError $ "ded! - failed\n\ndedekind output: " ∷nl dedOutput 
                     ∷nl "dedekind error:" ∷nl dedError 
                     ∷nl "dedekind input: " ∷nl [ dedInput ]ₑ )
   R.unify s h

module _ {ℓ} {A : Type ℓ}
  {x y z w : A}
  (p : x ≡ y)(q : y ≡ z)(r : z ≡ w)
  where
  open import Cubical.Foundations.GroupoidLaws




  cpf-ded : PathP (λ j → x ≡ q j) p (p ∙ q)
  cpf-ded = ded!

  _ : p ≡ refl ∙ p
  _ = ded!

  _ : p ≡ p ∙ refl
  _ = ded!


  assoc-ded : p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
  assoc-ded = ded!

  _ : Cube
       (λ i i₁ → p (i ∧ i₁)) (λ _ → p)
       (λ i i₁ → p (i ∧ i₁)) (λ _ → p)
       refl (λ i i₁ → p (i ∨ i₁))
  _ = ded!


  
  cpf-≡-cpf-ded : (compPath-filler {x = x} refl refl) ≡ (compPath-filler {x = x} refl refl) 
  cpf-≡-cpf-ded = {!ded!!}

  assoc-ded-≡-assoc : assoc-ded ≡ assoc p q r
  assoc-ded-≡-assoc = {!ded!!}

-- -- module gencode2 {ℓ} (A : Type ℓ)
-- --   (x y z w v : A)
-- --   (p : x ≡ y)(q : y ≡ z)(r : z ≡ w)(s : w ≡ v)
-- --   where
-- --   -- open import Cubical.Foundations.GroupoidLaws



-- --   -- pentagonIdentityViaDed : (assoc-ded p q (r ∙ s) ∙ assoc-ded (p ∙ q) r s)
-- --   --                             ≡
-- --   --        cong (p ∙_) (assoc-ded q r s) ∙ assoc-ded p (q ∙ r) s ∙ cong (_∙ s) (assoc-ded p q r)
-- --   -- pentagonIdentityViaDed = {!renderDedekindProblemM!}

-- module eckhil {ℓ} (A : Type ℓ)
--   (x : A)
--   (p q r : Path (x ≡ x) refl refl) where

--  _ : Square p p q q       
--  _ = ded!


--  -- _ : Cube p p q q r r       
--  -- _ = ded!
