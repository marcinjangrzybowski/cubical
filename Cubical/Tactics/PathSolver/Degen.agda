{-# OPTIONS --safe #-} 
module Cubical.Tactics.PathSolver.Degen where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.List as L
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sigma


import Agda.Builtin.Reflection as R
open import Cubical.Reflection.Base renaming (v to 𝒗)

open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.PathSolver.Dimensions
open import Cubical.Tactics.PathSolver.QuoteCubical
open import Cubical.Tactics.PathSolver.CuTerm
open import Cubical.Tactics.PathSolver.Error


undegenTerm : Bool → ℕ → ℕ → R.Term → R.TC R.Term
undegenTerm onEnd offset dim =
    atVarOrDefM.rv
      (λ n k _ args → R.var (n + k) <$> args)
      h
      zero ∘S (if onEnd then (idfun _) else (liftVarsFrom 1 (offset + dim))) 

 where

  g :  R.Name → List (R.Arg R.Term) → R.Term → Maybe R.Term
  g (quote _∨_) a@(_ v∷ v[ _ ]) tm = just tm
  g (quote _∧_) a@(_ v∷ v[ _ ]) tm = just tm
  g (quote ~_) a@(v[ _ ]) tm = just tm
  g _ _ _ = nothing

  h : ℕ →
        R.Name →
        List (R.Arg R.Term) → R.TC (List (R.Arg R.Term)) → R.TC R.Term
  h _ nm arg argM =
     Mb.rec (R.def nm <$> argM)
            ((extractIExprM >=&
              (IExpr→Term
              ∘ mapVarsInIExpr (_+ offset)
              ∘ undegen onEnd dim
              ∘ mapVarsInIExpr (_∸ offset) )))
       (g nm arg (R.def nm arg))

undegenTerm2 : Bool → ℕ → ℕ → R.Term → R.TC R.Term
undegenTerm2 onEnd offset dim =
    atVarOrDefM.rv
      (λ n k _ args → R.var (n + k) <$> args)
      h
      zero ∘S (if onEnd then (idfun _) else (liftVarsFrom 1 (offset + dim))) 

 where

  g :  R.Name → List (R.Arg R.Term) → R.Term → Maybe R.Term
  g (quote _∨_) a@(_ v∷ v[ _ ]) tm = just tm
  g (quote _∧_) a@(_ v∷ v[ _ ]) tm = just tm
  g (quote ~_) a@(v[ _ ]) tm = just tm
  g _ _ _ = nothing

  h : ℕ →
        R.Name →
        List (R.Arg R.Term) → R.TC (List (R.Arg R.Term)) → R.TC R.Term
  h _ nm arg argM =
     Mb.rec (R.def nm <$> argM)
            ((extractIExprM >=&
              (IExpr→Term
              ∘ mapVarsInIExpr (_+ offset)
              ∘ undegen2 onEnd dim
              ∘ mapVarsInIExpr (_∸ offset) )))
       (g nm arg (R.def nm arg))


module _ (dim : ℕ) where
 macro
  undegenTermTest : R.Term → R.Term → R.TC Unit
  undegenTermTest t h = do
    -- let t' = liftVarsFrom 1 dim t 
    t' ← undegenTerm false zero dim t
    R.unify t' h

-- module _ (A B : Type) (a : ℕ → A) (P : I → B → A) (Q : I → I → B) where

--  utt1 : Path (I → I → A)
--          (λ 𝓲₁ 𝓲₀ → P (𝓲₁ ∧ 𝓲₀ ∧ ~ 𝓲₀) (Q (𝓲₁ ∨ ~ 𝓲₁) (𝓲₁ ∧ 𝓲₀)))
--          λ z z₁ → P i0 (Q i1 ((z₁ ∧ z)))
--  utt1 𝓲₂ 𝓲₁ 𝓲₀ = undegenTermTest 2 (P (𝓲₁ ∧ 𝓲₀ ∧ ~ 𝓲₀) (Q (𝓲₁ ∨ ~ 𝓲₁) (𝓲₁ ∧ 𝓲₀)))

private
  variable
    ℓ : Level
    A : Type ℓ
    CongGuard : Type


-- constAbs : R.Term → R.Term
-- constAbs = vlam "_" ∘S liftVars

constPartialR : R.Term → R.Term → R.Term
constPartialR tI tA = R.def (quote constPartial) (tA v∷ v[ tI ])

module UndegenCell (dim : ℕ) where

 extractAllIExprs : R.Term → List IExpr
 extractAllIExprs tm =
   snd $ runIdentity $ unwrap (atVarOrDefM.rv {M = [ State₀T (List IExpr) RMT IdentityF ]_ }
         (λ _ v _ argM → R.var v <$> argM)
         gg zero tm) []
   where
 
   g :  R.Name → List (R.Arg R.Term) → Bool
   g (quote _∨_) a@(_ v∷ v[ _ ]) = true
   g (quote _∧_) a@(_ v∷ v[ _ ]) = true
   g (quote ~_) a@(v[ _ ]) = true
   g _ _  = false


   gg : _
   gg n nm arg argM = let t = R.def nm arg in
     if (g nm arg)
     then (Mb.rec (liftM (identity tt))
       (λ ie → modify ((mapVarsInIExpr (_∸ n) ie) ∷_)) (extractIExpr t) ) >> pure t
     else R.def nm <$> argM
     
 undegenCell : (R.Term × R.Term) → R.Term → R.TC R.Term
 undegenCell (t0 , tI) t = do
   fe ← undegenFcs dim (extractAllIExprs t0)
   -- Mb.rec (pure t)
   let ie = IExpr→Term (F→I dim fe) 
   pure
   -- addNDimsToCtx (suc dim) $ R.typeError $ [_]ₑ $
     (R.def (quote hcomp)
          (vlam "undegenCellDim"
            (R.def (quote primPOr)
              (R.def (quote ~_) v[ 𝒗 (suc dim) ] v∷ (R.def (quote _∨_) ((𝒗 (suc dim)) v∷
                v[ (liftVars ie) ])) v∷ 
               (constPartialR (R.def (quote ~_) v[ 𝒗 (suc dim) ]) (liftVarsFrom 1 (suc dim) tI))
                 v∷ v[ constPartialR ((R.def (quote _∨_) ((𝒗 (suc dim)) v∷
                v[ (liftVars ie) ]))) (liftVars t) ])) v∷ v[ t ])) 
     -- fex

 mbUndegen : R.Term → R.TC (Maybe (R.Term × R.Term) × R.Term)
 mbUndegen tm = do
  
  allNonDeg ← foldrM
            (\ie b →  (b and_)  <$> (isNonDegen dim ie))
              true (extractAllIExprs tm)
  if allNonDeg then (pure (nothing , tm)) else
    do idt0 ← undegenTerm2 true zero dim tm
       idt1 ← undegenTerm2 false zero dim tm
       -- addNDimsToCtx (1 + dim) $ R.typeError (liftVars idt0 ∷nl liftVars tm ∷nl [ idt1 ]ₑ)
       pure ( just (tm , idt1) , idt0)

 mbUndegen' : R.Term → R.TC (Maybe (R.Term × R.Term) × R.Term)
 mbUndegen' tm = do
  
  allNonDeg ← foldrM
            (\ie b →  (b and_)  <$> (isNonDegen dim ie))
              true (extractAllIExprs tm)
  if allNonDeg then (pure (nothing , tm)) else
    do idt0 ← undegenTerm true zero dim tm
       idt1 ← undegenTerm false zero dim tm
       -- addNDimsToCtx (1 + dim) $ R.typeError (liftVars idt0 ∷nl liftVars tm ∷nl [ idt1 ]ₑ)
       pure ( just (tm , idt1) , idt0)


module _ (onEnd : Bool) where
 undegenCubS :
   (List (SubFace × CuTerm' CongGuard A)) → R.TC (List (SubFace × CuTerm' CongGuard A))

 undegenCubA : ℕ → List (CuTerm' CongGuard A) → R.TC (List (CuTerm' CongGuard A))


 undegenCub : ℕ → CuTerm' CongGuard A → R.TC (CuTerm' CongGuard A)
 undegenCub dim (hco x y) =
        ⦇ hco (undegenCubS x) (undegenCub dim y) ⦈
 undegenCub dim (cell' a x) = cell' a <$> undegenTerm onEnd zero dim x  
 undegenCub dim (𝒄ong' {cg = cg} h t) =
          𝒄ong' {cg = cg}
      <$> undegenTerm onEnd (length t) dim h
      <*> undegenCubA dim t 

 undegenCubA dim [] = ⦇ [] ⦈
 undegenCubA dim (x ∷ l) = ⦇ undegenCub dim x ∷ undegenCubA dim l ⦈

 undegenCubS [] = ⦇ [] ⦈
 undegenCubS ((sf , x) ∷ xs) =
   ⦇ ( (sf ++ (if onEnd then [] else [ nothing ])) ,_ <$>
       undegenCub  (suc (sfDim sf)) x )
     ∷ undegenCubS xs ⦈





module _ (dim : ℕ) where

  macro
   testUndegenCub : R.Term → R.Term → R.TC Unit
   testUndegenCub t hole = do
    cu ← extractCuTerm nothing dim t
    udgn ← undegenCub false dim cu
    let p = toTerm (suc dim) udgn
    R.unify p hole


private
  variable
    x y z w v : A


module T1 {x : A} (p' p'' : x ≡ y) (xr xr' : x ≡ x) (q : y ≡ z) (~r : w ≡ z) (r' r : z ≡ w) (s : w ≡ v)
           (sq : Square xr (sym p'') p'' xr') where

 test0 : Path (x ≡ x) (λ i → p' (i ∧ ~ i)) refl
 test0 = testUndegenCub (suc zero) (λ (i : I) → p' (i ∧ ~ i))


 p : x ≡ y
 p i = sq i (~ i)

 P Q : x ≡ v 
 P = refl ∙ (p ∙' q ∙ sym (~r) ∙ (~r  ∙ (λ i → r (i ∧ ~ i)) ∙  (r ∙ ((λ i → r (i ∨  ~ i))) ∙  s )))
 Q = refl ∙ (p ∙' q ∙ sym (~r) ∙ (~r  ∙ refl ∙  (r ∙ refl ∙  s )))
  
 P≡Q : P ≡ Q
 P≡Q = testUndegenCub (suc zero) (λ (i : I) → P i)
 
