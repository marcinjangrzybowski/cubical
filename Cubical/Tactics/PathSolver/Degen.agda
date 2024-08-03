{-# OPTIONS --safe #-} 
module Cubical.Tactics.PathSolver.Degen where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws

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



-- really just refl ∙_  
reComp : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → x ≡ y
reComp p i =
  hcomp {φ = i ∨ ~ i} (λ k _ → (p (i ∧ k))) (p i0)


--  really just lUnit
reFill : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → p ≡ reComp p
reFill p j i =
  hcomp {φ = i ∨ ~ i ∨ ~ j} (λ k _ → (p (i ∧ k))) (p i0)

module unConnect (do-fill : Bool) where

 unConnCell : ℕ → R.Term → R.Term → R.TC CuTerm
 unConnCell dim jT (R.var k (z₀ v∷ v[ z₁ ])) =
   (if do-fill then (pure ∘S cell) else (quoteCuTerm nothing dim))
     (R.def (quote reFill)
       (vlam "𝒾"
       ((R.def (quote reFill) (R.var (suc k) v[ 𝒗 zero ] v∷ (liftVars jT) v∷ v[ liftVars z₁ ])))
        v∷ jT v∷  v[ z₀ ]))

 unConnCell dim jT (R.var k v[ z ]) =
   (if do-fill then (pure ∘S cell) else (quoteCuTerm nothing dim))
     (R.def (quote reFill) ((R.var k []) v∷ jT v∷ v[ z ]))
 unConnCell _ _ t = pure $ cell' _ t


 unConnS : List (SubFace × CuTerm) → R.TC (List (SubFace × CuTerm))

 unConnA : ℕ → List (CuTerm) → R.TC (List (CuTerm))


 unConn : ℕ → CuTerm → R.TC (CuTerm)
 unConn dim (hco x x₁) = ⦇ hco (unConnS x) (unConn dim x₁) ⦈
 unConn dim (cell' x x₁) =
   if do-fill
   then unConnCell (suc dim) (𝒗 dim) (liftVarsFrom (suc zero) dim x₁) 
   else unConnCell dim (endTerm true) x₁ 
 unConn dim (𝒄ong' {cg = cg} x x₁) = 𝒄ong' {cg = cg} x <$> unConnA dim x₁ 

 unConnS [] = ⦇ [] ⦈
 unConnS ((sf , x) ∷ xs) = ⦇ ⦇ ⦇ (sf ++ (if do-fill then [ nothing ] else [])) ⦈
  , unConn (suc (sfDim sf)) x ⦈ ∷ unConnS xs ⦈

 unConnA _ [] = ⦇ [] ⦈
 unConnA dim (x ∷ xs) = ⦇ (unConn dim x) ∷ (unConnA dim xs) ⦈



unConn = unConnect.unConn false
unConnFill = unConnect.unConn true


module _ (dim : ℕ) where
 macro
  unConnTest : R.Term → R.Term → R.TC Unit
  unConnTest t h = do
   cu ← (extractCuTerm nothing dim t)
   cu' ← unConn dim cu
   te0 ← ppCT dim 100 cu
   te0' ← ppCT dim 100 cu'
   wrapError h $
          "input:" ∷nl (indentₑ 4 te0)
     ++nl "\n∨,∧,~ - removed :" ∷nl (indentₑ 4 te0')

  unConnM : R.Term → R.Term → R.TC Unit
  unConnM t h = do
   cu ← (extractCuTerm nothing dim t)
   cu' ← unConn dim cu
   R.unify (toTerm dim cu') h

  unConnM≡ : R.Term → R.Term → R.TC Unit
  unConnM≡ t h = do
   cu ← (extractCuTerm nothing dim t)
   cu' ← unConnFill dim cu
   let cu'T = toTerm (suc dim) cu'
   -- cu'' ← R.checkType cu'T (R.def (quote PathP) (R.unknown v∷ R.unknown v∷ v[ R.unknown ]))
   R.unify cu'T h



module _ (A : Type ℓ) (x y z w : A) (p : x ≡ y)(q : y ≡ z)(r : z ≡ w) where

 _ : ResultIs
        ("input:                                       " ∷
         "                                             " ∷
         "     𝒉𝒄𝒐𝒎𝒑 λ 𝒛₀                              " ∷
         "     ║  (𝓲₀=0) → q 𝓲₁                        " ∷
         "     ║  (𝓲₁=0) → p (~ 𝓲₀ ∨ ~ 𝒛₀)             " ∷
         "     ║  (𝓲₁=1) → r (𝓲₀ ∧ 𝒛₀)                 " ∷
         "     ║                                       " ∷
         "     ├───────────                            " ∷
         "     │ q 𝓲₁                                  " ∷
         "     └───────────                            " ∷
         "∨,∧,~ - removed :                            " ∷
         "                                             " ∷
         "     𝒉𝒄𝒐𝒎𝒑 λ 𝒛₀                              " ∷
         "     ║  (𝓲₀=0) →                             " ∷
         "     ║     𝒉𝒄𝒐𝒎𝒑 λ 𝒛₁                        " ∷
         "     ║     ║  (𝓲₁=0) → y                     " ∷
         "     ║     ║  (𝓲₁=1) → q 𝒛₁                  " ∷
         "     ║     ║                                 " ∷
         "     ║     ├───────────                      " ∷
         "     ║     │ y                               " ∷
         "     ║     └───────────                      " ∷
         "     ║  (𝓲₁=0) →                             " ∷
         "     ║     𝒉𝒄𝒐𝒎𝒑 λ 𝒛₁                        " ∷
         "     ║     ║  (𝒛₀=1)(𝓲₀=1) → x               " ∷
         "     ║     ║  (𝒛₀=0)       → p 𝒛₁            " ∷
         "     ║     ║  (𝓲₀=0)       → p 𝒛₁            " ∷
         "     ║     ║                                 " ∷
         "     ║     ├───────────                      " ∷
         "     ║     │ x                               " ∷
         "     ║     └───────────                      " ∷
         "     ║  (𝓲₁=1) →                             " ∷
         "     ║     𝒉𝒄𝒐𝒎𝒑 λ 𝒛₁                        " ∷
         "     ║     ║  (𝒛₀=0)       → z               " ∷
         "     ║     ║  (𝓲₀=0)       → z               " ∷
         "     ║     ║  (𝒛₀=1)(𝓲₀=1) → r 𝒛₁            " ∷
         "     ║     ║                                 " ∷
         "     ║     ├───────────                      " ∷
         "     ║     │ z                               " ∷
         "     ║     └───────────                      " ∷
         "     ║                                       " ∷
         "     ├───────────                            " ∷
         "     │                                       " ∷
         "     │ 𝒉𝒄𝒐𝒎𝒑 λ 𝒛₀                            " ∷
         "     │ ║  (𝓲₁=0) → y                         " ∷
         "     │ ║  (𝓲₁=1) → q 𝒛₀                      " ∷
         "     │ ║                                     " ∷
         "     │ ├───────────                          " ∷
         "     │ │ y                                   " ∷
         "     │ └───────────                          " ∷
         "     └───────────                            " ∷ [])
 _ = unConnTest (suc (suc zero)) λ (i j : I) → doubleCompPath-filler p q r i j 


module _ (dim : ℕ) where
 macro
  unConnTest' : R.Term → R.Term → R.TC Unit
  unConnTest' t h = do
   cu ← (extractCuTerm nothing dim t)
   -- cu' ← unConn dim cu
   te0 ← ppCT dim 100 cu
   -- te0' ← ppCT dim 100 cu'
   wrapError h $
          "input:" ∷nl (indentₑ 4 te0)
     -- ++nl "\n∨,∧,~ - removed :" ∷nl (indentₑ 4 te0')


module _ {A : Type ℓ}
  {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
  {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
  (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
  (s : Square a₀₋ a₁₋ a₋₀ a₋₁) where



 s' : Square
        ((λ i → a₁₋ (~ i)) ∙' refl)
        ((λ i → a₀₋ (~ i)) ∙' refl)
        ((λ i → a₋₁ (~ i)) ∙' refl)
        ((λ i → a₋₀ (~ i)) ∙' refl)
 s' i j = reComp (λ i → reComp (λ j → s i j) (~ j)) (~ i)


 s'' : Square
        ((λ i → a₁₋ (~ i)) ∙' refl)
        ((λ i → a₀₋ (~ i)) ∙' refl)
        ((λ i → a₋₁ (~ i)) ∙' refl)
        ((λ i → a₋₀ (~ i)) ∙' refl)
 s'' i j = reComp (λ j → reComp (λ i → s i j) (~ i)) (~ j)


 interpI : I → I → I → I
 interpI z i₀ i₁ = ((~ z) ∧ i₀) ∨ (z ∧ i₁) ∨ (i₀ ∧ i₁) 

 s-rot : Cube
        s (λ i j → s j (~ i))
        _ _
        _ _
 s-rot z i j = s (interpI z i j) (interpI z j (~ i))

 s-rot-cc : ResultIs
              ("input:                                       " ∷
                "                                             " ∷
                "     𝒉𝒄𝒐𝒎𝒑 λ 𝒛₀                              " ∷
                "     ║  (𝓲₂=0)(𝓲₁=1) →                       " ∷
                "     ║     𝒉𝒄𝒐𝒎𝒑 λ 𝒛₁                        " ∷
                "     ║     ║  (𝓲₀=1) → a₀₀                   " ∷
                "     ║     ║  (𝓲₀=0) → a₀₋ 𝒛₁                " ∷
                "     ║     ║                                 " ∷
                "     ║     ├───────────                      " ∷
                "     ║     │ a₀₀                             " ∷
                "     ║     └───────────                      " ∷
                "     ║  (𝓲₁=1)(𝓲₀=1) →                       " ∷
                "     ║     𝒉𝒄𝒐𝒎𝒑 λ 𝒛₁                        " ∷
                "     ║     ║  (𝓲₂=0) → a₀₀                   " ∷
                "     ║     ║  (𝓲₂=1) → a₀₋ 𝒛₁                " ∷
                "     ║     ║                                 " ∷
                "     ║     ├───────────                      " ∷
                "     ║     │ a₀₀                             " ∷
                "     ║     └───────────                      " ∷
                "     ║  (𝓲₂=0)(𝓲₀=0) →                       " ∷
                "     ║     𝒉𝒄𝒐𝒎𝒑 λ 𝒛₁                        " ∷
                "     ║     ║  (𝓲₁=0) → a₀₀                   " ∷
                "     ║     ║  (𝓲₁=1) → a₀₋ 𝒛₁                " ∷
                "     ║     ║                                 " ∷
                "     ║     ├───────────                      " ∷
                "     ║     │ a₀₀                             " ∷
                "     ║     └───────────                      " ∷
                "     ║  (𝓲₂=1)(𝓲₁=0) →                       " ∷
                "     ║     𝒉𝒄𝒐𝒎𝒑 λ 𝒛₁                        " ∷
                "     ║     ║  (𝓲₀=0) → a₋₀ 𝒛₀                " ∷
                "     ║     ║  (𝓲₀=1) → s 𝒛₀ 𝒛₁               " ∷
                "     ║     ║                                 " ∷
                "     ║     ├───────────                      " ∷
                "     ║     │ a₋₀ 𝒛₀                          " ∷
                "     ║     └───────────                      " ∷
                "     ║  (𝓲₁=0)(𝓲₀=1) →                       " ∷
                "     ║     𝒉𝒄𝒐𝒎𝒑 λ 𝒛₁                        " ∷
                "     ║     ║  (𝓲₂=0) → a₋₀ 𝒛₀                " ∷
                "     ║     ║  (𝓲₂=1) → s 𝒛₀ 𝒛₁               " ∷
                "     ║     ║                                 " ∷
                "     ║     ├───────────                      " ∷
                "     ║     │ a₋₀ 𝒛₀                          " ∷
                "     ║     └───────────                      " ∷
                "     ║  (𝓲₂=1)(𝓲₀=0) →                       " ∷
                "     ║     𝒉𝒄𝒐𝒎𝒑 λ 𝒛₁                        " ∷
                "     ║     ║  (𝓲₁=0) → a₋₀ 𝒛₀                " ∷
                "     ║     ║  (𝓲₁=1) → s 𝒛₀ 𝒛₁               " ∷
                "     ║     ║                                 " ∷
                "     ║     ├───────────                      " ∷
                "     ║     │ a₋₀ 𝒛₀                          " ∷
                "     ║     └───────────                      " ∷
                "     ║                                       " ∷
                "     ├───────────                            " ∷
                "     │                                       " ∷
                "     │ 𝒉𝒄𝒐𝒎𝒑 λ 𝒛₀                            " ∷
                "     │ ║  (𝓲₂=0)(𝓲₁=0) → a₀₀                 " ∷
                "     │ ║  (𝓲₂=0)(𝓲₀=1) → a₀₀                 " ∷
                "     │ ║  (𝓲₁=0)(𝓲₀=0) → a₀₀                 " ∷
                "     │ ║  (𝓲₂=1)(𝓲₁=1) → a₀₋ 𝒛₀              " ∷
                "     │ ║  (𝓲₂=1)(𝓲₀=1) → a₀₋ 𝒛₀              " ∷
                "     │ ║  (𝓲₁=1)(𝓲₀=0) → a₀₋ 𝒛₀              " ∷
                "     │ ║                                     " ∷
                "     │ ├───────────                          " ∷
                "     │ │ a₀₀                                 " ∷
                "     │ └───────────                          " ∷
                "     └───────────                            " ∷ [])
 s-rot-cc = unConnTest' (suc (suc (suc zero))) λ (z i j : I) →
    
    reComp (λ i₀ → reComp (s i₀) (interpI z i j)) (interpI z j (~ i))

 

 s-rot' : Cube _ _ _ _ _ _
 s-rot' = unConnM (suc (suc (suc zero))) λ (z i j : I) →
            s-rot z i j


 s-rot≡ : Path (I → I → I → A) 
     (λ i j k → s-rot  i j k)
     (λ i j k → s-rot' i j k)
 s-rot≡ = 
    unConnM≡ (suc (suc (suc zero))) λ (z i j : I) →
            s-rot z i j
