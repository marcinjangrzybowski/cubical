{-# OPTIONS --safe -v 3 #-} 
module Cubical.Tactics.PathSolver.Tests.QuoteCubical where

import Agda.Builtin.Reflection as R

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Data.List as L

open import Cubical.Reflection.Base hiding (v)


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Tactics.Reflection 
open import Cubical.Tactics.Reflection.Utilities


open import Cubical.Tactics.PathSolver.Dimensions
open import Cubical.Tactics.PathSolver.QuoteCubical
open import Cubical.Tactics.PathSolver.CuTerm
open import Cubical.Tactics.PathSolver.Error



macro
 extractIExprTest : R.Term → R.Term → R.TC Unit 
 extractIExprTest t h = do
   t' ← extractIExprM t 
   R.unify t (IExpr→Term t')
   R.unify R.unknown h

 normIExprTest : R.Term → R.Term → R.TC Unit 
 normIExprTest t h = do
   t' ← R.normalise t >>= extractIExprM 
   R.unify t (IExpr→Term t')
   R.unify t (IExpr→Term (normIExpr t'))
   wrapError h ("t    : " ∷ₑ IExpr→Term t' ∷nl
                 "norm : " ∷ₑ (IExpr→Term (normIExpr t')) ∷ₑ [])

   
   -- R.unify R.unknown h

 -- degenTest : R.Term → R.Term → R.TC Unit 
 -- degenTest t h = do
 --   t' ← extractIExprM t
 --   let dim = (suc (getMaxVar t'))
 --   let i' = undegen dim t'
 --   -- let ii = undegen' dim t'
 --   -- addNDimsToCtx (suc dim) $ R.typeError [ IExpr→Term $ i' ]ₑ
 --   -- addNDimsToCtx dim $ R.typeError $ L.join $ L.map (λ (sf , ie , b , bb) →
 --   --        sf ∷ₑ " → " ∷ₑ IExpr→Term ie ∷ₑ " " ∷ₑ b ∷ₑ "/" ∷ₑ  bb ∷nl []) ii 
 --   R.unify (IExpr→Term $ i') h
   
_ : Unit
_ = extractIExprTest i0

_ : Unit
_ = extractIExprTest i1



module _ (i j k l : I) where
 _ : Unit
 _ = extractIExprTest (~ (j ∧ i ∧ ~ j) ∨ k ∨ (i ∧ ~ i) ∨ (l ∧ i))


 _ : Unit
 _ = extractIExprTest (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k)

 _ : Unit
 _ = extractIExprTest (~ (i ∨ ~ i ∨ j ∨ ~ j ∨ k ∨ ~ k))

 _ : ResultIs
        ("t    : i ∨ i ∨ (i ∧ i ∧ j) ∨ i ∧ i ∧ k       " ∷
         "norm : i                                     " ∷ [])
 _ = normIExprTest (i ∨ i ∨ (i ∧ i ∧ (j ∨ k)))

 _ : ResultIs
        ("t    : (i ∧ k) ∨ j ∧ k                       " ∷
         "norm : (j ∧ k) ∨ i ∧ k                       " ∷ [])
 _ = normIExprTest ((i ∧ k) ∨ (j ∧ k))


--  -- _ : Unit
--  -- _ = {!degenTest (k ∧ l ∧ ~ l)!}




-- module _ (f : ℕ → I) (i j k l : ℕ) where

--  _ : Unit
--  _ = extractIExprTest (~ (f j ∧ f i ∧ ~ f j) ∨ (f k) ∨ (f i ∧ ~ f i) ∨ (f l ∧ f i))


-- module _ (A : Type) (a : ℕ → A) (p : ∀ k k' → a k ≡ a k') (P : I → A) where 


--  xx : Path (I → I → A) (λ 𝓲₁ 𝓲₀ → P (𝓲₁ ∧ 𝓲₀ ∧ ~ 𝓲₀)) λ _ _ → P i0
--  xx 𝓲₂ 𝓲₁ 𝓲₀ = P (degenTest (𝓲₁ ∧ 𝓲₀ ∧ ~ 𝓲₀))

macro
 extractCuPathTermTest : R.Term → R.Term → R.TC Unit
 extractCuPathTermTest t h = do
  cu ← (extractCuTermFromPath nothing t)
  te ← ppCT 1 100 cu
  R.typeError te


module _ (dim : ℕ) where
 macro
  extractCuTermTest : R.Term → R.Term → R.TC Unit
  extractCuTermTest t h = do
   cu ← (extractCuTerm nothing dim t)
   te ← ppCT dim 100 cu
   R.typeError te


  getCuTerm : R.Term → R.Term → R.TC Unit
  getCuTerm t hole = do
   cu ← (extractCuTerm nothing dim t)
   R.unify (toTerm dim cu) hole

module E5 (A B C D : Type)
  (e₀ : A ≃ B) (e₁ : B ≃ C) (e₂ : C ≃ D) where


 _ : (ua e₀ ∙∙ ua e₁ ∙∙ ua e₂) ≡
                   getCuTerm (suc zero)
                     (λ (i : I) → (ua e₀ ∙∙ ua e₁ ∙∙ ua e₂) i)
 _ = refl

 -- _ : Unit
 -- _ = extractCuPathTermTest (ua e₀ ∙∙ ua e₁ ∙∙ ua e₂)

private
  variable
    ℓ : Level
    A : Type ℓ
    x y z w v : A

module _  {x : A}
           {B C : Type ℓ}
           (f f' : A → B)
         (g : B → B → C)
         (p p' : Path A x y) (q q' : y ≡ z)   (r : z ≡ w) where



 -- _ : Unit
 -- _ = {!printCu (cong-∙ f p q)!}


 
 -- _ : Unit
 -- _ = {!printCu zz!}
 --  where
 --    zz : _
 --    zz = (cong₂ g (cong f (p ∙' q)) (cong f' (p' ∙ q')))


 -- _ : Unit
 -- _ = extractCuPathTermTest (cong₂ g (cong f (p ∙' q)) (cong f' (p' ∙ q')))

 _ : cong-∙ f p q ≡
                   getCuTerm (suc (suc zero))
                     (λ (i j : I) → cong-∙ f p q i j)
 _ = refl


 _ : (cong₂ g (cong f (p ∙' q)) (cong f' (p' ∙ q')))
                 ≡ (getCuTerm (suc zero)
                     (λ (i : I) → cong₂ g (cong f (p ∙' q)) (cong f' (p' ∙ q')) i))
 _ = refl


module _ {x : A}  (p : x ≡ y) (q : y ≡ z)  (r : z ≡ w) (s : w ≡ v)  where


 _ : (pentagonIdentity p q r s)
                 ≡ 
                   (getCuTerm (suc (suc (suc zero)))
                     (λ (i j k : I) → pentagonIdentity p q r s i j k))
 _ = refl


 -- _ : Unit
 -- _ = {!extractCuTermTest (suc (suc (suc zero)))
 --          (λ (i j k : I) → pentagonIdentity p q r s i j k)!}
  








module NCubeTermTest where

 macro
  showCuFaces : R.Term → R.TC Unit
  showCuFaces h = do
    hTy ← R.inferType h >>= wait-for-term >>= R.normalise
    R.debugPrint "tactic" 3 $ [ hTy ]ₑ
    (A , fcs) ← matchNCube hTy -->>= nCubeToEq
    
    addNDimsToCtx (length fcs) $ R.debugPrint "tactic" 3 $
      "ok " ∷ₑ length fcs ∷ₑ " : \n\n:" ∷ₑ [ A ]ₑ

    addNDimsToCtx (length fcs ∸ 1) $ R.debugPrint "tactic" 3 $
      -- "ok : \n\n:" ∷ₑ A  ∷nl
      join ( L.map (λ (k , (f0 , f1)) →
             k ∷nl "i0 : \n" ∷ₑ f0  ∷nl
                "i1 : \n" ∷ₑ f1  ∷nl []
         ) $ zipWithIndex fcs)
    R.typeError [ "ok" ]ₑ

  getTermNCube : R.Term → R.Term → R.TC Unit
  getTermNCube tm h = do
    hTy ← R.normalise tm

    hTy' ← unquoteNCube <$> matchNCube hTy
    R.unify hTy' h

  getFlattenedTermNCube : R.Term → R.Term → R.TC Unit
  getFlattenedTermNCube tm h = do
    hTy ← R.normalise tm

    hTy' ← unquoteNCube <$> (matchNCube hTy >>= nCubeToEq)
    R.unify hTy' h

  getFlattenedTermNCubePath : R.Term → R.Term → R.TC Unit
  getFlattenedTermNCubePath tm h = do
    hTy ← R.normalise tm

    hTy' ← (nCubeToEqPath <$> matchNCube hTy)
    R.unify hTy' h



 module T2'fext' (A B : Type) {x y z : A} (f : A → A → B)
  (p : _≡_ {A = (A → B)} (λ x' → f x' x) (λ x' → f x' y))
  (q : _≡_ {A = (A → B)} (λ x' → f x' y) (λ x' → f x' z)) where

  X : Type 
  X = _≡_ {A = (A → B)} (λ x' → f x' x) (λ x' → f x' y) 

  P Q : X
  P = p ∙∙ q ∙∙ sym q
  Q = refl ∙ p

  -- _ : P ≡ Q -- _≡_ {A = (A → B)} (flip f x) (flip f y) 
  -- _ = {!showCuFaces!}
