{-# OPTIONS --safe #-} 

module Cubical.Tactics.PathSolver.Examples where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Relation.Nullary

-- open import Cubical.Algebra.Group.Free

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


open import Cubical.Tactics.PathSolver.CongComp
open import Cubical.Tactics.PathSolver.CuTerm

open import Cubical.Tactics.PathSolver.QuoteCubical
open import Cubical.Tactics.PathSolver.Dimensions
open import Cubical.Tactics.PathSolver.Coherence
-- open import Cubical.Tactics.PathSolver.Export

import Cubical.Tactics.PathSolver.ViaPrimPOr as ViaPrimPOr


private
  variable
    ℓ : Level


-- module E5 (A B C D : Type ℓ)
--   (e₀ : A ≃ B) (e₁ : B ≃ C) (e₂ : C ≃ D) where

--  e0 : ua e₀ ∙ ua e₁ ∙ ua e₂ ≡ ua e₀ ∙∙ ua e₁ ∙∙ ua e₂
--  e0 = solvePaths


module _ where

  private
   variable
     A B : Type ℓ
     x y z w v : A


  -- module T2'fext' {x y z : A} (f : A → A → B)
  --  (p : x ≡ y)
  --  (q : y ≡ z) where


  --  P Q : _≡_ {A = (A → B)} (λ x' → f x' x) (λ x' → f x' y)
  --  P = (λ i x' → f x' (p i)) ∙∙ (λ i x' → f x' (q i)) ∙∙ (λ i x' → f x' (q (~ i)))
  --  Q = refl ∙ (λ i x' → f x' (p i))


  --  -- P≡Q  : sym P ≡ sym Q 
  --  -- P≡Q = {!solvePaths!}

  -- module T1 {x : A} (p' p'' : x ≡ y) (xr xr' : x ≡ x) (q : y ≡ z) (~r : w ≡ z) (r' r : z ≡ w) (s : w ≡ v)
  --            (sq : Square xr (sym p'') p'' xr') where

  --  p : x ≡ y
  --  p i = sq i (~ i)

  --  P Q : x ≡ v -- ∙ (λ i → r (i ∧ ~ i))
  --  P = refl ∙ (p ∙' q ∙ sym (~r) ∙ ((λ i → ~r (i ∨ i))  ∙ (r ∙ s)))
  --  Q = p ∙ (q ∙ refl ∙ r ∙ s ∙ sym s) ∙ s


  --  P≡Q : sym P ≡ sym Q
  --  P≡Q = solvePaths




  -- module T2' {x : A} (p : x ≡ y) where


  --  P Q : x ≡ x 
  --  P = refl
  --  Q = λ i → p (i ∧ ~ i)


  --  P≡Q : sym P ≡ sym Q 
  --  P≡Q = solvePaths

  -- -- -- solvePaths




  -- module T2'I (p : I → A) where


  --  P Q : p i0 ≡ p i0 
  --  P = refl
  --  Q = λ i → p (i ∧ ~ i)


  --  P≡Q : sym P ≡ sym Q 
  --  P≡Q = solvePaths

  -- -- -- solvePaths




  -- module T2'fext {x y : A} (f g : {A} → A) (p : Path ({A} → A) (λ {x} → f {x}) (λ {x} → g {x})) (q : x ≡ y) where


  --  P Q : f {y}  ≡ f {y} 
  --  P = refl
  --  Q = (λ i → p i {q (~ i )}) ∙ (λ i → p (~ i) {q i})


  --  P≡Q : sym P ≡ sym Q 
  --  P≡Q = solvePaths


  -- module Tcong₂ {x : A} (f : A → A → B) (p : x ≡ y) where


  --  P Q : f x x ≡ f y y 
  --  P = cong (f x) p ∙ cong (flip f y) p
  --  Q = cong (flip f x) p ∙' cong (f y) p


  --  -- P≡Q : sym P ≡ sym Q 
  --  -- P≡Q = solvePaths


  -- module T2 {x : A} (p' p'' : x ≡ y) (xr xr' : x ≡ x) (q : y ≡ z) (~r : w ≡ z) (r' r : z ≡ w) (s : w ≡ v)
  --            (sq : Square xr (sym p'') p'' xr') where

  --  p : x ≡ y
  --  p i = sq i (~ i)

  --  P Q : x ≡ v 
  --  P = refl ∙ (p ∙' q ∙ sym (~r) ∙ (~r  ∙ (λ i → r (i ∧ ~ i)) ∙  (r ∙ ((λ i → r (i ∨  ~ i))) ∙  s )))
  --  Q = p ∙ (q ∙ refl ∙ refl ∙ r ∙ s ∙ sym s) ∙ s


  --  -- P≡Q : sym Q ≡ sym P
  --  -- P≡Q = solvePaths


  module PentaJ1Cong {x : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (s : w ≡ v) (f : A → B) where


   -- LHS RHS : (λ i → f (p i)) ∙ (λ i → f (q i)) ∙ (λ i → f (r i)) ≡ λ i → f (((p ∙ q) ∙ r) i)
   -- LHS = solvePathsC ∙ congP (λ _ → cong f) (assoc p q r) 

   -- RHS = assoc (cong f p) (cong f q) (cong f r) ∙ solvePathsC

   -- -- LHS≡RHS : LHS ≡ RHS
   -- -- LHS≡RHS = solvePathsC



   pLHS = assoc p q (r ∙ s) ∙ assoc (p ∙ q) r s
   rLHS = cong (p ∙_) (assoc q r s) ∙∙ assoc p (q ∙ r) s ∙∙ cong (_∙ s) (assoc p q r)

   pentagonTy = pLHS ≡ rLHS
   pentagonTy' = Square pLHS (assoc p (q ∙ r) s)
                (cong (p ∙_) (assoc q r s))
                 (sym (cong (_∙ s) (assoc p q r)))


   -- _ : p ∙ sym p ≡ refl
   -- _ = solvePaths 

   _ : pentagonTy'
   _ = solvePaths'' 

   pentagonIdentity' : pentagonTy
   pentagonIdentity' = solvePaths''

   -- pppiii : I → I → I → A
   -- pppiii = {!!}


   -- pentagonIdentity'≡pentagonIdentity : pentagonIdentity' ≡ pentagonIdentity p q r s
   -- pentagonIdentity'≡pentagonIdentity = solvePaths'


--   module PentaJJ1 {x : A} (p : x ≡ y) (q : y ≡ z) (~r : w ≡ z) (r' r : z ≡ w) (s : w ≡ v) where

--    P Q : x ≡ v
--    P = refl ∙ (p ∙' q ∙ sym (~r) ∙ (~r ∙ (r ∙ s)))
--    Q = p ∙ (q ∙ refl ∙ r ∙ s ∙ sym s) ∙ s


--    P≡Q : sym P ≡ sym Q
--    P≡Q = solvePaths



--    module _ (f : A → B) where



--     P' = refl ∙ cong f (p ∙' q ∙ sym (~r) ∙ (~r ∙ (r ∙ s)))
--     Q' = cong f p ∙ (cong f (q ∙ refl) ∙ cong f (r ∙∙ s ∙∙ sym s)) ∙ cong f s

--     _ : cong f (p ∙ sym p) ≡ cong f p ∙ cong f (sym p)
--     _ = solvePathsC


--     _ : cong f (p ∙ sym p ∙ p ∙ q) ≡ cong f p ∙ cong f q
--     _ = solvePathsC

--     _ : P' ≡ Q'
--     _ = solvePathsC


--    P'' Q'' : y ≡ z
--    P'' = (q ∙∙ sym (~r) ∙∙ (~r))
--    Q'' =  q


--    P''≡Q'' : P'' ≡ Q''
--    P''≡Q'' = solvePaths


-- module E3 {ℓ} where

--  data D : Type ℓ where
--   x y z w : D
--   p : x ≡ y
--   q : y ≡ z
--   r : z ≡ w
--   f : D → D
--   f₂ : D → D → D
--   f₄ : D → D → D → D → D
 
--  -- e0' : (((p ∙∙ q ∙∙ sym q ) ∙∙ q  ∙∙ r)) ≡ (p ∙' (q ∙' r))
--  -- e0' = solvePaths''

--  -- e1 : 
--  --        (invSides-filler p p) ≡ (λ i j → (invSides-filler (sym p) (sym p)) j (~ i))
      
--  -- e1 = solvePaths''

--  e1 : Cube {a₀₀₀ = x}
--          (invSides-filler refl refl) (invSides-filler refl refl)
--          (invSides-filler refl refl) (invSides-filler refl refl)
--          (invSides-filler refl refl) (invSides-filler refl refl)
--  e1 = solvePaths''


module _ {ℓ} {A : Type ℓ} {x y z w : A} (p : x ≡ y) (q : y ≡ z)(r : z ≡ w) where
 assocDed :  (p ∙ q) ∙ r ≡ p ∙ q ∙ r
 assocDed = λ i j → hcomp (λ k → λ {
      (i = i1) → hfill (λ l → λ {
        (j = i0) → p i0
      ; (j = i1) → hcomp (λ m → λ {
          (l = i0) → p i1
        ; (l = i1) → r m
        }) (q l)
      }) (inS (p j)) k
    ; (j = i0) → p i0
    ; (j = i1) → hcomp (λ l → λ {
        (i = i1) → hfill (λ m → λ {
          (k = i0) → p i1
        ; (k = i1) → r m
        }) (inS (q k)) l
      ; (k = i0) → p i1
      ; (k = i1) → r l
      ; (i = i0) → hfill (λ m → λ {
          (k = i0) → p i1
        ; (k = i1) → r m
        }) (inS (q k)) l
      }) (q k)
    ; (i = i0) → hcomp (λ l → λ {
        (j = i0) → p i0
      ; (j = i1) → hfill (λ m → λ {
          (k = i0) → p i1
        ; (k = i1) → r m
        }) (inS (q k)) l
      ; (k = i0) → p j
      ; (k = i1) → hfill (λ m → λ {
          (j = i0) → p i0
        ; (j = i1) → r m
        }) (inS (hcomp (λ m → λ {
          (j = i0) → p i0
        ; (j = i1) → q m
        }) (p j))) l
      }) (hfill (λ l → λ {
        (j = i0) → p i0
      ; (j = i1) → q l
      }) (inS (p j)) k)
    }) (p j)

 dedSq : sym (assocDed) ≡ assoc p q r
 dedSq = solvePaths''
