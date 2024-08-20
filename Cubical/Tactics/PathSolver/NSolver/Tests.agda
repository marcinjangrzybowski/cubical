{-# OPTIONS --safe #-} 

module Cubical.Tactics.PathSolver.NSolver.Tests where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

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


open import Cubical.Tactics.PathSolver.CongComp
open import Cubical.Tactics.Reflection.CuTerm

open import Cubical.Tactics.Reflection.QuoteCubical
open import Cubical.Tactics.Reflection.Dimensions
open import Cubical.Tactics.PathSolver.NSolver.NSolver
open import Cubical.Tactics.PathSolver.Path




private
 variable
   ℓ : Level
   A B : Type ℓ


module ReflTests (a' a : A) where

 _ : refl {x = a} ∙ refl ≡ refl
 _ = solvePaths

 -- _ : refl {x = a} ∙ refl ≡ refl
 -- _ = solvePaths


 zz : Cube
        refl (assoc (refl {x = a}) refl refl)
        (cong (refl ∙_) (lUnit refl)) (cong (_∙ refl) (rUnit refl))
        refl refl
 zz = solvePaths


 p00 : refl {x = a} ∙ refl ∙ refl ∙ refl ≡ ((refl ∙ refl) ∙ refl) ∙ refl 
 p00 = solvePaths



 penta-refl :    assoc (refl {x = a}) refl (refl ∙ refl) ∙ assoc (refl ∙ refl) refl refl
                          ≡
        cong (refl ∙_) (assoc refl refl refl) ∙∙ assoc refl (refl ∙ refl)
          refl ∙∙ cong (_∙ refl) (assoc refl refl refl)
 penta-refl = solvePaths


 -- zzz : Square _ _ _ _
 -- zzz i j = hcomp (λ z → λ { (i = i0) →
 --                    hcomp (λ z' → λ { (z = i0) → a ; (j = i0) → a ; (j = i1)(z = i1) → a })
 --                          a
 --              ; (j = i0) → a ; (j = i1)(i = i1) → a })
 --              a

 -- zzzz : zzz ≡ zzz
 -- zzzz = solvePaths

 -- zzzzz : zzzz ≡ zzzz
 -- zzzzz = solvePaths

 _ : penta-refl ≡ pentagonIdentity refl refl refl refl 
 _ = solvePaths




-- -- -- {!solvePaths!}

-- -- -- module Coherence (SA : NPath 7 A) where
-- -- --   open NPath SA 



 


--    -- pLHS = assoc p q (r ∙ s) ∙ assoc (p ∙ q) r s
--    -- rLHS = cong (p ∙_) (assoc q r s) ∙∙ assoc p (q ∙ r) s ∙∙ cong (_∙ s) (assoc p q r)


-- -- -- -- -- -- -- module E5 (A B C D : Type ℓ)
-- -- -- -- -- -- --   (e₀ : A ≃ B) (e₁ : B ≃ C) (e₂ : C ≃ D) where

-- -- -- -- -- -- --  e0 : Square (ua e₀ ∙ ua e₁) (ua e₀ ∙∙ ua e₁ ∙∙ ua e₂) refl (ua e₂)
-- -- -- -- -- -- --  e0 = solvePaths

-- -- -- -- -- -- --  -- e0L : Square (cong List (ua e₀) ∙ cong List (ua e₁))
-- -- -- -- -- -- --  --              (cong List (ua e₀ ∙∙ ua e₁ ∙∙ ua e₂))
-- -- -- -- -- -- --  --              refl (cong List (ua e₂))
-- -- -- -- -- -- --  -- e0L = solvePaths


-- -- -- -- -- -- -- module _ where

-- -- -- -- -- -- --   private
-- -- -- -- -- -- --    variable
-- -- -- -- -- -- --      A B : Type ℓ
-- -- -- -- -- -- --      x y z w v : A


-- -- -- -- -- -- --   module T2'fext' {x y z : A} (f : A → A → B)
-- -- -- -- -- -- --    (p : x ≡ y)
-- -- -- -- -- -- --    (q : y ≡ z) where


-- -- -- -- -- -- --    P Q : _≡_ {A = (A → B)} (λ x' → f x' x) (λ x' → f x' y)
-- -- -- -- -- -- --    P = (λ i x' → f x' (p i)) ∙∙ (λ i x' → f x' (q i)) ∙∙ (λ i x' → f x' (q (~ i)))
-- -- -- -- -- -- --    Q = refl ∙ (λ i x' → f x' (p i))



-- -- -- -- -- -- --   module PentaJJ1 {x : A} (p : x ≡ y) (q : y ≡ z) (~r : w ≡ z) (r' r : z ≡ w) (s : w ≡ v) where

-- -- -- -- -- -- --    module _ (f : A → B) where



-- -- -- -- -- -- --     P' = refl ∙ cong f (p ∙' q ∙ sym (~r) ∙ (~r ∙ (r ∙ s)))
-- -- -- -- -- -- --     Q' = cong f p ∙ (cong f (q ∙ refl) ∙ cong f (r ∙∙ s ∙∙ sym s)) ∙ cong f s

-- -- -- -- -- -- --     _ : cong f (p ∙ sym p) ≡ cong f p ∙ cong f (sym p)
-- -- -- -- -- -- --     _ = solvePaths

-- -- -- -- -- -- --   module compPathR-PathP∙∙ 
-- -- -- -- -- -- --           {p : x ≡ y} 
-- -- -- -- -- -- --       where

-- -- -- -- -- -- --    invSides-filler-rot' : (invSides-filler p p) ≡ (symP (invSides-filler (sym p) (sym p)))
         
-- -- -- -- -- -- --    invSides-filler-rot' = solvePaths

-- -- -- -- -- -- --    _ : invSides-filler-rot p ≡ invSides-filler-rot'
-- -- -- -- -- -- --    _ = solvePaths



-- -- -- -- -- -- --    P Q : x ≡ x 
-- -- -- -- -- -- --    P = refl
-- -- -- -- -- -- --    Q = λ i → p (i ∧ ~ i)


-- -- -- -- -- -- --    P≡Q : sym P ≡ sym Q 
-- -- -- -- -- -- --    P≡Q = solvePaths

-- -- -- -- -- -- --   module T2'I (p : I → A) where


-- -- -- -- -- -- --    P Q : p i0 ≡ p i0 
-- -- -- -- -- -- --    P = refl
-- -- -- -- -- -- --    Q = λ i → p (i ∧ ~ i)


-- -- -- -- -- -- --    P≡Q : sym P ≡ sym Q 
-- -- -- -- -- -- --    P≡Q = solvePaths




-- -- -- -- -- -- --   module T2'fext {x y : A} (f g : {A} → A) (p : Path ({A} → A) (λ {x} → f {x}) (λ {x} → g {x})) (q : x ≡ y) where


-- -- -- -- -- -- --    P Q : f {y}  ≡ f {y} 
-- -- -- -- -- -- --    P = refl
-- -- -- -- -- -- --    Q = (λ i → p i {q (~ i )}) ∙ (λ i → p (~ i) {q i})


-- -- -- -- -- -- --    P≡Q : sym P ≡ sym Q 
-- -- -- -- -- -- --    P≡Q = solvePaths


-- -- -- -- -- -- --   module T2 {x : A} (p' p'' : x ≡ y) (xr xr' : x ≡ x) (q : y ≡ z) (~r : w ≡ z) (r' r : z ≡ w) (s : w ≡ v)
-- -- -- -- -- -- --              (sq : Square xr (sym p'') p'' xr') where

-- -- -- -- -- -- --    p : x ≡ y
-- -- -- -- -- -- --    p i = sq i (~ i)

-- -- -- -- -- -- --    P Q : x ≡ v 
-- -- -- -- -- -- --    P = refl ∙ (p ∙' q ∙ sym (~r) ∙ (~r  ∙ (λ i → r (i ∧ ~ i)) ∙  (r ∙ ((λ i → r (i ∨  ~ i))) ∙  s )))
-- -- -- -- -- -- --    Q = p ∙ (q ∙ refl ∙ refl ∙ r ∙ s ∙ sym s) ∙ s


-- -- -- -- -- -- --    -- P≡Q : sym Q ≡ sym P
-- -- -- -- -- -- --    -- P≡Q = solvePaths


-- -- -- -- -- -- --   module PentaJ1Cong {x : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) (s : w ≡ v) (f : A → B) where


-- -- -- -- -- -- --    LHS RHS : (λ i → f (p i)) ∙ (λ i → f (q i)) ∙ (λ i → f (r i)) ≡ λ i → f (((p ∙ q) ∙ r) i)
-- -- -- -- -- -- --    LHS = solvePaths ∙ congP (λ _ → cong f) (assoc p q r) 

-- -- -- -- -- -- --    RHS = assoc (cong f p) (cong f q) (cong f r) ∙ solvePaths

-- -- -- -- -- -- --    LHS≡RHS : LHS ≡ RHS
-- -- -- -- -- -- --    LHS≡RHS = solvePaths



-- -- -- -- -- -- --    pLHS = assoc p q (r ∙ s) ∙ assoc (p ∙ q) r s
-- -- -- -- -- -- --    rLHS = cong (p ∙_) (assoc q r s) ∙∙ assoc p (q ∙ r) s ∙∙ cong (_∙ s) (assoc p q r)

-- -- -- -- -- -- --    pentagonTy = pLHS ≡ rLHS
-- -- -- -- -- -- --    pentagonTy' = Square pLHS (assoc p (q ∙ r) s)
-- -- -- -- -- -- --                 (cong (p ∙_) (assoc q r s))
-- -- -- -- -- -- --                  (sym (cong (_∙ s) (assoc p q r)))


-- -- -- -- -- -- --    _ : pentagonTy'
-- -- -- -- -- -- --    _ = solvePaths 

-- -- -- -- -- -- --    pentagonIdentity' : pentagonTy
-- -- -- -- -- -- --    pentagonIdentity' = solvePaths

-- -- -- -- -- -- --    -- this 4-cubes works, but takes lots of time, good oportunity to experiment with performance
-- -- -- -- -- -- --    -- pentagonIdentity'≡pentagonIdentity : pentagonIdentity' ≡ pentagonIdentity p q r s
-- -- -- -- -- -- --    -- pentagonIdentity'≡pentagonIdentity = solvePaths'


-- -- -- -- -- -- --   module PentaJJ1' {x : A} (p : x ≡ y) (q : y ≡ z) (~r : w ≡ z) (r' r : z ≡ w) (s : w ≡ v) where

-- -- -- -- -- -- --    P Q : x ≡ v
-- -- -- -- -- -- --    P = refl ∙ (p ∙' q ∙ sym (~r) ∙ (~r ∙ (r ∙ s)))
-- -- -- -- -- -- --    Q = p ∙ (q ∙ refl ∙ r ∙ s ∙ sym s) ∙ s


-- -- -- -- -- -- --    P≡Q : sym P ≡ sym Q
-- -- -- -- -- -- --    P≡Q = solvePaths



-- -- -- -- -- -- --    module _ (f : A → B) where



-- -- -- -- -- -- --     P' = refl ∙ cong f (p ∙' q ∙ sym (~r) ∙ (~r ∙ (r ∙ s)))
-- -- -- -- -- -- --     Q' = cong f p ∙ (cong f (q ∙ refl) ∙ cong f (r ∙∙ s ∙∙ sym s)) ∙ cong f s

-- -- -- -- -- -- --     _ : cong f (p ∙ sym p) ≡ cong f p ∙ cong f (sym p)
-- -- -- -- -- -- --     _ = solvePaths


-- -- -- -- -- -- --     _ : cong f (p ∙ sym p ∙ p ∙ q) ≡ cong f p ∙ cong f q
-- -- -- -- -- -- --     _ = solvePaths

-- -- -- -- -- -- --     _ : P' ≡ Q'
-- -- -- -- -- -- --     _ = solvePaths


-- -- -- -- -- -- --    P'' Q'' : y ≡ z
-- -- -- -- -- -- --    P'' = (q ∙∙ sym (~r) ∙∙ (~r))
-- -- -- -- -- -- --    Q'' =  q


-- -- -- -- -- -- --    P''≡Q'' : P'' ≡ Q''
-- -- -- -- -- -- --    P''≡Q'' = solvePaths


-- -- -- -- -- -- -- module E3 {ℓ} where

-- -- -- -- -- -- --  data D : Type ℓ where
-- -- -- -- -- -- --   x y z w : D
-- -- -- -- -- -- --   p : x ≡ y
-- -- -- -- -- -- --   q : y ≡ z
-- -- -- -- -- -- --   r : z ≡ w
-- -- -- -- -- -- --   f : D → D
-- -- -- -- -- -- --   f₂ : D → D → D
-- -- -- -- -- -- --   f₄ : D → D → D → D → D
 

-- -- -- -- -- -- --  e1 : Cube {a₀₀₀ = x}
-- -- -- -- -- -- --          (invSides-filler refl refl) (invSides-filler refl refl)
-- -- -- -- -- -- --          (invSides-filler refl refl) (invSides-filler refl refl)
-- -- -- -- -- -- --          (invSides-filler refl refl) (invSides-filler refl refl)
-- -- -- -- -- -- --  e1 = solvePaths

