{-# OPTIONS --safe #-}
module Cubical.Tactics.Reflection.Utilities where

open import Cubical.Foundations.Prelude hiding (Type)
open import Cubical.Foundations.Function

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_ ; _<_ to _<ℕ_)

open import Cubical.Reflection.Base
open import Cubical.Data.List
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Bool
open import Cubical.Data.FinData using () renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; suc; _+_; zero; _∸_)

open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Variables


finiteNumberAsTerm : Maybe ℕ → Term
finiteNumberAsTerm (just ℕ.zero) = con (quote fzero) []
finiteNumberAsTerm (just (ℕ.suc n)) = con (quote fsuc) (finiteNumberAsTerm (just n) v∷ [])
finiteNumberAsTerm _ = unknown

-- error message helper
errorOut : List (Arg Term) → TC (Template × Vars)
errorOut something = typeError (strErr "Don't know what to do with " ∷ map (λ {(arg _ t) → termErr t}) something)

errorOut' : Term → TC (Template × Vars)
errorOut' something = typeError (strErr "Don't know what to do with " ∷ termErr something ∷ [])


_==_ = primQNameEquality
{-# INLINE _==_ #-}


module replaceVarWithVar where
 ra : ℕ → ℕ → List (Arg Term) → List (Arg Term)
 rc : ℕ → ℕ → List Clause → List Clause
 rcl : ℕ → ℕ → Clause → Clause
 rtl : ℕ → ℕ → Telescope → Telescope
 rv : ℕ → ℕ →  Term → Term

 ra n n' [] = []
 ra n n' (arg i x ∷ x₂) = 
   arg i (rv n n' x) ∷ ra n n' x₂
 rv n n' (var x args) = var (if (x =ℕ n) then n' else x) (ra n n' args)
 rv n n' (con c args) = con c (ra n n' args)
 rv n n' (def f args) = def f (ra n n' args)
 rv n n' (lam v₁ (abs s x)) =
   lam v₁ (abs s (rv (suc n) (suc n') x))
 rv n n' (pat-lam cs args) = pat-lam (rc n n' cs) (ra n n' args)
 rv n n' (pi (arg i x) (abs s x₁)) =
  (pi (arg i (rv n n' x)) (abs s (rv (suc n) (suc n') x₁)))
 rv n n' (agda-sort s) = agda-sort s
 rv n n' (lit l) = lit l
 rv n n' (meta x x₁) = meta x (ra n n' x₁)
 rv n n' unknown = unknown

 rcl n n' (clause tel ps t) =
   clause (rtl n n' tel) ps (rv (length tel + n) (length tel + n') t)
 rcl n n' (absurd-clause tel ps) =
   absurd-clause (rtl n n' tel) ps

 rtl n n' [] = []
 rtl n n' ((v , arg i x) ∷ xs) =
    ((v , arg i (rv n n' x))) ∷ rtl (suc n) (suc n') xs

 rc n n' [] = []
 rc n n' (cl ∷ cls) =
   rcl n n' cl ∷ rc n n' cls

module replaceVarWithCon (cn : ℕ → (Maybe Name)) where
 -- only for not applied vars!!

 ra : ℕ → List (Arg Term) → List (Arg Term)
 rc : ℕ → List Clause → List Clause
 rcl : ℕ → Clause → Clause
 rtl : ℕ → Telescope → Telescope
 rv : ℕ →  Term → Term

 ra n [] = []
 ra n (arg i x ∷ x₂) = 
   arg i (rv n x) ∷ ra n x₂
 rv n (var x []) =
   if (x <ℕ n) then (var x [])
    else (Mb.rec (var x []) (λ nm → con nm []) (cn (x ∸ n)))
 rv n (var x args) = var x (ra n args)
 rv n (con c args) = con c (ra n args)
 rv n (def f args) = def f (ra n args)
 rv n (lam v₁ (abs s x)) =
   lam v₁ (abs s (rv (suc n) x))
 rv n (pat-lam cs args) = pat-lam (rc n cs) (ra n args)
 rv n (pi (arg i x) (abs s x₁)) =
  (pi (arg i (rv n x)) (abs s (rv (suc n) x₁)))
 rv n (agda-sort s) = agda-sort s
 rv n (lit l) = lit l
 rv n (meta x x₁) = meta x (ra n x₁)
 rv n unknown = unknown

 rcl n (clause tel ps t) =
   clause (rtl n tel) ps (rv (length tel + n) t)
 rcl n (absurd-clause tel ps) =
   absurd-clause (rtl n tel) ps

 rtl n [] = []
 rtl n ((v , arg i x) ∷ xs) =
    ((v , arg i (rv n x))) ∷ rtl (suc n) xs

 rc n [] = []
 rc n (cl ∷ cls) =
   rcl n cl ∷ rc n cls

replaceVarWithCon = flip replaceVarWithCon.rv zero

module liftVars (k : ℕ) where

 ra : ℕ → List (Arg Term) → List (Arg Term)
 rc : ℕ → List Clause → List Clause
 rcl : ℕ → Clause → Clause
 rpt : ℕ → Pattern → Pattern
 rpts : ℕ → List (Arg Pattern) → List (Arg Pattern)
 rtl : ℕ → Telescope → Telescope
 rv : ℕ →  Term → Term
 rs : ℕ →  Sort → Sort


 ra n [] = []
 ra n (arg i x ∷ x₂) = 
   arg i (rv n x) ∷ ra n x₂
 rv n (var x args) =
  var ( if (x <ℕ n) then x else (k + x))  (ra n args)
 rv n (con c args) = con c (ra n args)
 rv n (def f args) = def f (ra n args)
 rv n (lam v₁ (abs s x)) =
   lam v₁ (abs s (rv (suc n) x))
 rv n (pat-lam cs args) = pat-lam (rc n cs) (ra n args)
 rv n (pi (arg i x) (abs s x₁)) =
  (pi (arg i (rv n x)) (abs s (rv (suc n) x₁)))
 rv n (agda-sort s) = agda-sort (rs n s)
 rv n (lit l) = lit l
 rv n (meta x x₁) = meta x (ra n x₁)
 rv n unknown = unknown

 rs n (set t) = set (rv n t)
 rs n (lit n₁) = lit n₁
 rs n (prop t) = prop (rv n t)
 rs n (propLit n₁) = propLit n₁
 rs n (inf n₁) = inf n₁
 rs n unknown = unknown

 rcl n (clause tel ps t) =
   clause (rtl n tel) (rpts n ps) (rv (length tel + n) t)
 rcl n (absurd-clause tel ps) =
   absurd-clause (rtl n tel) (rpts n ps)

 rtl n [] = []
 rtl n ((v , arg i x) ∷ xs) =
    ((v , arg i (rv n x))) ∷ rtl (suc n) xs

 rc n [] = []
 rc n (cl ∷ cls) =
   rcl n cl ∷ rc n cls
 -- rc n (cl@(clause _ _ _) ∷ cls) =
 --   rcl n cl ∷ rc n cls
 -- rc n (_ ∷ cls) =
 --   rc n cls
 rpt n (con c ps) = con c (rpts n ps)
 rpt n (dot t) = dot (rv n t)
 rpt n (var x) = var x
 rpt n (lit l) = lit l
 rpt n (proj f) = proj f
 rpt n (absurd x) = absurd x
 -- rpt n x = x

 rpts n [] = []
 rpts n ((arg i x) ∷ xs) = arg i (rpt n x) ∷ rpts n xs

liftVars = liftVars.rv 1 0


module dropVars (k : ℕ) where

 ra : ℕ → List (Arg Term) → List (Arg Term)
 rc : ℕ → List Clause → List Clause
 rcl : ℕ → Clause → Clause
 rpt : ℕ → Pattern → Pattern
 rpts : ℕ → List (Arg Pattern) → List (Arg Pattern)
 rtl : ℕ → Telescope → Telescope
 rv : ℕ →  Term → Term
 rs : ℕ →  Sort → Sort


 ra n [] = []
 ra n (arg i x ∷ x₂) = 
   arg i (rv n x) ∷ ra n x₂
 rv n (var x args) =
  var ( if (x <ℕ n) then x else (x ∸ k))  (ra n args)
 rv n (con c args) = con c (ra n args)
 rv n (def f args) = def f (ra n args)
 rv n (lam v₁ (abs s x)) =
   lam v₁ (abs s (rv (suc n) x))
 rv n (pat-lam cs args) = pat-lam (rc n cs) (ra n args)
 rv n (pi (arg i x) (abs s x₁)) =
  (pi (arg i (rv n x)) (abs s (rv (suc n) x₁)))
 rv n (agda-sort s) = agda-sort (rs n s)
 rv n (lit l) = lit l
 rv n (meta x x₁) = meta x (ra n x₁)
 rv n unknown = unknown

 rs n (set t) = set (rv n t)
 rs n (lit n₁) = lit n₁
 rs n (prop t) = prop (rv n t)
 rs n (propLit n₁) = propLit n₁
 rs n (inf n₁) = inf n₁
 rs n unknown = unknown

 rcl n (clause tel ps t) =
   clause (rtl n tel) (rpts n ps) (rv (length tel + n) t)
 rcl n (absurd-clause tel ps) =
   absurd-clause (rtl n tel) (rpts n ps)

 rtl n [] = []
 rtl n ((v , arg i x) ∷ xs) =
    ((v , arg i (rv n x))) ∷ rtl (suc n) xs

 rc n [] = []
 rc n (cl ∷ cls) =
   rcl n cl ∷ rc n cls
 -- rc n (cl@(clause _ _ _) ∷ cls) =
 --   rcl n cl ∷ rc n cls
 -- rc n (_ ∷ cls) =
 --   rc n cls
 rpt n (con c ps) = con c (rpts n ps)
 rpt n (dot t) = dot (rv n t)
 rpt n (var x) = var x
 rpt n (lit l) = lit l
 rpt n (proj f) = proj f
 rpt n (absurd x) = absurd x
 -- rpt n x = x

 rpts n [] = []
 rpts n ((arg i x) ∷ xs) = arg i (rpt n x) ∷ rpts n xs

dropVar : ℕ → Term → Term
dropVar = dropVars.rv 1 
