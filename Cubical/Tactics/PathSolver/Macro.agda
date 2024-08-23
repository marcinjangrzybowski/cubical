{-# OPTIONS --safe #-}

module Cubical.Tactics.PathSolver.Macro where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.List as L
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sigma

open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_ ; _<_ to _<ℕ_)
open import Agda.Builtin.String
open import Agda.Builtin.Char

open import Cubical.Data.Sigma.Base

open import Cubical.Reflection.Base renaming (v to 𝒗)
open import Cubical.Reflection.Sugar
import Agda.Builtin.Reflection as R
open import Cubical.Tactics.PathSolver.Reflection
open import Cubical.Tactics.Reflection

open import Cubical.Tactics.Reflection.Utilities

open import Cubical.Tactics.PathSolver.CongComp

open import Cubical.Tactics.Reflection.QuoteCubical

open import Cubical.Tactics.Reflection.Error
open import Cubical.Tactics.Reflection.Dimensions
open import Cubical.Tactics.Reflection.CuTerm
open import Cubical.Tactics.PathSolver.Reflection
open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.PathSolver.Degen
open import Cubical.Tactics.PathSolver.Path


macro
 cong$ : R.Term → R.Term → R.TC Unit
 cong$ t h = do
   ty ← R.inferType t
   t ← normaliseWithType ty t
   cc ← getCuCtx
   let dim = length cc
   co ← R.getContext
   cu ← R.inContext (drop dim co) $ appCongs dim
           <$> quoteCuTerm (just (dropVars.rv dim zero ty)) dim (t)
   let r = ToTerm.toTerm cc cu
   R.unify r h <|> R.typeError [ r ]ₑ



macro
 cong! : R.Term → R.Term → R.TC Unit
 cong! t h = do
   ty ← R.inferType t
   t ← normaliseWithType ty t
   cc ← getCuCtx
   let dim = predℕ (length cc)
   co ← R.getContext
   cu ← R.inContext (drop (suc dim) co) $ fillCongs 100 dim
           <$> quoteCuTerm nothing --(just (dropVars.rv (suc dim) zero ty))
                          dim (dropVar dim t)
   let r = ToTerm.toTerm cc cu

   R.unify r h --<|> R.typeError [ r ]ₑ

makeH? : R.Term → R.Term → R.TC String
makeH? iT eT = do
  cuCtx ← getCuCtx
  let dim = length cuCtx
  fE ← iFxprFromSpec dim iT

  cuCtx ← L.map (map-snd (const nothing)) ∘S take dim <$> R.getContext
  (((hcoFromIExpr dim fE eT) >>= codeGen.ppCT'' false dim cuCtx 10) >>= R.formatErrorParts)

 where
 iFxprFromSpec : ℕ → R.Term → R.TC FExpr
 iFxprFromSpec dim t =
   (R.unquoteTC {A = ℕ} t <⊎> extractIExprM t)
     <|> (R.typeError $
         "Wrong parameter!"
         ∷nl [ "pass either ℕ or Interval Expr as first argument!" ]ₑ)
   >>= pure ∘S ⊎.rec (allSubFacesOfSfDim dim ∘S min (predℕ dim))
                     ((_++fe (allSubFacesOfSfDim dim 0)) ∘S I→F)

macro

 h? : R.Term → R.Term → R.Term → R.TC Unit
 h? iT eT h = do
  src ← makeH? iT eT
  unifyFromString src h

 h?' : R.Term → R.Term → R.Term → R.TC Unit
 h?' iT eT _ = do
  src ← makeH? iT eT
  R.typeError [ src ]ₑ
