module Cubical.Experiments.HL.Lurk where

open import Cubical.Foundations.Everything
open import Cubical.Data.Bool renaming (Bool to 𝟚) hiding (_≤_)
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe

open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Relation.Nullary

open import Cubical.Experiments.HL.ZK

record LurkLanguage : Type₁ where
 field
  LurkExpression : Type
  LurkEvaluator : LurkExpression → LurkExpression
  -- LurkCompiler : LurkSource → zk-SNARK

 record LurkCompiler (zks : zk-SNARK) : Type₁ where
  open zk-SNARK zks
  field
   compile : LurkExpression → Circuit
   translateInput : (le : LurkExpression) → Input (compile le)
   translateOutput : ∀ {le} → Output (compile le) → LurkExpression
   soundness : ∀ (le : LurkExpression) →
                  let c = compile le in
                  let i = translateInput le in
                  let o = computeOutput i in
                  let p = prove {c = c} i (generateProver c) in
                  LurkEvaluator le ≡ translateOutput o
