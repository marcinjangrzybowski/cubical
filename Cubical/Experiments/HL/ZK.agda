module Cubical.Experiments.HL.ZK where

open import Cubical.Foundations.Everything
open import Cubical.Data.Bool renaming (Bool to 𝟚) hiding (_≤_)
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe

open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Relation.Nullary

   

record zk-SNARK : Type₁ where
 field
  Circuit : Type
  Input : Circuit → Type
  Output : Circuit → Type
  computeOutput : ∀ {c} → Input c → Output c
  Verifier : Circuit → Type
  Prover : Circuit → Type
  Proof : ∀ {c} → Input c → Output c → Type
  prove : ∀ {c} → (i : Input c)
     → Prover c
     → Proof i (computeOutput i)
  proofSemantics : ∀ {c} → {i : Input c} → {o : Output c}
     → (i : Input c)
     → (o : Output c)
     → Proof i o
     → computeOutput i ≡ o
  generateProver : ∀ c → Prover c
  generateVerifier : ∀ c → Verifier c


 record Claim : Type₁ where
  field
   circuit : Circuit
   input : Input circuit
   output : Output circuit
   proof : Proof input output
