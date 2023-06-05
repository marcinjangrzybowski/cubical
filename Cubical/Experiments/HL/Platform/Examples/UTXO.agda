module Cubical.Experiments.HL.Platform.Examples.UTXO where

open import Cubical.Foundations.Everything
open import Cubical.Data.Bool renaming (Bool to 𝟚) hiding (_≤_)
open import Cubical.Data.Nat
open import Cubical.Data.Int
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Empty

open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Relation.Nullary

open import Cubical.Experiments.HL.Platform.Base

open Platform

module _ (Signature : Type) (PubKey : Type) (Script : Type) where

 record UTXO-Actor : Type where
   constructor mkUTXO-Actor
   field
     pubkey : PubKey

 data UTXO : Type where
   mkUTXO : UTXO-Actor → UTXO-Actor → ℤ → UTXO


 record UTXO-State : Type where
   constructor mkUTXO-State
   field
     unspent : List UTXO

 record UTXO-Contract : Type where
   constructor mkUTXO-Contract
   field
     script : Script

 record UTXO-Request (s₁ : UTXO-State) (a : UTXO-Actor) (c : UTXO-Contract) : Type where
   constructor mkUTXO-Request
   field
     txInputs  : List UTXO
     txOutputs : List (UTXO-Actor × ℤ)
     txSig     : Signature


 PlatformUTXO : Platform
 State PlatformUTXO = UTXO-State
 Actor PlatformUTXO = UTXO-Actor
 Contract PlatformUTXO = UTXO-Contract
 Request PlatformUTXO = UTXO-Request
 dynamics PlatformUTXO = {!!}
