module Cubical.Experiments.HL.Platform.Examples.Trivial where

open import Cubical.Foundations.Everything
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Empty

open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Relation.Nullary

open import Cubical.Experiments.HL.Platform.Base


module Trivial where

 platform : Platform
 platform = record
   { State = Unit
   ; Actor = Unit
   ; Contract = ⊥
   ; Request = λ s a ()
   ; dynamics = λ s a ()
   }


 accountModel : Platform.AccountModel platform 
 accountModel = record
   { Address = Unit
   ; Token = Unit
   ; Transaction = ⊥
   ; balance = λ s _ _ → 0
   ; transactionSemantics = λ s t → _
   }


module OneWallet where

 platform : Platform
 platform = record
   { State = ℕ
   ; Actor = Unit
   ; Contract = ⊥
   ; Request = λ s a ()
   ; dynamics = λ s a ()
   }


 accountModel : Platform.AccountModel platform 
 accountModel = record
   { Address = Unit
   ; Token = Unit
   ; Transaction = ℕ
   ; balance = λ s _ _ → s
   ; transactionSemantics = λ s t → s + t
   }
