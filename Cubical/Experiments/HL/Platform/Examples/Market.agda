module Cubical.Experiments.HL.Platform.Examples.Market where

open import Cubical.Foundations.Everything
open import Cubical.Data.Bool renaming (Bool to 𝟚) hiding (_≤_)
open import Cubical.Data.Nat
open import Cubical.Data.Int
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty

open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Relation.Nullary

open import Cubical.Experiments.HL.Platform.Base

-- open Platform

module _ (String : Type) (Key PublicKey Signature : Type) (Script : Type) where

 -- define the Transaction type
 record Transaction : Type where
   field
     from : PublicKey
     to : PublicKey
     value : ℕ
     dataT : String
     nonce : ℕ
     gasLimit : ℕ

 -- define the Block type
 record Block : Type where
   field
     prevHash : String
     transactions : List Transaction

 -- define the Account type
 record Account : Type where
   field
     address : PublicKey
     balance : ℕ
     nonce : ℕ

 -- define the State type
 record State : Type where
   field
     ledger : List Block
     accounts : List Account

 -- define the Actor type
 data Actor : Type where
   Alice Bob : Actor

 -- define the Contract type
 data Contract : Type where
   NativeToken NFT : Contract

 -- define a function to validate a transaction
 validTransaction : State → Actor → Contract → Transaction → Type
 validTransaction s a c tx = {!!}
   -- let
   --   -- retrieve the sender's account from the ledger
   --   senderAccount : Maybe Account
   --   senderAccount = lookupAccount (from tx) (accounts s)
   --   -- retrieve the recipient's account from the ledger
   --   recipientAccount : Maybe Account
   --   recipientAccount = lookupAccount (to tx) (accounts s)
   --   -- ensure that the sender's account exists and has enough balance
   --   senderHasBalance : senderAccount ≡ just { address = from tx ; balance = suc ?n ; nonce = ?nonce } =
   --     (senderAccount ≡ just { address = from tx ; balance = suc n ; nonce = nonce }) ∧ (value tx ≤ balance senderAccount)
   --   -- ensure that the recipient's account exists
   --   recipientExists : recipientAccount ≢ nothing { A = Account } = recipientAccount ≢ nothing
   --   -- ensure that the transaction nonce matches the sender's account nonce
   --   validNonce : tx . nonce ≡ nonce senderAccount = tx . nonce ≡ nonce senderAccount
   --   -- ensure that the gas limit is sufficient
   --   sufficientGas : gasLimit tx ≥ costOfComputing c tx = gasLimit tx ≥ costOfComputing c tx
   -- in
   --   senderHasBalance × recipientExists × validNonce × sufficientGas


 -- define the Request type
 record Request (s : State) (a : Actor) (c : Contract) : Type where
   field
     tx : Transaction
     validTx : validTransaction s a c tx

 -- define the cost of computation
 record Gas : Type where
   field
     amount : ℕ


--  -- define a function to look up an account in the ledger by address
--  lookupAccount : PublicKey → List Account → Maybe Account
--  lookupAccount _ [] = nothing
--  lookupAccount pk (account ∷ accounts) with pk ≟ address account
--  ... | yes _ = just account
--  ... | no _ = lookupAccount pk accounts


 marketPlatform : Platform
 marketPlatform =
   record
     { State = State
     ; Actor = Actor
     ; Contract = Contract
     ; Request = Request
     ; dynamics = {!!}
     }
-- -- -- -- -- define the cost of computing a transaction for a given contract
-- -- -- -- costOfComputing : Contract → Transaction → Gas
-- -- -- -- costOfComputing NativeToken tx = gas { amount = 1000 } -- example value, arbitrary gas cost
-- -- -- -- costOfComputing NFT tx = gas { amount = 5000 } -- example value, arbitrary gas cost

-- -- -- -- -- define the Platform record
-- -- -- -- record Platform : Type where
-- -- -- --   field
-- -- -- --     State

