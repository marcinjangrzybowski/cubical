module Cubical.Experiments.HL.Platform.Examples.Filecoin where

open import Cubical.Foundations.Everything
open import Cubical.Data.Bool renaming (Bool to 𝟚) hiding (_≤_)
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Empty

open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Relation.Nullary

open import Cubical.Experiments.HL.Platform.Base


module FilecoinExample (Address : Type)
  (_A≟_ : Discrete Address)
  (_-_ : ℕ → ℕ → ℕ) where


 -- define the value type
 data Value : Type where
   VNat : ℕ → Value
   VBool : 𝟚 → Value
   VAddress : Address → Value
 


 -- define the program type
 data Program : Type where
   Halt : Program
   Transfer : Address → Address → ℕ → Program
   Log : List Value → Program
   Call : Address → Program
   If : Value → Program → Program → Program
   Seq : List Program → Program
   
 -- define the account state
 record AccountState : Type where
   field
     balance : ℕ
     allowance : List (Address × ℕ)
     code : Maybe Program

 -- define the native token state
 record TokenState : Type where
   field
     totalSupply : ℕ
     balances : List (Address × ℕ)


 -- define the global state for the Filecoin network
 record FilecoinState : Type where
   field
     accounts : List (Address × AccountState)
     token : TokenState
     
 open FilecoinState

 -- define the contract type
 record Contract : Type where
   field
     code : Program


 -- define the event type
 data Event : Type where
   Log : List Value → Event
   Transfer : Address → Address → ℕ → Event

 -- define the request type
 record Request (st : FilecoinState) (a : Address) (c : Contract) : Type where
   field
     sender : Address
     value : ℕ
     input : Program
     newState : Maybe FilecoinState
     events : List Event

 updateBalances : Address → List (Address × ℕ) → Address → ℕ → List (Address × ℕ)
 updateBalances from [] to amount = [(to , amount)]
 updateBalances from ((addr , balance) ∷ rest) to amount with addr A≟ from
 ... | yes _ = (addr , balance - amount) ∷ updateBalances from rest to amount
 ... | no _ with addr A≟ to
 ...   | yes _ = (addr , balance + amount) ∷ rest
 ...   | no _ = (addr , balance) ∷ updateBalances from rest to amount

 eventDynamics : 
  (s : FilecoinState)
  → (a : Address)
  → (c : Contract)
  → Event → FilecoinState
 eventDynamics s a c (Log x) = s
 eventDynamics s a c (Transfer from to amount) = {!!}
 dynamics : (s : FilecoinState) → (a : Address) → (c : Contract) → Request s a c → FilecoinState
 dynamics s a c req = w s (events req)
  where
   open Request
   w : FilecoinState → List Event → FilecoinState
   w s [] = s
   w s (e ∷ x₁) = w (eventDynamics s a c e) x₁


 filecoin : Platform
 filecoin = record
              { State = FilecoinState
              ; Actor = Address
              ; Contract = Contract
              ; Request = Request
              ; dynamics = dynamics
              }

 filecoinAM : Platform.AccountModel filecoin
 filecoinAM = {!!}
