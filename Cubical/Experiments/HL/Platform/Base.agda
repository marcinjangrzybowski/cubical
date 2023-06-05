module Cubical.Experiments.HL.Platform.Base where

open import Cubical.Foundations.Everything
open import Cubical.Data.Bool renaming (Bool to 𝟚) hiding (_≤_)
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe

open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Relation.Nullary


record Platform : Type₁ where
 field
  State : Type
  Actor : Type
  Contract : Type
  Request : State → Actor → Contract → Type
  dynamics :
    (s : State) →
    (a : Actor) →
    (c : Contract) →
    Request s a c →
    State

 History : Type
 History = List State

 record AccountModel : Type₁ where
  field
    Address : Type
    Token : Type
    Transaction : Type
    balance : State → Address → Token → ℕ  
    transactionSemantics : State → Transaction → State


record PlatformSafe : Type₁ where
 field
  State : Type
  _⤇_ : State → State → Type 
  Actor : Type
  Contract : Type
  Request : State → Actor → Contract → Type
  dynamics :
    (s : State) →
    (a : Actor) →
    (c : Contract) →
    Request s a c →
    Σ State (s ⤇_)

 isRealHistory : List State → Type
 isRealHistory [] = Unit
 isRealHistory (x ∷ []) = Unit
 isRealHistory (x ∷ l@(x₁ ∷ _)) = (x ⤇ x₁) × isRealHistory l

 History : Type
 History = Σ _ isRealHistory

fromSafe : PlatformSafe → Platform
fromSafe x = record
               { State = State
               ; Actor = Actor
               ; Contract = Contract
               ; Request = Request
               ; dynamics = λ s₁ a c x₁ → fst (dynamics s₁ a c x₁)
               }
 where
  open PlatformSafe x 
