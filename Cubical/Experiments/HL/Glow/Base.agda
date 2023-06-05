module Cubical.Experiments.HL.Glow.Base where


open import Cubical.Foundations.Everything
open import Cubical.Data.Bool renaming (Bool to 𝟚) hiding (_≤_)
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Sum

open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Relation.Nullary

open import Cubical.Experiments.HL.Platform.Base

record GlowLang : Type₁ where
 field
  Source : Type
  -- Value : Type
  Parameters : (s : Source) → Type
  Participants : (s : Source) → Type
  Call : Type
  
  
  -- isParameterOf : Source → Value → hProp₀

 

 record AbstractSemantics : Type₁ where
  field
   ConsensusState : Type
   semantics :
     ConsensusState →
     (s : Source) →
     Parameters s →
     Participants s →
     Call →
     ConsensusState

  record DeploymentData (p : Platform) : Type₁ where
   open Platform p
   field
    stateOnDeployment : State
    source : Source
    actor : Actor
    participants : (Participants source) → Actor
    parameters : Parameters source

  -- fact that we are paremtrising call by participant, not by actor
  -- signify that we are modeling closed contract, this will be the place
  -- to introuce open contracts in the future
  record ConcreteSemantics (p : Platform) : Type₁ where
   open Platform p
   open DeploymentData
   field
    mapState : State → ConsensusState
    deploy : DeploymentData p → Contract
   
    call : ∀ st → 
        (dd : DeploymentData p) →
        (prtcp : Participants (dd .source)) → 
        Call → Request st (dd .participants prtcp) (deploy dd)
        
    mechanicsCoherence :
     ∀ (st : State)
     (dd : DeploymentData p) →
     (prtcp : Participants (dd .source)) → 
     (c : Call) → 
     semantics (mapState st) (dd .source) (dd .parameters) prtcp c ≡
       mapState (dynamics st (dd .participants prtcp) (deploy dd)
         (call st dd prtcp c))
      
