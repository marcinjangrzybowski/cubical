module Cubical.Experiments.HL.Main where

open import Cubical.Foundations.Everything
open import Cubical.Data.Bool renaming (Bool to 𝟚) hiding (_≤_)
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe

open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Relation.Nullary


hProp₀ = hProp ℓ-zero


record Platform : Type₁ where
 field
  State : Type
  Actor : Type
  -- Value : Type
  -- Key : Type
  Contract : Type
  Request : State → Actor → Contract → Type
  dynamics :
    (s : State) →
    (a : Actor) →
    (c : Contract) →
    Request s a c →
    State



 History : {!!}
 History = {!!}

record GlowLang : Type₁ where
 field
  Source : Type
  -- Value : Type
  Parameters : (s : Source) → Type
  Call : Source → Type
  
  
  -- isParameterOf : Source → Value → hProp₀

 

 record AbstractSemantics : Type₁ where
  field
   ConsensusState : Type
   semantics :
     ConsensusState →
     (s : Source) →
     Parameters s →
     Call s →
     ConsensusState

  record ConcreteSemantics (p : Platform) : Type₁ where
   open Platform p
   field
    mapState : State → ConsensusState
    deploy : 
       (st : State) →
       (s : Source) →
       (a : Actor) →
       (p : Parameters s) →
       Contract
    call :
        (st : State) →
        (s : Source) →
        (a : Actor) →
        (p : Parameters s) →
        Call s →
        Request st a (deploy st s a p)
    mechanicsCoherence :
     ∀ (st : State)
     (a : Actor)
     (s : Source) →
     (pars : Parameters s) →
     (c : Call s) →
     semantics (mapState st) s pars c ≡
       mapState (dynamics st a (deploy st s a pars)
         (call st s a pars c))
      
   

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
   
  

module GlowOnLurk
  (platform : Platform)
  (lurkLanguage : LurkLanguage)
  (glowLang : GlowLang) where

 open Platform platform
 open LurkLanguage lurkLanguage
 open GlowLang glowLang

 module _ (aSem : AbstractSemantics)
          (cSem : AbstractSemantics.ConcreteSemantics aSem platform) where
  open AbstractSemantics aSem
  open AbstractSemantics.ConcreteSemantics cSem


  


-- module FilecoinExample (Address : Type)
--   (_A≟_ : Discrete Address)
--   (_-_ : ℕ → ℕ → ℕ) where


--  -- define the value type
--  data Value : Type where
--    VNat : ℕ → Value
--    VBool : 𝟚 → Value
--    VAddress : Address → Value
 


--  -- define the program type
--  data Program : Type where
--    Halt : Program
--    Transfer : Address → Address → ℕ → Program
--    Log : List Value → Program
--    Call : Address → Program
--    If : Value → Program → Program → Program
--    Seq : List Program → Program
   
--  -- define the account state
--  record AccountState : Type where
--    field
--      balance : ℕ
--      allowance : List (Address × ℕ)
--      code : Maybe Program

--  -- define the native token state
--  record TokenState : Type where
--    field
--      totalSupply : ℕ
--      balances : List (Address × ℕ)


--  -- define the global state for the Filecoin network
--  record FilecoinState : Type where
--    field
--      accounts : List (Address × AccountState)
--      token : TokenState
     
--  open FilecoinState

--  -- define the contract type
--  record Contract : Type where
--    field
--      code : Program


--  -- define the event type
--  data Event : Type where
--    Log : List Value → Event
--    Transfer : Address → Address → ℕ → Event

--  -- define the request type
--  record Request (st : FilecoinState) (a : Address) (c : Contract) : Type where
--    field
--      sender : Address
--      value : ℕ
--      input : Program
--      newState : Maybe FilecoinState
--      events : List Event

--  updateBalances : Address → List (Address × ℕ) → Address → ℕ → List (Address × ℕ)
--  updateBalances from [] to amount = [(to , amount)]
--  updateBalances from ((addr , balance) ∷ rest) to amount with addr A≟ from
--  ... | yes _ = (addr , balance - amount) ∷ updateBalances from rest to amount
--  ... | no _ with addr A≟ to
--  ...   | yes _ = (addr , balance + amount) ∷ rest
--  ...   | no _ = (addr , balance) ∷ updateBalances from rest to amount

--  eventDynamics : 
--   (s : FilecoinState)
--   → (a : Address)
--   → (c : Contract)
--   → Event → FilecoinState
--  eventDynamics s a c (Log x) = s
--  eventDynamics s a c (Transfer from to amount) = {!!}
--  dynamics : (s : FilecoinState) → (a : Address) → (c : Contract) → Request s a c → FilecoinState
--  dynamics s a c req = w s (events req)
--   where
--    open Request
--    w : FilecoinState → List Event → FilecoinState
--    w s [] = s
--    w s (e ∷ x₁) = w (eventDynamics s a c e) x₁


-- -- -- -- -- module example1 where

-- -- -- -- --  PlatformExample : Platform
-- -- -- -- --  PlatformExample = record
-- -- -- -- --    { State = ℕ
-- -- -- -- --    ; Actor = Unit
-- -- -- -- --    ; Contract = 𝟚
-- -- -- -- --    ; Request = λ s a c → if c then Unit else 1 ≤ s
-- -- -- -- --    ; dynamics = dyn
-- -- -- -- --    }
-- -- -- -- --    where
-- -- -- -- --     dyn : (s : ℕ) (a : Unit) (c : 𝟚) → if c then Unit else 1 ≤ s → ℕ
-- -- -- -- --     dyn (suc s) a false x = s
-- -- -- -- --     dyn s a true x = suc s

-- -- -- -- --  GlowLangExample : GlowLang
-- -- -- -- --  GlowLangExample = record
-- -- -- -- --    { Source = 𝟚
-- -- -- -- --    ; Parameters = λ _ → ℕ
-- -- -- -- --    ; Call = λ _ → ℕ
-- -- -- -- --    }

-- -- -- -- --  -- -- AbstractSemanticsExample : AbstractSemantics
-- -- -- -- --  -- -- AbstractSemanticsExample = record
-- -- -- -- --  -- --   { ConsensusState = ℕ
-- -- -- -- --  -- --   ; semantics = λ s _ p c → s + p + c
-- -- -- -- --  -- --   }

-- -- -- -- --  -- -- ConcreteSemanticsExample : ConcreteSemantics PlatformExample
-- -- -- -- --  -- -- ConcreteSemanticsExample = record
-- -- -- -- --  -- --   { mapState = λ s → s
-- -- -- -- --  -- --   ; deploy = λ st s a p → λ x → p x + if a then st else 0
-- -- -- -- --  -- --   ; call = λ st s a p c → c
-- -- -- -- --  -- --   ; mechanicsCoherence = λ st a s p c →
-- -- -- -- --  -- --       begin
-- -- -- -- --  -- --         AbstractSemanticsExample.semantics st s p c
-- -- -- -- --  -- --         ≡⟨⟩
-- -- -- -- --  -- --         st + p + c
-- -- -- -- --  -- --         ≡⟨⟩
-- -- -- -- --  -- --         mapState (dynamics st a (deploy st s a p) (call st s a p c))
-- -- -- -- --  -- --       ∎
-- -- -- -- --  -- --   }
