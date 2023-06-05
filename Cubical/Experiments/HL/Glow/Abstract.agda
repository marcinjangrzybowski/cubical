module Cubical.Experiments.HL.Glow.Abstract where


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
open import Cubical.Experiments.HL.Glow.Base


module _
  (GExpr : Type)
  (Participant : Type) where


 data Effect : Type where
    depositE withdrawE : ℕ → Effect

 
 data GMonad : Type where
  action : Participant → Effect → GMonad
  require : GExpr → GMonad
  expectPub : Participant → GMonad
  bind : GMonad → GMonad → GMonad
  pure : GExpr → GMonad
  branch : GExpr → GMonad → GMonad → GMonad


 callMG : GMonad → Type
 callMG (action x x₁) = {!!}
 callMG (require x) = {!!}
 callMG (expectPub x) = {!!}
 callMG (bind x x₁) = {!!}
 callMG (pure x) = {!!}
 callMG (branch x x₁ x₂) = {!!}

 MonadicGlow : GlowLang
 GlowLang.Source MonadicGlow = GMonad
 GlowLang.Parameters MonadicGlow _ = GExpr
 GlowLang.Call MonadicGlow = callMG

 record MGlowState : Type where
  field
   publishedValues : List (Participant × GExpr)
   transaction : List (Participant × Effect)
   toExecute : GMonad

 MonadicGlowSemantics : GlowLang.AbstractSemantics MonadicGlow
 MonadicGlowSemantics = w
  where
  open GlowLang.AbstractSemantics
  w : GlowLang.AbstractSemantics MonadicGlow
  ConsensusState w = MGlowState
  semantics w = {!!}
