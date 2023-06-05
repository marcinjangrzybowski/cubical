module Cubical.Experiments.HL.GlowOnLurk where

open import Cubical.Foundations.Everything
open import Cubical.Data.Bool renaming (Bool to 𝟚) hiding (_≤_)
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe

open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Relation.Nullary


open import Cubical.Experiments.HL.Platform.Base
open import Cubical.Experiments.HL.Glow.Base
open import Cubical.Experiments.HL.ZK
open import Cubical.Experiments.HL.Lurk
  

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
