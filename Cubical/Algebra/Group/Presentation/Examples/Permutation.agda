{-# OPTIONS --safe --lossy-unification #-} 
module Cubical.Algebra.Group.Presentation.Examples.Permutation where

open import Cubical.Data.Sigma

open import Cubical.Foundations.Everything
-- open import Cubical.Foundations.Function
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Bool using (false ; true) renaming (Bool to 𝟚) 

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties

open import Cubical.HITs.EilenbergMacLane1

open import Cubical.HITs.GroupoidTruncation as GT

open import Cubical.Algebra.Group.Presentation.Base


data PermRels : Type₀ where 
 invo : {!!}
 comm : {!!}
 braid : {!!}
