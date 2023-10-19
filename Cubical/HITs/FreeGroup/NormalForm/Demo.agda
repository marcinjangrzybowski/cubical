{-# OPTIONS --safe #-}

module Cubical.HITs.FreeGroup.NormalForm.Demo where

-- open import Cubical.HITs.FreeGroup.Base renaming (assoc to ·assoc)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv.Properties
-- open import Cubical.Foundations.Equiv.BiInvertible
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Relation.Nullary

open import Cubical.Functions.Involution
open import Cubical.Functions.FunExtEquiv

open import Cubical.Functions.Embedding
import Cubical.Functions.Logic as L

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_)
open import Cubical.Data.Nat.Order.Recursive as OR
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Data.List as Li
open import Cubical.Data.Maybe
import Cubical.Data.Int as Int
import Cubical.Data.Fin as Fin

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/₂_ ; [_] to [_]/)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
-- open import Cubical.HITs.TypeQuotients as TQ renaming ([_] to [_]/ₜ ; eq/ to eq/ₜ )


open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.HLevels
open import Cubical.Relation.Binary.Base

open import Cubical.HITs.FreeGroup.NormalForm.Base

open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Groups
open import Cubical.Categories.NaturalTransformation
open import Cubical.HITs.FreeGroup.NormalForm.EqEps


 
