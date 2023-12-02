{-# OPTIONS --safe #-}
module Cubical.Relation.Binary.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary.Base
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma

private
  variable
    ℓA ℓA' ℓB ℓB' : Level
    A : Type ℓA
    B : Type ℓB
    f : A → B
    rA : Rel A A ℓA'
    rB : Rel B B ℓB'

open BinaryRelation

module _ (R : Rel B B ℓB') where

  -- Pulling back a relation along a function.
  -- This can for example be used when restricting an equivalence relation to a subset:
  --   _~'_ = on fst _~_

  pulledbackRel : (A → B) → Rel A A ℓB'
  pulledbackRel f x y = R (f x) (f y)

  funRel : Rel (A → B) (A → B) _
  funRel f g = ∀ x → R (f x) (g x) 
   
module _ (isEquivRelR : isEquivRel rB) where
 open isEquivRel

 isEquivRelPulledbackRel : (f : A → _) → isEquivRel (pulledbackRel rB f)
 reflexive (isEquivRelPulledbackRel _) _ = reflexive isEquivRelR _ 
 symmetric (isEquivRelPulledbackRel _) _ _ = symmetric isEquivRelR _ _
 transitive (isEquivRelPulledbackRel _) _ _ _ = transitive isEquivRelR _ _ _ 

 isEquivRelFunRel : isEquivRel (funRel rB {A = A})
 reflexive isEquivRelFunRel _ _ =
   reflexive isEquivRelR _ 
 symmetric isEquivRelFunRel _ _ =
   symmetric isEquivRelR _ _ ∘_
 transitive isEquivRelFunRel _ _ _ u v _ =
   transitive isEquivRelR _ _ _ (u _) (v _)

module _ (rA : Rel A A ℓA') (rB : Rel B B ℓB') where

 ×Rel : Rel (A × B) (A × B) (ℓ-max ℓA' ℓB')
 ×Rel (a , b) (a' , b') = (rA a a') × (rB b b')


module _ (isEquivRelRA : isEquivRel rA) (isEquivRelRB : isEquivRel rB) where
 open isEquivRel

 module eqrA = isEquivRel isEquivRelRA
 module eqrB = isEquivRel isEquivRelRB
 
 isEquivRel×Rel : isEquivRel (×Rel rA rB)
 reflexive isEquivRel×Rel _ =
   eqrA.reflexive _ , eqrB.reflexive _
 symmetric isEquivRel×Rel _ _ =
   map-× (eqrA.symmetric _ _) (eqrB.symmetric _ _)
 transitive isEquivRel×Rel _ _ _ (ra , rb) =
   map-× (eqrA.transitive _ _ _ ra) (eqrB.transitive _ _ _ rb)

