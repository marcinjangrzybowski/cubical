{-# OPTIONS --cubical --no-exact-split --safe #-}

module Cubical.DataDefinitions.CubiEdu where

open import Cubical.Foundations.Everything
open import Cubical.Core.Everything
open import Cubical.Foundations.Logic

open import Cubical.Data.Sum

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool

open import Cubical.Data.Universe

import Cubical.Data.Nat as orgℕ

record TwoTypes : Type₁ where
  constructor 2t
  field
    a : Set
    b : Set

TwoTypes≡ : ∀ tt1 tt2
              → TwoTypes.a tt1 ≡ TwoTypes.a tt2
              → TwoTypes.b tt1 ≡ TwoTypes.b tt2
                → tt1 ≡ tt2
TwoTypes.a (TwoTypes≡ tt1 tt2 x x₁ i) = x i
TwoTypes.b (TwoTypes≡ tt1 tt2 x x₁ i) = x₁ i

record FamWithBase : Type₁ where
  constructor fwb
  field
    a : Set
    b : a → Set



FamWithBase≡ : ∀ fwb1 fwb2
              → (e1 : FamWithBase.a fwb1 ≡ FamWithBase.a fwb2)
              → (e2 : ∀ a₁ → ∀ a₂ → transport e1 a₁ ≡ a₂ → (FamWithBase.b fwb1 a₁) ≡ (FamWithBase.b fwb2 a₂))
                → fwb1 ≡ fwb2
FamWithBase.a (FamWithBase≡ fwb1 fwb2 e1 e2 i) = e1 i
FamWithBase.b (FamWithBase≡ fwb1 fwb2 e1 e2 i) x = 
    hcomp {A = Set}
      (λ j → λ { (i = i0) →  FamWithBase.b fwb1 x
          ; (i = i1) → (e2 (transport (sym e1) x) x (transportTransport⁻ e1 x)) j 
           } )
          (  FamWithBase.b fwb1 (coei→0 (λ j → e1 j) i x) )


--  FamWithBase.b fwb2
-- (transp (λ i → e1 i) i0 (transp (λ i → e1 (~ i)) i0 x))

-- IsoBool-id : Iso Bool Bool
-- Iso.fun IsoBool-id = idfun _
-- Iso.inv IsoBool-id = idfun _
-- Iso.rightInv IsoBool-id b = refl
-- Iso.leftInv IsoBool-id a = refl

-- IsoBool-not : Iso Bool Bool
-- Iso.fun IsoBool-not = not
-- Iso.inv IsoBool-not = not
-- Iso.rightInv IsoBool-not = notnot
-- Iso.leftInv IsoBool-not = notnot


-- Bool-≡-Bool→Bool : (Bool × Bool) ≡ (Bool → Bool)
-- Bool-≡-Bool→Bool = ?

-- iso-Bool : (Iso Bool Bool) ≡ Bool
-- iso-Bool = isoToPath (iso
--   (λ x → caseBool true false (Iso.fun x true))
--   (caseBool IsoBool-id IsoBool-not)
--   h1
--   h2
--   )
--   where
--     h1 : (b : Bool) →
--            caseBool true false
--            (Iso.fun (caseBool IsoBool-id IsoBool-not b) true)
--            ≡ b
--     h1 false = refl
--     h1 true = refl

--     h2 : (a : Iso Bool Bool) →
--            caseBool IsoBool-id IsoBool-not
--            (caseBool true false (Iso.fun a true))
--            ≡ a
--     h2 a with (Iso.fun a true)
--     h2 a | false = {!!}
--     h2 a | true = {!!}
