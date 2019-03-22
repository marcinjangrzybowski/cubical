{-# OPTIONS --cubical --safe #-}
module Cubical.Data.DiffInt.Properties where

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.Data.DiffInt.Base
open import Cubical.Core.Prelude
open import Cubical.Data.Nat
open import Cubical.Core.Glue
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients
open import Cubical.Data.Prod

open BinaryRelation

relIsEquiv : isEquivRel rel
relIsEquiv = EquivRel {A = ℕ ×Σ ℕ} relIsRefl relIsSym relIsTrans
  where
    relIsRefl : isRefl rel
    relIsRefl (a0 , a1) = refl

    relIsSym : isSym rel
    relIsSym (a0 , a1) (b0 , b1) p = sym p

    relIsTrans : isTrans rel
    relIsTrans (a0 , a1) (b0 , b1) (c0 , c1) p0 p1 =
      inj-m+ {m = (b0 + b1)} ((b0 + b1) + (a0 + c1) ≡⟨ +-assoc (b0 + b1) a0 c1  ⟩
            ((b0 + b1) + a0) + c1 ≡⟨ cong (λ x → x + a0 + c1) (+-comm b0 b1)⟩
            ((b1 + b0) + a0) + c1 ≡⟨ cong (λ x → x + c1) (+-comm (b1 + b0) a0) ⟩
            (a0 + (b1 + b0)) + c1 ≡⟨ cong (λ x → x + c1) (+-assoc a0 b1 b0) ⟩
            (a0 + b1) + b0 + c1 ≡⟨ sym (+-assoc (a0 + b1) b0 c1) ⟩
            (a0 + b1) + (b0 + c1) ≡⟨ cong (λ p → p . fst + p .snd) (transport (ua Σ≡) (p0 , p1))⟩
            (b0 + a1) + (c0 + b1) ≡⟨ sym (+-assoc b0 a1 (c0 + b1))⟩
            b0 + (a1 + (c0 + b1)) ≡⟨ cong (λ x → b0 + (a1 + x)) (+-comm c0 b1)⟩
            b0 + (a1 + (b1 + c0)) ≡⟨ cong (λ x → b0 + x) (+-comm a1 (b1 + c0)) ⟩
            b0 + ((b1 + c0) + a1) ≡⟨ cong (λ x → b0 + x) (sym (+-assoc b1 c0 a1))⟩
            b0 + (b1 + (c0 + a1)) ≡⟨ +-assoc b0 b1 (c0 + a1)⟩
            (b0 + b1) + (c0 + a1) ∎ )

relIsProp : BinaryRelation.isPropValued rel
relIsProp a b x y = isSetℕ _ _ _ _

discreteℤ : Discrete ℤ
discreteℤ = discreteSetQuotients (discreteΣ discreteℕ λ _ → discreteℕ) relIsProp relIsEquiv (λ _ _ → discreteℕ _ _)

a : ℤ
a = [ (2 , 4) ]

b : ℤ
b = [ (3 , 3) ]
