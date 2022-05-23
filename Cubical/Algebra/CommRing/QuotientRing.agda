{-# OPTIONS --safe #-}
module Cubical.Algebra.CommRing.QuotientRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

open import Cubical.Data.Nat
open import Cubical.Data.FinData

open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/sq_)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Ideal
open import Cubical.Algebra.CommRing.FGIdeal
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.QuotientRing renaming (_/_ to _/Ring_) hiding (asRing)

private
  variable
    ℓ ℓ' : Level

_/_ : (R : CommRing ℓ) → (I : IdealsIn R) → CommRing ℓ
R / I =
  fst asRing , commringstr _ _ _ _ _
                 (iscommring (RingStr.isRing (snd asRing))
                             (elimProp2 (λ _ _ → squash/ _ _)
                                        commEq))
   where
       asRing = (CommRing→Ring R) /Ring (CommIdeal→Ideal I)
       _·/_ : fst asRing → fst asRing → fst asRing
       _·/_ = RingStr._·_ (snd asRing)
       commEq : (x y : fst R) → ([ x ] ·/ [ y ]) ≡ ([ y ] ·/ [ x ])
       commEq x y i = [ CommRingStr.·Comm (snd R) x y i ]

[_]/ : {R : CommRing ℓ} {I : IdealsIn R} → (a : fst R) → fst (R / I)
[ a ]/ = [ a ]


--

module Quotient-FGideal-CommRing-Ring
  (A'@(A , Ar) : CommRing ℓ)
  (B'@(B , Br) : Ring ℓ')
  (g'@(g , gr) : RingHom (CommRing→Ring A') B')
  where

  open RingStr Br using (0r)
  open IsRingHom

  module _
    {n : ℕ}
    (v : FinVec A n)
    (gnull : (k : Fin n) → g ( v k) ≡ 0r)
    where

    zeroOnGeneratedIdeal : (n : ℕ) → (x : ⟨ A' ⟩) → x ∈ fst (generatedIdeal A' v) → g' $ x ≡ 0r
    zeroOnGeneratedIdeal n x x∈FGIdeal =
      PT.elim
        (λ _ → isSetRing B' (g' $ x) 0r)
        (λ {(α , isLC) → subst _ (sym isLC) (cancelLinearCombination A' B' g' _ α v gnull)})
        x∈FGIdeal

    inducedHom : RingHom (CommRing→Ring (A' / (generatedIdeal _ v))) B'
    inducedHom = UniversalProperty.inducedHom (CommRing→Ring A') (CommIdeal→Ideal ideal) g' (zeroOnGeneratedIdeal n)
      where ideal = generatedIdeal A' v

module Quotient-FGideal-CommRing-CommRing
  (A'@(A , Ar) : CommRing ℓ)
  (B'@(B , Br) : CommRing ℓ')
  (g'@(g , gr) : CommRingHom A' B')
  {n : ℕ}
  (v : FinVec A n)
  (gnull : (k : Fin n) → g ( v k) ≡ CommRingStr.0r (snd B'))
  where

  f : CommRingHom (A' / (generatedIdeal _ v)) B'
  f = Quotient-FGideal-CommRing-Ring.inducedHom A' (CommRing→Ring B') g' v gnull
