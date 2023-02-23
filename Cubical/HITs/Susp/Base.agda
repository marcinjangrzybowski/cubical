{-# OPTIONS --safe #-}
module Cubical.HITs.Susp.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Path

open import Cubical.Data.Bool
open import Cubical.Data.Empty

open import Cubical.HITs.S1
open import Cubical.HITs.S2.Base
open import Cubical.HITs.S3

open Iso

private
  variable
    ℓ ℓ' : Level

data Susp (A : Type ℓ) : Type ℓ where
  north : Susp A
  south : Susp A
  merid : (a : A) → north ≡ south

Susp∙ : (A : Type ℓ) → Pointed ℓ
Susp∙ A = Susp A , north

-- induced function
suspFun : {A : Type ℓ} {B : Type ℓ'} (f : A → B)
       → Susp A → Susp B
suspFun f north = north
suspFun f south = south
suspFun f (merid a i) = merid (f a) i

BoolIsoSusp⊥ : Iso Bool (Susp ⊥)
fun BoolIsoSusp⊥ = λ {true  → north; false → south}
inv BoolIsoSusp⊥ = λ {north → true;  south → false}
rightInv BoolIsoSusp⊥ = λ {north → refl;  south → refl}
leftInv BoolIsoSusp⊥  = λ {true  → refl;  false → refl}

Bool≃Susp⊥ : Bool ≃ Susp ⊥
Bool≃Susp⊥ = isoToEquiv BoolIsoSusp⊥

SuspBool : Type₀
SuspBool = Susp Bool

SuspBool→S¹ : SuspBool → S¹
SuspBool→S¹ north = base
SuspBool→S¹ south = base
SuspBool→S¹ (merid false i) = loop i
SuspBool→S¹ (merid true i)  = base

S¹→SuspBool : S¹ → SuspBool
S¹→SuspBool base     = north
S¹→SuspBool (loop i) = (merid false ∙ sym (merid true)) i

SuspBool→S¹→SuspBool : (x : SuspBool) → Path _ (S¹→SuspBool (SuspBool→S¹ x)) x
SuspBool→S¹→SuspBool north = refl
SuspBool→S¹→SuspBool south = merid true
SuspBool→S¹→SuspBool (merid false i) j = hcomp (λ k → (λ { (j = i1) → merid false i
                                                         ; (i = i0) → north
                                                         ; (i = i1) → merid true (j ∨ ~ k)}))
                                               (merid false i)
SuspBool→S¹→SuspBool (merid true i) j = merid true (i ∧ j)

S¹→SuspBool→S¹ : (x : S¹) → SuspBool→S¹ (S¹→SuspBool x) ≡ x
S¹→SuspBool→S¹ base       = refl
S¹→SuspBool→S¹ (loop i) j = hfill (λ k → λ { (i = i0) → base
                                           ; (i = i1) → base })
                                  (inS (loop i)) (~ j)

S¹IsoSuspBool : Iso S¹ SuspBool
fun S¹IsoSuspBool      = S¹→SuspBool
inv S¹IsoSuspBool      = SuspBool→S¹
rightInv S¹IsoSuspBool = SuspBool→S¹→SuspBool
leftInv S¹IsoSuspBool  = S¹→SuspBool→S¹

S¹≃SuspBool : S¹ ≃ SuspBool
S¹≃SuspBool = isoToEquiv S¹IsoSuspBool

S¹≡SuspBool : S¹ ≡ SuspBool
S¹≡SuspBool = ua S¹≃SuspBool

-- Now the sphere

SuspS¹ : Type₀
SuspS¹ = Susp S¹

SuspS¹→S² : SuspS¹ → S²
SuspS¹→S² north = base
SuspS¹→S² south = base
SuspS¹→S² (merid base i) = base
SuspS¹→S² (merid (loop j) i) = surf i j

meridian-contraction : I → I → I → SuspS¹
meridian-contraction i j l = hfill (λ k → λ { (i = i0) → north
                                            ; (i = i1) → merid base (~ k)
                                            ; (j = i0) → merid base (~ k ∧ i)
                                            ; (j = i1) → merid base (~ k ∧ i) })
                                   (inS (merid (loop j) i)) l

S²→SuspS¹ : S² → SuspS¹
S²→SuspS¹ base = north
S²→SuspS¹ (surf i j) = meridian-contraction i j i1


pp1 pp-1 pp0 : Square {A = SuspS¹}
             (λ j → merid base j )
             (λ j → south)
             (λ i → merid base i)
             (λ i → south)
pp0 i j = merid base (j ∨ i)
pp1 i j = merid (loop (j ∧ i)) (j ∨ i)
pp-1 i j = merid (loop (~ (j ∧ i))) (j ∨ i)


data dS² : Type where
 no ce  : dS²
 no≡ce : no ≡ ce
 surf : Square no≡ce refl no≡ce refl

-- ww : Susp S¹ → Type
-- ww north = S¹
-- ww south = S¹
-- ww (merid base i) = {!!}
-- ww (merid (loop i₁) i) = {!!}

-- zz : Susp S¹ → (x : Susp S¹) → x ≡ x
-- zz = {!!}

-- IsoDS²SuspS¹ : Iso dS² (Susp S¹)
-- fun IsoDS²SuspS¹ no = north
-- fun IsoDS²SuspS¹ ce = south
-- fun IsoDS²SuspS¹ (no≡ce i) = merid base i
-- fun IsoDS²SuspS¹ (surf i j) = pp1 i j
-- inv IsoDS²SuspS¹ north = no
-- inv IsoDS²SuspS¹ south = ce
-- inv IsoDS²SuspS¹ (merid base i) = no≡ce i
-- inv IsoDS²SuspS¹ (merid (loop i) j) = no≡ce j
-- rightInv IsoDS²SuspS¹ north = refl
-- rightInv IsoDS²SuspS¹ south = refl
-- rightInv IsoDS²SuspS¹ (merid base i) = refl
-- rightInv IsoDS²SuspS¹ (merid (loop i) j) k = {!merid (loop i) j!}
-- leftInv IsoDS²SuspS¹ no = refl
-- leftInv IsoDS²SuspS¹ ce = refl
-- leftInv IsoDS²SuspS¹ (no≡ce i) j = {!surf (i ∧ j) !}
-- leftInv IsoDS²SuspS¹ (surf i j) k = {!!}

-- dS²Co : dS² → Type
-- dS²Co no = S¹
-- dS²Co ce = S¹
-- dS²Co (no≡ce i) = ua (rotIsEquiv loop) i
-- dS²Co (surf i i₁) = {!!}

-- IsoDS²S² : Iso dS² S²
-- fun IsoDS²S² no = base
-- fun IsoDS²S² so = base
-- fun IsoDS²S² ce = base
-- fun IsoDS²S² (no≡ce i) = base
-- fun IsoDS²S² (ce≡so i) = base
-- fun IsoDS²S² (surf i j) = surf i j 
-- inv IsoDS²S² base = ce
-- inv IsoDS²S² (surf i i₁) = {!!}
-- rightInv IsoDS²S² = {!!}
-- leftInv IsoDS²S² = {!!}


-- pp' : Square {A = SuspS¹}
--              (λ j → merid base j )
--              (λ j → south)
--              (λ i → merid base i)
--              (λ i → south)
-- pp' i j = merid (loop (j ∧ i)) (j ∧ (~ i))


-- S²→SuspS¹' : S² → SuspS¹
-- S²→SuspS¹' base = north
-- S²→SuspS¹' (surf i j) =
--   hcomp
--     ((λ k → λ { (i = i0) → {!!}
--               ; (i = i1) → {!!}
--               ; (j = i0) → {!!}
--               ; (j = i1) → {!!} }))
--     {!!}




S²→SuspS¹→S² : ∀ x → SuspS¹→S² (S²→SuspS¹ x) ≡ x
S²→SuspS¹→S² base k = base
S²→SuspS¹→S² (surf i j) k = SuspS¹→S² (meridian-contraction i j (~ k))

SuspS¹→S²→SuspS¹ : ∀ x → S²→SuspS¹ (SuspS¹→S² x) ≡ x
SuspS¹→S²→SuspS¹ north k = north
SuspS¹→S²→SuspS¹ south k = merid base k
SuspS¹→S²→SuspS¹ (merid base j) k = merid base (k ∧ j)
SuspS¹→S²→SuspS¹ (merid (loop j) i) k = meridian-contraction i j (~ k)

S²IsoSuspS¹ : Iso S² SuspS¹
fun S²IsoSuspS¹      = S²→SuspS¹
inv S²IsoSuspS¹      = SuspS¹→S²
rightInv S²IsoSuspS¹ = SuspS¹→S²→SuspS¹
leftInv S²IsoSuspS¹  = S²→SuspS¹→S²

S²≃SuspS¹ : S² ≃ SuspS¹
S²≃SuspS¹ = isoToEquiv S²IsoSuspS¹

S²≡SuspS¹ : S² ≡ SuspS¹
S²≡SuspS¹ = ua S²≃SuspS¹

-- And the 3-sphere

SuspS² : Type₀
SuspS² = Susp S²

SuspS²→S³ : SuspS² → S³
SuspS²→S³ north = base
SuspS²→S³ south = base
SuspS²→S³ (merid base i) = base
SuspS²→S³ (merid (surf j k) i) = surf i j k

meridian-contraction-2 : I → I → I → I → SuspS²
meridian-contraction-2 i j k l = hfill (λ m → λ { (i = i0) → north
                                                ; (i = i1) → merid base (~ m)
                                                ; (j = i0) → merid base (~ m ∧ i)
                                                ; (j = i1) → merid base (~ m ∧ i)
                                                ; (k = i0) → merid base (~ m ∧ i)
                                                ; (k = i1) → merid base (~ m ∧ i) })
                                       (inS (merid (surf j k) i)) l

S³→SuspS² : S³ → SuspS²
S³→SuspS² base = north
S³→SuspS² (surf i j k) = meridian-contraction-2 i j k i1

S³→SuspS²→S³ : ∀ x → SuspS²→S³ (S³→SuspS² x) ≡ x
S³→SuspS²→S³ base l = base
S³→SuspS²→S³ (surf i j k) l = SuspS²→S³ (meridian-contraction-2 i j k (~ l))

SuspS²→S³→SuspS² : ∀ x → S³→SuspS² (SuspS²→S³ x) ≡ x
SuspS²→S³→SuspS² north l = north
SuspS²→S³→SuspS² south l = merid base l
SuspS²→S³→SuspS² (merid base j) l = merid base (l ∧ j)
SuspS²→S³→SuspS² (merid (surf j k) i) l = meridian-contraction-2 i j k (~ l)

S³IsoSuspS² : Iso S³ SuspS²
fun S³IsoSuspS²      = S³→SuspS²
inv S³IsoSuspS²      = SuspS²→S³
rightInv S³IsoSuspS² = SuspS²→S³→SuspS²
leftInv S³IsoSuspS²  = S³→SuspS²→S³

S³≃SuspS² : S³ ≃ SuspS²
S³≃SuspS² = isoToEquiv S³IsoSuspS²

S³≡SuspS² : S³ ≡ SuspS²
S³≡SuspS² = ua S³≃SuspS²

IsoType→IsoSusp : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → Iso A B → Iso (Susp A) (Susp B)
fun (IsoType→IsoSusp is) north = north
fun (IsoType→IsoSusp is) south = south
fun (IsoType→IsoSusp is) (merid a i) = merid (fun is a) i
inv (IsoType→IsoSusp is) north = north
inv (IsoType→IsoSusp is) south = south
inv (IsoType→IsoSusp is) (merid a i) = merid (inv is a) i
rightInv (IsoType→IsoSusp is) north = refl
rightInv (IsoType→IsoSusp is) south = refl
rightInv (IsoType→IsoSusp is) (merid a i) j = merid (rightInv is a j) i
leftInv (IsoType→IsoSusp is) north = refl
leftInv (IsoType→IsoSusp is) south = refl
leftInv (IsoType→IsoSusp is) (merid a i) j = merid (leftInv is a j) i

IsoSuspS²SuspSuspS¹ : Iso (Susp S²) (Susp (Susp S¹))
IsoSuspS²SuspSuspS¹ = IsoType→IsoSusp S²IsoSuspS¹

IsoS³S3 : Iso S³ (Susp (Susp S¹))
IsoS³S3 = compIso S³IsoSuspS² IsoSuspS²SuspSuspS¹
