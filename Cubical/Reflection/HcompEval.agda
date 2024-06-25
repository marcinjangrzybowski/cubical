{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Reflection.HcompEval where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Data.List as List
open import Cubical.Data.Nat
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Sigma

open import Agda.Builtin.String
import Agda.Builtin.Reflection as R
open import Cubical.Reflection.Base



t1 : I → I → Type₁
t1 i j = hcomp
  (λ k → λ {
    (i = i0) → compPath-filler (λ _ → Type) (λ _ → Type) k j
   ;(j = i1) → Type
   ;(j = i0)(i = i1) → Type   
     } )
  Type

t1' : I → I → Type₁
t1' i j = hcomp
  (λ k → primPOr (~ i) j
    (λ _ → compPath-filler (λ _ → Type) (λ _ → Type) k j)
    λ _ → Type)
  Type




-- t1≡t1' : ∀ i j → t1 i j ≡ t1' i j
-- t1≡t1' i j = {!!}

toFaces : R.Term → R.Term
toFaces = {!!}

toPrimPOr' : R.Term → R.Term
toPrimPOr' (R.def (quote hcomp) (_ ∷ _ ∷ (R.arg _ dims) ∷ _)) = dims
toPrimPOr' _ =
 ((R.con (quote i0) []))


macro
 -- toPrimPOr : R.Term → R.Term → R.TC Unit
 -- toPrimPOr (R.con (quote zero) []) hole =
 --   R.unify hole (R.con (quote zero) [])
 -- toPrimPOr _ hole = R.unify hole
 --  ((R.con (quote suc) (varg (R.con (quote zero) []) ∷ [])))

   



 toPrimPOr : R.Term → R.Term → R.TC Unit
 toPrimPOr t' hole = do
   t <- R.normalise t'
   R.unify (toPrimPOr' t) hole

-- thm : (a b : Nat) → plus-to-times (a + b) ≡ a * b
-- thm a b = refl

test : I → I → I → I
test i j = {!toPrimPOr
  (compPath-filler (refl {x = Type}) refl i j)!}
