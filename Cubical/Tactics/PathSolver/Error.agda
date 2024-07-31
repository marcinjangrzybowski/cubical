{-# OPTIONS --safe  #-} 

module Cubical.Tactics.PathSolver.Error where


import Agda.Builtin.Reflection as R
open import Agda.Builtin.String
open import Agda.Builtin.Char

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function


open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Bool

open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.Reflection.Utilities

record ToErrorPart {ℓ} (A : Type ℓ) : Type ℓ where
 field
   toErrorPart : A → R.ErrorPart

open ToErrorPart

infixr 5 _∷ₑ_ _∷nl_ _++ₑ_

_∷ₑ_ :  ∀ {ℓ} {A : Type ℓ} → {{ToErrorPart A}} → A → List R.ErrorPart → List R.ErrorPart
_∷ₑ_  ⦃ tep ⦄ x = (toErrorPart tep x) ∷_

_++ₑ_ :  ∀ {ℓ} {A : Type ℓ} → {{ToErrorPart A}} → List A → List R.ErrorPart → List R.ErrorPart
_++ₑ_  ⦃ tep ⦄ x = (map (toErrorPart tep) x) ++_

[_]ₑ :  ∀ {ℓ} {A : Type ℓ} → {{ToErrorPart A}} → A → List R.ErrorPart
[_]ₑ = _∷ₑ []

instance
 ToErrorPartString : ToErrorPart String
 ToErrorPart.toErrorPart ToErrorPartString = R.strErr
 
 ToErrorPartChar : ToErrorPart Char
 ToErrorPart.toErrorPart ToErrorPartChar = R.strErr ∘S primStringFromList ∘S [_] 


 ToErrorPartℕ : ToErrorPart ℕ
 ToErrorPart.toErrorPart ToErrorPartℕ = R.strErr ∘ primShowNat

 ToErrorPartBool : ToErrorPart Bool
 ToErrorPart.toErrorPart ToErrorPartBool = R.strErr ∘ (if_then "𝟙" else "𝟘")


 ToErrorPartTerm : ToErrorPart R.Term
 ToErrorPart.toErrorPart ToErrorPartTerm = R.termErr

 ToErrorPartName : ToErrorPart R.Name
 ToErrorPart.toErrorPart ToErrorPartName = R.nameErr

 ToErrorPartErrorPart : ToErrorPart R.ErrorPart
 ToErrorPart.toErrorPart ToErrorPartErrorPart x = x


_∷nl_ :  ∀ {ℓ} {A : Type ℓ} → {{ToErrorPart A}} → A → List R.ErrorPart → List R.ErrorPart
_∷nl_  x y = x ∷ₑ "\n" ∷ₑ y


niceAtomList : List (R.Term) → List R.ErrorPart
niceAtomList = h 0
 where
  h : _ → _
  h _  [] = []
  h k (x ∷ xs) = (mkNiceVar k  <> " = ") ∷ₑ x ∷ₑ  "\n"  ∷ₑ h (suc k) xs



unArgs : List (R.Arg (R.Term)) → List R.ErrorPart
unArgs [] = []
unArgs (R.arg i x ∷ x₁) = x ∷ₑ unArgs x₁


getConTail : R.Term → List R.ErrorPart
getConTail (R.var x args) = "𝒗𝒂𝒓 " ∷ₑ x ∷ₑ " " ∷ₑ unArgs args
getConTail (R.con c args) = "𝒄𝒐𝒏 " ∷ₑ c ∷ₑ " " ∷ₑ unArgs args
getConTail (R.def f args) = "𝒅𝒆𝒇 " ∷ₑ f ∷ₑ " " ∷ₑ unArgs args
getConTail (R.lam v₁ t) = [ "𝒍𝒂𝒎" ]ₑ
getConTail (R.pat-lam cs args) = [ "𝒑𝒂𝒕" ]ₑ
getConTail (R.pi a b) = [ "𝒑𝒊" ]ₑ
getConTail (R.agda-sort s) = [ "𝒔𝒐𝒓𝒕" ]ₑ
getConTail (R.lit l) = [ "𝒍𝒊𝒕" ]ₑ
getConTail (R.meta x x₁) = [ "𝒎𝒆𝒕𝒂" ]ₑ
getConTail R.unknown = [ "𝒖𝒏𝒌𝒏𝒐𝒘𝒏" ]ₑ
-- getConTail _ = "other..." ∷ₑ []

renderTerm : R.Term → R.TC String
renderTerm = R.formatErrorParts ∘ [_]ₑ

renderArg : R.Arg R.Term → R.TC String
renderArg (R.arg i x) = renderTerm x


stringLength : String → ℕ
stringLength = length ∘S primStringToList


indent' : Bool → Char → ℕ → String → String
indent' _ _ zero x = x 
indent' b ch k =
  primStringFromList ∘S
   (if b then ((ch ∷_) ∘S (ind ++_)) else (idfun _)) ∘S h ∘S primStringToList

  where
  ind = repeat k ' '

  h : List Char → List Char
  h [] = []
  h (x ∷ xs) with primCharEquality x '\n'
  ... | false = x ∷ h xs
  ... | true =  '\n' ∷ ch ∷ ind ++ h xs
    -- {!!} ++ h xs

indent = indent' true

offsetStr : ℕ → String → String
offsetStr k =   primStringFromList ∘S offset ' ' k ∘S primStringToList

offsetStrR : ℕ → String → String
offsetStrR k =   primStringFromList ∘S offsetR ' ' k ∘S primStringToList
