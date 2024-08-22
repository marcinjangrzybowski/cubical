{-# OPTIONS --safe -v testMarkVert:3 -v tactic:3 #-}
-- -v 3
module Cubical.Tactics.PathSolver.MonoidalSolver.PathEval where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.List as L
open import Cubical.Data.Nat as ℕ

open import Cubical.Data.Sigma.Base


open import Cubical.Reflection.Base renaming (v to 𝒗)
open import Cubical.Reflection.Sugar
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_ ; _<_ to _<ℕ_)

import Agda.Builtin.Reflection as R

open import Cubical.Tactics.PathSolver.Reflection
open import Cubical.Tactics.PathSolver.Path

open import Agda.Builtin.String

open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Error
open import Cubical.Tactics.Reflection.Dimensions
open import Cubical.Tactics.Reflection.QuoteCubical


data ASTMarkers : Type where
 PathWrap' FillWrap' CompWrap' : ASTMarkers

PathWrap FillWrap CompWrap : ASTMarkers
PathWrap = PathWrap'
FillWrap = FillWrap'
CompWrap = CompWrap'

WTerm = R.Term
CTerm = R.Term


pattern fw[1,_] x = R.def (quote FillWrap) (R.lit (R.name (quote true)) v∷ v[ x ])
pattern fw[0,_] x = R.def (quote FillWrap) (R.lit (R.name (quote false)) v∷ v[ x ])


pattern pw[_] x = R.def (quote PathWrap) (x v∷ [])
pattern pwd args = R.def (quote PathWrap) args


pattern cwd args = R.def (quote CompWrap) args

pattern cw[] = R.def (quote CompWrap) []
pattern cw[_] x = R.def (quote CompWrap) (x v∷ [])
pattern cw xs = R.def (quote CompWrap) xs
pattern _∷cw_ x xs = R.def (quote CompWrap) (x v∷ xs)


intervalTest : ℕ → R.Term → Bool
intervalTest _ (R.def (quote _∨_) _) = true
intervalTest _ (R.def (quote _∧_) _) = true
intervalTest _ (R.def (quote ~_) _) = true
intervalTest n (R.var k []) = n =ℕ k
intervalTest _ _ = false


wrapPaths : R.Term → WTerm
wrapPaths = atVarOrConM' f h g
 where
  f : ℕ → ℕ → List (R.Arg R.Term) → Maybe R.Term
  f n v args =
     if any? (L.map (intervalTest n ∘S unArg) args)
     then  just pw[ (R.var (v + n) args) ]
     else nothing

  h : ℕ → R.Name → List (R.Arg R.Term) → Maybe R.Term
  h n nm args =
     if any? (L.map (intervalTest n ∘S unArg) args)
     then  just pw[ (R.con nm args) ]
     else nothing

  g : ℕ → R.Name → List (R.Arg R.Term) → Maybe R.Term
  g n nm args =
     if any? (L.map (intervalTest n ∘S unArg) args)
     then  just pw[ (R.def nm args) ]
     else nothing

wrapFills : R.Term → WTerm
wrapFills = atVarOrConM' f h g
 where
  f : ℕ → ℕ → List (R.Arg R.Term) → Maybe R.Term
  f n v args =
     if any? (L.map (intervalTest n ∘S unArg) args)
     then  just fw[1, pw[ (R.var (v + n) args) ] ]
     else nothing

  h : ℕ → R.Name → List (R.Arg R.Term) → Maybe R.Term
  h n nm args =
     if any? (L.map (intervalTest n ∘S unArg) args)
     then  just fw[1, pw[ (R.con nm args) ] ]
     else nothing


  g : ℕ → R.Name → List (R.Arg R.Term) → Maybe R.Term
  g n nm args =
     if any? (L.map (intervalTest n ∘S unArg) args)
     then  just fw[1, pw[ (R.def nm args) ] ]
     else nothing



dropPathWraps : CTerm → R.Term
dropPathWraps = atVarOrDefM {{_}} {{RawMonadIdentityM}}
  (λ _ v _ argsM → R.var v argsM)
  λ _ d _ argsM → w (R.def d argsM)

 where
  w : R.Term → R.Term
  w pw[ x ] = x
  w x = x


absorb : ℕ → WTerm → CTerm → R.TC CTerm


absorbStep : ℕ → WTerm → WTerm → R.TC (Maybe CTerm)
absorbStep n (cwd _) _ = R.typeError [ "cwd in absorbStep" ]ₑ
absorbStep n _ (cwd _) = R.typeError [ "cwd in absorbStep" ]ₑ
absorbStep zero pw[ x ] pw[ y ] = do
  -- R.debugPrint "testMarkVert" 3 $ "-----" ∷nl x ∷nl "** \n" ∷nl [ y ]ₑ
  (if_then (just fw[0, y ]) else nothing) <$> unifyTest (suc zero) x (invVar zero y)
absorbStep (suc _) pw[ x ] pw[ y ] =
 R.typeError [ "absorbStep: todo - paths under abstraction" ]ₑ
absorbStep n x pw[ y ] = pure nothing
absorbStep n pw[ x ] y = pure nothing
absorbStep n (pwd _) _ = R.typeError [ "pwd1 in absorbStep!" ]ₑ
absorbStep n _ (pwd _) = R.typeError [ "pwd2 in absorbStep!" ]ₑ
absorbStep n x y = just <$> h x y
 where

 hs : R.Sort → R.Sort → R.TC R.Sort
 h : WTerm → WTerm → R.TC CTerm

 ha : List (R.Arg R.Term) → List (R.Arg R.Term) → R.TC (List (R.Arg R.Term))
 ha [] [] = pure []
 ha (R.arg ax x ∷ xs) (R.arg _ x' ∷ xs')  =
   ⦇ ⦇ R.arg ⦇ ax ⦈ (absorb n x x') ⦈  ∷ ha xs xs' ⦈
 ha _ _ = R.typeError [ "absorbStep: ha-failed" ]ₑ

 h (R.var x args) (R.var _ args') = R.var x <$> ha args args'
 h (R.con c args) (R.con _ args') = R.con c <$> ha args args'
 h (R.def f args) (R.def _ args') = R.def f <$> ha args args'
 h (R.lam v (R.abs ai t)) (R.lam v' (R.abs _ t')) =
    ⦇ R.lam ⦇ v ⦈ ⦇ R.abs ⦇ ai ⦈ (absorb (suc n) t t') ⦈  ⦈
 h (R.pat-lam cs args) (R.pat-lam cs' args') = R.typeError [ "absorbStep: todo - patLamb" ]ₑ
 h (R.pi (R.arg ai a) (R.abs bi b)) (R.pi (R.arg ai' a') (R.abs bi' b')) =
     ⦇ R.pi ⦇ R.arg ⦇ ai ⦈ (absorb n a a') ⦈ ⦇ R.abs ⦇ bi ⦈ (absorb (suc n) b b') ⦈  ⦈
 h (R.agda-sort s) (R.agda-sort s') = R.agda-sort <$> hs s s'
 h (R.lit l) (R.lit l') = pure (R.lit l)
 h (R.meta x x₂) (R.meta x' x₂') = R.typeError [ "absorbStep: todo - meta" ]ₑ
 h R.unknown R.unknown = ⦇ R.unknown ⦈
 h t t' = R.typeError
   $ "absorbStep: h-failed" ∷nl t ∷nl "---" ∷nl [ t' ]ₑ

 hs (R.set t) (R.set t') = R.set <$> absorb n t t'
 hs (R.lit n) (R.lit _) = pure (R.lit n)
 hs (R.prop t) (R.prop t') = R.prop <$> absorb n t t'
 hs (R.propLit n) (R.propLit n') = pure (R.propLit n)
 hs (R.inf n) (R.inf n') = pure (R.inf n)
 hs R.unknown R.unknown = pure (R.unknown)
 hs _ _ = R.typeError [ "absorbStep: hs-failed" ]ₑ

absorbStep' : ℕ → WTerm → WTerm → R.TC (Maybe CTerm)
absorbStep' n x y =
  w (hasVar zero x) (hasVar zero y)

 where
  w : Bool → Bool → R.TC (Maybe CTerm)
  w true true = absorbStep n x y
  w true false = pure $ just (wrapFills (dropPathWraps x))
  w false false = pure (just x)
  w false true = pure (just y)

absorb _ _ cw[] = R.typeError [ "cw[] in absorb!" ]ₑ
absorb _ _ (cw[ y ]) = R.typeError [ "cw[_] in absorb!" ]ₑ
absorb n x (y ∷cw ys) =
 absorbStep' n x y >>=
  Mb.rec (pure (cw (fw[1, x ] v∷ y v∷ ys))) (pure ∘S _∷cw ys)
absorb n x y = absorbStep' n x y >>=
  Mb.rec (pure (fw[1, x ] ∷cw v[ y ]))
          pure


cTermEnd : CTerm → R.TC (Maybe WTerm)
cTermEnd = fixMb ∘S
  atVarOrDefM (λ _ v _ argM → R.var v <$> argM)
     (λ n def _ argsM → ((R.def def) <$> argsM) >>= reduceComps n) ∘S evFills

 where
  evFills : CTerm → CTerm
  evFills =
   atVarOrM
    (λ _ _ _ → nothing )
    λ _ nm args → atD (R.def nm args)

   where
    atD : R.Term → Maybe R.Term
    atD fw[1, x ] = just x
    atD fw[0, x ] = just (replaceVarWithCon (λ { zero → just (quote i1) ; _ → nothing }) x)
    atD _ = nothing

  reduceComps : ℕ → R.Term → R.TC R.Term
  reduceComps _ cw[] = R.typeError [ "cTermEnd : reduceComps : unexpected cw[]" ]ₑ
  reduceComps n cw[ p ] = pure p --if (hasVar n p) then  else {!!}
  reduceComps n t@(p ∷cw ps@((R.arg _ ps0) ∷ _)) =
   if (hasVar n p) then pure t  else
    (pure (if length ps =ℕ 1 then ps0 else cw ps))
  reduceComps _ x = pure x

  fixMb : R.TC WTerm → R.TC (Maybe WTerm)
  fixMb x = x >>= λ x → pure $ if (hasVar 0 x) then just x else nothing

data FillWrapEval : Type where
 headFW dropFW : FillWrapEval

dropFillWraps : FillWrapEval -> CTerm → R.Term
dropFillWraps fwe = atVarOrDefM {{_}} {{RawMonadIdentityM}}
  (λ _ v _ argsM → R.var v argsM)
  λ _ d _ argsM → w fwe (R.def d argsM)

 where

  lift0Dim = remapVars λ { zero → suc zero ; n → n }

  w : FillWrapEval → R.Term → R.Term
  -- w offsetFW fw[1, x ] = lift0Dim x
  -- w offsetFW fw[0, x ] = invVar 1 (lift0Dim x)
  w headFW fw[1, x ] = replaceVarWithTerm
    (λ { zero → just (R.def (quote _∨_) (𝒗 1 v∷ v[ 𝒗 0 ]))
       ; _ → nothing }) x
  w headFW fw[0, x ] = replaceVarWithTerm
    (λ { zero → just (R.def (quote _∨_) ((R.def (quote ~_) v[ 𝒗 1 ]) v∷ v[ 𝒗 0 ])) ; _ → nothing }) x
  w dropFW fw[1, x ] = x
  w dropFW fw[0, x ] = x
  w _ x = x


transpose : ∀ {ℓ} {A : Type ℓ} → A → List (List A) → List (List A)
transpose default [] = [ [] ]
transpose default xss@(xs ∷ _) =
  L.map (λ (k , ys) → L.map (λ ys → lookupAlways default ys k) xss ) (zipWithIndex xs)

fill-flatten' : CTerm → List R.Term
fill-flatten' = hTop ∘S atVarOrConOrDefMmp
  (λ _ v _ _ args' → R.var v <$> (h args'))
  (λ _ c _ _ args' → R.con c <$> (h args'))
  df ∘S dropPathWraps ∘S liftVarsFrom 1 1

 where



 fill-offsetPa' : ℕ → List (R.Arg R.Term) → List (R.Arg R.Term)
 fill-offsetPa' n xs =
  let hd = fromJust-def (varg (R.lit (R.string "fatal in PathEval - offsetPa'")))
            (lookup xs zero)
      hs* = mapArg (dropFillWraps headFW) hd
      hd' = mapArg
             (replaceVarWithCon (λ { zero → just (quote i0) ; _ → nothing })) hs*
  in repeat (n ∸ length xs ) hd' ++
       hs* ∷ L.map (mapArg (dropFillWraps dropFW)) (tail xs)


 h : List (List (R.Arg R.Term)) → List (List (R.Arg R.Term))
 h xs =
  let maxL = foldr (max ∘S length) 1 xs
      xs' = L.map (fill-offsetPa' maxL) xs
  in transpose ((varg (R.lit (R.string "fatal in PathEval - flatten")))) xs'

 hTop : List R.Term → List R.Term
 hTop = L.map (Mb.fromJust-def ( (R.lit (R.string "imposible in fill-flatten'")) )
   ∘S map-Maybe (unArg) ∘S flip lookup zero) ∘S h ∘S [_] ∘S L.map varg

 df : ℕ →
        R.Name →
        List (R.Arg R.Term) →
        List (List (R.Arg R.Term)) →
        List (List (R.Arg R.Term)) → List R.Term
 df _ (quote CompWrap) _ _ args' = unArg <$> join args'
 df _ nm _ _ args' = R.def nm <$> (h args')



foldPath : List R.Term → R.Term
foldPath [] = q[ refl ]
foldPath (x ∷ []) = vlam "𝓲" x
foldPath (x ∷ xs@(_ ∷ _)) = R∙' (vlam "𝓲" x) (foldPath xs)

foldPath' : List R.Term → Maybe R.Term
foldPath' [] = nothing
foldPath' (x ∷ []) = just $ vlam "𝓲" x
foldPath' (x ∷ xs@(_ ∷ _)) = just $ R∙' (vlam "𝓲" x) (foldPath xs)

fillHeadTrm : R.Term → Maybe R.Term → R.TC R.Term
fillHeadTrm p nothing = pure (vlam "𝒋" (vlam "𝒊" p))
fillHeadTrm p (just q) = do
   p₀ ← hasVar 0
       <$> (addNDimsToCtx 2 $ R.normalise
        (replaceVarWithCon (λ { (suc zero) → just (quote i0) ; _ → nothing }) p))
   p₁ ←  hasVar 0 <$> (addNDimsToCtx 2 $ R.normalise
        (replaceVarWithCon (λ { (suc zero) → just (quote i1) ; _ → nothing }) p))
   h p₀ p₁

 where
  h : Bool → Bool → R.TC R.Term
  h false false = R.typeError [ "imposible in fillHeadTrm" ]ₑ
  h false true = pure $ R.def (quote _∙f1_) (vlam "𝒋" (vlam "𝒊" p) v∷ v[ vlam "𝒋" q ])
  h true false = pure $ R.def (quote _∙f0_) (vlam "𝒋" (vlam "𝒊" p) v∷ v[ vlam "𝒋" q ])
  h true true = pure $ vlam "𝒋" (R∙' (vlam "𝓲" p) q)
