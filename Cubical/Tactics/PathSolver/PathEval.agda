{-# OPTIONS --safe -v testMarkVert:3 -v tactic:3 #-} 
-- -v 3 
module Cubical.Tactics.PathSolver.PathEval where

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
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_ ; _<_ to _<ℕ_)

import Agda.Builtin.Reflection as R

open import Cubical.Tactics.PathSolver.Reflection
-- open import Cubical.Tactics.Reflection 
open import Agda.Builtin.String
-- open import Agda.Builtin.Char
open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.PathSolver.Error
open import Cubical.Tactics.PathSolver.Dimensions
open import Cubical.Tactics.PathSolver.QuoteCubical


-- absorbStep : R.Term → R.Term →
--   R.TC ((Maybe (R.Term × R.Term)) ×
--        (R.Term × Maybe R.Term)
--        × Maybe R.Term) 
-- absorbStep = {!!} 

-- absorb : R.Term → List R.Term → R.TC ((List (R.Term × Maybe Bool)) × List R.Term)
-- absorb y [] = pure $ [ ({!!} , just true) ] , [ y ] 
-- absorb y (x ∷ xs) = do
--   preT , (atT , atT1) , postT ← absorbStep x y
--   (xs' , zs')  ← Mb.rec (pure $ (L.map ((_, nothing) ∘S liftVars) xs) , xs) (λ y' → absorb y' xs) postT
--   pure ((maybeToList (map-Maybe ((_, just true) ∘S fst) preT) ++
--                (atT , caseMaybe (just false) nothing atT1) ∷ xs' ,
--          maybeToList (map-Maybe snd preT) ++ maybeToList atT1 ++ zs') )
--   -- pure {!!}


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



-- pattern pw[] = R.def (quote PathWrap) []   

pattern pw[_] x = R.def (quote PathWrap) (x v∷ [])   
pattern pwd args = R.def (quote PathWrap) args

-- pattern pw xs = R.def (quote PathWrap) xs

-- pattern _∷pw_ x xs = R.def (quote PathWrap) (x v∷ xs)  


pattern cwd args = R.def (quote CompWrap) args

pattern cw[] = R.def (quote CompWrap) []   
pattern cw[_] x = R.def (quote CompWrap) (x v∷ [])   
pattern cw xs = R.def (quote CompWrap) xs
pattern _∷cw_ x xs = R.def (quote CompWrap) (x v∷ xs)  




                                 -- just - merged
                                 -- nothing - cons



-- module WrapPaths where

--  wp : ℕ → R.Term → R.Term
--  wp = {!!}

-- record WTerm : Type where
--  constructor wterm
--  field
--   term : R.Term 

-- open WTerm

-- _∙■_

_∙f0_ : ∀ {ℓ} {A : Type ℓ} →
         ∀ {x₀ y₀ y₁ z : A}
         → {p₀ : x₀ ≡ y₀} {q₀ : y₀ ≡ z} {q₁ : y₁ ≡ z}
         → {r : x₀ ≡ y₁} {y≡ : y₀ ≡ y₁}
         → Square p₀ (λ _ → y₁)  r y≡
         → Square q₀ q₁ y≡ (λ _ → z)

         → Square (p₀ ∙' q₀) q₁ r λ _ → z
(u ∙f0 v) j i =
  hcomp (λ k → primPOr (~ i) (i ∨ j) (λ _ → u j (~ k)) λ _ → v j i)
        (v j i)

_∙f1_ : ∀ {ℓ} {A : Type ℓ} →
         ∀ {x₁ y₀ y₁ z : A}
         → {p₁ : x₁ ≡ y₁} {q₀ : y₀ ≡ z} {q₁ : y₁ ≡ z}
         → {r : y₀ ≡ x₁} {y≡ : y₀ ≡ y₁}
         → Square (λ _ → y₀) p₁ r y≡
         → Square q₀ q₁ y≡ (λ _ → z)

         → Square q₀ (p₁ ∙' q₁) r λ _ → z
(u ∙f1 v) j i =
    hcomp (λ k → primPOr (~ i) (i ∨ (~ j)) (λ _ → u j (~ k)) λ _ → v j i)
        (v j i)



_∙■_ : ∀ {ℓ} {A : Type ℓ} →
         ∀ {x y z : A}
         → {p : x ≡ y} {q : y ≡ z} {r : y ≡ z} {s : x ≡ z}
         → Square s r p (λ _ → z) 
         → Square r refl q refl

         → Square s (λ _ → z)  (p ∙ q) (λ _ → z)
(u ∙■ v) j i = 
    hcomp (λ k → primPOr j (i ∨ (~ j)) (λ _ → v k i) λ _ → u j i)
        (u j i)

_∙∙■_∙∙■_ : ∀ {ℓ} {A : Type ℓ} →
         ∀ {x x₀ x₁ x₂ x₃ : A}
         → {p₀ : x₀ ≡ x₁} {p₁ : x₁ ≡ x₂} {p₂ : x₂ ≡ x₃}
           {q₀ : x₀ ≡ x} {q₁ : x₁ ≡ x} {q₂ : x₂ ≡ x} {q₃ : x₃ ≡ x}
         → Square q₀ q₁ p₀ refl  
         → Square q₁ q₂ p₁ refl
         → Square q₂ q₃ p₂ refl
         → Square q₀ q₃ (p₀ ∙∙ p₁ ∙∙ p₂) refl 
_∙∙■_∙∙■_ {x = x} s₀ s₁ s₂ j i = 
  hcomp (λ k → λ where
     (j = i0) → s₀ (~ k) i 
     (j = i1) → s₂ k i 
     (i = i1) → x 
             ) (s₁ j i)

◪→≡ : ∀ {ℓ} {A : Type ℓ} {x y : A} {p p' : x ≡ y} →
           Square p' refl p refl → p ≡ p' 
◪→≡ s i j = 
   hcomp (λ k → λ where
     (j = i0) → s i0 (i ∧ ~ k)
     (i = i1) → s i0 (j ∨ ~ k)
     (i = i0) → s j i ; (j = i1) → s j i) (s j i)

◪→◪→≡ : ∀ {ℓ} {A : Type ℓ} {x y : A} {p₀ p₁ p : x ≡ y}
         → Square p refl p₀ refl
         → Square p refl p₁ refl
         → p₀ ≡ p₁ 
◪→◪→≡ {y = y} {p = p} s₀ s₁ i j =
   hcomp
    (λ k → primPOr (~ i ∨ ~ j ∨ j) i (λ _ →  s₀ j (~ k))
         λ _ → s₁ j (~ k)) y

comp₋₀ : ∀ {ℓ} {A : Type ℓ} →
    {a a₀₀ : A} {a₀₋ : a₀₀ ≡ a}
  {a₁₀ : A} {a₁₋ : a₁₀ ≡ a} 
  {a₋₀ a₋₀' : a₀₀ ≡ a₁₀} 
  → Square a₀₋ a₁₋ a₋₀ refl
  → a₋₀' ≡ a₋₀
  → Square a₀₋ a₁₋ a₋₀' refl
comp₋₀ s p i j =
  hcomp (λ k → primPOr (~ j) (j ∨ i ∨ ~ i) (λ _ → p (~ k) i) λ _ → s i j)  (s i j)

comp₋₀' : ∀ {ℓ} {A : Type ℓ} →
    {a a₀₀ : A} {a₀₋ : a₀₀ ≡ a}
  {a₁₀ : A} {a₁₋ : a₁₀ ≡ a} 
  {a₋₀ a₋₀' : a₀₀ ≡ a₁₀} 
  → Square a₀₋ a₁₋ a₋₀ refl
  → a₋₀ ≡ a₋₀'
  → Square a₀₋ a₁₋ a₋₀' refl
comp₋₀' s p i j =
  hcomp (λ k → primPOr (~ j) (j ∨ i ∨ ~ i) (λ _ → p k i) λ _ → s i j)  (s i j)

◪mkSq : ∀ {ℓ} {A : Type ℓ} →
    {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ p₁₀ : a₁₀ ≡ a₁₁} 
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ p₀₁ : a₀₁ ≡ a₁₁}
  → {p : a₀₀ ≡ a₁₁}
  → Square p p₀₁ a₀₋ refl
  → Square p₁₀ refl a₁₋ refl
  → Square p p₁₀ a₋₀ refl
  → Square  p₀₁ refl a₋₁ refl
  → Square a₀₋ a₁₋ a₋₀ a₋₁  
◪mkSq {a₁₁ = a₁₁} s₀₋ s₁₋ s₋₀ s₋₁ i j =
  hcomp (λ k → λ where
     (i = i0) → s₀₋ j (~ k)
     (i = i1) → s₁₋ j (~ k)
     (j = i0) → s₋₀ i (~ k)
     (j = i1) → s₋₁ i (~ k))
    a₁₁

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


-- absorb : WTerm → CTerm → R.TC CTerm
-- absorb _ pw[] = R.typeError [ "pw[] in absorb! 1" ]ₑ
-- absorb pw[] _ = R.typeError [ "pw[] in absorb! 0" ]ₑ
-- absorb (x ∷pw (_ ∷ _)) _ = R.typeError [ "pw in absorb! 0" ]ₑ
-- absorb x (y ∷pw ys) =
--   absorbStep x pw[ y ]
--   >>= Mb.rec (pure (pw (x v∷ y v∷ ys))) (pure ∘S _∷pw ys) 
-- absorb x y =
--  absorbStep x y >>=
--   Mb.rec (R.typeError [ "imposible (absorb x y)" ]ₑ)
--           pure


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
  





fillStepCT : R.Term → (Maybe CTerm) → R.TC (Maybe CTerm)
fillStepCT x =
  Mb.rec
    (if (hasVar zero x) then pure (just (wrapFills x)) else pure nothing)
    (if (hasVar zero x) then (λ xs' → just <$> (absorb 0 (wrapPaths x) xs')) else pure ∘S just )




foldCT : List R.Term → R.TC (Maybe CTerm)
foldCT [] = pure nothing
foldCT (x ∷ xs) = (foldCT xs) >>= 
  fillStepCT x
   >>= Mb.rec (pure nothing) (cTermEnd)


fillFoldCT' : Maybe CTerm → List R.Term →  R.TC (Maybe CTerm × List (Maybe CTerm))
fillFoldCT' nothing [] = pure (nothing , [] )
fillFoldCT' mbct [] = R.typeError [ "iimposible fillFOldCT'" ]ₑ
fillFoldCT' mbct (x ∷ xs) = do
  (mbct' , xs') ← fillFoldCT' mbct xs
   
  mbct'' ← fillStepCT x mbct'
  -- R.debugPrint "testMarkVert" 3 $ Mb.rec [ "nothing" ]ₑ [_]ₑ mbct''
  ⦇ (Mb.rec (pure nothing) cTermEnd mbct'') , pure (mbct'' ∷ xs') ⦈

fillFoldCT : List R.Term → R.TC (List (Maybe CTerm))
fillFoldCT = (snd <$>_) ∘S fillFoldCT' nothing


data FillWrapEval : Type where
 -- offsetFW
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
  -- L.map (flip (lookupAlways default) zero) xs ∷
  --  {!transpose L.map ?!} 

-- cTermLength : CTerm → ℕ
-- cTermLength t = snd $ runIdentity $ (unwrap (atVarOrDefM f g t) zero)
--   where
--     f : ℕ → ℕ → List (R.Arg R.Term)
--       → ([ State₀T ℕ RMT IdentityF ] List (R.Arg R.Term))
--       → ([ State₀T ℕ RMT IdentityF ] R.Term)
--     f _ v _ argsM = R.var v <$> argsM

--     g : ℕ → R.Name → List (R.Arg R.Term)
--       → ([ State₀T ℕ RMT IdentityF ] List (R.Arg R.Term))
--       → ([ State₀T ℕ RMT IdentityF ] R.Term)
--     g _ (quote CompWrap) _ argsM = argsM >>=
--       (λ args' → (modify (max (length args'))) >>
--          pure (R.def (quote CompWrap) args'))
--     g _ nm _ argsM = R.def nm <$> argsM


offsetPa : ℕ → List (R.Arg R.Term) → List (R.Arg R.Term) 
offsetPa n xs =
 let lst = fromMaybe (varg (R.lit (R.string "fatal in PathEval - offsetPa")))
           (lookup xs (predℕ (length xs)))
     lst' = R.arg (argInfo lst)
       ((replaceVarWithCon (λ { zero → just (quote i1) ; _ → nothing }) (unArg lst)))
 in xs ++ repeat (n ∸ length xs ) lst'

offsetPa' : ℕ → List (R.Arg R.Term) → List (R.Arg R.Term) 
offsetPa' n xs =
 let hd = fromMaybe (varg (R.lit (R.string "fatal in PathEval - offsetPa'")))
           (lookup xs zero)
     hd' = R.arg (argInfo hd)
            ((replaceVarWithCon (λ { zero → just (quote i0) ; _ → nothing }) (unArg hd)))
 in repeat (n ∸ length xs ) hd' ++ xs 


flatten : CTerm → List R.Term
flatten = atVarOrConOrDefMmp
  (λ _ v _ _ args' → R.var v <$> (h args'))
  (λ _ c _ _ args' → R.con c <$> (h args'))
  df ∘S dropPathWraps

 where
 h : List (List (R.Arg R.Term)) → List (List (R.Arg R.Term))
 h xs =
  let maxL = foldr (max ∘S length) 1 xs
      xs' = L.map (offsetPa maxL) xs
  in transpose ((varg (R.lit (R.string "fatal in PathEval - flatten")))) xs'

 df : ℕ →
        R.Name →
        List (R.Arg R.Term) →
        List (List (R.Arg R.Term)) →
        List (List (R.Arg R.Term)) → List R.Term
 df _ (quote CompWrap) _ _ args' = unArg <$> join args'
 df _ nm _ _ args' = R.def nm <$> (h args')

flatten' : CTerm → List R.Term
flatten' = atVarOrConOrDefMmp
  (λ _ v _ _ args' → R.var v <$> (h args'))
  (λ _ c _ _ args' → R.con c <$> (h args'))
  df ∘S dropPathWraps

 where
 h : List (List (R.Arg R.Term)) → List (List (R.Arg R.Term))
 h xs =
  let maxL = foldr (max ∘S length) 1 xs
      xs' = L.map (offsetPa' maxL) xs
  in transpose ((varg (R.lit (R.string "fatal in PathEval - flatten")))) xs'
  
 df : ℕ →
        R.Name →
        List (R.Arg R.Term) →
        List (List (R.Arg R.Term)) →
        List (List (R.Arg R.Term)) → List R.Term
 df _ (quote CompWrap) _ _ args' = unArg <$> join args'
 df _ nm _ _ args' = R.def nm <$> (h args')

fill-flatten' : CTerm → List R.Term
fill-flatten' = hTop ∘S atVarOrConOrDefMmp
  (λ _ v _ _ args' → R.var v <$> (h args'))
  (λ _ c _ _ args' → R.con c <$> (h args'))
  df ∘S dropPathWraps ∘S liftVarsFrom 1 1

 where



 fill-offsetPa' : ℕ → List (R.Arg R.Term) → List (R.Arg R.Term) 
 fill-offsetPa' n xs =
  let hd = fromMaybe (varg (R.lit (R.string "fatal in PathEval - offsetPa'")))
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
 hTop = L.map (Mb.fromMaybe ( (R.lit (R.string "imposible in fill-flatten'")) )
   ∘S map-Maybe (unArg) ∘S flip lookup zero) ∘S h ∘S [_] ∘S L.map varg

 df : ℕ →
        R.Name →
        List (R.Arg R.Term) →
        List (List (R.Arg R.Term)) →
        List (List (R.Arg R.Term)) → List R.Term
 df _ (quote CompWrap) _ _ args' = unArg <$> join args'
 df _ nm _ _ args' = R.def nm <$> (h args')



foldPath : List R.Term → R.Term
foldPath [] = RexplicitRefl R.unknown
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






bfs : CTerm → R.TC R.Term
bfs xs =  do
    let q = (foldPath' (tail (fill-flatten' xs)))
    hd ← Mb.rec (R.typeError [ "imposible tfct≡" ]ₑ )
           pure (listToMaybe (fill-flatten' xs)) 
    fillHeadTrm hd q


-- fillFoldCT' : Maybe CTerm → List R.Term →  R.TC (Maybe CTerm × List (Maybe CTerm))
-- fillFoldCT' nothing [] = pure (nothing , [] )
-- fillFoldCT' mbct [] = R.typeError [ "iimposible fillFOldCT'" ]ₑ
-- fillFoldCT' mbct (x ∷ xs) = do
--   (mbct' , xs') ← fillFoldCT' mbct xs
   
--   mbct'' ← fillStepCT x mbct'
--   -- R.debugPrint "testMarkVert" 3 $ Mb.rec [ "nothing" ]ₑ [_]ₑ mbct''
--   ⦇ (Mb.rec (pure nothing) cTermEnd mbct'') , pure (mbct'' ∷ xs') ⦈

-- fillFoldCT : List R.Term → R.TC (List (Maybe CTerm))
-- fillFoldCT = (snd <$>_) ∘S fillFoldCT' nothing



-- fillStepCT2 : R.Term → (Maybe CTerm) → R.TC (Maybe CTerm)
-- fillStepCT2 x nothing = {!!}
-- fillStepCT2 x (just x₁) = {!!}
--   -- Mb.rec
--   --   (if (hasVar zero x) then pure (just ( (wrapFills x) )) else pure nothing)
--   --   (if (hasVar zero x) then (λ xs' → just <$> (absorb 0 (wrapPaths x) xs')) else pure ∘S just )


-- fillFold1D : Maybe CTerm → List R.Term →  R.TC (CTerm × Maybe R.Term)
-- fillFold1D nothing [] = pure (nothing , nothing)
-- fillFold1D _ [] = R.typeError [ "iimposible fillFold1D'" ]ₑ
-- fillFold1D mbct (x ∷ xs) = do
--   (mbct' , xs') ← fillFold1D mbct xs
   
--   mbct'' ← fillStepCT x mbct'
--   s ← bfs {!mbct''!}
--   -- R.debugPrint "testMarkVert" 3 $ Mb.rec [ "nothing" ]ₑ [_]ₑ mbct''
--   ⦇ (Mb.rec (pure nothing) cTermEnd mbct'') , (Mb.rec {!!} {!!} xs') ⦈


-- bigFillStep : Maybe R.Term → R.Term → R.TC (Maybe R.Term × R.Term ) 
-- bigFillStep mbT t = do
--  {!!}


macro
 testPathCT : R.Term → R.Term → R.Term → R.Term → R.Term → R.TC Unit
 testPathCT t0 t1 t2 t3 h = do
   r ← mapM (addNDimsToCtx 1 ∘S R.normalise ∘S pathApp)
         (t0 ∷ t1 ∷ t2 ∷ [ t3 ]) >>= foldCT
   
   -- Mb.rec (R.typeError [ "nothing" ]ₑ  ) (R.typeError ∘S [_]ₑ ∘S dropPathWraps) r
   Mb.rec (R.typeError [ "nothing" ]ₑ  )
     (addNDimsToCtx 1 ∘S R.typeError ∘S ((_>>= λ t → "\n******" ∷nl [ t ]ₑ)) ∘S flatten' ) r


 testPathCT≡ : R.Term → R.Term → R.Term → R.Term → R.Term → R.Term → R.TC Unit
 testPathCT≡ t0 t1 t2 t3 t4 h = do
   r ← mapM (addNDimsToCtx 1 ∘S R.normalise ∘S pathApp)  (t0 ∷ t1 ∷ t2 ∷ t3 ∷ [ t4 ]) >>= foldCT
   let r' = Mb.rec (RexplicitRefl R.unknown) (foldPath ∘S flatten') r
   -- R.typeError [ r' ]ₑ
   R.unify r' h

 testFoldCT : R.Term → R.Term → R.Term → R.Term → R.Term → R.Term → R.TC Unit
 testFoldCT t0 t1 t2 t3 t4 h = do
   r ← mapM (addNDimsToCtx 1 ∘S R.normalise ∘S pathApp)
         (t0 ∷ t1 ∷ t2 ∷ t3 ∷ [ t4 ]) >>= fillFoldCT

   addNDimsToCtx 2 $ R.typeError $
     L.join (L.map (λ r →
            [ "\n\n≣≣≣≣≣≣≣≣≣≣≣≣≣≣≣≣≣≣≣≣≣≣≣≣≣≣≣≣\n\n"]ₑ ++ Mb.rec ([ "nothing" ]ₑ  )
              ((_>>= λ t → "\n******" ∷nl [ t ]ₑ) ∘S fill-flatten' ) r ) r)



module _ (k : ℕ) where


 macro
  testFillCT≡ : R.Term → R.Term → R.Term → R.Term → R.Term → R.Term → R.TC Unit
  testFillCT≡ t0 t1 t2 t3 t4 h = do
    r ← mapM (addNDimsToCtx 1 ∘S R.normalise ∘S pathApp)  (t0 ∷ t1 ∷ t2 ∷ t3 ∷ [ t4 ]) >>= fillFoldCT
    r' ← Mb.rec (pure (RexplicitRefl R.unknown)) bfs (joinM (lookup r k))
    R.unify r' h 
    -- R.typeError [ r' ]ₑ


-- bigTestFillCT≡ : R.Term → R.Term → R.Term → R.Term → R.Term → R.Term → R.TC Unit
-- bigTestFillCT≡ t0 t1 t2 t3 t4 h = do
--   r ← mapM (addNDimsToCtx 1 ∘S R.normalise ∘S pathApp)  (t0 ∷ t1 ∷ t2 ∷ t3 ∷ [ t4 ]) >>= fillFoldCT
--   r' ← Mb.rec (pure Rrefl) bfs (joinM (lookup r k))
--   R.unify r' h 
--   -- R.typeError [ r' ]ₑ






module foldCTTest {ℓ} {A B : Type ℓ} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
   (f : A → A → A) (s : f z y ≡ y) where

 P₀ : _ ≡ _  
 P₁ : _ ≡ _  
 P₂ : _ ≡ _
 P₃ : _ ≡ _
 P₄ : _ ≡ _

 P₀ i = f (f (p (~ i)) (p (~ i))) (f x x)
 P₁ i = f (f (p i) x) (f (p i) (p i))
 P₂ i = f (f (q i) (p i)) (f (q i) (q i))
 P₃ i = f (s i) (f (q (~ i)) z)
 P₄ i = f (q i) (f (p (~ i)) (r i))

 pt1 : A
 pt1 = P₄ i1

 P P' : f (f y y) (f x x) ≡ f (z) (f x w)
 P =  P₀ ∙
      P₁ ∙
      P₂ ∙
      P₃ ∙
      P₄ 

 -- _ : String
 -- _ = {!testPathCT P₁ P₂ P₃ P₄!}

 -- _ : String
 -- _ = {!testFoldCT P₀ P₁ P₂ P₃ P₄!}


 P' = testPathCT≡ P₀ P₁ P₂ P₃ P₄

 PF₀ : Square
         (_ ∙' (_ ∙' _) )
         (_ ∙' (_ ∙' (_ ∙' _)))
         P₀ λ _ → pt1
 PF₀ = testFillCT≡ 0 P₀ P₁ P₂ P₃ P₄

 PF₁ : Square
         (_ ∙' (_ ∙' (_ ∙' _)))
         (_ ∙' (_ ∙' _))
          P₁ λ _ → pt1
 PF₁ = testFillCT≡ 1 P₀ P₁ P₂ P₃ P₄

 PF₂ : Square
         (_ ∙' (_ ∙' _))
         (_ ∙' _)
         P₂ λ _ → pt1
 PF₂ = testFillCT≡ 2 P₀ P₁ P₂ P₃ P₄

 PF₃ : Square
         (_ ∙' _)
         _
         P₃ λ _ → pt1
 PF₃ = testFillCT≡ 3 P₀ P₁ P₂ P₃ P₄

 PF₄ : Square
         P₄
         refl P₄ λ _ → pt1
 PF₄ = testFillCT≡ 4 P₀ P₁ P₂ P₃ P₄


 -- P≡P' : P ≡ P'
 -- P≡P' = {!!}

 SQ : Square P' refl P refl
 SQ = PF₀ ∙■ (PF₁ ∙■ (PF₂ ∙■  (PF₃ ∙■ PF₄)))


module foldCTTest2 {ℓ} {A B : Type ℓ} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
   (f : A → A → A) (s : f z y ≡ y) where

 P₀ : _ ≡ _  
 P₁ : _ ≡ _  
 P₂ : _ ≡ _
 P₃ : _ ≡ _
 P₄ : _ ≡ _

 P₀ i = f x (f x (q i))
 P₁ i = f x (f (p i) z)
 P₂ i = f x (f (q i) z)
 P₃ i = f x (f (q (~ i)) z)
 P₄ i = f x (f (p (~ i)) z)

 pt1 : A
 pt1 = P₄ i1

 P P' : f x (f x y) ≡ f x (f x z)
 P =  P₀ ∙
      P₁ ∙
      P₂ ∙
      P₃ ∙
      P₄ 

 -- -- _ : String
 -- -- _ = {!testPathCT P₁ P₂ P₃ P₄!}

 -- -- _ : String
 -- -- _ = {!testFoldCT P₀ P₁ P₂ P₃ P₄!}


 P' = testPathCT≡ P₀ P₁ P₂ P₃ P₄

 PF₀ : Square
         _ _
         P₀ λ _ → pt1
 PF₀ = testFillCT≡ 0 P₀ P₁ P₂ P₃ P₄

 PF₁ : Square
         _ _
         P₁ λ _ → pt1
 PF₁ = testFillCT≡ 1 P₀ P₁ P₂ P₃ P₄

 PF₂ : Square
         _ _
         P₂ λ _ → pt1
 PF₂ = testFillCT≡ 2 P₀ P₁ P₂ P₃ P₄

 PF₃ : Square
         _
         _
         P₃ λ _ → pt1
 PF₃ = testFillCT≡ 3 P₀ P₁ P₂ P₃ P₄

 PF₄ : Square
         _
         refl P₄ λ _ → pt1
 PF₄ = testFillCT≡ 4 P₀ P₁ P₂ P₃ P₄


 -- P≡P' : P ≡ P'
 -- P≡P' = {!!}

 SQ : Square P' refl P refl
 SQ = PF₀ ∙■ (PF₁ ∙■ (PF₂ ∙■  (PF₃ ∙■ PF₄)))

module foldCTTest3 {ℓ} {A B : Type ℓ} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
   (f : A → A → A) (s : f z y ≡ y) where

 P₀ : _ ≡ _  
 P₁ : _ ≡ _  
 P₂ : _ ≡ _
 P₃ : _ ≡ _
 P₄ : _ ≡ _

 P₀ i = f x (f x z)
 P₁ i = f x (f (p i) z)
 P₂ i = f x (f (q i) z)
 P₃ i = f x (f (q (~ i)) z)
 P₄ i = f x (f (p (~ i)) z)

 pt1 : A
 pt1 = P₄ i1

 P P' : f x (f x z) ≡ f x (f x z)
 P =  P₀ ∙
      P₁ ∙
      P₂ ∙
      P₃ ∙
      P₄ 

 -- -- _ : String
 -- -- _ = {!testPathCT P₁ P₂ P₃ P₄!}

 -- -- _ : String
 -- -- _ = {!testFoldCT P₀ P₁ P₂ P₃ P₄!}


 P' = testPathCT≡ P₀ P₁ P₂ P₃ P₄

 -- PF₀ : Square
 --         _ _
 --         P₀ λ _ → pt1
 -- PF₀ = testFillCT≡ 0 P₀ P₁ P₂ P₃ P₄

 PF₁ : Square
         _ _
         P₁ λ _ → pt1
 PF₁ = testFillCT≡ 1 P₀ P₁ P₂ P₃ P₄

 PF₂ : Square
         _ _
         P₂ λ _ → pt1
 PF₂ = testFillCT≡ 2 P₀ P₁ P₂ P₃ P₄

 PF₃ : Square
         _
         _
         P₃ λ _ → pt1
 PF₃ = testFillCT≡ 3 P₀ P₁ P₂ P₃ P₄

 PF₄ : Square
         _
         refl P₄ λ _ → pt1
 PF₄ = testFillCT≡ 4 P₀ P₁ P₂ P₃ P₄


 -- -- P≡P' : P ≡ P'
 -- -- P≡P' = {!!}

 SQ : Square P' refl P refl
 SQ = (testFillCT≡ 0 P₀ P₁ P₂ P₃ P₄) ∙■ (PF₁ ∙■ (PF₂ ∙■  (PF₃ ∙■ PF₄)))





