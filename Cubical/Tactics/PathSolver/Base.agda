{-# OPTIONS --safe  #-} 

module Cubical.Tactics.PathSolver.Base where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Relation.Nullary

open import Cubical.Data.Bool
import Cubical.Data.Vec as V
open import Cubical.Data.Empty
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.List as L
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sigma

open import Cubical.Reflection.Base renaming (v to 𝒗)
import Agda.Builtin.Reflection as R
open import Cubical.Tactics.PathSolver.Reflection
open import Cubical.Tactics.Reflection 
open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Cubical.Tactics.Reflection.Utilities

open import Cubical.Foundations.Cubes as C
open import Cubical.Foundations.Cubes.Dependent


private
  variable
    ℓ : Level
    A B : Type ℓ
    x y z w v : A

vlamⁿ : ℕ → R.Term → R.Term
vlamⁿ zero t = t
vlamⁿ (suc n) t = vlam "𝒊" (vlamⁿ n t)

hcomp-congI' : (φ : I) (f : A → B) →
   (u : I → Partial φ A) → (u0 : A [ φ ↦ u i0 ])
    →  I → B 
hcomp-congI' φ f u u0 j = f (hfill ((λ k o → u k o)) u0 j)


hcomp-congI : (φ : I) (f : A → B) →
   (u : I → Partial φ A) → (u0 : A [ φ ↦ u i0 ])
    →  I → B 
hcomp-congI φ f u u0 j =
  hcomp {φ = ~ j ∨ φ}
    (λ k o → f (hfill ((λ k o → u k o)) u0 k)) (f (outS u0))


hcomp-cong' : (φ : I) (f : A → B) →
   (u : I → Partial φ A) → (u0 : A [ φ ↦ u i0 ])
    →  f (hcomp u (outS u0)) ≡ hcomp (λ k o → f (u k o)) (f (outS u0))
hcomp-cong' φ f u u0 j = hcomp-congI _ f u u0 j 

hcomp-cong'impl : (φ : I) (f : {A} → B) →
   (u : I → Partial φ A) → (u0 : A [ φ ↦ u i0 ])
    →  f {hcomp u (outS u0)} ≡ hcomp (λ k o → f {u k o}) (f {outS u0})
hcomp-cong'impl φ f u u0 j = hcomp-congI φ (λ x → f {x}) u u0 j 


-- cong-∙∙' : ∀ {B : Type ℓ} (f : A → B) (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
--           → cong f (p ∙∙ q ∙∙ r) ≡ (cong f p) ∙∙ (cong f q) ∙∙ (cong f r)
-- cong-∙∙' f p q r i j = hcomp-cong' (j ∨ ~ j) f (doubleComp-faces p r j) (inS (q j)) i


I^n→ItyTm : ℕ → R.Term
I^n→ItyTm zero = R.def (quote I) []
I^n→ItyTm (suc x) = R.pi (varg (R.def (quote I) [])) (R.abs "i" (I^n→ItyTm x) )




I^_⟶_ : ℕ → Type ℓ → Type ℓ 
I^ zero ⟶ A = A
I^ suc n ⟶ A = I → I^ n ⟶ A

tmI^_⟶_ : ℕ → R.Term → R.Term
tmI^ zero ⟶ tmA = tmA
tmI^ suc x ⟶ tmA = R.pi (varg (R.def (quote I) [])) (R.abs "tmI" ((tmI^ x ⟶ tmA)))


nCycle : ∀ n → (I^ n ⟶ A)  → (I^ n ⟶ A) 
nCycle zero x = x
nCycle (suc zero) x = x
nCycle (suc (suc n)) x i j = nCycle (suc n) (x j) i

-- flipI⟶ : {!!}
-- flipI⟶ = {!!}

nCycle⁻ : ∀ n → (I^ n ⟶ A)  → (I^ n ⟶ A) 
nCycle⁻ zero x = x
nCycle⁻ (suc zero) x = x
nCycle⁻ (suc (suc zero)) x i j = x j i
nCycle⁻ (suc (suc (suc n))) x i j k = x k i j


I^→Cu : ∀ n → I^ n ⟶ A → C.Cube n A   
-- I^→∂ : ∀ n → I^ n ⟶ A → C.∂Cube n A
-- I^→∂ zero x = tt*
-- I^→∂ (suc zero) x = (x i0) , (x i1)
-- I^→∂ (suc (suc n)) x =
--   (_ , {!!}) , ((_ , {!!}) , λ i → (I^→∂ (suc n) (x i)))
--  -- ((I^→∂ (suc n) (x i0))) , {!!}


I^→Cu zero x = x
I^→Cu (suc zero) x = _ , λ i → x i
I^→Cu (suc (suc n)) x = _ , (λ i → snd (I^→Cu (suc n) (x i)))

cubeEv : ∀ n → C.Cube n A →  I^ n ⟶ A 
cubeEv zero x = x
cubeEv (suc zero) x i = snd x i
cubeEv {A = A} (suc (suc n)) x i = cubeEv (suc n)  (CubeRel→Cube {A = A} (snd x i))

cubeEv-sec : ∀ n → section (cubeEv {A = A} n) (I^→Cu n)
cubeEv-sec zero b = refl
cubeEv-sec (suc zero) b = refl
cubeEv-sec (suc (suc n)) b j i = cubeEv-sec (suc n) (b i) j

cubeEv-ret : ∀ n → retract (cubeEv {A = A} n) (I^→Cu n)
cubeEv-ret zero a = refl
cubeEv-ret (suc zero) a = refl

fst (fst (cubeEv-ret (suc (suc n)) a j)) = _ ,
 snd (cubeEv-ret (suc n) (fst (fst a) .fst , fst (fst a) .snd) j)
snd (fst (cubeEv-ret (suc (suc n)) a j)) =
  ((cubeEv-ret (suc n)
      (fst (snd (fst a)) .fst , fst (snd (fst a)) .snd) j)) ,
  λ i → fst (cubeEv-ret (suc n) (snd (snd (fst a)) i , snd a i) j)
snd (cubeEv-ret (suc (suc n)) a j) i = snd (cubeEv-ret (suc n) (snd (snd (fst a)) i , snd a i) j) 


IsoCuI^→ : ∀ n → Iso (C.Cube n A) (I^ n ⟶ A )
IsoCuI^→ n = iso (cubeEv n) (I^→Cu n) (cubeEv-sec n) (cubeEv-ret n)

toCu : ∀ n → ∀ (x : I^ (suc n) ⟶ A) → CubeRel (suc n) _ (fst (Iso.inv (IsoCuI^→ (suc n)) x))
toCu n = snd ∘ (Iso.inv (IsoCuI^→ (suc n)))


fromCu : ∀ n → ∀ {bd} → CubeRel (suc n) A bd → I^ (suc n) ⟶ A
fromCu zero {bd} x = λ i → x i
fromCu n@(suc zero) {bd} x = λ i i₁ → x i i₁
fromCu n@(suc (suc _)) {bd} x = (Iso.fun (IsoCuI^→ (suc n))) (bd , x)

fromCuTmWithApp : ℕ → R.Term → R.Term
fromCuTmWithApp zero t = t
fromCuTmWithApp (suc n) t = R.def (quote fromCu)
 (toℕTerm n v∷ (liftVars.rv (suc n) 0 t) v∷ L.map (λ k → varg (𝒗 k)) (range (suc n)))



data SubFaceω : SSet where 
 [] : SubFaceω
 _∷_ : I → SubFaceω → SubFaceω

data SubFacesω : SSet where 
 [] : SubFacesω
 _∷_ : SubFaceω → SubFacesω → SubFacesω

SubFaceω→I : SubFaceω → I
SubFaceω→I [] = i1
SubFaceω→I (x ∷ xs) = x ∧ SubFaceω→I xs 

SubFacesω→I : SubFacesω → I
SubFacesω→I [] = i0
SubFacesω→I (x ∷ xs) = SubFaceω→I x ∨ SubFacesω→I xs 


cart : List  A → List B → List (A × B) 
cart la lb = L.join (L.map (λ b → L.map (_, b) la) lb)

IExpr : Type
IExpr = List (List (Bool × ℕ))



_∨'_ : IExpr → IExpr → IExpr
_∨'_ = _++_


_∧'_ : IExpr → IExpr → IExpr
x ∧' y = L.map (uncurry _++_) (cart x y)


~' : IExpr → IExpr
~' = foldl (λ x y → x ∧' L.map ([_] ∘S map-fst not) y) [ [] ]

ie[_] : ℕ → IExpr
ie[ x ] = [ [ true , x ] ]


$i : ∀ {ℓ} {A : Type ℓ} → (I → A) → I → A
$i = λ f i → f i

-- {-# INLINE $i #-}


$I : ∀ {ℓ} {A : I → SSet ℓ} → (∀ i → A i) → ∀ i → A i
$I f i = f i

$≡ : ∀ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1} → (PathP A x y) → ∀ i → A i
$≡ f i = f i


$PI : ∀ {ℓ} (A : Type ℓ) → (I → (Partial i1 A)) → I → A
$PI _ f i = f i 1=1



appNDimsI : ℕ → R.Term → R.Term
appNDimsI zero t = t
appNDimsI (suc n) t =
 appNDimsI n $ R.def (quote $i) ( t v∷ v[ R.var n [] ])

SubFace = List (Maybe Bool)


filter : (A → Bool) → List A → List A
filter f [] = []
filter f (x ∷ xs) = if f x then (x ∷ filter f xs) else (filter f xs)
 
sfDim : SubFace → ℕ
sfDim sf = length sf ∸ length (filter (λ { (just _) → true ; _ → false} ) sf)


subFaceConstraints : SubFace → List (Bool × ℕ)
subFaceConstraints [] = []
subFaceConstraints (x ∷ xs) =
  Mb.rec (idfun _) (_∷_ ∘S (_, zero)) x $
    (L.map (map-snd suc) (subFaceConstraints xs))


data <SF> : Type where
 ⊂ ⊃ ⊃⊂ ⊂⊃ : <SF>

SF⊃⊂ : <SF> → Type
SF⊃⊂ ⊃⊂ = Unit
SF⊃⊂ _ = ⊥

_<⊕>_ : <SF> → <SF> → <SF>
⊃⊂ <⊕> x₁ = ⊃⊂
⊂⊃ <⊕> x₁ = x₁

⊂ <⊕> ⊂ = ⊂
⊂ <⊕> ⊂⊃ = ⊂
⊂ <⊕> _ = ⊃⊂

⊃ <⊕> ⊂⊃ = ⊃
⊃ <⊕> ⊃ = ⊃
⊃ <⊕> _ = ⊃⊂

_<mb>_ : Maybe Bool → Maybe Bool → <SF>
nothing <mb> nothing = ⊂⊃
nothing <mb> just x = ⊃
just x <mb> nothing = ⊂
just x <mb> just x₁ = if (x ⊕ x₁) then ⊃⊂ else ⊂⊃ 

_<sf>_ : SubFace → SubFace → <SF>
[] <sf> [] = ⊂⊃
[] <sf> (y ∷ ys) = (nothing <mb> y) <⊕> ([] <sf> ys)
(x ∷ xs) <sf> [] =  (x <mb> nothing) <⊕> (xs <sf> [])
(x ∷ xs) <sf> (y ∷ ys) = (x <mb> y) <⊕> (xs <sf> ys)



FExpr = List SubFace

FEG : SubFace → FExpr → Type


FEG x [] = Unit
FEG x (sf ∷ x₁) = SF⊃⊂ (x <sf> sf) × FEG x x₁

infixr 5 _fe∷_

_fe∷_ : SubFace → FExpr → FExpr
x fe∷ [] = x ∷ []
x fe∷ y@(sf ∷ x₁) with sf <sf> x 
... | ⊂ = x fe∷ x₁
... | ⊃ = y
... | ⊃⊂ = sf ∷ (x fe∷ x₁) 
... | ⊂⊃ = y


_⊂?_ : SubFace → FExpr → Bool
x ⊂? [] = false
x ⊂? (y ∷ sf) with x <sf> y
... | ⊂ = true
... | ⊃ = x ⊂? sf
... | ⊃⊂ = x ⊂? sf
... | ⊂⊃ = true


-- mkFaceTail : ℕ → SubFace
-- mkFaceTail zero = []
-- mkFaceTail (suc x) = nothing ∷ mkFaceTail x

-- mkFacePlus : ℕ → SubFace → SubFace
-- mkFacePlus = ?

mkFace : Bool → ℕ → SubFace 
mkFace b k = iter k (nothing ∷_ ) (just b ∷ [])

_∪Mb_ : Maybe Bool → Maybe Bool → Maybe (Maybe Bool)
nothing ∪Mb x₁ = just x₁
just x ∪Mb nothing = just (just x)
just x ∪Mb just x₁ = if (x ⊕ x₁) then nothing else just (just x)

_∪SF_ : SubFace → SubFace → Maybe SubFace
[] ∪SF x₁ = just x₁
(x ∷ x₂) ∪SF [] = just ((x ∷ x₂))
(x ∷ x₂) ∪SF (x₁ ∷ x₃) =
 map2-Maybe _∷_  (x ∪Mb x₁) (x₂ ∪SF x₃)

fromSF : (List (Bool × ℕ)) → Maybe SubFace
fromSF [] = nothing
fromSF (x ∷ xs) =
 foldr (flip (Mb.rec (λ _ → nothing) _∪SF_ ) ∘S uncurry mkFace) (just (mkFace (fst x) (snd x))) xs


I→F : IExpr → FExpr
I→F [] = []
I→F (x ∷ x₁) =
 Mb.rec
   (I→F x₁)
   (λ x → x fe∷ I→F x₁)
   (fromSF x) 

SubFace→Term : SubFace → R.Term
SubFace→Term = h 0
 where
 h : ℕ → SubFace → R.Term
 h k [] = R.con (quote i1) []
 h k (nothing ∷ xs) = h (suc k) xs
 h k (just x ∷ xs) =
  let x' = R.var k []
      x'' = if x then x' else R.def (quote ~_) v[ x' ]
  in R.def (quote _∧_) (x'' v∷ v[ h (suc k) xs ])

IExpr→Term : IExpr → R.Term
IExpr→Term = foldl (λ x y → R.def (quote _∨_) (x v∷
       v[ foldl (λ x (b , k) → R.def (quote _∧_) (x v∷
              v[ (let x' = R.var (k) []
                      x'' = if b then x' else R.def (quote ~_) v[ x' ]
                  in x'')
                  ] ))
               (R.con (quote i1) []) y ] ))
     (R.con (quote i0) [])


extractIExpr : R.Term → R.TC IExpr
extractIExpr (R.var x []) = ⦇ (ie[ x ]) ⦈
extractIExpr (R.con (quote i0) []) = ⦇ [] ⦈
extractIExpr (R.con (quote i1) []) = ⦇ ([ [] ]) ⦈
extractIExpr (R.def (quote _∨_) (x v∷ v[ y ])) =
  ⦇ extractIExpr x ∨' extractIExpr y ⦈
extractIExpr (R.def (quote _∧_) (x v∷ v[ y ])) =
  ⦇ extractIExpr x ∧' extractIExpr y ⦈
extractIExpr (R.def (quote ~_) v[ x ] ) =
    ⦇ ~' (extractIExpr x) ⦈
extractIExpr t = R.typeError (R.strErr "extractIExpr FAIL : " ∷ getConTail t)


macro
 extractIExprTest : R.Term → R.Term → R.TC Unit 
 extractIExprTest t h = do
   t' ← (extractIExpr t) -->>= R.quoteTC
   let tm = IExpr→Term (~' t')
   R.unify (R.def (quote ~_) v[ t ]) (tm)
   R.typeError $ "ok " ∷ₑ [ tm ]ₑ
   -- R.unify h t'

 extractIExprTest' : R.Term → R.Term → R.TC Unit 
 extractIExprTest' t h = R.typeError (getConTail t)

-- module extractIExprTests (i j k l : I) where
--  zz zz' : FExpr
--  zz = {!extractIExprTest (~ (j ∧ i ∧ ~ j) ∨ k ∨ (i ∧ ~ i) ∨ (l ∧ i))!}

--  zz' = {!extractIExprTest (j ∧ (~ i) ∧ k)!}


data TermHead : Type where
  var : (x : ℕ)  → TermHead
  con : (c : R.Name) → TermHead
  def : (f : R.Name) → TermHead


data CuTerm' (CongGuard : Type) (A : Type ℓ) : Type ℓ

data CuArg' (CongGuard : Type) (A : Type ℓ) : Type ℓ where
 iArg : IExpr → CuArg' CongGuard A
 tArg : CuTerm' CongGuard A → CuArg' CongGuard A

data CuTerm' CongGuard A where
 hco : List (SubFace × CuTerm' CongGuard A) → CuTerm' CongGuard A → CuTerm' CongGuard A
 cell' : A → R.Term → CuTerm' CongGuard A
 𝒄ong' : {cg : CongGuard} → TermHead → List (R.Arg (CuArg' CongGuard A)) → CuTerm' CongGuard A

pattern
 cell x = cell' tt x
-- pattern
--  hco x y = hco' tt x y

pattern
 𝒄ong th tl = 𝒄ong' {cg = tt} th tl

CuTerm = CuTerm' Unit Unit 
CuArg = CuArg' Unit Unit

-- mapTermUnderDims : ℕ → (R.Term → R.Term) → R.Term → R.Term
-- mapTermUnderDims dim f x =
--   vlamⁿ dim $ f (appNDimsI dim (liftVars.rv dim 0 x))

module MapCuTerm (f : ℕ → R.Term → R.Term) where

 mapCuTermS : List (SubFace × CuTerm) → List (SubFace × CuTerm)
 mapCuTermT : ℕ → List (R.Arg CuArg) → List (R.Arg CuArg)

 mapCuTerm : ℕ → CuTerm → CuTerm
 mapCuTerm dim (hco x x₁) = hco (mapCuTermS x) (mapCuTerm dim x₁)
 mapCuTerm dim (cell x) = cell (f dim x)
 mapCuTerm dim (𝒄ong x x₁) = 𝒄ong x (mapCuTermT dim x₁)


 mapCuTermS [] = []
 mapCuTermS ((fc , x) ∷ xs) = (fc , mapCuTerm (suc (sfDim fc)) x) ∷ mapCuTermS xs
 mapCuTermT _ [] = []
 mapCuTermT dim (R.arg i (iArg x) ∷ xs) = R.arg i (iArg x) ∷ mapCuTermT dim xs
 mapCuTermT dim (R.arg i (tArg x) ∷ xs) = R.arg i (tArg $ mapCuTerm dim x) ∷ mapCuTermT dim xs 


open MapCuTerm using (mapCuTerm) public
 
isCell : CuTerm → Bool
isCell (cell x) = true
isCell _ = false

isLeafCuArg : CuArg → Bool
isLeafCuArg (iArg x) = true
isLeafCuArg (tArg x) = isCell x


is𝑪ongFreeF : List (SubFace × CuTerm) → Bool

is𝑪ongFree : CuTerm → Bool 
is𝑪ongFree (hco x x₁) = is𝑪ongFreeF x and is𝑪ongFree x₁
is𝑪ongFree (cell x) = true
is𝑪ongFree (𝒄ong x x₁) = false

is𝑪ongFreeF [] = true
is𝑪ongFreeF ((_ , x) ∷ xs) = is𝑪ongFree x and is𝑪ongFreeF xs


CuCtx = List (String × Maybe Bool)

defaultCtx : ℕ → CuCtx
defaultCtx dim = L.map ((_, nothing) ∘S mkNiceVar' "𝓲") $ range dim


inCuCtx : CuCtx → R.TC A → R.TC A
inCuCtx ctx x = foldl (λ x → uncurry
  λ v → Mb.caseMaybe (R.extendContext v ((varg (R.def (quote I) []))) x) x) x ctx

inCuCtx' : CuCtx → R.TC A → R.TC A
inCuCtx' ctx x = foldl (λ x → uncurry
  λ v _ → R.extendContext v ((varg (R.def (quote I) []))) x) x ctx



SubFace→TermInCtx : CuCtx → SubFace → R.Term
SubFace→TermInCtx ctx = h 0
 where

 kInCtx : CuCtx → ℕ → ℕ
 kInCtx [] k = k
 kInCtx ((fst₁ , nothing) ∷ xs) zero = zero
 kInCtx ((fst₁ , nothing) ∷ xs) (suc k) = suc (kInCtx xs k)
 kInCtx ((fst₁ , just x) ∷ xs) k = suc (kInCtx (xs) k) 
 
 h : ℕ → SubFace → R.Term
 h k [] = R.con (quote i1) []
 h k (nothing ∷ xs) = h (suc k) xs
 h k (just x ∷ xs) =
  let x' = R.var (kInCtx ctx k) []
      x'' = if x then x' else R.def (quote ~_) v[ x' ]
  in R.def (quote _∧_) (x'' v∷ v[ h (suc k) xs ])

IExpr→TermInCtx : CuCtx → IExpr → R.Term
IExpr→TermInCtx ctx =
   foldl (λ x y → R.def (quote _∨_) (x v∷
       v[ foldl (λ x (b , k) → R.def (quote _∧_) (x v∷
              v[ (let x' = R.var (kInCtx ctx k) []
                      x'' = if b then x' else R.def (quote ~_) v[ x' ]
                  in x'')
                  ] ))
               (R.con (quote i1) []) y ] ))
     (R.con (quote i0) [])
 where

 kInCtx : CuCtx → ℕ → ℕ
 kInCtx [] k = k
 kInCtx ((fst₁ , nothing) ∷ xs) zero = zero
 kInCtx ((fst₁ , nothing) ∷ xs) (suc k) = suc (kInCtx xs k)
 kInCtx ((fst₁ , just x) ∷ xs) k = suc (kInCtx (xs) k) 


applyFaceConstraints : SubFace → CuCtx → CuCtx
applyFaceConstraints sf [] = []
applyFaceConstraints [] ctx@(_ ∷ _) = ctx
applyFaceConstraints sf@(_ ∷ _) (c@(_ , just _) ∷ ctx) =
  c ∷ applyFaceConstraints sf ctx
applyFaceConstraints (mbC ∷ sf) ((v , nothing) ∷ ctx) =
  (v , mbC) ∷ applyFaceConstraints sf ctx


freeVars : CuCtx → List String
freeVars = L.map fst ∘S filter (λ { (_ , (nothing)) → true ; _ → false} )

catMaybes : List (Maybe A) → List A
catMaybes [] = []
catMaybes (nothing ∷ xs) = catMaybes xs
catMaybes (just x ∷ xs) = x ∷ catMaybes xs

boundedDims : CuCtx → List (String × Bool)
boundedDims = catMaybes ∘S L.map (uncurry λ s → map-Maybe (s ,_)) 

liftTermHead : ℕ → TermHead → TermHead
liftTermHead k (var x) = var (x + k)
liftTermHead _ (con c) = con c
liftTermHead _ (def f) = def f

TermHead→Term : TermHead → List (R.Arg R.Term) → R.Term
TermHead→Term (var x) = R.var x
TermHead→Term (con c) = R.con c
TermHead→Term (def f) = R.def f


module _ (cellTermRender : CuCtx → R.Term →  R.TC (List R.ErrorPart)) (dim : ℕ) where

 renderSubFaceExp : SubFace → R.TC String 
 renderSubFaceExp sf = R.normalise (SubFace→Term sf) >>= renderTerm

  
 renderSubFacePattern : CuCtx → SubFace → String 
 renderSubFacePattern ctx sf =
   foldl _<>_ "" (L.map
       ((λ (b , k) → let k' = L.lookupAlways "‼"
                                   (freeVars ctx) k
                     in "(" <> k' <> "=" <> (if b then "1" else "0") <> ")"))
      (subFaceConstraints sf))
   -- (mapM (λ (b , k) → do k' ← renderTerm (R.var k [])
   --                       pure $ "(" <> k' <> "=" <> (if b then "1" else "0") <> ")")
   -- ∘S subFaceConstraints) >=& foldl _<>_ ""

 ppCT'' : CuCtx → ℕ → CuTerm → R.TC (List R.ErrorPart)
 ppCArg : CuCtx → ℕ → CuArg → R.TC (List R.ErrorPart)
  
 ppCT'' _ zero _ = R.typeError [ "pPCT FAIL" ]ₑ
 ppCT'' ctx (suc d) (hco x x₁) = do
   let l = length ctx ∸ dim
   indN ← foldr max zero <$> (
              (mapM ((((pure ∘ (renderSubFacePattern ctx)) >=& stringLength)) ∘S fst ) x))

   let newDimVar = (mkNiceVar' "𝒛" l)
   rest ← (L.intersperse (R.strErr "\n") ∘S L.join)  <$> mapM
         (λ (sf , cu) → do



            -- R.extendContext "zz" (varg (R.def (quote I) [])) $
            ( do
               let sfTm = renderSubFacePattern ctx sf 
               -- R.extendContext newDimVar (varg (R.def (quote I) [])) $         
               (do sfTm' ← inCuCtx' (("z" , nothing) ∷ ctx) $ R.formatErrorParts [ liftVars (SubFace→TermInCtx ctx sf) ]ₑ
                   cu' ← (ppCT'' ((newDimVar , nothing) ∷ applyFaceConstraints sf ctx) d cu)
                   cu'' ← R.formatErrorParts cu'
                   let cu''' = indent' false ' ' 2 cu''
                   pure (offsetStrR indN sfTm  ∷ₑ
                             -- "/" ∷ₑ sfTm' ∷ₑ
                             " → " ∷ₑ [ cu''' ]ₑ))) >>=
                      (R.formatErrorParts >=& [_]ₑ)) x
   lid ← indent '│' 1 <$> (ppCT'' ctx d x₁ >>= R.formatErrorParts)
   rest' ← indent '║' 2 <$> R.formatErrorParts rest
   pure $ (R.strErr ("\n𝒉𝒄𝒐𝒎𝒑 λ " <> newDimVar <> "\n")) ∷
                   (rest' ∷ₑ "\n├─────────── \n" ∷ₑ
                   lid ∷ₑ [ "\n└─────────── "]ₑ)
  
 ppCT'' ctx _ (cell x) = do
  ctr ← cellTermRender ctx x >>=
             --inCuCtx ctx ∘
             R.formatErrorParts
  pure [ ctr ]ₑ
 ppCT'' ctx d (𝒄ong h t) = do
  rT ← mapM (argRndr >=> R.formatErrorParts) t
  rHead ← renderTerm (TermHead→Term h [])
  pure  [ rHead <> indent ' ' 2 (foldr (_<>_  ∘S ("\n" <>_)) "" rT)]ₑ 

  where
  argRndr : R.Arg CuArg → R.TC _
  argRndr (R.arg (R.arg-info R.visible m) x) =
      ((λ s → [ "(" ]ₑ ++ s ++ [ ")" ]ₑ) <$> (ppCArg ctx d x))
  argRndr (R.arg (R.arg-info R.hidden m) x) =
      ((λ s → [ "{" ]ₑ ++ s ++ [ "}" ]ₑ) <$> (ppCArg ctx d x))
  argRndr (R.arg (R.arg-info R.instance′ m) x) =
      ((λ s → [ "⦃" ]ₑ ++ s ++ [ "⦄" ]ₑ) <$> (ppCArg ctx d x))

 ppCArg ctx zero _ = R.typeError [ "ppCArg FAIL" ]ₑ
 ppCArg ctx (suc d) (iArg x) =
     inCuCtx' ctx ([_]ₑ <$> renderTerm R.unknown)
 ppCArg ctx (suc d) (tArg x) = ppCT'' ctx d x

 ppCT' :  ℕ → CuTerm → R.TC (List R.ErrorPart)
 ppCT' = ppCT'' (defaultCtx dim)


endTerm : Bool → R.Term 
endTerm = (if_then R.con (quote i1) [] else R.con (quote i0) [])

constPartial : A → ∀ φ → Partial φ A
constPartial a φ 1=1 = a


-- replaceVarWithEnd : ℕ → Bool → R.Term → R.Term
-- replaceVarWithEnd k b =
--   replaceVarWithCon
--   (λ { zero → just (quote i0) ; _ → nothing })
  

dropWhere : List Bool → R.Term → R.Term
dropWhere = dw ∘S rev
 where
 dw : List Bool → R.Term → R.Term
 dw [] t = t
 dw (b ∷ xs) t = dw xs (if b then dropVar (length xs) t else t)

liftWhere : List Bool → R.Term → R.Term
liftWhere = lw ∘S rev
 where
 lw : List Bool → R.Term → R.Term
 lw [] t = t
 lw (b ∷ xs) t =
  let t' = lw xs t
  in (if b then (liftVars.rv 1 (length xs) t') else t')
 
subfaceCell : SubFace → R.Term → R.Term
subfaceCell sf = dropWhere (L.map (λ {(just _) → true ; _ → false }) sf) ∘S replaceVarWithCon (r sf)
 where
 r : SubFace → ℕ → Maybe R.Name
 r sf = map-Maybe (if_then quote i1 else quote i0) ∘S lookupAlways nothing sf


pick : List Bool → List A → List A
pick [] _ = []
pick (_ ∷ _) [] = []
pick (false ∷ bs) (x ∷ xs) = pick bs xs
pick (true ∷ bs) (x ∷ xs) = x ∷ pick bs xs

pickNpad : A → List Bool → List A → List A
pickNpad a bs [] = L.map (λ _ → a) bs
pickNpad a [] (x ∷ xs) = []
pickNpad a (false ∷ bs) (x ∷ xs) = pickNpad a bs xs
pickNpad a (true ∷ bs) (x ∷ xs) = x ∷ pickNpad a bs xs



feMask : FExpr → List Bool
feMask = foldr (alwaysZipWith
      (λ x y → (fromMaybe false x) or (fromMaybe false y)) ∘S L.map (caseMaybe false true)) []




macro
 showContext : R.Term → R.TC Unit
 showContext _ =
  R.getContext >>= (λ tel → do
    let maxL = foldr (max ∘S stringLength ∘S fst) zero tel 
    concatMapM (λ (s , ty)
       → ⦇ ⦇ ( "\n" <> offsetStrR maxL s <> " : " ) ⦈  ∷ₑ ([_]ₑ <$> renderArg ty)  ⦈  ) tel 
    ) >>= R.typeError

cellQ : CuTerm → Bool
cellQ (cell x) = true
cellQ _ = false

almostLeafQ : CuTerm → Bool
almostLeafQ (hco x (hco x₁ x₂)) = false
almostLeafQ (hco x (cell x₁)) =
  foldr (_and_ ∘S cellQ ∘S snd) true x
almostLeafQ _ = false


module _ (s : String) where

 addNDimsToCtx' : ℕ → R.TC A → R.TC A 
 addNDimsToCtx' zero f = f
 addNDimsToCtx' (suc k) =
  R.extendContext (mkNiceVar' s k) (varg (R.def (quote I) []))
    ∘S (addNDimsToCtx' k)

addNDimsToCtx = addNDimsToCtx' "𝓲" 

appNDims≡ : ℕ → R.Term → R.Term
appNDims≡ zero t = t
appNDims≡ (suc n) t =
 appNDims≡ n $ R.def (quote $≡) ( t v∷ v[ R.var n [] ])


inGlobalCtx : CuCtx → R.Term → R.Term
inGlobalCtx ctx = liftWhere (L.map ((λ { (just _) → true ; _ → false }) ∘S snd ) ctx) 


-- global2local : CuCtx → R.Term → R.Term
-- global2local ctx t = (h 0 ctx (vlamⁿ (length ctx) (liftVars.rv (length (freeVars ctx)) (length ctx) t)))

--  where
--  h : ℕ → CuCtx → R.Term → R.Term
--  h n [] t = t
--  h n ((_ , just b) ∷ xs) t =
--    (R.def (quote $i) ((h n xs  t) v∷ v[ if b then R.con (quote i1) [] else R.con (quote i0) [] ]))
  
--  h n ((s , nothing) ∷ xs) t = (R.def (quote $i) ((h (suc n) xs  t) v∷ v[ R.var n [] ]))


module ToTerm where

 toTerm : CuCtx → CuTerm → R.Term

 toTermA : CuCtx → List (R.Arg CuArg) → List (R.Arg R.Term)


 mkSFTrm : CuCtx → SubFace × CuTerm → R.Term 
 mkSFTrm ctx (sf , cu) =
   R.def (quote constPartial)
    (toTerm (("𝒛" , nothing) ∷ applyFaceConstraints sf ctx) cu v∷
       v[ liftVars (SubFace→TermInCtx ctx sf) ])
 
 toSides : CuCtx → List (SubFace × CuTerm) → R.Term
 toSides ctx [] = R.pat-lam [] []
 toSides ctx (x ∷ []) = mkSFTrm ctx x

 

 toSides ctx ((sf , cu) ∷ xs@(_ ∷ _)) =
   R.def (quote primPOr)
     (liftVars (SubFace→TermInCtx ctx sf) v∷ R.unknown v∷
        (mkSFTrm ctx (sf , cu)) v∷ v[ toSides ctx xs ])

 toTermA ctx [] = []
 toTermA ctx (R.arg i (iArg x) ∷ xs) =
    R.arg i (IExpr→TermInCtx ctx x) ∷  toTermA ctx xs
 toTermA ctx (R.arg i (tArg x) ∷ xs) =
    R.arg i (toTerm ctx x) ∷  toTermA ctx xs 

 toTerm ctx (hco x x₁) =
   R.def (quote hcomp)
     (vlam "𝒛" (toSides ctx x) v∷ v[ toTerm ctx x₁ ])
 toTerm ctx (cell x) = 
   liftWhere (L.map ((λ { (just _) → true ; _ → false }) ∘S snd ) ctx) x
    -- appFreeDimsI ctx (liftVars.rv (length ctx) 0 x)
    -- let d = length $ freeVars ctx
    -- in appNDimsI dim (liftVars.rv d 0 x)
 toTerm ctx (𝒄ong h t) =
  appTH h (toTermA ctx t)

  where
  appTH : TermHead → List (R.Arg R.Term) → R.Term
  appTH (var x) = R.var (length (ctx)  + x )
  appTH (con c) = R.con c
  appTH (def f) = R.def f


toTerm : ℕ → CuTerm → R.Term
toTerm dim = vlamⁿ dim ∘ (ToTerm.toTerm (defaultCtx dim)) 


ppCTn : Bool →  ℕ → ℕ → CuTerm → R.TC (List R.ErrorPart)
ppCTn b =
  ppCT' (λ ctx x →
        do inCuCtx ctx $ do
            nt ← (if b then R.normalise else R.reduce) x
            x'' ← R.formatErrorParts [ nt ]ₑ
            pure [ R.strErr x'' ]) 


ppCT : ℕ → ℕ → CuTerm → R.TC (List R.ErrorPart)
ppCT = ppCTn true


ppCTs : ℕ → ℕ → CuTerm → R.TC (List R.ErrorPart)
ppCTs = ppCT' (λ _ x → pure [ R.strErr "■" ]) 

module cuTermInsLift (k : ℕ) where

 ctila : ℕ →  List (R.Arg CuArg) → List (R.Arg CuArg)

 ctils : List (SubFace × CuTerm) → List (SubFace × CuTerm)
 
 ctil : ℕ → CuTerm → CuTerm
 ctil dim (hco x c) =
   hco (ctils x) (ctil dim c)
 ctil dim (cell x) = cell $ (liftVars.rv k dim x)
 ctil dim (𝒄ong h l) = 𝒄ong h (ctila dim l)

 ctils [] = []
 ctils ((sf , x) ∷ xs) =
   (sf ++ repeat k nothing , ctil (suc (sfDim sf)) x) ∷ ctils xs

 ctila _ [] = []
 ctila dim (R.arg i (iArg x) ∷ xs) = R.arg i (iArg x) ∷ ctila dim xs
 ctila dim (R.arg i (tArg x) ∷ xs) = R.arg i (tArg (ctil dim x)) ∷ ctila dim xs

cuTermInsLift :  ℕ → ℕ → CuTerm → CuTerm
cuTermInsLift = cuTermInsLift.ctil


-- evCellInCtx : CuCtx → List IExpr → R.Term → R.Term 
-- evCellInCtx ctx [] t = t
-- evCellInCtx ctx (x ∷ es) t = 
--   R.def (quote $i) ( evCellInCtx ctx es t v∷ v[ IExpr→TermInCtx ctx x ])

-- evCell :  List IExpr → R.Term → R.Term 
-- evCell [] t = t
-- evCell (x ∷ es) t = 
--   R.def (quote $i) ( evCell es t v∷ v[ IExpr→Term x ])


-- remapCell : ℕ → List IExpr → R.Term → R.Term 
-- remapCell dim es t = 
--   vlamⁿ dim (evCell es (liftVars.rv dim 0 t)) 


-- remapIExpr : List IExpr → IExpr → IExpr
-- remapIExpr es =
--   foldl (λ x y →
--        --   R.def (quote _∨_) (x v∷
--        -- v[ foldl (λ x (b , k) → R.def (quote _∧_) (x v∷
--        --        v[ (let x' = R.var (k) []
--        --                x'' = if b then x' else R.def (quote ~_) v[ x' ]
--        --            in x'')
--        --            ] ))
--        --         (R.con (quote i1) []) y ] ))
--        x ∨' foldl (λ x (b , k) →
--           let k' = lookupAlways [] es k
--           in x ∧' (if b then k' else ~' k')) [] y
--               )
--      []


-- -- remapSubFace : ℕ → List IExpr → SubFace → FExpr
-- -- remapSubFace = {!!}


-- mapVarsInIExpr : (ℕ → ℕ) → IExpr → IExpr
-- mapVarsInIExpr f = L.map (L.map (map-snd f))

-- liftIExpr : IExpr → IExpr
-- liftIExpr = mapVarsInIExpr suc


-- -- _++pa_ : List (SubFace × CuTerm) → List (SubFace × CuTerm) → List (SubFace × CuTerm)
-- -- _++pa_ = {!!}

-- -- module RemapCu where

-- --  remapCuA : ℕ → List IExpr → List (R.Arg CuArg) → List (R.Arg CuArg)

-- --  remapCuS : ℕ → List IExpr → List (SubFace × CuTerm) → List (SubFace × CuTerm)

-- --  remapCu : ℕ → List IExpr → CuTerm → CuTerm
-- --  remapCu dim es (hco x x₁) =
-- --    hco
-- --      ( remapCuS dim es x)
-- --      ( remapCu dim es x₁)
-- --  remapCu dim es (cell x) = cell (remapCell dim es x) 
-- --  remapCu dim es (𝒄ong th ta) = 𝒄ong th (remapCuA dim es ta)

-- --  remapCuA dim es [] = []
-- --  remapCuA dim es (R.arg i (iArg x) ∷ xs) =
-- --     R.arg i (iArg (remapIExpr es x)) ∷ remapCuA dim es xs
-- --  remapCuA dim es (R.arg i (tArg x) ∷ xs) = 
-- --     R.arg i (tArg (remapCu dim es x)) ∷ remapCuA dim es xs

-- --  remapCuS dim es [] = []
-- --  remapCuS dim es ((sf , x) ∷ xs) =
-- --    (let sfs = remapSubFace dim es sf
-- --         es' : List (IExpr)
-- --         es' = [ [ true , 0 ] ] ∷ L.map liftIExpr es
-- --     in L.map (λ sf' → sf' , remapCu (suc (sfDim sf')) {!!} x )
-- --            sfs)


-- --      ++pa  (remapCuS dim es xs)
