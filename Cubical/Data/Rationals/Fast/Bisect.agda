module Cubical.Data.Rationals.Fast.Bisect where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Involution

open import Cubical.Functions.Logic using (_⊔′_; ⇔toPath)

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fast.Int.Base as ℤ using (ℤ;pos;negsuc)
import Cubical.Data.Bool as 𝟚
open import Cubical.Data.Fast.Int.Properties as ℤ using ()
open import Cubical.Data.Fast.Int.Order as ℤ using ()
open import Cubical.Data.Fast.Int.Divisibility as ℤ

open import Cubical.Data.Nat as ℕ using (ℕ; suc; zero;znots)
open import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.List
import Cubical.Data.Fin as Fin
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr; isProp⊎)

open import Cubical.HITs.PropositionalTruncation as ∥₁ using (isPropPropTrunc; ∣_∣₁)
open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base


open import Cubical.Data.Rationals.Fast.Base as ℚ
open import Cubical.Data.Rationals.Fast.Properties
open import Cubical.Data.Rationals.Fast.Order
open import Cubical.Data.Rationals.Fast.Order.Properties
open import Cubical.Data.Bool

open import Cubical.Algebra.CommRing.Instances.Rationals.Fast
open import Cubical.Tactics.CommRingSolverFast.IntPlusReflection
open import Cubical.Tactics.CommRingSolverFast.RationalsReflection
open import Cubical.Tactics.CommRingSolverFast.FastRationalsReflectionPre

open import Cubical.Foundations.Powerset


module RawBisection (f : ℚ → Bool) where 

 bisectStepRaw : (a b : ℚ) → ℚ × ℚ
 bisectStepRaw a b = choose (f m)
   where

     half : ℚ
     half = [ pos 1 / 1+ 1 ]        -- 1/2

     m : ℚ
     m = reduce ((a + b) · half)

     choose : Bool → ℚ × ℚ
     choose true = a , m
     choose false = m , b

 -- Run exactly n steps, returning the final endpoints.
 -- Again: no proofs that the result is inside [a,b], etc.
 bisectNRaw : (n : ℕ) → (a b : ℚ) → ℚ × ℚ
 bisectNRaw zero    a b = a , b
 bisectNRaw (suc n) a b =
   next (bisectStepRaw a b)
   where
     next : ℚ × ℚ → ℚ × ℚ
     next (a' , b') = bisectNRaw n a' b'



module RootFromRawBisection (deg : ℕ) (x : ℕ) where

  open RawBisection (λ q → Dec→Bool (≤Dec (fromNat x) (q ℚ^ⁿ deg)))

  rootRaw : ℕ → ℚ
  rootRaw n = snd (bisectNRaw n 0 (fromNat x))


  rootRawErr : ℕ → ℚ
  rootRawErr n = reduce (abs ((snd (bisectNRaw n 0 (fromNat x)) ℚ^ⁿ deg) - fromNat x))


-- rootRawTest : ℚ
-- rootRawTest = {!RootFromRawBisection.rootRawErr 2 2 102!}


-1ⁿ : ℕ → ℤ
-1ⁿ zero = 1
-1ⁿ (suc zero) = -1
-1ⁿ (suc (suc x)) = -1ⁿ x

module Baseₙ (base : ℕ) where

 -- floor[x·base^m] : ℕ → ℕ → ℕ → ℕ
 -- floor[x·base^m] p q m = p ℕ.· (base ℕ.^ m) ℕ.mod q

 -- digitsOfInt : ℕ → List (Fin.Fin base)
 -- digitsOfInt = {!!}
 
 -- digits' : ℕ → ℕ → ℕ → List (Fin.Fin base)
 -- digits' p q m =
 --  {!!}

 -- digits : ℚ → ℕ → List (Fin.Fin base) 
 -- digits q n = {!23 ℕ.mod 10!}

-- module Ramanujan–Sato-π where


--  p : ℕ → ℚ
--  p k =  [  (pos (((4 ℕ.· k) ℕ.!) ℕ.·
--             ((26390 ℕ.· k) ℕ.+ 1103))) /
--               1+ (((((k ℕ.!) ℕ.^ 4)
--                ℕ.· (396 ℕ.^ (4 ℕ.· k))) ℕ.∸ 1)) ]

--  s : ℕ → ℚ
--  s zero = reduce (p 0)
--  s (suc x) = reduce (s x + reduce (p (suc x)))



--  fctr : ℚ
--  fctr = 
--    (reduce (2 · (RootFromRawBisection.rootRaw 2 2 100) · [ 1 / fromNat 9801 ]))


--  π : ℕ → ℚ
--  π k = reduce ((fctr · s k))

--  _ : ℚ
--  _ = {!π 5!}



-- -- private
-- --  variable
-- --   ℓ : Level

-- -- record DecidableCut : Type₁ where
-- --  constructor decCut
-- --  field
-- --   P : ℙ ℚ
-- --   P? : ∀ q → Dec (q ∈ P)
-- --   P< : ∀ x y → x < y → x ∈ P → y ∈ P
-- --   <P : ∀ x y → x < y → ¬ (y ∈ P) → ¬ (x ∈ P)


-- --  BisectWitness : (a b : ℚ) (ε : ℚ₊) → Type
-- --  BisectWitness a b ε =
-- --   Σ-syntax ℚ (λ l →
-- --   Σ-syntax ℚ (λ h →
-- --       (a ≤ l)
-- --     × (l < h)
-- --     × (h ≤ b)
-- --     × (h - l < fst ε)
-- --     × (¬ (l ∈ P))
-- --     × (h ∈ P)))

-- --  record Bracket (a b : ℚ) : Type where
-- --   constructor bracket
-- --   field
-- --    a<b : a < b
-- --    a∉P : ¬ (a ∈ P)
-- --    b∈P :   (b ∈ P)


-- --  noWitness-leftInP :
-- --    ∀ {a b : ℚ} {ε : ℚ₊} → (a ∈ P) → ¬ BisectWitness a b ε
-- --  noWitness-leftInP {a} {b} {ε} a∈P
-- --    (l , h , a≤l , l<h , h≤b , h-l<ε , l∉P , h∈P) =
-- --    case ≤→<⊎≡ a l a≤l of λ where
-- --      (inl a≡l) → l∉P (subst (λ q → q ∈ P) a≡l a∈P)
-- --      (inr a<l) → l∉P (P< a l a<l a∈P)

-- --  noWitness-rightNotInP :
-- --    ∀ {a b : ℚ} {ε : ℚ₊} → ¬ (b ∈ P) → ¬ BisectWitness a b ε
-- --  noWitness-rightNotInP {a} {b} {ε} b∉P
-- --    (l , h , a≤l , l<h , h≤b , h-l<ε , l∉P , h∈P) =
-- --    case ≤→<⊎≡ h b h≤b of λ where
-- --      (inl h≡b) → b∉P (subst (λ q → q ∈ P) h≡b h∈P)
-- --      (inr h<b) → (<P h b h<b b∉P) h∈P

-- --  half : ℚ
-- --  half = [ pos 1 / 1+ 1 ]   -- 1/2

 
-- --  mid : ℚ → ℚ → ℚ
-- --  mid a b = (a + b) · half

-- --  a<mid<b :
-- --    ∀ {a b : ℚ} → a < b → (a < mid a b) × (mid a b < b)
-- --  a<mid<b a<b = {!!} , {!!}

-- --  width-left :
-- --    ∀ {a b : ℚ} → (a<b : a < b) → (mid a b - a) ≡ (b - a) · half
-- --  width-left a<b = ℚ!

-- --  width-right :
-- --    ∀ {a b : ℚ} → (a<b : a < b) → (b - mid a b) ≡ (b - a) · half
-- --  width-right a<b = ℚ!

-- --  halfPow : ℕ → ℚ
-- --  halfPow zero    = 1
-- --  halfPow (suc n) = (halfPow n) · half

-- --  Refined : (n : ℕ) (a b : ℚ) → Bracket a b → Type
-- --  Refined n a b br =
-- --   Σ[ l ∈ ℚ ] Σ[ h ∈ ℚ ]
-- --       (a ≤ l)
-- --     × (l < h)
-- --     × (h ≤ b)
-- --     × (¬ (l ∈ P))
-- --     × (h ∈ P)
-- --     × (h - l ≡ (b - a) · halfPow n)

-- --  refine : (n : ℕ) (a b : ℚ) (br : Bracket a b) → Refined n a b br
-- --  refine zero a b br =
-- --   a , b ,
-- --     isRefl≤ a ,
-- --     Bracket.a<b br ,
-- --     isRefl≤ b ,
-- --     Bracket.a∉P br ,
-- --     Bracket.b∈P br ,
-- --     ℚ!

-- --  refine (suc n) a b br = refineStep (P? m)
-- --   where
-- --   a<b : a < b
-- --   a<b = Bracket.a<b br

-- --   m : ℚ
-- --   m = mid a b

-- --   refineStep : Dec (m ∈ P) → Refined (suc n) a b br
-- --   refineStep (yes m∈P) =
-- --     -- recurse on [a , m]
-- --     let
-- --       a<m : a < m
-- --       a<m = fst (a<mid<b a<b)

-- --       brL : Bracket a m
-- --       brL = bracket a<m (Bracket.a∉P br) m∈P

-- --       ih : Refined n a m brL
-- --       ih = refine n a m brL

-- --       -- unpack ih
-- --       l : ℚ
-- --       l = fst ih

-- --       h : ℚ
-- --       h = fst (snd ih)

-- --       a≤l : a ≤ l
-- --       a≤l = fst (snd (snd ih))

-- --       l<h : l < h
-- --       l<h = fst (snd (snd (snd ih)))

-- --       h≤m : h ≤ m
-- --       h≤m = fst (snd (snd (snd (snd ih))))

-- --       l∉P : ¬ (l ∈ P)
-- --       l∉P = fst (snd (snd (snd (snd (snd ih)))))

-- --       h∈P : h ∈ P
-- --       h∈P = fst (snd (snd (snd (snd (snd (snd ih))))))

-- --       w≡ : (h - l) ≡ (m - a) · halfPow n
-- --       w≡ = snd (snd (snd (snd (snd (snd (snd ih))))))

-- --       m≤b : m ≤ b
-- --       m≤b = <Weaken≤ m b (snd (a<mid<b a<b))

-- --       h≤b : h ≤ b
-- --       h≤b = isTrans≤ h m b h≤m m≤b

-- --       w≡' : (h - l) ≡ (b - a) · halfPow (suc n)
-- --       w≡' = {!width-left a<b!}
-- --       -- idea: use w≡ plus width-left a<b and algebra:
-- --       --   m - a ≡ (b - a)·half
-- --       --   (m-a)·halfPow n ≡ (b-a)·(half·halfPow n) ≡ (b-a)·halfPow (suc n)
-- --     in
-- --       l , h , a≤l , l<h , h≤b , l∉P , h∈P , w≡'

-- --   refineStep (no m∉P) =
-- --     -- recurse on [m , b]
-- --     let
-- --       m<b : m < b
-- --       m<b = snd (a<mid<b a<b)

-- --       brR : Bracket m b
-- --       brR = bracket m<b m∉P (Bracket.b∈P br)

-- --       ih : Refined n m b brR
-- --       ih = refine n m b brR

-- --       l : ℚ
-- --       l = fst ih

-- --       h : ℚ
-- --       h = fst (snd ih)

-- --       m≤l : m ≤ l
-- --       m≤l = fst (snd (snd ih))

-- --       l<h : l < h
-- --       l<h = fst (snd (snd (snd ih)))

-- --       h≤b : h ≤ b
-- --       h≤b = fst (snd (snd (snd (snd ih))))

-- --       l∉P : ¬ (l ∈ P)
-- --       l∉P = fst (snd (snd (snd (snd (snd ih)))))

-- --       h∈P : h ∈ P
-- --       h∈P = fst (snd (snd (snd (snd (snd (snd ih))))))

-- --       w≡ : (h - l) ≡ (b - m) · halfPow n
-- --       w≡ = snd (snd (snd (snd (snd (snd (snd ih))))))

-- --       a≤m : a ≤ m
-- --       a≤m = <Weaken≤ a m (fst (a<mid<b a<b))

-- --       a≤l : a ≤ l
-- --       a≤l = isTrans≤ a m l a≤m m≤l

-- --       w≡' : (h - l) ≡ (b - a) · halfPow (suc n)
-- --       w≡' = {!!}
-- --       -- idea: use w≡ plus width-right a<b and algebra:
-- --       --   b - m ≡ (b - a)·half
-- --       --   (b-m)·halfPow n ≡ (b-a)·halfPow (suc n)
-- --     in
-- --       l , h , a≤l , l<h , h≤b , l∉P , h∈P , w≡'

-- --  ----------------------------------------------------------------------
-- --  -- 5) Fuel: compute n so that (b-a)·halfPow n < ε, and prove it.
-- --  --    This is the “termination via distance vs nat fuel” bridge.
-- --  ----------------------------------------------------------------------

-- --  fuel : (a b : ℚ) → a < b → (ε : ℚ₊) → ℕ
-- --  fuel a b a<b ε = {!!}

-- --  fuelSound :
-- --    ∀ (a b : ℚ) (a<b : a < b) (ε : ℚ₊)
-- --      → (b - a) · halfPow (fuel a b a<b ε) < fst ε
-- --  fuelSound a b a<b ε = {!!}

-- --  ----------------------------------------------------------------------
-- --  -- 6) Construct BisectWitness from the refined interval + fuelSound
-- --  ----------------------------------------------------------------------

-- --  buildWitness :
-- --    (a b : ℚ) (a<b : a < b) (ε : ℚ₊)
-- --    → ¬ (a ∈ P) → (b ∈ P) → BisectWitness a b ε
-- --  buildWitness a b a<b ε a∉P b∈P =
-- --   let
-- --     br : Bracket a b
-- --     br = bracket a<b a∉P b∈P

-- --     n : ℕ
-- --     n = fuel a b a<b ε

-- --     r : Refined n a b br
-- --     r = refine n a b br

-- --     l : ℚ
-- --     l = fst r

-- --     h : ℚ
-- --     h = fst (snd r)

-- --     a≤l : a ≤ l
-- --     a≤l = fst (snd (snd r))

-- --     l<h : l < h
-- --     l<h = fst (snd (snd (snd r)))

-- --     h≤b : h ≤ b
-- --     h≤b = fst (snd (snd (snd (snd r))))

-- --     l∉P : ¬ (l ∈ P)
-- --     l∉P = fst (snd (snd (snd (snd (snd r)))))

-- --     h∈P : h ∈ P
-- --     h∈P = fst (snd (snd (snd (snd (snd (snd r))))))

-- --     w≡ : (h - l) ≡ (b - a) · halfPow n
-- --     w≡ = snd (snd (snd (snd (snd (snd (snd r))))))

-- --     h-l<ε : (h - l) < fst ε
-- --     h-l<ε = subst (λ t → t < fst ε) (sym w≡) (fuelSound a b a<b ε)
-- --   in
-- --     l , h , a≤l , l<h , h≤b , h-l<ε , l∉P , h∈P

-- --  ----------------------------------------------------------------------
-- --  -- 7) Final decision: ONLY decide endpoint feasibility, then build
-- --  --    (helper does the pattern match; NO "with" used)
-- --  ----------------------------------------------------------------------

-- --  bisect : (a b : ℚ) → a < b → (ε : ℚ₊) → Dec (BisectWitness a b ε)
-- --  bisect a b a<b ε = bisectCase (P? a) (P? b)
-- --   where
-- --   bisectCase : Dec (a ∈ P) → Dec (b ∈ P) → Dec (BisectWitness a b ε)
-- --   bisectCase (yes a∈P) _ =
-- --     no (noWitness-leftInP {a = a} {b = b} {ε = ε} a∈P)

-- --   bisectCase (no a∉P) (no b∉P) =
-- --     no (noWitness-rightNotInP {a = a} {b = b} {ε = ε} b∉P)

-- --   bisectCase (no a∉P) (yes b∈P) =
-- --     yes (buildWitness a b a<b ε a∉P b∈P)
