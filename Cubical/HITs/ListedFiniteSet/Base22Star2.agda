{-# OPTIONS --safe   #-} --experimental-lossy-unification 
module Cubical.HITs.ListedFiniteSet.Base22Star2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)
open import Cubical.Data.Nat
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Sigma

open import Cubical.Data.FinData.Transpositions

import Cubical.Functions.Logic as Lo
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv

open import Cubical.Foundations.Function
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path

open import Cubical.Foundations.Univalence


open import Cubical.HITs.EilenbergMacLane1

-- open import Cubical.Data.FinData

open import Cubical.Data.Nat.Order.Recursive

import Cubical.Data.SumFin as F


open import Cubical.HITs.ListedFiniteSet.Base3

-- open import Cubical.Data.FinData.GTrun

import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.GroupoidTruncation as GT
open import Cubical.HITs.SetTruncation as ST


open import Cubical.Functions.Involution

open import Cubical.Homotopy.EilenbergMacLane.Properties

open import Cubical.Data.FinSet


open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.SymmetricGroup
open import Cubical.Algebra.Group.Generators

private
  variable
    ℓ : Level
    A B : Type ℓ

mb≡ : {A' : Type} → 
         {f : Maybe A' → A}
         {g : Maybe A' → A}
         → f nothing  ≡ g nothing
         → f ∘ just ≡ g ∘ just
         → f ≡ g
mb≡ n≡ j≡ i nothing = n≡ i
mb≡ n≡ j≡ i (just x) = j≡ i x

mb3≡ : {A' : Type} → 
         {f : Maybe (Maybe (Maybe A')) → A}
         {g : Maybe (Maybe (Maybe A')) → A}
         → f nothing  ≡ g nothing
         → f (just nothing) ≡ g (just nothing)
         → f (just (just nothing)) ≡ g (just (just nothing))
         → f ∘' just ∘' just ∘' just ≡ g ∘' just ∘' just ∘' just
        → f ≡ g
mb3≡ a a' a'' f i nothing = a i
mb3≡ a a' a'' f i (just nothing) = a' i
mb3≡ a a' a'' f i (just (just nothing)) = a'' i
mb3≡ a a' a'' f i (just (just (just x))) = f i x


mbSqP : {A' : I → I → Type} → 
  {a₀₀ : Maybe (A' i0 i0) → A}
  {a₀₁ : Maybe (A' i0 i1) → A}
  (a₀₋ : PathP (λ j → Maybe (A' i0 j) → A) a₀₀ a₀₁)
  {a₁₀ : Maybe (A' i1 i0) → A}
  {a₁₁ : Maybe (A' i1 i1) → A}
  (a₁₋ : PathP (λ j → Maybe (A' i1 j) → A) a₁₀ a₁₁)
  (a₋₀ : PathP (λ i → Maybe (A' i i0) → A) a₀₀ a₁₀)
  (a₋₁ : PathP (λ i → Maybe (A' i i1) → A) a₀₁ a₁₁)
  → Square (λ j → a₀₋ j nothing)
           (λ j → a₁₋ j nothing)
           (λ i → a₋₀ i nothing)
           (λ i → a₋₁ i nothing)
  → SquareP (λ i j → A' i j → A) 
           (λ j → a₀₋ j ∘ just)
           (λ j → a₁₋ j ∘ just)
           (λ i → a₋₀ i ∘ just)
           (λ i → a₋₁ i ∘ just)
           

  → SquareP (λ i j → Maybe (A' i j) → A)
         a₀₋ a₁₋ a₋₀ a₋₁
mbSqP a₀₋ a₁₋ a₋₀ a₋₁ sq-n sq-j i j nothing = sq-n i j
mbSqP a₀₋ a₁₋ a₋₀ a₋₁ sq-n sq-j i j (just x) = sq-j i j x

mb3sq : {A' : Type} → 
           {a₀₀ a₀₁ : Maybe (Maybe (Maybe A')) → A} {a₀₋ : a₀₀ ≡ a₀₁}
           {a₁₀ a₁₁ : Maybe (Maybe (Maybe A')) → A} {a₁₋ : a₁₀ ≡ a₁₁}
           {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
         → Square (funExt⁻ a₀₋ nothing) (funExt⁻ a₁₋ nothing)
                  (funExt⁻ a₋₀ nothing) (funExt⁻ a₋₁ nothing)
         → Square (funExt⁻ a₀₋ (just nothing)) (funExt⁻ a₁₋ (just nothing))
                  (funExt⁻ a₋₀ (just nothing)) (funExt⁻ a₋₁ (just nothing))
         → Square (funExt⁻ a₀₋ (just (just nothing)))
                  (funExt⁻ a₁₋ (just (just nothing)))
                  (funExt⁻ a₋₀ (just (just nothing)))
                  (funExt⁻ a₋₁ (just (just nothing)))
         → Square (cong (_∘' just ∘' just ∘' just) a₀₋ )
                  (cong (_∘' just ∘' just ∘' just) a₁₋ )
                  (cong (_∘' just ∘' just ∘' just) a₋₀ )
                  (cong (_∘' just ∘' just ∘' just) a₋₁ )
        → Square a₀₋ a₁₋ a₋₀ a₋₁
mb3sq a a' a'' f i j nothing = a i j
mb3sq a a' a'' f i j (just nothing) = a' i j
mb3sq a a' a'' f i j (just (just nothing)) = a'' i j
mb3sq a a' a'' f i j (just (just (just x))) = f i j x


sqWhisk : 
  (A : I → I → Type ℓ)
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
  {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
  (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
  {a₀₀' : A i0 i0} {a₀₁' : A i0 i1} (a₀₋' : PathP (λ j → A i0 j) a₀₀' a₀₁')
  {a₁₀' : A i1 i0} {a₁₁' : A i1 i1} (a₁₋' : PathP (λ j → A i1 j) a₁₀' a₁₁')
  (a₋₀' : PathP (λ i → A i i0) a₀₀' a₁₀') (a₋₁' : PathP (λ i → A i i1) a₀₁' a₁₁')
  → (sq : SquareP A a₀₋ a₁₋ a₋₀ a₋₁)
  → {p₀₀ : PathP (λ i → A i0 i0) a₀₀ a₀₀'}
    {p₀₁ : PathP (λ i → A i0 i1) a₀₁ a₀₁'} 
    {p₁₀ : PathP (λ i → A i1 i0) a₁₀ a₁₀'}
    {p₁₁ : PathP (λ i → A i1 i1) a₁₁ a₁₁'}
  →   
  (sq₀₋ : SquareP (λ _ j → A i0 j) a₀₋ a₀₋' p₀₀ p₀₁)
  (sq₁₋ : SquareP (λ _ j → A i1 j) a₁₋ a₁₋' p₁₀ p₁₁)
  (sq₋₀ : SquareP (λ _ i → A i i0) a₋₀ a₋₀' p₀₀ p₁₀)
  (sq₋₁ : SquareP (λ _ i  → A i i1) a₋₁ a₋₁' p₀₁ p₁₁)
  → SquareP A a₀₋' a₁₋' a₋₀' a₋₁'
  
sqWhisk A a₀₋ a₁₋ a₋₀ a₋₁ a₀₋' a₁₋' a₋₀' a₋₁' sq sq₀₋ sq₁₋ sq₋₀ sq₋₁ i j =
   hcomp
     ((λ z → λ {
     (i =  i0) → sq₀₋ z j 
     ;(i = i1) → sq₁₋ z j
     ;(j = i0) → sq₋₀ z i
     ;(j = i1) → sq₋₁ z i
     }))
     (sq i j)

sqWhisk' : 
  (A : I → I → Type ℓ)
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
  {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
  (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
  {a₀₀' : A i0 i0} {a₀₁' : A i0 i1} (a₀₋' : PathP (λ j → A i0 j) a₀₀' a₀₁')
  {a₁₀' : A i1 i0} {a₁₁' : A i1 i1} (a₁₋' : PathP (λ j → A i1 j) a₁₀' a₁₁')
  (a₋₀' : PathP (λ i → A i i0) a₀₀' a₁₀') (a₋₁' : PathP (λ i → A i i1) a₀₁' a₁₁')
  → (sq : SquareP A a₀₋ a₁₋ a₋₀ a₋₁)
  → {p₀₀ : PathP (λ i → A i0 i0) a₀₀ a₀₀'}
    {p₀₁ : PathP (λ i → A i0 i1) a₀₁ a₀₁'} 
    {p₁₀ : PathP (λ i → A i1 i0) a₁₀ a₁₀'}
    {p₁₁ : PathP (λ i → A i1 i1) a₁₁ a₁₁'}
  →   
  (sq₀₋ : SquareP (λ j _ → A i0 j) p₀₀ p₀₁ a₀₋ a₀₋')
  (sq₁₋ : SquareP (λ j _ → A i1 j) p₁₀ p₁₁ a₁₋ a₁₋')
  (sq₋₀ : SquareP (λ i _ → A i i0) p₀₀ p₁₀ a₋₀ a₋₀')
  (sq₋₁ : SquareP (λ i _  → A i i1) p₀₁ p₁₁ a₋₁ a₋₁')
  → SquareP A a₀₋' a₁₋' a₋₀' a₋₁'
  
sqWhisk' A a₀₋ a₁₋ a₋₀ a₋₁ a₀₋' a₁₋' a₋₀' a₋₁' sq sq₀₋ sq₁₋ sq₋₀ sq₋₁ i j =
   hcomp
     ((λ z → λ {
     (i =  i0) → sq₀₋ j z 
     ;(i = i1) → sq₁₋ j z
     ;(j = i0) → sq₋₀ i z
     ;(j = i1) → sq₋₁ i z
     }))
     (sq i j)


unglue-Sq-elim' : ∀ {ℓ'} {A : Type  ℓ} {C : Type ℓ'} → (ϕ : I → I → I) →
         (e : ∀ i j → Partial (ϕ i j) (Σ-syntax (Type ℓ) (λ T → T ≃ _))) →
       ∀ {a₀₀ a₀₁ a₁₀ a₁₁} 
       {a₀₋ : PathP _ a₀₀ a₀₁}
       {a₁₋ : PathP _ a₁₀ a₁₁}
       {a₋₀ : PathP _ a₀₀ a₁₀}
       {a₋₁ : PathP _ a₀₁ a₁₁}
       → SquareP (λ i j → A → C)
           a₀₋
           a₁₋
           a₋₀
           a₋₁
       → SquareP (λ i j → Glue A {ϕ i j} (e i j) → C)
           (λ j → a₀₋ j ∘ unglue (ϕ i0 j))
           (λ j → a₁₋ j ∘ unglue (ϕ i1 j))
           (λ i → a₋₀ i ∘ unglue (ϕ i i0))
           (λ i → a₋₁ i ∘ unglue (ϕ i i1))
unglue-Sq-elim' ϕ e x  i j = x i j ∘ unglue (ϕ i j)


unglue-Sq-elim'' : ∀ {ℓ'} {A : Type  ℓ} {C : Type ℓ'} → (ϕ : I) →
         (e : ∀ i j → Partial (ϕ) (Σ-syntax (Type ℓ) (λ T → T ≃ _))) →
       ∀ {a₀₀ a₀₁ a₁₀ a₁₁} 
       {a₀₋ : PathP _ a₀₀ a₀₁}
       {a₁₋ : PathP _ a₁₀ a₁₁}
       {a₋₀ : PathP _ a₀₀ a₁₀}
       {a₋₁ : PathP _ a₀₁ a₁₁}
       -- (f : {!!})
       → (f : ∀ i j → Partial (i ∨ ~ i ∨ j ∨ ~ j) (
             A → Glue A (e i j)))
       → (f= : ∀ i j → PartialP (i ∨ ~ i ∨ j ∨ ~ j) (λ o →
                (a : Glue A (e i j)) →
                  f i j o (unglue ϕ a) ≡ a) ) 
       → SquareP (λ i j → A → C)
           (λ j → a₀₋ j ∘ f i0 j 1=1)
           (λ j → a₁₋ j ∘ f i1 j 1=1)
           (λ i → a₋₀ i ∘ f i i0 1=1)
           (λ i → a₋₁ i ∘ f i i1 1=1)
       → SquareP (λ i j → Glue A {ϕ} (e i j) → C)
           a₀₋
           a₁₋
           a₋₀
           a₋₁
unglue-Sq-elim'' ϕ e {a₀₋ = a₀₋} {a₁₋} {a₋₀} {a₋₁} f f= sq i j =
  hcomp {φ = i ∨ ~ i ∨ j ∨ ~ j}      
     (λ z → λ {
     (i =  i0) → a₀₋ j ∘' (λ x → f= i j 1=1 x z) 
     ;(i = i1) → a₁₋ j ∘' (λ x → f= i j 1=1 x z)
     ;(j = i0) → a₋₀ i ∘' (λ x → f= i j 1=1 x z)
     ;(j = i1) → a₋₁ i ∘' (λ x → f= i j 1=1 x z)
     })
     (sq i j ∘ unglue ϕ)


-- unglue-Sq-elim'' : ∀ {ℓ'} {A B : Type  ℓ} {C : Type ℓ'} → (ϕ : I → I → I) →
--          (e : ∀ i j → Partial (ϕ i j) (Σ-syntax (Type ℓ) (λ T → T ≃ _))) →
--        ∀ {a₀₀ a₀₁ a₁₀ a₁₁} 
--        {a₀₋ : PathP _ a₀₀ a₀₁}
--        {a₁₋ : PathP _ a₁₀ a₁₁}
--        {a₋₀ : PathP _ a₀₀ a₁₀}
--        {a₋₁ : PathP _ a₀₁ a₁₁}
--        -- (f : {!!})
--        → (f : ∀ i j → Partial (i ∨ ~ i ∨ j ∨ ~ j) (
--              A → Glue A (e i j)))
--        → (f= : ∀ i j → PartialP (i ∨ ~ i ∨ j ∨ ~ j) (λ o →
--                 (a : Glue A (e i j)) →
--                   f i j o (unglue (ϕ i j) a) ≡ a) ) 
--        → SquareP (λ i j → A → C)
--            (λ j → a₀₋ j ∘ f i0 j 1=1)
--            (λ j → a₁₋ j ∘ f i1 j 1=1)
--            (λ i → a₋₀ i ∘ f i i0 1=1)
--            (λ i → a₋₁ i ∘ f i i1 1=1)
--        → SquareP (λ i j → Glue A {ϕ i j} (e i j) → C)
--            a₀₋
--            a₁₋
--            a₋₀
--            a₋₁
-- unglue-Sq-elim'' ϕ e {a₀₋ = a₀₋} {a₁₋} {a₋₀} {a₋₁} f f= sq i j =
--   hcomp {φ = i ∨ ~ i ∨ j ∨ ~ j}      
--      (λ z → λ {
--      (i =  i0) → a₀₋ j ∘' (λ x → f= i j 1=1 x z) 
--      ;(i = i1) → a₁₋ j ∘' (λ x → f= i j 1=1 x z)
--      ;(j = i0) → a₋₀ i ∘' (λ x → f= i j 1=1 x z)
--      ;(j = i1) → a₋₁ i ∘' (λ x → f= i j 1=1 x z)
--      })
--      ?
--      -- (sq i j ∘ unglue (ϕ i j))




-- unglue-Sq-elim : ∀ {ℓ'} {A B : Type  ℓ} {C : Type ℓ'} → (ϕ : I) →
--          (e : ∀ i j → Partial (ϕ) (Σ-syntax (Type ℓ) (λ T → T ≃ _))) →
--          -- (f : ∀ i j → PartialP (ϕ i j) (
--          --    λ o → A → fst (e i j o))) →
--         (f : I → I → (A → C)) →
--        ∀ {a₀₀ a₀₁ a₁₀ a₁₁} 
--        {a₀₋ : PathP _ a₀₀ a₀₁}
--        {a₁₋ : PathP _ a₁₀ a₁₁}
--        {a₋₀ : PathP _ a₀₀ a₁₀}
--        {a₋₁ : PathP _ a₀₁ a₁₁}
--        → 
--          -- (g : ∀ i j →
--          --  PartialP (ϕ i j)
--          --    λ o → fst (e i j o))
--          -- → (sq : ∀ i j → PartialP
--          --           (ϕ i j)
--          --           λ o → Σ (A → C)
--          --                (λ f' → (f' ∘ fst (snd (e i j o))) ≡ {!!})

--          --           )
--       -- (g : ∀ i j →
--       --     PartialP (ϕ)
--       --       λ o → fst (e i j o))
--       --    → (sq : ∀ i j → PartialP {a = ℓ-max ℓ ℓ'} 
--       --              ((i ∨ ~ i ∨ j ∨ ~ j) ∧ (ϕ)) 
--       --           -- let ϕ' = ϕ i j in 
--       --             λ {
--       --          (i = i0)(ϕ = i1) → f i j ∘ fst (snd (e i j 1=1)) ≡ a₀₋ j 
--       --         ;(i = i1)(ϕ = i1) → f i j ∘ fst (snd (e i j 1=1)) ≡ a₁₋ j
--       --         ;(j = i0)(ϕ = i1) → f i j ∘ fst (snd (e i j 1=1)) ≡ a₋₀ i
--       --         ;(j = i1)(ϕ = i1) → f i j ∘ fst (snd (e i j 1=1)) ≡ a₋₁ i
--       --         }
--       --         ) → 
--       (g : ∀ i j z → 
--           Sub C {!!} {!!}
--               )
     
--        -- → (∀ i j → (IsOne (i ∨ ~ i ∨ j ∨ ~ j) → IsOne ϕ))
--        → SquareP (λ i j → Glue A {ϕ} (e i j) → C)
--            a₀₋
--            a₁₋
--            a₋₀
--            a₋₁
-- unglue-Sq-elim ϕ e f sq i j =
--    hcomp {φ = i ∨ ~ i ∨ j ∨ ~ j}      
--      (λ z → λ {
--      (i =  i0) → {!sq i j (q i j 1=1) !}
--      ;(i = i1) → {!!}
--      ;(j = i0) → {!!}
--      ;(j = i1) → {!!}
--      })
--      {!x i j ∘ unglue (ϕ i j)!}



-- lemSucUA : ∀ {n} → (e : Fin n ≃ Fin n) → ua (sucPerm e) ≡
--                       {!ua e!} 
-- lemSucUA = {!!}

-- isSetMaybe : ∀ {ℓ} {A : Type ℓ}
--    → isSet A → isSet (Maybe A)
-- isSetMaybe x nothing nothing x₂ y₁ = {!!}
-- isSetMaybe x (just x₁) nothing x₂ y₁ = {!!}
-- isSetMaybe x nothing (just x₁) x₂ y₁ = {!!}
-- isSetMaybe x (just x₁) (just x₃) p q =
--   {!MaybePath.decodeEncode x !}

Mb^ : ℕ → (hSet ℓ-zero) → (hSet ℓ-zero) 
Mb^ zero x₁ = x₁
Mb^ (suc x) b' =
  let b = Mb^ x b'
  in Maybe (fst b) , isSetMaybe (snd b)

Mb^-≡-hlpTy : ∀ n → (b : hSet ℓ-zero) → fst (Mb^ n b) → fst (Mb^ n b) → Type  
Mb^-≡-hlpTy zero b x x₁ = x ≡ x₁
Mb^-≡-hlpTy (suc n) b nothing nothing = Unit
Mb^-≡-hlpTy (suc n) b nothing (just x) = ⊥
Mb^-≡-hlpTy (suc n) b (just x) nothing = ⊥
Mb^-≡-hlpTy (suc n) b (just x) (just x₁) = Mb^-≡-hlpTy n b x x₁

Mb^-≡-hlp : ∀ {n} → {b : hSet ℓ-zero} → (x y : fst (Mb^ n b)) →
        x ≡ y → Mb^-≡-hlpTy n b x y 
Mb^-≡-hlp {zero} {b} x y x₁ = x₁
Mb^-≡-hlp {suc n} {b} nothing nothing x₁ = tt
Mb^-≡-hlp {suc n} {b} nothing (just x) = ¬nothing≡just
Mb^-≡-hlp {suc n} {b} (just x) nothing = ¬just≡nothing
Mb^-≡-hlp {suc n} {b} (just x) (just x₂) =
  Mb^-≡-hlp {n} {b} x x₂ ∘ just-inj _ _

Mb^-≡-hlp≃ : ∀ {n} → {b : hSet ℓ-zero} → (x y : fst (Mb^ n b)) →
        Mb^-≡-hlpTy n b x y ≃ (x ≡ y) 
Mb^-≡-hlp≃ {zero} {b} x y = idEquiv _
Mb^-≡-hlp≃ {suc n} {b} nothing nothing =
   isoToEquiv (invIso z)
 where
  z : Iso (nothing ≡ nothing) (Unit)
  Iso.fun z _ = _
  Iso.inv z _ = refl
  Iso.rightInv z _ = refl
  Iso.leftInv z a = isProp-x≡nothing _ _ _
Mb^-≡-hlp≃ {suc n} {b} nothing (just x) =
  uninhabEquiv (idfun _) ¬nothing≡just 
Mb^-≡-hlp≃ {suc n} {b} (just x) nothing =
 uninhabEquiv  (idfun _) ¬just≡nothing
Mb^-≡-hlp≃ {suc n} {b} (just x) (just x₁) =
  Mb^-≡-hlp≃ {n} {b} (x) (x₁) ∙ₑ isoToEquiv (invIso z)
 where
  z : Iso (just x ≡ just x₁) (x ≡ x₁)
  Iso.fun z = just-inj _ _
  Iso.inv z = cong just
  Iso.rightInv z _ = refl
  Iso.leftInv z _ = snd (Mb^ (suc n) b) _ _ _ _


-- Mb^-≡-hlp-elimTy : ∀ {ℓ} → ∀ n → (b : hSet ℓ-zero) →
--     (C : (x x' : fst (Mb^ n b)) → Mb^-≡-hlpTy n b x x' → Type ℓ)
--     → Type ℓ
-- Mb^-≡-hlp-elimTy zero b C = ∀ x₁ x' p → C x₁ x' p
-- Mb^-≡-hlp-elimTy (suc n) b C = {!!}

-- Mb^-≡-hlp-elim : ∀ {ℓ} → ∀ n → (b : hSet ℓ-zero) →
--     (C : (x x' : fst (Mb^ n b)) → Mb^-≡-hlpTy n b x x' → Type ℓ)
--     → Mb^-≡-hlp-elimTy n b C
--     → ∀ x x' → ∀ p → C x x' p
-- Mb^-≡-hlp-elim zero b C x = x
-- Mb^-≡-hlp-elim (suc n) b C x nothing nothing p = {!!}
-- Mb^-≡-hlp-elim (suc n) b C x (just x₁) (just x₂) p = {!!}

funExtDepMb^ : ∀ {ℓ} → ∀ n → (b : hSet ℓ-zero) →
            {P : fst (Mb^ n b) ≡ fst (Mb^ n b)}
            {B : ∀ i → P i → Type ℓ}
            → ∀ {f₀ f₁}
            → (∀ x x' → (p' : Mb^-≡-hlpTy n b (transport P x) x') →
                PathP (λ i → B i
                  (toPathP {A = λ i → P i }
                    (fst (Mb^-≡-hlp≃ {n = n} {b} (transport P x) x') p') i))
                   (f₀ x) (f₁ x')
                  )
            → PathP (λ i → ∀ x → B i x )
                   f₀ f₁            
funExtDepMb^ n b {P} {B} {f₀} {f₁} x =
   funExtDep λ {x₀} {x₁} p →
      (subst {A = PathP (λ z → P z) x₀ x₁}
       {y = p} (λ p → PathP (λ i → B i (p i)) (f₀ x₀) (f₁ x₁))
       
       ((isOfHLevelRespectEquiv 1 (invEquiv (PathP≃Path _ _ _))
        (snd (Mb^ n b) _ _))
        _ _)
         (x _ _ (invEq (Mb^-≡-hlp≃ {n = n} {b} _ _) (fromPathP p))))


mb^ext : ∀ {ℓ'} {B : Type ℓ'} (e : Maybe (Maybe (Maybe B))
                                → Maybe (Maybe (Maybe B))) →
                              (f : B → A)
                              (p : ∀ x → e (just (just (just  x))) ≡ just (just (just  x))) 
          (a a' a'' : A) →
            Path ( Maybe (Maybe (Maybe B)) → A )
              (Mb.rec a (Mb.rec a' (Mb.rec a'' f)) ∘ e)
              ((Mb.rec (Mb.rec a (Mb.rec a' (Mb.rec a'' f)) (e nothing))
                (Mb.rec
                  ((Mb.rec a (Mb.rec a' (Mb.rec a'' f)) (e (just nothing))))
                 (Mb.rec ((Mb.rec a (Mb.rec a' (Mb.rec a'' f)) (e (just (just (nothing)))))) f))))
mb^ext e f _ a a' a'' i nothing = Mb.rec a (Mb.rec a' (Mb.rec a'' f)) (e nothing)
mb^ext e f _ a a' a'' i (just nothing) = Mb.rec a (Mb.rec a' (Mb.rec a'' f)) (e (just nothing))
mb^ext e f _ a a' a'' i (just (just nothing)) = Mb.rec a (Mb.rec a' (Mb.rec a'' f))
         (e (just (just nothing)))
mb^ext e f p a a' a'' i (just (just (just x))) =
  cong (Mb.rec a (Mb.rec a' (Mb.rec a'' f))) (p x) i

swap0and1Mf : (b : hSet ℓ-zero) → fst (Mb^ 2 b) → fst (Mb^ 2 b)  
swap0and1Mf b nothing = just nothing
swap0and1Mf b (just nothing) = nothing
swap0and1Mf b (just (just x)) = (just (just x))

involSwap0and1Mf : ∀ b → isInvolution (swap0and1Mf b)
involSwap0and1Mf b nothing = refl
involSwap0and1Mf b (just nothing) = refl
involSwap0and1Mf b (just (just x)) = refl

sym-app : (f : A → A) → (isInvolF : isInvolution f) →
            Path (f ∘ f ≡ f ∘ f) (λ i a → isInvolF (isInvolF a (~ i)) i) refl
sym-app f isInvolF j i a =
  hcomp
   (λ z → λ {
     (j = i0) → isInvolF (isInvolF a (~ i ∨ ~ z)) (i ∨ ~ z) 
    ;(j = i1) → isInvolF a (~ z)
    ;(i = i0) → isInvolF a (~ z)
    ;(i = i1) → isInvolF a (~ z)
    })
    a


involSwap0and1Mf-coh : ∀ b x →
    (λ i → involSwap0and1Mf b (involSwap0and1Mf b x (~ i)) i) ≡
    refl
involSwap0and1Mf-coh b nothing = refl
involSwap0and1Mf-coh b (just nothing) = refl
involSwap0and1Mf-coh b (just (just x)) = refl


swap0and1M : (b : hSet ℓ-zero) → fst (Mb^ 2 b) ≃ fst (Mb^ 2 b)  
swap0and1M b = involEquiv {f = swap0and1Mf b} (involSwap0and1Mf b)

MbRecβ₂ : ∀ {ℓ} (A : Type ℓ) → (b : hSet ℓ-zero) →
           (f : (fst (Mb^ 2 b) → A))
            → Mb.rec (f nothing) (Mb.rec (f (just nothing))
             (f ∘ just ∘ just)) ≡ f 
MbRecβ₂ A b f = funExt (Mb.elim _ refl (Mb.elim _ refl λ x → refl))

gluePathExtSwap0and1 : (b : hSet ℓ-zero) →
      PathP (λ i → fst (Mb^ 2 b) → ua (swap0and1M b) i)
         (fst (swap0and1M b)) (idfun (fst (Mb^ 2 b)))
  
gluePathExtSwap0and1 b i x =
 glue (λ { (i = i0) → swap0and1Mf b x
         ; (i = i1) → x })
         (involSwap0and1Mf b x i)

elimUaSwapPath→ : ∀ {ℓ} (b : hSet ℓ-zero) →
     (B : ∀ j → ua (swap0and1M b) j → Type ℓ)
     (b₀ : (x' : Maybe (Maybe (fst b))) → B i0 x')
     (b₁ : (x' : Maybe (Maybe (fst b))) → B i1 x')
    → PathP (λ j → B j (ua-gluePath (swap0and1M b) {x = nothing}
                   refl j))
        (b₀ nothing) (b₁ (just nothing))
   → PathP (λ j → B j (ua-gluePath (swap0and1M b) {x = just nothing}
                   refl j))
        (b₀ (just  nothing)) (b₁ (nothing))
    → PathP (λ j → ∀ x' → B j (ua-gluePath (swap0and1M b) {x = just (just x')}
                   refl j))
        (b₀ ∘ just ∘ just) (b₁ ∘ just ∘ just)
    → PathP (λ j → (x' : ua (swap0and1M b) j) → B j x')
      b₀
      b₁
elimUaSwapPath→ b B b₀ b₁ p-n p-jn p-jj = funExtDep w
 where

   wCo' : (x₀ x₁ : Maybe (Maybe (fst b))) → hProp ℓ-zero
   wCo' nothing nothing = Lo.⊥
   wCo' nothing (just nothing) = Lo.⊤
   wCo' nothing (just (just x)) = Lo.⊥
   wCo' (just nothing) nothing = Lo.⊤
   wCo' (just (just x)) nothing = Lo.⊥
   wCo' (just nothing) (just x₁) = Lo.⊥
   wCo' (just (just x)) (just nothing) = Lo.⊥
   wCo' (just (just x)) (just (just x₁)) = (x ≡ x₁) ,  snd b _ _

   wCo : (x₀ x₁ : Maybe (Maybe (fst b))) → Type 
   wCo x₀ x₁ = fst (wCo' x₀ x₁) 
   

   wCo→Pa : (x₀ x₁ : Maybe (Maybe (fst b))) →
      wCo x₀ x₁ → PathP (λ z → ua (swap0and1M b) z) x₀ x₁
   wCo→Pa nothing (just nothing) x =
     ua-gluePath (swap0and1M b) refl
   wCo→Pa (just nothing) nothing x =
     ua-gluePath (swap0and1M b) refl
   wCo→Pa (just (just x₁)) (just (just x₂)) x =
     ua-gluePath (swap0and1M b) (cong (just ∘ just) x)

   PaHlp : ∀ x₀ → wCo x₀ (transport (λ z → ua (swap0and1M b) z) x₀)
   PaHlp nothing = _
   PaHlp (just nothing) = _
   PaHlp (just (just x)) = sym (transportRefl _)

   Pa→wCo : (x₀ x₁ : Maybe (Maybe (fst b))) →
      PathP (λ z → ua (swap0and1M b) z) x₀ x₁ → wCo x₀ x₁
   Pa→wCo x₀ x₁ x = subst (wCo x₀) (fromPathP x)
     (PaHlp x₀)

   Pa≡wCo : (x₀ x₁ : Maybe (Maybe (fst b))) →
      PathP (λ z → ua (swap0and1M b) z) x₀ x₁ ≃ wCo x₀ x₁
   Pa≡wCo x₀ x₁ = propBiimpl→Equiv
     (isOfHLevelRespectEquiv 1 (invEquiv (PathP≃Path _ _ _))
        (isOfHLevelMaybe 0 (isOfHLevelMaybe 0 (snd b)) _ _ ))
        (snd (wCo' x₀ x₁))
     (Pa→wCo x₀ x₁) (wCo→Pa x₀ x₁)
   
   w' : (x₀ x₁ : Maybe (Maybe (fst b))) → (p : wCo x₀ x₁)
      → PathP (λ i → B i (wCo→Pa x₀ x₁ p i)) (b₀ x₀) (b₁ x₁)
   w' nothing (just nothing) p = p-n
   w' (just nothing) nothing p = p-jn
   w' (just (just x)) (just (just x₁)) p j = p-jj j (p j)

   w : {x₀ x₁ : Maybe (Maybe (fst b))} → 
      (p : PathP (λ z → ua (swap0and1M b) z) x₀ x₁) →
      PathP (λ i → B i (p i)) (b₀ x₀) (b₁ x₁)
   w {x₀} {x₁} p =
     (subst {A = PathP (λ z → ua (swap0and1M b) z) x₀ x₁}
       {y = p} (λ p → PathP (λ i → B i (p i)) (b₀ x₀) (b₁ x₁))
       
       ((isOfHLevelRespectEquiv 1 (invEquiv (PathP≃Path _ _ _))
        (isOfHLevelMaybe 0 (isOfHLevelMaybe 0 (snd b)) _ _ ))
        _ _) ∘ w' x₀ x₁ ∘ Pa→wCo x₀ x₁) p

≡ᵍ : ∀ {A B C : Type ℓ} → A ≃ B → C ≃ B → A ≡ C
≡ᵍ {A = A} {B = B} {C = C} e f i =
         Glue B (λ { (i = i0) → (A , e)
                   ; (i = i1) → (C , f) })

ungluePathᵍ : ∀ {A B C : Type ℓ} → (e : A ≃ B) → (f : C ≃ B) →
            ∀ {a b}
             → PathP (λ i → ≡ᵍ e f i) a b
             → fst e a ≡ fst f b
ungluePathᵍ e f x i = unglue (i ∨ ~ i) (x i)


gluePathᵍ : ∀ {A B C : Type ℓ} → (e : A ≃ B) → (f : C ≃ B) →
           ∀ {a c} → fst e a ≡ fst f c
               → PathP (λ i → ≡ᵍ e f i)
               a c
gluePathᵍ e f x i =
  glue (λ { (i = i0) → _
          ; (i = i1) → _
          }) (x i)

gluePathᵍ' : ∀ {A B C : Type ℓ} → (e : A ≃ B) → (f : C ≃ B) →
           (f' : B → C) →
           (f= : section (fst f) f')
           →  ∀ a →
              PathP (λ i → ≡ᵍ e f i)
               a (f' (fst e a))
gluePathᵍ' e f f' f= a i =
  glue (λ { (i = i0) → a
          ; (i = i1) → f' (fst e a)
          }) (f= (fst e a) (~ i))


-- elimGlueMbPath→ : ∀ {ℓ} (b : hSet ℓ-zero) →
--         (e₀ e₁ : fst (Mb^ 3 b) ≃ fst (Mb^ 3 b))
--         (e₁' : fst (Mb^ 3 b) → fst (Mb^ 3 b))
--         (e₁'= : section (fst e₁) e₁')
--         (B : ∀ j → (x' : ≡ᵍ e₀ e₁ j) → Type ℓ)
--      → ∀ b₀ b₁
--      → (∀ x → PathP
--          (λ j → B j (gluePathᵍ' e₀ e₁ e₁' e₁'= x  j))
--         (b₀ x) (b₁ (e₁' (fst e₀ x))))
--      → PathP (λ j → (x' : ≡ᵍ e₀ e₁ j) → B j x')
--       b₀
--       b₁
-- elimGlueMbPath→ b e₀ e₁ e₁' e₁'= B b₀ b₁ x =
--    funExtDep {!!}


swap0and1MfunSq' : ∀ {ℓ} (A : Type ℓ) → (b : hSet ℓ-zero) →
    PathP (λ j → (x' : ua (swap0and1M b) j) →
             (f : (ua (swap0and1M b) j) → A) → Path A
                (let f' = f ∘ ua-gluePathExt (swap0and1M b) j 
                   in Mb.rec (f' (just nothing))
                     (Mb.rec (f' nothing) (f' ∘ just ∘ just))
                     (ua-unglue (swap0and1M b) j x')) (f x'))
        (Mb.elim _ (λ _ → refl) (Mb.elim _ (λ _ → refl) λ x → λ _ → refl))
        (Mb.elim _ (λ _ → refl) (Mb.elim _ (λ _ → refl) λ x → λ _ → refl))
swap0and1MfunSq' A b =
  elimUaSwapPath→ b
    (λ j x' → (f : (ua (swap0and1M b) j) → A) → Path A
                (let f' = f ∘ ua-gluePathExt (swap0and1M b) j 
                   in Mb.rec (f' (just nothing))
                     (Mb.rec (f' nothing) (f' ∘ just ∘ just))
                     (ua-unglue (swap0and1M b) j x')) (f x'))
    _ _
      (funExtDep λ pf → flipSquareP λ _ i → pf i
           (ua-gluePathExt (swap0and1M b) i nothing))
      ((funExtDep λ pf → flipSquareP λ _ i → pf i
           (ua-gluePathExt (swap0and1M b) i (just nothing))))
      (funExtDep λ p → funExtDep λ pf →
         flipSquareP λ _ i → pf i (ua-gluePathExt (swap0and1M b) i
           (just (just (p i)))))
    
swap0and1MfunSq : ∀ {ℓ} (A : Type ℓ) → (b : hSet ℓ-zero) →
        SquareP (λ _ j → ((ua (swap0and1M b) j) → A) →
          (ua (swap0and1M b) j) → A)
          (λ j f x →
            let f' = f ∘ ua-gluePathExt (swap0and1M b) j 
            in Mb.rec (f' (just nothing))
              (Mb.rec (f' nothing) (f' ∘ just ∘ just))
              (ua-unglue (swap0and1M b) j x))
          (λ j f x → f x)
          (funExt₂ λ f → Mb.elim _ refl (Mb.elim _ refl λ x → refl))
          (funExt₂ λ f → Mb.elim _ refl (Mb.elim _ refl λ x → refl))
swap0and1MfunSq A b =
  flipSquareP (w' ◁ (λ j i f x' →
       swap0and1MfunSq' A b j x' f i) ▷ w)

  where
   w : _ ≡ _
   w i i₁ x nothing = x nothing
   w i i₁ x (just nothing) = x (just nothing)
   w i i₁ x (just (just x₁)) = x (just (just x₁))

   w' : _ ≡ _
   w' i i₁ x nothing = x nothing
   w' i i₁ x (just nothing) = x (just nothing)
   w' i i₁ x (just (just x₁)) = x (just (just x₁))


rot201M≡ : (b : hSet ℓ-zero) →
                  fst (Mb^ 3 b) ≡ fst (Mb^ 3 b)
rot201M≡ b i = 
  Glue (Maybe ((ua (swap0and1M b)) i))
    λ { (i = i0) → _ , swap0and1M (Mb^ 1 b)
      ; (i = i1) → _ , idEquiv _ }


swap-braidF : (b : hSet ℓ-zero) → ∀ x → 
        fst (swap0and1M (Mb^ 1 b) ∙ₑ congMaybeEquiv (swap0and1M b)
          ∙ₑ swap0and1M (Mb^ 1 b)) x ≡
        fst (congMaybeEquiv (swap0and1M b) ∙ₑ swap0and1M (Mb^ 1 b)
         ∙ₑ congMaybeEquiv (swap0and1M b)) x
swap-braidF b nothing = refl
swap-braidF b (just nothing) = refl
swap-braidF b (just (just nothing)) = refl
swap-braidF b (just (just (just x))) = refl

swap-braid : (b : hSet ℓ-zero) →
        swap0and1M (Mb^ 1 b) ∙ₑ congMaybeEquiv (swap0and1M b)
          ∙ₑ swap0and1M (Mb^ 1 b) ≡
        congMaybeEquiv (swap0and1M b) ∙ₑ swap0and1M (Mb^ 1 b)
         ∙ₑ congMaybeEquiv (swap0and1M b) 
swap-braid b = equivEq (funExt (swap-braidF b))

invol-invol-suc : (b : hSet ℓ-zero) → ∀ w → 
        (swap0and1Mf (Mb^ 1 b) ((swap0and1Mf (Mb^ 1 b)) w)) ≡
        (map-Maybe (equivFun (swap0and1M b))
          (map-Maybe (swap0and1Mf b) w))
invol-invol-suc b nothing = refl
invol-invol-suc b (just nothing) = refl
invol-invol-suc b (just (just nothing)) = refl
invol-invol-suc b (just (just (just x))) = refl

-- hexCong : ∀ (b : hSet ℓ-zero) →
--      map-Maybe (swap0and1Mf b) ∘ swap0and1Mf (Mb^ 1 b) ∘ map-Maybe (swap0and1Mf b)
--        ≡
--       swap0and1Mf (Mb^ 1 b) ∘ map-Maybe (swap0and1Mf b) ∘ swap0and1Mf (Mb^ 1 b)
-- hexCong b i nothing = just (just nothing)
-- hexCong b i (just nothing) = just nothing
-- hexCong b i (just (just nothing)) = nothing
-- hexCong b i (just (just (just x))) = just (just (just x))


-- Square-b : (b : hSet ℓ-zero) → Square
--               (ua (swap0and1M (Mb^ 1 b)))
--               (sym (ua (swap0and1M (Mb^ 1 b))))
--               (ua (swap0and1M (Mb^ 1 b)
--                  ∙ₑ congMaybeEquiv  (swap0and1M b)
--                  ∙ₑ swap0and1M (Mb^ 1 b)))
--               (ua (congMaybeEquiv  (swap0and1M b)))
-- Square-b b i j =
--   Glue (fst (Mb^ 3 b))
--       λ {  (i = i0) → ua (swap0and1M (Mb^ 1 b)) j , swap0and1Mf (Mb^ 1 b) ∘
--                fst (congMaybeEquiv (swap0and1M b))
--               ∘ ua-ungluePathExt (swap0and1M (Mb^ 1 b)) j , {!!}
--          ; (i = i1) (j = i0) → _ , idEquiv _
--          ; (j = i1) → ua (congMaybeEquiv (swap0and1M b)) i ,
--               swap0and1Mf (Mb^ 1 b) ∘
--                 ua-ungluePathExt (congMaybeEquiv (swap0and1M b)) i
--                 , {!!}
--          }


-- Square-b : (b : hSet ℓ-zero) → Square
--               (ua (swap0and1M (Mb^ 1 b)))
--               (sym (ua (swap0and1M (Mb^ 1 b))))
--               (ua (swap0and1M (Mb^ 1 b)
--                  ∙ₑ congMaybeEquiv  (swap0and1M b)
--                  ∙ₑ swap0and1M (Mb^ 1 b)))
--               (cong Maybe (ua (swap0and1M b)))
-- Square-b b = λ i j → 
--   Glue (fst (Mb^ 3 b))
--       λ {  (i = i0) → ua (swap0and1M (Mb^ 1 b)) j ,
--               ei0 j
--               ,
--               {!!}
--          ; (i = i1) (j = i0) → _ , idEquiv _
--          ; (j = i1) → Maybe (ua (swap0and1M b) i) ,
--                ej1 i
--               , {!!}
--          }
--  where
--   ej1 : PathP (λ i → Maybe (ua (swap0and1M b) i) → fst (Mb^ 3 b))
--              (fst (swap0and1M (Mb^ 1 b)) ∘ map-Maybe (swap0and1Mf b))
--              (fst (swap0and1M (Mb^ 1 b)))
--   ej1 i nothing = just nothing
--   ej1 i (just x) = fst
--          (swap0and1M (Maybe (fst b) , isOfHLevelMaybe zero (snd b)))
--          (just (unglue (i ∨ ~ i) x))

--   ei0 : PathP (λ j → ua (swap0and1M (Mb^ 1 b)) j → fst (Mb^ 3 b))
--              ((fst (swap0and1M (Mb^ 1 b)) ∘ map-Maybe (swap0and1Mf b))
--                  ∘ fst (swap0and1M (Mb^ 1 b)))
--              (fst (swap0and1M (Mb^ 1 b)) ∘ map-Maybe (swap0and1Mf b))             
--   ei0 j = (fst (swap0and1M (Mb^ 1 b)) ∘ map-Maybe (swap0and1Mf b))
--             ∘ ua-ungluePathExt (swap0and1M (Mb^ 1 b)) j

-- Square-bb : (b : hSet ℓ-zero) → Square
--               {!!}
--               {!!}
--               {!!}
--               {!!}
-- Square-bb b i j =
--    Glue (fst (Mb^ 3 b))
--       λ { (i = i0) → {!!}
--         ; (i = i1) → {!!}
--          } 

-- -- swap0and1Mf (Mb^ 1 b)
-- --               ∘ ua-ungluePathExt (congMaybeEquiv (swap0and1M b)) i
-- -- Square-cc : (b : hSet ℓ-zero) →
-- --               SquareP (λ i j → {!!} → {!!})
-- --                 {!!}
-- --                 {!!}
-- --                 (λ j x → {!!} )
-- --                 {!!}
-- -- Square-cc b i j =
-- --       map-Maybe (ua-gluePathExt (swap0and1M b) (i ∨ ~ j))
-- --      ∘ {!swap-braidF!}
-- --      ∘ ua-ungluePathExt (swap0and1M (Mb^ 1 b)) (i ∧ j)
    

-- -- swap-commm : (b : hSet ℓ-zero) →
-- --             Square              
-- --               (rot201M≡ b)
-- --               refl
-- --               (ua (swap0and1M (Mb^ 1 b)))
-- --               (sym (cong Maybe (ua ((swap0and1M b)))))
              
-- -- swap-commm b i j = 
-- --   Glue (Maybe ((ua (swap0and1M b)) (j ∧ ~ i)))
-- --      λ { (i = i0)(j = i0) → _ , swap0and1M (Mb^ 1 b)
-- --         ; (j = i1) → _ , idEquiv _
-- --         ; (i = i1) → _ , idEquiv _ }
     

-- -- swap-commm : (b : hSet ℓ-zero) →
-- --             Square              
-- --               (rot201M≡ b)
-- --               (cong Maybe (ua ((swap0and1M b))))
-- --               (ua (swap0and1M (Mb^ 1 b)))
-- --               refl
              
-- -- swap-commm b i j =
-- --   Glue (Maybe ((ua (swap0and1M b)) j))
-- --      λ { (i = i0)(j = i0) → _ , swap0and1M (Mb^ 1 b)
-- --         ; (j = i1) → _ , idEquiv _
-- --         ; (i = i1) → _ , idEquiv _ }
     

-- swap0and2M≡ : (b : hSet ℓ-zero) →
--                   fst (Mb^ 3 b) ≡ fst (Mb^ 3 b)
-- swap0and2M≡ b i = 
--   Glue (Maybe ((ua (swap0and1M b)) i))
--     λ { (i = i0) → _ , swap0and1M (Mb^ 1 b)
--       ; (i = i1) → _ , swap0and1M (Mb^ 1 b)
--        }

-- hexUswap : (b : hSet ℓ-zero) →
--             Square
--               (swap0and2M≡ b)
--               (cong Maybe (ua ((swap0and1M b))))
--               (ua (swap0and1M (Mb^ 1 b)))
--               (ua (swap0and1M (Mb^ 1 b)))
-- hexUswap b i j = Glue
--      (Maybe ((ua (swap0and1M b)) j))
--      λ { (i = i1) → (Maybe ((ua (swap0and1M b)) j)) , idEquiv _
--         ; (j = i0) (i = i0) → _ , swap0and1M (Mb^ 1 b)
--         ; (j = i1) (i = i0) → _ , swap0and1M (Mb^ 1 b)
--         }


-- -- hexLswap : (b : hSet ℓ-zero) →
-- --             Square
-- --               (swap0and2M≡ b)
-- --               (cong Maybe (ua ((swap0and1M b))))
-- --               (ua (swap0and1M (Mb^ 1 b)))
-- --               (ua (swap0and1M (Mb^ 1 b)))
-- -- hexLswap b i j = Glue
-- --      (Maybe ((ua (swap0and1M b)) j))
-- --      λ { (i = i1) → (Maybe ((ua (swap0and1M b)) j)) , idEquiv _
-- --         ; (j = i0) (i = i0) → _ , swap0and1M (Mb^ 1 b)
-- --         ; (j = i1) (i = i0) → _ , swap0and1M (Mb^ 1 b)
-- --         }


-- -- ua-unglueSwap0and1M : (b : hSet ℓ-zero) → ∀ x y → 
-- --      PathP (λ i → ua (swap0and1M b) i) x y → x ≡ swap0and1Mf b y
-- -- ua-unglueSwap0and1M b x y p with MaybePath.encode _ _ (ua-ungluePath (swap0and1M b) p)  
-- -- ua-unglueSwap0and1M b nothing (just nothing) p | w = refl
-- -- ua-unglueSwap0and1M b nothing (just (just x)) p | w = ⊥.rec (¬nothing≡just w)
-- -- ua-unglueSwap0and1M b (just nothing) nothing p | w = refl
-- -- ua-unglueSwap0and1M b (just (just x)) (just nothing) p | w = ⊥.rec (¬just≡nothing w)
-- -- ua-unglueSwap0and1M b (just (just x)) (just (just x₁)) p | w = cong just w


-- -- -- glue-unglue-ExtSwap0and1M : (b : hSet ℓ-zero) →
-- -- --         PathP (λ i → fst (Mb^ 2 b) → ua (swap0and1M b) i)
-- -- --            (idfun _)
-- -- --            (swap0and1Mf b)
-- -- -- glue-unglue-ExtSwap0and1M b = ua-gluePathExt (swap0and1M b)

-- -- -- ua-unglueExtSwap0and1M : (b : hSet ℓ-zero) →
-- -- --         PathP (λ i → ua (swap0and1M b) i → fst (Mb^ 2 b))
-- -- --            (idfun _)
-- -- --            (swap0and1Mf b)
-- -- -- ua-unglueExtSwap0and1M b i x = {!!}

swap0and2Mf : (b : hSet ℓ-zero) → fst (Mb^ 3 b) → fst (Mb^ 3 b)  
swap0and2Mf b nothing = (just (just nothing))
swap0and2Mf b (just nothing) = just nothing
swap0and2Mf b (just (just nothing)) = nothing
swap0and2Mf b (just (just (just x))) = (just (just (just x)))

-- -- involSwap0and2Mf : ∀ b → isInvolution (swap0and2Mf b)
-- -- involSwap0and2Mf b nothing = refl
-- -- involSwap0and2Mf b (just nothing) = refl
-- -- involSwap0and2Mf b (just (just nothing)) = refl
-- -- involSwap0and2Mf b (just (just (just x))) = refl

-- -- swap0and2M : (b : hSet ℓ-zero) → fst (Mb^ 3 b) ≃ fst (Mb^ 3 b)  
-- -- swap0and2M b = involEquiv {f = swap0and2Mf b} (involSwap0and2Mf b)


ei0= : (b : hSet ℓ-zero) → PathP
    (λ z → Maybe (ua (swap0and1M b) z) → Maybe (Maybe (Maybe (fst b))))
    (fst
     (congMaybeEquiv (swap0and1M b) ∙ₑ
      swap0and1M (Mb^ 1 b) ∙ₑ
      congMaybeEquiv (swap0and1M b)))
    (fst
     (swap0and1M (Mb^ 1 b) ∙ₑ
      congMaybeEquiv (swap0and1M b)))
ei0= b z nothing = just (just nothing)
ei0= b z (just x) = fst
       (swap0and1M (Mb^ 1 b) ∙ₑ
        congMaybeEquiv (swap0and1M b))
       (just (unglue (z ∨ ~ z) x))

ei1= : (b : hSet ℓ-zero) → PathP
    (λ z →
       ua (swap0and1M (Mb^ 1 b)) z →
       Maybe (Maybe (Maybe (fst b))))
     (fst
     (swap0and1M (Mb^ 1 b) ∙ₑ congMaybeEquiv (swap0and1M b) ∙ₑ
      swap0and1M (Mb^ 1 b)))
    (fst
     (congMaybeEquiv (swap0and1M b) ∙ₑ
      swap0and1M (Mb^ 1 b)))
ei1= b z x = 
 swap0and1Mf (Mb^ 1 b)
   (fst (congMaybeEquiv (swap0and1M b)) ((unglue (z ∨ ~ z) x)))

swapMlsq-R-ei0 : (b : hSet ℓ-zero)  → PathP (λ j  → Maybe (ua (swap0and1M b) j) ≃ Maybe (Maybe (Maybe (fst b))))
         ((ua-unglueEquiv (swap0and1M (Mb^ 1 b)) i1 ∙ₑ
            congMaybeEquiv (swap0and1M b)))
         (idEquiv _)
swapMlsq-R-ei0 b = ΣPathPProp isPropIsEquiv ei0='
  -- {!!}
  -- -- (congP (λ _ → map-Maybe) (ua-ungluePathExt (swap0and1M b))
  -- --   ▷ funExt map-Maybe-id )
    
   -- ((λ i → map-Maybe
   --          (ua-ungluePathExt (swap0and1M b) i)) ▷ {!!})
  -- λ i → mb3≡ (λ _ → nothing)
  --        (λ _ → just nothing) (λ _ → just (just nothing))
  --         (λ _ → just ∘' just ∘' just) i ∘' map-Maybe (unglue (i ∨ ~ i))
  -- (congP₂ (λ _ → _∘_) (λ i → mb3≡ (λ _ → nothing)
  --        (λ _ → just nothing) (λ _ → just (just nothing))
  --         (λ _ → just ∘' just ∘' just) i) λ i → map-Maybe (unglue (i ∨ ~ i)))
  -- λ i → mb3≡ {!!} {!!} {!!} {!!} i ∘' map-Maybe (unglue (i ∨ ~ i))
  where

    ei0=' : PathP (λ j  → Maybe (ua (swap0and1M b) j) → Maybe (Maybe (Maybe (fst b))))
             (fst (ua-unglueEquiv (swap0and1M (Mb^ 1 b)) i1 ∙ₑ
                congMaybeEquiv (swap0and1M b)))
             (idfun _)

    ei0=' j nothing = nothing
    ei0=' j (just x) = just (unglue (j ∨ ~ j) x)


swapMlsq-L-sides : (b : hSet ℓ-zero) → ∀ i j →
        Partial (i ∨ ~ i ∨ ~ j) (Σ Type (λ T → T ≃ Maybe (Maybe (Maybe (fst b)))))
swapMlsq-L-sides b i j =
       λ { (i = i0) → (Maybe (ua (swap0and1M b) j )) , ei0 j
         ; (i = i1) → (ua (swap0and1M (Mb^ 1 b)) j) ,
                ei1 j
         ; (j = i0) → fst (Mb^ 3 b) , (swap-braid b (~ i))
        --     equivEq {e = congMaybeEquiv (ua-unglueEquiv (swap0and1M b) j)
        --         ∙ₑ swap0and1M (Mb^ 1 b) ∙ₑ
        --             congMaybeEquiv (swap0and1M b)}
        --             {f = (swap0and1M (Mb^ 1 b) ∙ₑ congMaybeEquiv (swap0and1M b) ∙ₑ
        -- swap0and1M (Mb^ 1 b))}
        --       {!cong fst (sym (swap-braid b)!} i
         }
 where


  ei0 : PathP (λ j → Maybe (ua (swap0and1M b) j) ≃ Maybe (Maybe (Maybe (fst b))))
           (congMaybeEquiv (ua-unglueEquiv (swap0and1M b) i0)
                ∙ₑ swap0and1M (Mb^ 1 b) ∙ₑ
                    congMaybeEquiv (swap0and1M b))
           ((ua-unglueEquiv (swap0and1M (Mb^ 1 b)) i0 ∙ₑ
                congMaybeEquiv (swap0and1M b)))
  ei0 = ΣPathPProp isPropIsEquiv (ei0= b)



  ei1 : PathP (λ j → ua (swap0and1M (Mb^ 1 b)) j ≃ Maybe (Maybe (Maybe (fst b))))
            ((swap0and1M (Mb^ 1 b) ∙ₑ congMaybeEquiv (swap0and1M b) ∙ₑ
        swap0and1M (Mb^ 1 b)))

           (congMaybeEquiv (ua-unglueEquiv (swap0and1M b) i0)
                ∙ₑ swap0and1M (Mb^ 1 b))
  ei1 = ΣPathPProp isPropIsEquiv (ei1= b)



swapMlsq-L swapMlsq-R swapMlsq-H :
    (b : hSet ℓ-zero) → I → I → Type ℓ-zero

swapMlsq-L b i j =
  Glue (fst (Mb^ 3 b))
       (swapMlsq-L-sides b i j)


swapMlsq-R-sides : (b : hSet ℓ-zero) → ∀ i j →
        Partial (i ∨ ~ i ∨  j) (Σ Type (λ T → T ≃ Maybe (Maybe (Maybe (fst b)))))
swapMlsq-R-sides b i j =
   λ { (i = i0) → (Maybe (ua (swap0and1M b) j )) ,
                 swapMlsq-R-ei0 b j
         ; (i = i1) → (ua (swap0and1M (Mb^ 1 b)) j) ,
              ua-unglueEquiv (swap0and1M (Mb^ 1 b)) j 
         ; (j = i1) → fst (Mb^ 3 b) , idEquiv _ --idEquiv _          
         }

swapMlsq-R b i j =
     Glue (fst (Mb^ 3 b))
       (swapMlsq-R-sides b i j)


swapMlsq-H-sides : (b : hSet ℓ-zero) → ∀ i j →
   Partial (i ∨ ~ i) (Σ-syntax Type (λ T → T ≃ fst (Mb^ 3 b)))
 
swapMlsq-H-sides b i j  =  
       λ { (i = i0) → (ua (swap0and1M (Mb^ 1 b)) j) ,
                (ua-unglueEquiv (swap0and1M (Mb^ 1 b)) j ∙ₑ
                congMaybeEquiv (swap0and1M b)) 
          ;(i = i1) → (Maybe (ua (swap0and1M b) j )) , ei1 j }
  where
   ei1=' : PathP
            (λ z → Maybe (ua (swap0and1M b) z) → Maybe (Maybe (Maybe (fst b))))
            (fst
             (congMaybeEquiv (ua-unglueEquiv (swap0and1M b) i0) ∙ₑ
              swap0and1M (Mb^ 1 b)))
            (fst (swap0and1M (Mb^ 1 b)))
   ei1=' z nothing = just nothing
   ei1=' z (just x) = swap0and1Mf (Mb^ 1 b) (just (unglue (z ∨ ~ z) x))

   ei1 : PathP (λ j → Maybe (ua (swap0and1M b) j) ≃ Maybe (Maybe (Maybe (fst b))))
         (congMaybeEquiv (ua-unglueEquiv (swap0and1M b) i0)
           ∙ₑ swap0and1M (Mb^ 1 b)) (swap0and1M (Mb^ 1 b))
   ei1 = ΣPathPProp isPropIsEquiv ei1='


swapMlsq-H b i j =
    Glue (fst (Mb^ 3 b)) {i ∨ ~ i} (swapMlsq-H-sides b i j)

swapM-cL swapM-cR : (b : hSet ℓ-zero) → fst (Mb^ 3 b) ≡ fst (Mb^ 3 b)
swapM-cL b i = swapMlsq-H b i i0
swapM-cR b i = swapMlsq-H b i i1


Rh𝔽in : RRec {A = A} (isGroupoidHSet {ℓ = ℓ-zero})
RRec.[]* Rh𝔽in = ⊥.⊥ , isProp→isSet isProp⊥
(Rh𝔽in RRec.∷* _) =  Mb^ 1 
RRec.comm* Rh𝔽in _ _ b = TypeOfHLevel≡ 2 (ua (swap0and1M b))
RRec.comm-inv* Rh𝔽in _ _ b =
  ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
   (involPathSym _)
RRec.commmL* Rh𝔽in x y z b = TypeOfHLevel≡ 2 (swapM-cL b)
RRec.commmR* Rh𝔽in x y z b = TypeOfHLevel≡ 2 (swapM-cR b)
RRec.commpL* Rh𝔽in x y z b =   
  ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
    (λ i j → swapMlsq-L b i j)
RRec.commpR* Rh𝔽in x y z b =
  ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
    (λ i j → swapMlsq-R b i j)
RRec.hex* Rh𝔽in x y z b = 
     ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
      (λ i j → swapMlsq-H b i j)


rep : A → ℕ → FMSet2 A
rep a zero = []
rep a (suc n) = a ∷2 rep a n

h𝔽in : FMSet2 A → hSet ℓ-zero
h𝔽in = RRec.f Rh𝔽in

𝔽in : FMSet2 A → Type
𝔽in = fst ∘ h𝔽in

𝔽in∘rep→Fin : ∀ n (a : A) → 𝔽in (rep a n) → Fin n
𝔽in∘rep→Fin (suc n) a nothing = zero , _
𝔽in∘rep→Fin (suc n) a (just x) = sucF (𝔽in∘rep→Fin n a x)

Fin→𝔽in∘rep : ∀ n (a : A) → Fin n → 𝔽in (rep a n)
Fin→𝔽in∘rep (suc n) a (zero , k<) = nothing
Fin→𝔽in∘rep (suc n) a (suc k , k<) = just (Fin→𝔽in∘rep n a (k , k<))

IsoFin𝔽in∘rep : ∀ n (a : A) → Iso (Fin n) (𝔽in (rep a n))
Iso.fun (IsoFin𝔽in∘rep n a) = Fin→𝔽in∘rep n a
Iso.inv (IsoFin𝔽in∘rep n a) = 𝔽in∘rep→Fin n a
Iso.rightInv (IsoFin𝔽in∘rep (suc n) a) nothing = refl
Iso.rightInv (IsoFin𝔽in∘rep (suc n) a) (just x) =
 cong just (Iso.rightInv (IsoFin𝔽in∘rep n a) x)
Iso.leftInv (IsoFin𝔽in∘rep (suc n) a) (zero , k<) = refl
Iso.leftInv (IsoFin𝔽in∘rep (suc n) a) (suc k , k<) =
  ≡Fin {n = suc n}
   (cong (suc ∘ fst) (Iso.leftInv (IsoFin𝔽in∘rep n a) (k , k<)))



𝔽→ : ∀ (A : Type ℓ) → ∀ p → Type ℓ
𝔽→ A p = 𝔽in {A = Unit} p → A

Σ𝔽→ : ∀ (A : Type ℓ) → Type ℓ
Σ𝔽→ A = Σ _ (𝔽→ A)

module _ {ℓ'} {B : Type ℓ'} {A : Type ℓ} (xs : FMSet2 B) where

 swap01coh : (y : Maybe (Maybe (fst (h𝔽in xs)))) →
      Square
      (λ j →
         swap0and1Mf (h𝔽in xs)
         (swap0and1Mf (h𝔽in xs) (swap0and1Mf (h𝔽in xs) y)))
      (λ j → swap0and1Mf (h𝔽in xs) y)
      (λ i →
         swap0and1Mf (h𝔽in xs)
         (involSwap0and1Mf (fst (RRec.f Rh𝔽in xs) , snd (RRec.f Rh𝔽in xs)) y
          i))
      (λ i →
         involSwap0and1Mf (fst (RRec.f Rh𝔽in xs) , snd (RRec.f Rh𝔽in xs))
         (swap0and1Mf (h𝔽in xs) y) i)
 swap01coh nothing = refl
 swap01coh (just nothing) = refl
 swap01coh (just (just x)) = refl

 module PCI = preCompInvol* {f = swap0and1Mf (h𝔽in xs)} A 
   (involSwap0and1Mf _) swap01coh

 -- swap02coh : (y : Maybe (Maybe (Maybe (fst (h𝔽in xs))))) →
 --      Square
 --      (λ j →
 --         swap0and2Mf (h𝔽in xs)
 --         (swap0and2Mf (h𝔽in xs) (swap0and2Mf (h𝔽in xs) y)))
 --      (λ j → swap0and2Mf (h𝔽in xs) y)
 --      (λ i →
 --         swap0and2Mf (h𝔽in xs)
 --         (involSwap0and2Mf (fst (RRec.f Rh𝔽in xs) , snd (RRec.f Rh𝔽in xs)) y
 --          i))
 --      (λ i →
 --         involSwap0and2Mf (fst (RRec.f Rh𝔽in xs) , snd (RRec.f Rh𝔽in xs))
 --         (swap0and2Mf (h𝔽in xs) y) i)
 -- swap02coh nothing = refl
 -- swap02coh (just nothing) = refl
 -- swap02coh (just (just nothing)) = refl
 -- swap02coh (just (just (just x))) = refl

 -- module PCI' = preCompInvol* {f = swap0and2Mf (h𝔽in xs)} A 
 --   (involSwap0and2Mf _) swap02coh


singlTy : (A : Type ℓ) → Type (ℓ-suc ℓ)
singlTy {ℓ} A = Σ (Σ (Type ℓ) λ T → A → T) (isEquiv ∘ snd)

isContr-singlTy : (A : Type ℓ) → isContr (singlTy A)
isContr-singlTy A = isOfHLevelRespectEquiv 0
  ((Σ-cong-equiv-snd λ _ → invEquivEquiv)  ∙ₑ invEquiv Σ-assoc-≃)
     (EquivContr A) 


-- -- hexUT : ∀ {ℓ'} {B : Type ℓ'} → (x y z : B) (xs : FMSet2 B) →  Square
-- --              (λ i → 𝔽in (y ∷2 comm x z xs i) → A)
-- --              (symP (PCI'.p' {B = B} {A = A} xs))
-- --              (symP (PCI.p' {B = B} {A = A} (z ∷2 xs)))
-- --              (symP (PCI.p' {B = B} {A = A} (x ∷2 xs)))
-- -- hexUT x y z xs i j  = {!!}

Glue≡ : ∀ {A₀ A₁ : Type ℓ} → (φ : I) →
           {f₀ : Partial φ (Σ[ T ∈ Type ℓ ] T ≃ A₀)}
           {f₁ : Partial φ (Σ[ T ∈ Type ℓ ] T ≃ A₁)}
           → (A : A₀ ≡ A₁)
           → (T : PartialP φ (λ o → fst (f₀ o) ≡ fst (f₁ o) ))
           → PartialP φ (λ o →
               PathP (λ i → T o i → A i)
                   (fst (snd (f₀ o)))
                   (fst (snd (f₁ o))) )
           → Glue A₀ f₀ ≡ Glue A₁ f₁
Glue≡ φ {f₀} {f₁} A T x i =
  Glue (A i) λ o → (T o i) ,
   ΣPathPProp {B = λ _ → isEquiv} {u =  snd (f₀ o)} {v = snd (f₁ o)}
      isPropIsEquiv (x o) i


involSymΣ01 : ∀ (A : Type ℓ) → (A' : Type ℓ) →
       ua (Σ-swap-01-≃ {A = A} {A} {A'}) ≡ sym (ua (Σ-swap-01-≃ {A = A} {A} {A'}))
involSymΣ01 A A' i j =
  Glue≡ (j ∨ ~ j)
     {f₀ = λ { (j = i0) → _ , Σ-swap-01-≃ ; (j = i1) → _ , idEquiv _}}
     {f₁ = λ { (j = i0) → _ , idEquiv _ ; (j = i1) → _ , Σ-swap-01-≃}} 
    (ua (Σ-swap-01-≃ {A = A} {A' = A} {A'' = A'}))
    (λ { (j = i0) → λ _ → A × A × A' ; (j = i1) → λ _ → A × A × A' })  
    (λ { (j = i0) → λ i x → ua-gluePath
               (Σ-swap-01-≃ {A = A} {A' = A} {A'' = A'})
                  (λ i₂ → (fst x) , (fst (snd x) , snd (snd x))) i
       ; (j = i1) → ua-gluePathExt Σ-swap-01-≃
       }) i



glue-commmL : {A : Type ℓ} → ∀ x y z xs → PathP (λ i →  Maybe (Maybe (Maybe (𝔽in {A = A} xs)))
                      → 𝔽in (commmL x y z xs i))
                       
                (map-Maybe (swap0and1Mf (h𝔽in xs)))
                (swap0and1Mf (Mb^ 1 (h𝔽in (xs))))       
glue-commmL x y z xs i w = glue
  (λ { (i = i0) → (map-Maybe (swap0and1Mf (h𝔽in xs))) w
     ; (i = i1) → swap0and1Mf (Mb^ 1 (h𝔽in (xs))) w
     })
  ((swap-braidF (h𝔽in (xs))) w (~ i))


glue-commmR : {A : Type ℓ} → ∀ x y z xs → PathP (λ i →  Maybe (Maybe (Maybe (𝔽in {A = A} xs)))
                      → 𝔽in (commmR x y z xs i))
                       
                (map-Maybe (swap0and1Mf (h𝔽in xs)))
                (swap0and1Mf (Mb^ 1 (h𝔽in (xs))))       
glue-commmR x y z xs i w = glue
  (λ { (i = i0) → (map-Maybe (swap0and1Mf (h𝔽in xs))) w
     ; (i = i1) → swap0and1Mf (Mb^ 1 (h𝔽in (xs))) w
     }) (invol-invol-suc (h𝔽in (xs)) w (~ i))





RFM2tab : ∀ {ℓ'} {B : Type ℓ'} →
   RElim {A = B} (λ xs → (𝔽in xs → A) → FMSet2 A)
RElim.[]* RFM2tab _ = []
(RFM2tab RElim.∷* _) b f = f nothing ∷2 b (f ∘ just)
RElim.comm* (RFM2tab {A = A} {B = B}) _ _ {xs} b i f = 
 let z = f ∘' ua-gluePathExt (PCI.e {B = B} {A = A} xs) i
 in comm (z nothing) (z (just nothing)) (b (z ∘ just ∘ just)) i
RElim.comm-inv* (RFM2tab {A = A}) _ _ {xs} b i j f =
 let z : Maybe (Maybe (𝔽in xs)) → A
     z = f ∘' λ x → glue
             (λ { (j = i0) → x
                ; (j = i1) → swap0and1Mf (h𝔽in xs) x })
                 (glue (λ { (i = i0) → swap0and1Mf (h𝔽in xs) x
                          ; (i = i1) → _ })
                 (involSwap0and1Mf (RRec.f Rh𝔽in xs) x (~ j ∧ i)))
 in comm-inv (z nothing) (z (just nothing)) (b (z ∘ just ∘ just)) i j
RElim.commmL* RFM2tab x y z {xs} b i f =
 let z = f ∘' glue-commmL x y z xs i
 in commmL (z nothing)
           (z (just (just nothing)))
           (z (just nothing))
           (b (z ∘ just ∘ just ∘ just)) i
RElim.commmR* RFM2tab x y z {xs} b i f =
 let z = f ∘' glue-commmR x y z xs i
 in commmR (z nothing)
           (z (just (just nothing)))
           (z (just nothing))
           (b (z ∘ just ∘ just ∘ just)) i
 
RElim.commpL* (RFM2tab {A = A} {B = B}) x y z {xs} b i j f =
  commpL
       (zH nothing)
       (zH (just nothing))
       (zH (just (just  nothing)))
       (b (zH ∘ just ∘ just ∘ just)) i j
 where

  zHH : (x : Maybe (Maybe (Maybe (𝔽in xs)))) →
       Square {A = Maybe (Maybe (Maybe (𝔽in xs)))}
         (λ j → ei0= (h𝔽in xs)
           j (map-Maybe (ua-gluePathExt (PCI.e {B = B} {A = A} (xs)) j) x) )
         ((λ j → ei1= (h𝔽in xs)
           j ((ua-gluePathExt (PCI.e {B = B} {A = A} (z ∷2 xs)) j) x)) )
         (λ i → (swap-braidF (h𝔽in xs) (map-Maybe-id x i)) (~ i))
         λ i → ((swap-braidF (h𝔽in (xs))) x (~ i))
  zHH nothing i j = just (just nothing)
  zHH (just nothing) i j = just nothing
  zHH (just (just nothing)) i j = nothing
  zHH (just (just (just x))) i j = just (just (just x))

  zH : Maybe (Maybe (Maybe (𝔽in xs))) → A
  zH = f ∘' λ x → glue
          (λ {(i = i0) →
                   map-Maybe (ua-gluePathExt (PCI.e {B = B} {A = A} (xs)) j) x
                  ;(i = i1) → ua-gluePathExt (PCI.e {B = B} {A = A} (z ∷2 xs)) j x 
                  ;(j = i0) → map-Maybe-id x i
                  }) (zHH x i j)


RElim.commpR* (RFM2tab {A = A} {B = B}) x y z {xs} b i j f = 
  commpR
       (zH nothing)
       (zH (just (just nothing)))
       (zH (just nothing))
       (b (zH ∘ just ∘ just ∘ just)) i j
  where

   zHj1 : Path (Maybe (Maybe (Maybe (𝔽in xs)))
         →  Maybe (Maybe (Maybe (𝔽in xs))))
          (map-Maybe (ua-gluePathExt (PCI.e {B = B} {A = A} (xs)) i1
                   ∘ swap0and1Mf (h𝔽in xs)))
          ((ua-gluePathExt (PCI.e {B = B} {A = A} (y ∷2  xs)) i1 ∘
            swap0and1Mf (Mb^ 1 (h𝔽in xs))))
   zHj1 i nothing = nothing
   zHj1 i (just nothing) = just nothing
   zHj1 i (just (just nothing)) = just (just nothing)
   zHj1 i (just (just (just x))) = just (just (just x))

   zHj0 : ∀ x → fst
      (idEquiv (Maybe (Maybe (Maybe (fst (h𝔽in xs))))) ∙ₑ
       congMaybeEquiv (swap0and1M (h𝔽in xs)))
      (map-Maybe
       (idfun (Maybe (Maybe (fst (h𝔽in xs)))) ∘ swap0and1Mf (h𝔽in xs)) x)
      ≡
      fst
      (swap0and1M
       (Mb^ 1 (h𝔽in xs)))
      ((idfun (Maybe (Maybe (fst (h𝔽in (y ∷2 xs))))) ∘
        swap0and1Mf
        (Mb^ 1 (h𝔽in xs)))
       x)
   zHj0 nothing i = nothing
   zHj0 (just nothing) i = (just nothing)
   zHj0 (just (just nothing)) i = (just (just nothing))
   zHj0 (just (just (just x))) i = (just (just (just x)))
 
   zHH : (x : Maybe (Maybe (Maybe (𝔽in xs)))) →
       Square {A = Maybe (Maybe (Maybe (𝔽in xs)))}
         (λ j → fst (swapMlsq-R-ei0 (h𝔽in xs) j)
              (map-Maybe (ua-gluePathExt (PCI.e {B = B} {A = A} (xs)) j
                   ∘ swap0and1Mf (h𝔽in xs)) x))
         (λ j → fst (ua-unglueEquiv (swap0and1M (Mb^ 1 (h𝔽in xs))) j)
                 ((ua-gluePathExt (PCI.e {B = B} {A = A} (y ∷2  xs)) j ∘
            swap0and1Mf (Mb^ 1 (h𝔽in xs))) x))
         (zHj0 x)
         (funExt⁻ zHj1 x) 
   zHH nothing _ _ = nothing
   zHH (just nothing) _ _ = (just nothing)
   zHH (just (just nothing)) _ _ = (just (just nothing))
   zHH (just (just (just x))) _ _ = (just (just (just x)))



   zH : Maybe (Maybe (Maybe (𝔽in xs))) → A
   zH = f ∘ λ x → glue
     (λ {(i = i0) → map-Maybe (ua-gluePathExt (PCI.e {B = B} {A = A} (xs)) j
                   ∘ swap0and1Mf (h𝔽in xs)) x
        ;(i = i1) → (ua-gluePathExt (PCI.e {B = B} {A = A} (y ∷2  xs)) j ∘
            swap0and1Mf (Mb^ 1 (h𝔽in xs))) x
        ;(j = i1) → zHj1 i x }) (zHH x i j)
   
RElim.hex* (RFM2tab {A = A} {B = B}) x y z {xs} b i j f = 
  hex (zH nothing)
       (zH (just (just nothing)))
       (zH (just nothing))
       (b (zH ∘ just ∘ just ∘ just)) i j

 where

   zHH : Square {A = Maybe (Maybe (Maybe (𝔽in xs)))
                    → Maybe (Maybe (Maybe (𝔽in xs)))}
              (λ j →
                fst (snd ((swapMlsq-H-sides (h𝔽in xs) i0) j 1=1))
                   ∘ ua-gluePathExt (swap0and1M (Mb^ 1 (h𝔽in xs))) j
                 ∘ (map-Maybe (swap0and1Mf ((h𝔽in xs)))))
              (λ j → fst (snd ((swapMlsq-H-sides (h𝔽in xs) i1) j 1=1))
                   ∘ (map-Maybe (ua-gluePathExt (swap0and1M (h𝔽in xs)) j ))
                  ∘ (swap0and1Mf (Mb^ 1 (h𝔽in xs))))
              (funExt
                 (Mb.elim _ refl (Mb.elim _ refl
                   (Mb.elim _ refl (λ _ → refl)))))
              (sym (cong fst (swap-braid (h𝔽in xs))))
   zHH _ _ nothing = just (just nothing)
   zHH _ _ (just nothing) = just nothing
   zHH _ _ (just (just nothing)) = nothing
   zHH _ _ (just (just (just x))) = just (just (just x))


   zH : Maybe (Maybe (Maybe (𝔽in xs))) → A
   zH = f ∘ λ x → glue
     (λ {(i = i0) → ua-gluePathExt (swap0and1M (Mb^ 1 (h𝔽in xs))) j
                ((map-Maybe (swap0and1Mf ((h𝔽in xs))) x))
        ;(i = i1) → map-Maybe (ua-gluePathExt (swap0and1M (h𝔽in xs)) j )
                ((swap0and1Mf (Mb^ 1 (h𝔽in xs)) x)) 
        }) (zHH i j x)
  

RElim.trunc* RFM2tab xs = isGroupoidΠ λ _ → trunc


fm2tab : ∀ {ℓ'} {B : Type ℓ'} {A : Type ℓ}
 → (xs : FMSet2 B) → (𝔽in xs → A) → FMSet2 A
fm2tab = RElim.f (RFM2tab)


swap-lem : ∀ (xs : FMSet2 B) (a a' : A)
             (f : 𝔽in {A = B} xs → A) →
              Mb.rec a (Mb.rec a' f) ∘ (swap0and1Mf (h𝔽in xs)) ≡
               Mb.rec a' (Mb.rec a f)
swap-lem xs a a' f i nothing = a'
swap-lem xs a a' f i (just nothing) = a
swap-lem xs a a' f i (just (just x)) = f x

comm-→pa : ∀ {ℓ'} {B : Type ℓ'}  → ∀ b b' → ∀ (a : A) a' (xs : FMSet2 B)
                 (f : 𝔽in xs → A) →
                   PathP (λ j → 𝔽in (b' ∷2 b ∷2 xs) → A)
                     (Mb.rec a (Mb.rec a' f)
                             ∘' (swap0and1Mf (RRec.f Rh𝔽in xs)))
                     (Mb.rec a' (Mb.rec a f))
comm-→pa b b' a a' xs f = (funExt (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))

-- ΣPathPcommIso : ∀ {x y : Unit} xs → 
--        Iso
--          (Σ (Σ (𝔽in (x ∷2 y ∷2 xs) → A) (λ _ → 𝔽in (y ∷2 x ∷2 xs) → A))
--          (λ aa → PathP (λ z → 𝔽in (comm x y xs z) → A) (fst aa) (snd aa)))
--          (((Σ _ (uncurry (Path A))) × (Σ _  (uncurry (Path A))))
--             × (𝔽in xs → Σ _  (uncurry (Path A)))) 
           
-- fst (fst (Iso.fun (ΣPathPcommIso xs) (_ , p))) =
--  _ , funExtDep⁻ p {nothing} {just nothing} (ua-gluePath _ refl)
-- snd (fst (Iso.fun (ΣPathPcommIso xs) (_ , p))) =
--   _ , funExtDep⁻ p {just nothing} {nothing} (ua-gluePath _ refl)
-- snd (Iso.fun (ΣPathPcommIso xs) (_ , p)) x =
--  _ , funExtDep⁻ p {just (just x)} {just (just x)} (ua-gluePath _ refl)
-- Iso.inv (ΣPathPcommIso xs) ((((a₀ , a₁) , p) , ((a₀' , a₁') , p')) , f) =
--    _
--   , λ i → Mb.rec (p' i) (Mb.rec (p i) (funExt (snd ∘ f) i))
--        ∘' ua-ungluePathExt (swap0and1M (h𝔽in xs)) i
-- Iso.rightInv (ΣPathPcommIso xs) _ = refl
-- Iso.leftInv (ΣPathPcommIso xs) ((f₀ , f₁) , p) =
--   {!!}
--  -- ΣPathP
--  --  ( _
--  --    -- ΣPathP (mb≡ refl (mb≡ refl refl)  , mb≡ refl (mb≡ refl refl))
--  --    ,
--  --   (λ i j → p i ∘ 
--  --       {!ua-gluePathExt (swap0and1M (h𝔽in xs)) i!} ∘ ua-ungluePathExt (swap0and1M (h𝔽in xs)) j))
--    -- flipSquareP (congP (λ _ → funExt)
--    --   (elimUaSwapPath→ (h𝔽in xs)
--    --    _ _ _ (flipSquare refl) (flipSquare refl)
--    --      λ j x₁ i → p j (ua-gluePath (swap0and1M (h𝔽in xs)) refl j))) )


-- comm-inv→sq' : ∀ {ℓ'} {B : Type ℓ'}  → ∀ b b' → ∀ (a : A) a' (xs : FMSet2 B)
--                  (f : 𝔽in xs → A) →
--                SquareP (λ i j → 𝔽in (comm-inv b b' xs i j) → A)
--                   (λ j x → Mb.rec a (Mb.rec a' f)
--                              (swap0and1Mf (RRec.f Rh𝔽in xs)
--                               (unglue (j ∨ ~ j) x)))
--                   (λ j x → Mb.rec a (Mb.rec a' f) (unglue (j ∨ ~ j) x))
--                   (λ i →  Mb.rec a (Mb.rec a' f) ∘
--                        funExt (involSwap0and1Mf (h𝔽in xs)) i)
--                   refl
-- comm-inv→sq' b b' a a' xs f i j = 
--   (Mb.rec a (Mb.rec a' f) ∘ (unglue (i ∨ ~ i) ∘ (unglue (j ∨ ~ j))))


-- comm-inv→sqJ0 :  ∀ (b b' : B) → ∀ (a : A) a' (xs : FMSet2 B)
--                  (f : 𝔽in xs → A) →
--                   Square
--                     (λ i x → Mb.rec a (Mb.rec a' f) (involSwap0and1Mf (h𝔽in xs) x i))
--                     (swap-lem xs a' a f)
--                     --(funExt (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))
--                     (λ z → (comm-→pa b b' a a' xs f z) ∘
--                        swap0and1Mf (RRec.f Rh𝔽in xs))
--                     refl
-- comm-inv→sqJ0 b b' a a' xs f z i nothing = a
-- comm-inv→sqJ0 b b' a a' xs f z i (just nothing) = a'
-- comm-inv→sqJ0 b b' a a' xs f z i (just (just x)) = f x

-- comm-inv→sqJ1 : ∀ {ℓ'} {B : Type ℓ'}  → ∀ (b b' : B) → ∀ (a a' : A) (xs : FMSet2 B)
--                  (f : 𝔽in xs → A) →
--                   Square
--                     refl
--                     (sym (swap-lem xs a a' f))
--                     (λ z x → comm-→pa b b' a a' xs f z x)
--                     refl
                   
-- comm-inv→sqJ1 b b' a a' xs f z i nothing = a'
-- comm-inv→sqJ1 b b' a a' xs f z i (just nothing) = a
-- comm-inv→sqJ1 b b' a a' xs f z i (just (just x)) = f x

-- comm-inv→sq : ∀ {ℓ'} {B : Type ℓ'}  → ∀ b b' → ∀ (a : A) a' (xs : FMSet2 B)
--                  (f : 𝔽in xs → A) → 
--                SquareP (λ i j → 𝔽in (comm-inv b b' xs i j) → A)
--                   (λ i x → Mb.rec a' (Mb.rec a f) (unglue (i ∨ ~ i) x))
--                   (λ i x → Mb.rec a (Mb.rec a' f) (unglue (i ∨ ~ i) x))
--                   (swap-lem xs a' a f)
--                   (sym (swap-lem xs a a' f))
-- comm-inv→sq {A = A} b b' a a' xs f i j =
--   hcomp
--    (λ z →  λ {
--      (i = i0) → λ x → (comm-→pa b b' a a' xs f z) (unglue (j ∨ ~ j) x)
--     ;(i = i1) → (comm-inv→sq' b b' a a' xs f i j)
--     ;(j = i0) → comm-inv→sqJ0 b b' a a' xs f z i
--     ;(j = i1) → comm-inv→sqJ1 b b' a a' xs f z i
--        }) (comm-inv→sq' b b' a a' xs f i j)

comm-inv→sq : ∀ {ℓ'} {B : Type ℓ'}  → ∀ b b' → ∀ (a : A) a' (xs : FMSet2 B)
                 (f : 𝔽in xs → A) → 
               SquareP (λ i j → 𝔽in (comm-inv b b' xs i j) → A)
                  (λ i x → Mb.rec a' (Mb.rec a f) (unglue (i ∨ ~ i) x))
                  (λ i x → Mb.rec a (Mb.rec a' f) (unglue (i ∨ ~ i) x))
                  (swap-lem xs a' a f)
                  (sym (swap-lem xs a a' f))
comm-inv→sq b b' a a' xs f =
  funExtSqDep _ _ _ _
    (Mb.elim _ refl (Mb.elim _ refl
      λ x → congSq f (isSet→isSet' (snd (h𝔽in xs)) _ _ _ _)))


-- module fm2Look' (isGroupoidA : isGroupoid A)  where


--  fm⊤ : FMSet2 A → FMSet2 Unit
--  fm⊤ = fm2Map (λ _ → _)

--  RFM2look' : RElim {A = A} (λ xs → 𝔽in (fm⊤ xs) → A)
--  RElim.[]* RFM2look' ()
--  (RFM2look' RElim.∷* a) f = Mb.rec a f
--  RElim.comm* RFM2look' a a' {xs} f =
--    elimUaSwapPath→ (h𝔽in (fm⊤ xs))
--      (λ _ _ → A)
--       _ _ refl refl refl
--  RElim.comm-inv* RFM2look' = {!!}
--  RElim.commmL* RFM2look' = {!!}
--  RElim.commmR* RFM2look' = {!!}
--  RElim.commpL* RFM2look' = {!!}
--  RElim.commpR* RFM2look' = {!!}
--  RElim.hex* RFM2look' = {!!}
--  RElim.trunc* RFM2look' = {!!}

-- module fm2Look (isGroupoidA : isGroupoid A)  where

--  fm⊤ : FMSet2 A → FMSet2 Unit
--  fm⊤ = fm2Map (λ _ → _)


--  commmL-≡0 : ∀ (a a' a'' : A) → (xs : FMSet2 A) → (f : 𝔽in (fm⊤ xs) → A) → 
--              Mb.rec a (Mb.rec a' (Mb.rec a'' f)) ≡
--       (Mb.rec a' (Mb.rec a'' (Mb.rec a f))) ∘'
--         map-Maybe (swap0and1Mf ((h𝔽in (fm⊤ xs))))
--          ∘' swap0and1Mf (Mb^ 1 (h𝔽in (fm⊤ xs)))
--  commmL-≡0 a a' a'' xs f i nothing = a
--  commmL-≡0 a a' a'' xs f i (just nothing) = a'
--  commmL-≡0 a a' a'' xs f i (just (just nothing)) = a''
--  commmL-≡0 a a' a'' xs f i (just (just (just x))) = f x

--  commmL-≡1 : ∀ (a a' a'' : A) → (xs : FMSet2 A) → (f : 𝔽in (fm⊤ xs) → A) →
--       Mb.rec a' (Mb.rec a'' (Mb.rec a f)) ∘
--        swap0and1Mf (Mb^ 1 (h𝔽in (fm⊤ xs)))
--        ∘' map-Maybe (swap0and1Mf ((h𝔽in (fm⊤ xs))))
--           ≡ Mb.rec a'' (Mb.rec a (Mb.rec a' f))
--  commmL-≡1 a a' a'' xs f i nothing = a''
--  commmL-≡1 a a' a'' xs f i (just nothing) = a
--  commmL-≡1 a a' a'' xs f i (just (just nothing)) = a'
--  commmL-≡1 a a' a'' xs f i (just (just (just x))) = f x

 -- commmL-≡J0-0 : ∀ (a a' a'' : A) → (xs : FMSet2 A) → (f : 𝔽in (fm⊤ xs) → A) →
 --      (λ x' → Mb.rec a'' (Mb.rec a' (Mb.rec a f))
 --            (swap-braidF
 --             (h𝔽in (fm⊤ xs))
 --             x' (~ i0))) ≡ Mb.rec a (Mb.rec a' (Mb.rec a'' f))
 -- commmL-≡J0-0 a a' a'' xs f i nothing = a
 -- commmL-≡J0-0 a a' a'' xs f i (just nothing) = a'
 -- commmL-≡J0-0 a a' a'' xs f i (just (just nothing)) = a''
 -- commmL-≡J0-0 a a' a'' xs f i (just (just (just x))) = f x

 -- commmL-≡J0-1 : ∀ (a a' a'' : A) → (xs : FMSet2 A) → (f : 𝔽in (fm⊤ xs) → A) →
 --      (λ x' → Mb.rec a'' (Mb.rec a' (Mb.rec a f))
 --            (swap-braidF
 --             (h𝔽in (fm⊤ xs))
 --             x' (~ i1))) ≡ Mb.rec a (Mb.rec a' (Mb.rec a'' f))
 -- commmL-≡J0-1 a a' a'' xs f i nothing = a
 -- commmL-≡J0-1 a a' a'' xs f i (just nothing) = a'
 -- commmL-≡J0-1 a a' a'' xs f i (just (just nothing)) = a''
 -- commmL-≡J0-1 a a' a'' xs f i (just (just (just x))) = f x


 -- commmL-≡J0 : ∀ (a a' a'' : A) → (xs : FMSet2 A) → (f : 𝔽in (fm⊤ xs) → A) →
 --     Square {A = fst (Mb^ 3 (h𝔽in (fm⊤ xs))) → A}
 --       (λ i x' → Mb.rec a'' (Mb.rec a' (Mb.rec a f))
 --            (swap-braidF
 --             (h𝔽in (fm⊤ xs))
 --             x' (~ i)))
 --       (λ _ → Mb.rec a (Mb.rec a' (Mb.rec a'' f)))
 --       (commmL-≡J0-0 a a' a'' xs f)
 --       (commmL-≡J0-1 a a' a'' xs f)
 -- commmL-≡J0 a a' a'' xs f _ _ nothing = a
 -- commmL-≡J0 a a' a'' xs f _ _ (just nothing) = a'
 -- commmL-≡J0 a a' a'' xs f _ _ (just (just nothing)) = a''
 -- commmL-≡J0 a a' a'' xs f _ _ (just (just (just x))) = f x

 -- commpL-≡0 : ∀ (a a' a'' : A) → (xs : FMSet2 A) → (f : 𝔽in (fm⊤ xs) → A) →
 --       Square
 --         {!!}
 --         {!!}
 --         {!!}
 --         {!!}
 -- commpL-≡0 a a' a'' xs f = {!!}


 -- commpL-sq : (a a' a'' : A) →
 --       (xs  : FMSet2 A) → (f : 𝔽in (fm⊤ xs) → A) → 
 --    SquareP (λ i j → 𝔽in (fm⊤ (commpL a a' a'' xs i j)) → A)
 --      (congP (λ z f₁ → Mb.rec a f₁)
 --       (_◁_ {A = λ i → ua (swap0and1M (h𝔽in (fm⊤ xs))) i → A}
 --          (λ i → (swap-lem (fm⊤ xs) a'' a' f (~ i))) 
 --        (λ i x → Mb.rec a'' (Mb.rec a' f) (unglue (i ∨ ~ i) x))))
 --      ((λ i → swap-lem (fm⊤ (a'' ∷2 xs)) a' a (Mb.rec a'' f) (~ i)) ◁
 --       (λ i x → Mb.rec a' (Mb.rec a (Mb.rec a'' f)) (unglue (i ∨ ~ i) x)))
 --      refl
 --      (commmL-≡0 a a'' a' xs f ◁
 --       (λ i x → Mb.rec a'' (Mb.rec a' (Mb.rec a f)) (unglue (i ∨ ~ i) x))
 --       ▷ commmL-≡1 a a'' a' xs f)
 -- commpL-sq a a' a'' xs f i j =
 --   -- sqWhisk {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}
 --   --    (unglue-Sq-elim' (λ i j → i ∨ ~ i ∨ ~ j) {!!}
 --   --       (λ i j → Mb.rec a'' (Mb.rec a' (Mb.rec a f))))
 --   --    {!!} {!!} {!!} {!!}
 --   --  hcomp {!!}
 --   --    (unglue-Sq-elim' (λ i j → i ∨ ~ i ∨ ~ j) {!!}
 --   --       (λ i j → Mb.rec a'' (Mb.rec a' (Mb.rec a f))) i j )
 --   hcomp
 --     (λ z →
 --       λ {
 --        (i = i0) → Mb.rec a
 --           (doubleWhiskFiller {A = λ i → ua (swap0and1M (h𝔽in (fm⊤ xs))) i → A}
 --             (sym (swap-lem (fm⊤ xs) a'' a' f ))
 --             ((λ i x → Mb.rec a'' (Mb.rec a' f) (unglue (i ∨ ~ i) x)))
 --                refl z j)
 --       ;(j = i0) →  sJ0 (~ z) i
 --       ;(j = i1) → sZ0 i j })
 --     (sZ0 i j)
 --   where
 --    pJ0Z0 : Mb.rec a (swap-lem (fm⊤ xs) a'' a' f (~ i1)) ≡
 --              swap-lem (fm⊤ (a'' ∷2 xs)) a' a (Mb.rec a'' f) (~ i1)
 --    pJ0Z0 i nothing = a
 --    pJ0Z0 i (just nothing) = a' 
 --    pJ0Z0 i (just (just nothing)) = a''
 --    pJ0Z0 i (just (just (just x))) = f x
    
 --    sJ0 : Square
 --            (λ _ → Mb.rec a (swap-lem (fm⊤ xs) a'' a' f i1))
 --            pJ0Z0
 --            (λ i₁ → Mb.rec a (swap-lem (fm⊤ xs) a'' a' f (~ i₁)))
 --            λ i₁ → swap-lem (fm⊤ (a'' ∷2 xs)) a' a (Mb.rec a'' f) (~ i₁)
 --    sJ0 i j nothing = a
 --    sJ0 i j (just nothing) = a' 
 --    sJ0 i j (just (just nothing)) = a''
 --    sJ0 i j (just (just (just x))) = f x

 --    sZ0 : SquareP (λ i j → 𝔽in (fm⊤ (commpL a a' a'' xs i j)) → A)
 --             (congP (λ z f₁ → Mb.rec a f₁)
 --               ((λ i x → Mb.rec a'' (Mb.rec a' f) (unglue (i ∨ ~ i) x))))
 --             (λ i x → Mb.rec a' (Mb.rec a (Mb.rec a'' f)) (unglue (i ∨ ~ i) x))
 --             pJ0Z0
 --             ((commmL-≡0 a a'' a' xs f ◁
 --       (λ i x → Mb.rec a'' (Mb.rec a' (Mb.rec a f)) (unglue (i ∨ ~ i) x))
 --       ▷ commmL-≡1 a a'' a' xs f))
 --    sZ0 = {!!}

           -- doubleCompPath-filler
           --          ((λ i → Mb.rec a ((swap-lem (fm⊤ xs) a'' a' f) i)))
           --          (refl)
           --          (sym (swap-lem (fm⊤ (a'' ∷2 xs)) a' a (Mb.rec a'' f)))

-- -- i = i0 ⊢ Mb.rec a' (Mb.rec a'' (Mb.rec a f))
-- --          (swap0and1Mf
-- --           (Maybe
-- --            (fst
-- --             (RRec.f Rh𝔽in
-- --              (Cubical.HITs.ListedFiniteSet.Base3.f' (λ _ → tt) xs)))
-- --            ,
-- --            isSetMaybe
-- --            (snd
-- --             (RRec.f Rh𝔽in
-- --              (Cubical.HITs.ListedFiniteSet.Base3.f' (λ _ → tt) xs))))
-- --           (just (Agda.Builtin.Cubical.Glue.prim^unglue x)))
-- -- i = i1 ⊢ Mb.rec a' (Mb.rec a f)
-- --          (Agda.Builtin.Cubical.Glue.prim^unglue x)
-- -- j = i0 ⊢ _a₋₀_6498 i (just x)
-- -- j = i1 ⊢ _a₋₁_6499 i (just x)

--  RFM2look' : RElim {A = A} (λ xs → 𝔽in (fm⊤ xs) → A)
--  RElim.[]* RFM2look' ()
--  (RFM2look' RElim.∷* a) f = Mb.rec a f
--  RElim.comm* RFM2look' a a' {xs} f =
--    sym (swap-lem (fm⊤ xs) a' a f)
--    ◁ (λ i x → Mb.rec a' (Mb.rec a f) (unglue (i ∨ ~ i) x))
     
--  RElim.comm-inv* RFM2look' a a' {xs} f i j = 
--     ((λ j → (swap-lem (fm⊤ xs) a' a f) (~ (j ∧ ~ i)))
--      ◁ comm-inv→sq  _ _ a a' (fm⊤ xs) f i ▷
--       λ j → (swap-lem (fm⊤ xs) a a' f ((j ∨  ~ i) ))) j

--  RElim.commmL* RFM2look' a a' a'' {xs} f = 
--      commmL-≡0 a a' a'' xs f ◁
--        (λ i x → Mb.rec a' (Mb.rec a'' (Mb.rec a f)) (unglue (i ∨ ~ i) x))
--        ▷ commmL-≡1 a a' a'' xs f
--  RElim.commmR* RFM2look' a a' a'' {xs} f = {!!}
--      -- {!!} ◁
--      --   (λ i x → Mb.rec a (Mb.rec a'' (Mb.rec a' f)) (unglue (i ∨ ~ i) x))
--      --   ▷ {!!}
--  RElim.commpL* RFM2look' a a' a'' {xs} f = {!!}
--       -- ((λ j → {!!}) ◁ λ i₁ → {!!}) j  
--     -- {!!} ◁
--     --   (λ i j → hcomp
--     --         (λ z → λ {
--     --     (i = i1)(j = i1) → commmL-≡1 a a'' a' xs f z
--     --   ; (i = i0)(j = i1) → commmL-≡0 a a'' a' xs f (~ z)
--     --   ; (j = i0) →  
--     --         commmL-≡J0 a a' a'' xs f z i
--     --         })
--     --         λ x' → Mb.rec a'' (Mb.rec a'
--     --               (Mb.rec a f)) (unglue (i ∨ ~ i ∨  ~ j) x'))
--     --      ▷ λ i →  {!!} ◁ {!!} ▷ {!!}
--  RElim.commpR* RFM2look' a a' a'' {xs} f = --swapMlsq-H-sides (h𝔽in xs)
--    sqWhisk _ {!!} {!!} {!!} {!!} _ _ _ _
--       {!unglue-Sq-elim' (λ i j → i ∨ ~ i) {!!}
--          (λ i j → Mb.rec a'' (Mb.rec a' (Mb.rec a f)))!}
--       {!!}
--       {!!}
--       {!!}
--       {!!}
--  RElim.hex* RFM2look' a a' a'' {xs} f = 
--    -- swapMlsq-H-sides (h𝔽in xs)
--    sqWhisk _ _ _ _ _ _ _ _ _
--       (unglue-Sq-elim' (λ i j → i ∨ ~ i) (swapMlsq-H-sides (h𝔽in (fm⊤ xs)))
--          (λ i j → Mb.rec a' (Mb.rec a'' (Mb.rec a f))))
--       {funExt ((Mb.elim _ (refl) (Mb.elim _ (refl)
--             (Mb.elim _ (refl) λ x → refl))))}
--       {funExt ((Mb.elim _ (refl) (Mb.elim _ (refl)
--             (Mb.elim _ (refl) λ x → refl))))}
--       {funExt ((Mb.elim _ (refl) (Mb.elim _ (refl)
--             (Mb.elim _ (refl) λ x → refl))))}
--       {funExt ((Mb.elim _ (refl) (Mb.elim _ (refl)
--             (Mb.elim _ (refl) λ x → refl))))}
--       zi0
--       zi1
--       zj0
--       {!!}

--    where
--     zi0 : SquareP _ _ _ _ _
--     zi0 = sqWhisk _ _ _ _ _ _ _ _ _
--              (λ i j → 
--                 mb^ext (map-Maybe (swap0and1Mf (h𝔽in (fm⊤ xs))))
--                      f (λ _ → refl) a' a'' a (i) ∘
--                   unglue (j ∨ ~ j)
--                   )
--              {refl}{refl} refl
--              (doubleWhiskFiller
--                (λ i → swap-lem (fm⊤ (a'' ∷2 xs)) a' a (Mb.rec a'' f) (~ i)) _ _)
--              (λ { _ _ nothing → a 
--                 ; _ _ (just nothing) → a' 
--                 ; _ _ (just (just nothing)) → a''
--                 ; _ _ (just (just (just x))) →  f x
--                 })
--              (λ { _ _ nothing → a' 
--                 ; _ _ (just nothing) → a 
--                 ; _ _ (just (just nothing)) → a''
--                 ; _ _ (just (just (just x))) →  f x
--                 })

--     zi1 :  SquareP
--       (λ _ j →
--          Glue (Maybe (Maybe (Maybe (fst (h𝔽in (fm⊤ xs))))))
--          (swapMlsq-H-sides (h𝔽in (fm⊤ xs)) i1 j) →
--          A)
--       _ _ _ _
--     zi1 = sqWhisk _ _ _ _ _ _ _ _ _
             
--              (λ { _ _ nothing  → a''
--                 ; i j (just x) → {!!}
--                 })
--              {refl} {refl}
--              refl
--              (λ i j → Mb.rec a''
--                (doubleWhiskFiller {A = λ i → 𝔽in (comm _ _ (fm⊤ xs) i) → A}
--                 (λ i → swap-lem (fm⊤ xs) a' a f (~ i))
--                 (λ i x → Mb.rec a' (Mb.rec a f) (unglue (i ∨ ~ i) x))
--                 refl i j))
--                 {!!}
--                 {!!}
--              -- (λ { _ _ nothing → a''
--              --    ; _ _ (just nothing) → a
--              --    ; _ _ (just (just nothing)) → a'
--              --    ; _ _ (just (just (just x))) →  f x
--              --    })
--              -- (λ { _ _ nothing → a''
--              --    ; _ _ (just nothing) → a'
--              --    ; _ _ (just (just nothing)) → a
--              --    ; _ _ (just (just (just x))) →  f x
--              --    })


--     zj0 : SquareP _ _ _ _ _
--     zj0 = sqWhisk _ _ _ _ _ _ _ _ _
--            (λ _ i → Mb.rec a' (Mb.rec a'' (Mb.rec a f)) ∘ unglue (i ∨ ~ i))
--            {refl} {refl}
--            refl
--            (doubleWhiskFiller (commmL-≡0 a a' a'' xs f) _ _)
--            ((λ { _ _ nothing → a 
--                 ; _ _ (just nothing) → a' 
--                 ; _ _ (just (just nothing)) → a''
--                 ; _ _ (just (just (just x))) →  f x
--                 }))
--            (λ { _ _ nothing → a'' 
--                 ; _ _ (just nothing) → a 
--                 ; _ _ (just (just nothing)) → a'
--                 ; _ _ (just (just (just x))) →  f x
--                 })
--  RElim.trunc* RFM2look' xs = isGroupoidΠ λ _ → isGroupoidA

-- --  FM2look' : ∀ xs → 𝔽in (fm⊤ xs) → A
-- --  FM2look' = RElim.f RFM2look'

-- --  lt-ret : RElimSet' λ (xs : FMSet2 A) → fm2tab (fm⊤ xs) (FM2look' xs) ≡ xs 
-- --  RElimSet'.[]* lt-ret = refl
-- --  (lt-ret RElimSet'.∷* a) {xs} p = cong (a ∷2_) p
-- --  RElimSet'.comm* lt-ret a a' {xs} p i j =
-- --     hcomp (λ z → primPOr (i ∨ ~ i ∨ j) (~ j) (λ _ → (comm a a' (p j) i))
-- --      λ _ → comm
-- --      (compPathRefl {x = a} z i)
-- --      (compPathRefl {x = a'} z i)
-- --      (fm2tab (fm⊤ xs) (compPathRefl {x = FM2look' xs} z i)) i)
-- --      (comm a a' (p j) i)

-- --  RElimSet'.trunc* lt-ret _ = trunc _ _

-- --  lt-sec-fst : RElimSet' λ (xs : FMSet2 Unit) →
-- --        ∀ f → Path (FMSet2 Unit)
-- --          (fm⊤ (fm2tab xs f))
-- --          (xs)
-- --  RElimSet'.[]* lt-sec-fst f = refl
-- --  (lt-sec-fst RElimSet'.∷* tt) p f =
-- --    cong (tt ∷2_) (p _)
-- --  RElimSet'.comm* lt-sec-fst x y {xs} b i f j =
-- --    comm tt tt
-- --      (b (f ∘ ua-gluePathExt (PCI.e {B = Unit} {A = A} xs) i ∘ just ∘ just) j) i
-- --  RElimSet'.trunc* lt-sec-fst _ = isSetΠ λ _ → trunc _ _


-- --  qqzz : ∀ (xs : FMSet2 Unit) → ∀ (f : 𝔽in xs → A) → 𝔽in (fm⊤ (fm2tab xs f)) → 𝔽in xs
-- --  qqzz xs f = subst 𝔽in ((RElimSet'.f lt-sec-fst xs f))

-- --   -- subst⁻ 𝔽in ((RElimSet'.f lt-sec-fst xs f))
-- --  -- zzqqR : RElimSet' (λ z → (f : 𝔽in z → A) → 𝔽in z → 𝔽in (fm⊤ (fm2tab z f)))
-- --  -- RElimSet'.[]* zzqqR _ ()
-- --  -- (zzqqR RElimSet'.∷* x) x₁ f nothing = nothing
-- --  -- (zzqqR RElimSet'.∷* x) x₁ f (just x₂) = just (x₁ (f ∘ just) x₂)
-- --  -- -- map-Maybe {!x₁ (f ∘ just)!}
-- --  -- RElimSet'.comm* zzqqR = {!!}
-- --  -- RElimSet'.trunc* zzqqR = {!!}

-- --  zzqq : ∀ (xs : FMSet2 Unit) → ∀ (f : 𝔽in xs → A) → 𝔽in xs
-- --        → 𝔽in (fm⊤ (fm2tab xs f))
-- --  zzqq xs f = subst⁻ 𝔽in ((RElimSet'.f lt-sec-fst xs f))
-- --  -- RElimSet'.f zzqqR


-- --  qqzzA : ∀ (xs : FMSet2 Unit) →
-- --         (f : 𝔽in xs → A) → 𝔽in (fm⊤ (fm2tab xs f)) → A
-- --  qqzzA xs f = f ∘ qqzz xs f

-- --  -- zzqqA : ∀ (xs : FMSet2 Unit) →
-- --  --        (f : 𝔽in (fm⊤ (fm2tab xs f)) → A) → 𝔽in xs → A
-- --  -- zzqqA xs f = f ∘ zzqq xs f


-- --  -- R-lt-sec-fst-F : RElimSet' λ z →
-- --  --            PathP
-- --  --            (λ j →
-- --  --               (f : 𝔽in z → A) → 𝔽in (RElimSet'.f lt-sec-fst z f j) → 𝔽in z)
-- --  --            (qqzz z) (λ z₁ → idfun (𝔽in (RElimSet'.f lt-sec-fst z z₁ i1)))
-- --  -- RElimSet'.[]* R-lt-sec-fst-F = refl
-- --  -- (R-lt-sec-fst-F RElimSet'.∷* x) x₁ j f nothing = nothing
-- --  -- (R-lt-sec-fst-F RElimSet'.∷* x) x₁ j f (just x₂) =
-- --  --   just (x₁ j (f ∘ just) x₂) 
-- --  -- RElimSet'.comm* R-lt-sec-fst-F = {!!}
-- --  -- RElimSet'.trunc* R-lt-sec-fst-F = {!!}

-- --  -- lt-sec-fst-F : ∀ xs →
-- --  --    PathP (λ j → ∀ f → 𝔽in (RElimSet'.f lt-sec-fst xs f j) →
-- --  --              𝔽in (xs))
-- --  --               (qqzz xs) λ _ → idfun _
-- --  -- lt-sec-fst-F = RElimSet'.f R-lt-sec-fst-F


-- --  -- lt-sec-snd'' : ∀ (xs : FMSet2 Unit) →
-- --  --       PathP
-- --  --         (λ j → ∀ f → 𝔽in (RElimSet'.f lt-sec-fst xs f j) → A)
-- --  --          (λ f → FM2look' (fm2tab xs f))
-- --  --          (idfun _)
-- --  -- lt-sec-snd'' xs = toPathP {!!}


-- -- -- RElim.comm* (RFM2tab {A = A} {B = B}) _ _ {xs} b i f = 
-- -- --  let z = f ∘' ua-gluePathExt (PCI.e {B = B} {A = A} xs) i
-- -- --  in comm (z nothing) (z (just nothing)) (b (z ∘ just ∘ just)) i


-- --  -- RElim.comm* RFM2look' a a' {xs} f =
-- --  --   sym (swap-lem (fm⊤ xs) a' a f)
-- --  --   ◁ (λ i x → Mb.rec a' (Mb.rec a f) (unglue (i ∨ ~ i) x))


-- --  tab-hlp : (a a' : A) → (xsa : FMSet2 A) → 
-- --           PathP (λ i → 𝔽in (comm tt tt (fm⊤ xsa) i) → A)
-- --             (Mb.rec a' (Mb.rec a (FM2look' xsa))
-- --               ∘ swap0and1Mf (h𝔽in (fm⊤ xsa)))
-- --             (Mb.rec a' (Mb.rec a (FM2look' xsa)))
-- --  tab-hlp a a' xsa i =
-- --     let f' = FM2look' xsa
-- --     in Mb.rec a' (Mb.rec a f')
-- --          ∘ ua-ungluePathExt (swap0and1M (h𝔽in (fm⊤ xsa))) i


-- --  ∷-sec-snd : (x : Unit) {xs : FMSet2 Unit} →
-- --       PathP
-- --       (λ j → (f : 𝔽in xs → A) → 𝔽in (RElimSet'.f lt-sec-fst xs f j) → A)
-- --       (λ f → FM2look' (fm2tab xs f)) (idfun (𝔽in xs → A)) →
-- --       PathP
-- --       (λ j →
-- --          (f : 𝔽in (x ∷2 xs) → A) →
-- --          𝔽in (RElimSet'.f lt-sec-fst (x ∷2 xs) f j) → A)
-- --       (λ f → FM2look' (fm2tab (x ∷2 xs) f)) (idfun (𝔽in (x ∷2 xs) → A))
-- --  ∷-sec-snd x {xs} p i f nothing = f nothing
-- --  ∷-sec-snd x {xs} p i f (just x₁) = p i (f ∘ just) x₁ 


-- --  comm-sec-snd-bot : (x y : Unit) {xs : FMSet2 Unit} →
-- --           (X
-- --        : PathP
-- --          (λ j → (f : 𝔽in xs → A) → 𝔽in (RElimSet'.f lt-sec-fst xs f j) → A)
-- --          (λ f → FM2look' (fm2tab xs f)) (idfun (𝔽in xs → A))) →
-- --          SquareP (λ i j →  (f : 𝔽in (comm x y xs i) → A) →
-- --             𝔽in (RElimSet'.f lt-sec-fst (comm x y xs i) f j) → A)
-- --             (λ j f x' →
-- --                (Mb.rec (f (just nothing))
-- --                   (Mb.rec (f (nothing)) (X j (f ∘ just ∘ just)))) 
-- --                    (swap0and1Mf
-- --                       (RRec.f Rh𝔽in
-- --                        (RElim.f (RElimSet'.fR lt-sec-fst) xs
-- --                         (λ x → f (just (just x))) j))
-- --                       x'))
-- --             (λ j f x' → (Mb.rec (f (nothing))
-- --                   (Mb.rec (f (just nothing)) (X j (f ∘ just ∘ just)))) 
-- --                    x')
-- --             (λ i f x' → Mb.rec ((f ∘ (ua-gluePathExt (swap0and1M (h𝔽in xs)) i))
-- --                       (just nothing))
-- --                 (Mb.rec ((f ∘ (ua-gluePathExt (swap0and1M (h𝔽in xs)) i)) nothing) ((X i0 ((f ∘ ua-gluePathExt
-- --                        (PCI.e {B = Unit} {A = A} xs) i ∘ just ∘ just)))))
-- --                 ((ua-unglue (swap0and1M (h𝔽in
-- --                    (RElimSet'.f lt-sec-fst xs
-- --                      (f ∘ ua-gluePathExt
-- --                        (PCI.e {B = Unit} {A = A} xs) i ∘ just ∘ just) i0))) i
-- --                x')))
-- --             (swap0and1MfunSq A (h𝔽in xs) i0)
-- --  comm-sec-snd-bot x y {xs} X i j f x' =
-- --    (let f' = f ∘ (ua-gluePathExt (swap0and1M (h𝔽in xs)) i)
-- --        in Mb.rec (f' (just nothing))
-- --           (Mb.rec (f' nothing) (X j ((f ∘ ua-gluePathExt
-- --                        (PCI.e {B = Unit} {A = A} xs) i ∘ just ∘ just))))
-- --             (ua-unglue (swap0and1M (h𝔽in
-- --                    (RElimSet'.f lt-sec-fst xs
-- --                      (f ∘ ua-gluePathExt
-- --                        (PCI.e {B = Unit} {A = A} xs) i ∘ just ∘ just) j))) i
-- --                x')) 


-- --  comm-sec-sndI1 : (x y : Unit) {xs : FMSet2 Unit}
-- --       (X
-- --        : PathP
-- --          (λ j → (f : 𝔽in xs → A) → 𝔽in (RElimSet'.f lt-sec-fst xs f j) → A)
-- --          (λ f → FM2look' (fm2tab xs f)) (idfun (𝔽in xs → A))) →
-- --       SquareP (λ z j →  (f : 𝔽in (comm x y xs i1) → A) →
-- --             𝔽in (RElimSet'.f lt-sec-fst (comm x y xs i1) f j) → A)
-- --           (comm-sec-snd-bot x y {xs} X i1)
-- --           ((∷-sec-snd y {_ ∷2 xs} (∷-sec-snd x {xs} X)))
-- --           refl
-- --           λ z → swap0and1MfunSq A (h𝔽in xs) z i1 
-- --  comm-sec-sndI1 x y {xs} X z j f nothing = f nothing
-- --  comm-sec-sndI1 x y {xs} X z j f (just nothing) = f (just nothing)
-- --  comm-sec-sndI1 x y {xs} X z j f (just (just x₁)) =
-- --    X j (λ x₂ → f (just (just x₂))) x₁


-- --  comm-sec-sndI0 : (x y : Unit) {xs : FMSet2 Unit}
-- --       (X
-- --        : PathP
-- --          (λ j → (f : 𝔽in xs → A) → 𝔽in (RElimSet'.f lt-sec-fst xs f j) → A)
-- --          (λ f → FM2look' (fm2tab xs f)) (idfun (𝔽in xs → A))) →
-- --       SquareP (λ z j →  (f : 𝔽in (comm x y xs i0) → A) →
-- --             𝔽in (RElimSet'.f lt-sec-fst (comm x y xs i0) f j) → A)
-- --           (comm-sec-snd-bot x y {xs} X i0)
-- --           ((∷-sec-snd x {_ ∷2 xs} (∷-sec-snd x {xs} X)))
-- --           (λ z f x' → swap-lem
-- --              (fm⊤ ((fm2tab (xs) (f ∘ just ∘ just))))
-- --                 (f (just nothing)) (f nothing)
-- --                (X i0 (f ∘ just ∘ just)) z x')
-- --           λ z → swap0and1MfunSq A (h𝔽in xs) z i0

-- --  comm-sec-sndI0 x y {xs} X i j f nothing = f nothing
-- --  comm-sec-sndI0 x y {xs} X i j f (just nothing) = f (just nothing)
-- --  comm-sec-sndI0 x y {xs} X i j f (just (just x₁)) =
-- --    X j (λ x₂ → f (just (just x₂))) x₁
   

-- --  comm-sec-snd : (x y : Unit) {xs : FMSet2 Unit}
-- --       (X
-- --        : PathP
-- --          (λ j → (f : 𝔽in xs → A) → 𝔽in (RElimSet'.f lt-sec-fst xs f j) → A)
-- --          (λ f → FM2look' (fm2tab xs f)) (idfun (𝔽in xs → A))) →
-- --       PathP
-- --       (λ i →
-- --          PathP
-- --          (λ j →
-- --             (f : 𝔽in (comm x y xs i) → A) →
-- --             𝔽in (RElimSet'.f lt-sec-fst (comm x y xs i) f j) → A)
-- --          (λ f → FM2look' (fm2tab (comm x y xs i) f))
-- --          (idfun (𝔽in (comm x y xs i) → A)))
-- --       (∷-sec-snd x {_ ∷2 xs} (∷-sec-snd y {xs} X))
-- --       (∷-sec-snd y {_ ∷2 xs} (∷-sec-snd x {xs} X))
-- --  comm-sec-snd x y {xs} X = 
-- --    λ i j f x' →
-- --             hcomp
-- --           (λ z → λ {
-- --            (i = i0) → comm-sec-sndI0 x y {xs} X z j f x'
-- --           ;(i = i1) → comm-sec-sndI1 x y {xs} X z j f x'
-- --           ;(j = i1) → swap0and1MfunSq A (h𝔽in xs) z i f x'
-- --            }) (comm-sec-snd-bot x y {xs} X i j f x')

         

-- --  lt-sec-snd : RElimSet' λ  (xs : FMSet2 Unit) →
-- --        PathP
-- --          (λ j → (f : 𝔽in xs → A) → 𝔽in (RElimSet'.f lt-sec-fst xs f j) → A)
-- --           (λ f → FM2look' (fm2tab xs f))
-- --           (idfun _)
-- --  RElimSet'.[]* lt-sec-snd j f ()
-- --  RElimSet'._∷*_ lt-sec-snd = ∷-sec-snd
-- --  RElimSet'.comm* lt-sec-snd = comm-sec-snd
-- --  RElimSet'.trunc* lt-sec-snd xs =
-- --    isOfHLevelRespectEquiv 2 (invEquiv (PathP≃Path _ _ _))
-- --      (isGroupoidΠ (λ _ → isGroupoidΠ λ _ → isGroupoidA) _ _)

-- --  look-tab-Iso : Iso (FMSet2 A) (Σ (FMSet2 Unit) λ xs → 𝔽in xs → A)
-- --  Iso.fun look-tab-Iso xs = fm⊤ xs , FM2look' xs
-- --  Iso.inv look-tab-Iso = uncurry fm2tab
-- --  Iso.rightInv look-tab-Iso =
-- --     uncurry λ xs f → ΣPathP
-- --      (RElimSet'.f lt-sec-fst xs f ,
-- --       λ i → RElimSet'.f lt-sec-snd xs i f)
-- --  Iso.leftInv look-tab-Iso = RElimSet'.f lt-ret









-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module fm2Look₀ (isGroupoidA : isGroupoid A)  where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  comm-inv-sqJ0 : ∀ a a' b (f : fst b → A) → Square {A = fst (Mb^ 2 b) → A}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     {Mb.rec a' (Mb.rec a f)} {Mb.rec a' (Mb.rec a f)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (λ _ → {!!}) {Mb.rec a' (Mb.rec a f)} {Mb.rec a' (Mb.rec a f)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (λ _ → Mb.rec a' (Mb.rec a f))
                    
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (funExt (Mb.elim _ (refl {x = a'}) (Mb.elim _ (refl {x = a})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         λ _ → refl)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     (funExt (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  comm-inv-sqJ0 a a' b f i j = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- comm-inv-sqJ0 a a' b f i j nothing = ?
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- comm-inv-sqJ0 a a' b f i j (just nothing) = ?
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- comm-inv-sqJ0 a a' b f i j (just (just x)) = ?

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  comm-inv→sq : ∀ a a' xs (b : 𝔽in xs → A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  SquareP (λ i j → 𝔽in (comm-inv a a' xs i j) → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     -- (λ i x → Mb.rec a' (Mb.rec a b) (unglue (i ∨ ~ i) x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     -- (λ i x → Mb.rec a (Mb.rec a' b) (unglue (i ∨ ~ i) x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     -- (funExt (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     -- (funExt (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  comm-inv→sq a a' xs b i j x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {! unglue (i ∨ ~ i) (unglue (j ∨ ~ j) x)!}
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RFM2look : RElim {A = A} (λ xs → 𝔽in xs → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.[]* RFM2look ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  (RFM2look RElim.∷* a) x₁ = Mb.rec a x₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.comm* RFM2look a a' b =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    funExt (Mb.elim _ refl (Mb.elim _ refl λ _ → refl))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ◁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ i x → Mb.rec a' (Mb.rec a b) (unglue (i ∨ ~ i) x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ▷ funExt (Mb.elim _ refl (Mb.elim _ refl λ _ → refl))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- ua→ (Mb.elim _ refl (Mb.elim _ refl λ _ → refl))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.comm-inv* RFM2look a a' {xs} b i j =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hcomp (λ z → λ { (j = i0) → comm-inv-sqJ0 a a' (h𝔽in xs) b z i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ; (j = i1) → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.commmL* RFM2look = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.commmR* RFM2look = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.commpL* RFM2look = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.commpR* RFM2look = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.hex* RFM2look = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.trunc* RFM2look = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hexUΣsq : ∀ (A : Type ℓ) → (A' : Type ℓ) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         Square
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (cong (A ×_) (sym (ua ((Σ-swap-01-≃ {A = A} {A} {A'})))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (sym (ua (Σ-swap-02-≃ {A = A} {A} {A} {A'})))          
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (sym (ua (Σ-swap-01-≃ {A = A} {A} {A × A'})))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (sym (ua (Σ-swap-01-≃ {A = A} {A} {A × A'})))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- hexUΣsq A A' i j =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Glue (A × A × A × A')
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         λ { (i = i0) → (Σ A (λ _ → sym (ua (Σ-swap-01-≃ {A = A} {A} {A'})) j)) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         ≃-× (idEquiv A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                          (ua-unglueEquiv (Σ-swap-01-≃ {A = A} {A} {A'}) (~ j))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ; (j = i0) → (ua (Σ-swap-01-≃ {A = A} {A} {A × A'})) (~ i) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ; (j = i1) → (ua (Σ-swap-01-≃ {A = A} {A} {A × A'})) (~ i) , {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            }


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Rh𝕍 : ∀ {ℓ'} {B : Type ℓ'} → RElim {A = B}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (λ xs → singlTy (𝔽in xs → A))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.[]* Rh𝕍 = (Unit* , λ _ → _) , snd (invEquiv (Unit*≃⊥→A _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (Rh𝕍 {A = A} {B = B} RElim.∷* x) {xs} ((T , F) , E) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (A × T , λ f → f nothing , F (f ∘ just)) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       snd (≃MaybeFunProd ∙ₑ ≃-× (idEquiv _) (F , E))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.comm* (Rh𝕍 {A = A} {B = B}) x y {xs} ((T , F) , E) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ΣPathPProp (isPropIsEquiv ∘ snd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (ΣPathP (sym (ua Σ-swap-01-≃)  ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      λ i x → glue (λ { (i = i0) → _ ; (i = i1) → _ })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (x (ua-gluePathExt (swap0and1M (h𝔽in xs)) i nothing)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          , (x ((ua-gluePathExt (swap0and1M (h𝔽in xs)) i (just nothing)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          , (F (x ∘ ua-gluePathExt (swap0and1M (h𝔽in xs)) i ∘ just ∘ just ))))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.comm-inv* (Rh𝕍) _ _ ((_ , F) , _) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ΣSquarePSet (λ _ _ → isProp→isSet ∘ isPropIsEquiv ∘ snd) _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (ΣSquareP (sym (involSymΣ01 _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         , λ i j f → glue (λ { (j = i0) → _ ; (j = i1) → _ })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (glue (λ { (i = i0) → _ ; (i = i1) → _ })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 ((f (((glue (λ { (j = i0) → nothing ; (j = i1) → just nothing })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (glue (λ { (i = i0) → just nothing ; (i = i1) → nothing }) nothing)))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ((f ((((glue (λ { (j = i1) → nothing
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                ; (j = i0) → just nothing
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            }) (glue (
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                              λ { (i = i1) → just nothing
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                ; (i = i0) → nothing }) (just nothing)))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  , (F λ y → f ((glue (λ { (j = i1) → (just (just y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                ; (j = i0) → (just (just y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                            }) (glue (
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                              λ { (i = i1) → (just (just y))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                ; (i = i0) → (just (just y)) })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                (just (just y)))))))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.hexDiag* Rh𝕍 _ _ _ {xs} ((T , F) , E) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ΣPathPProp (isPropIsEquiv ∘ snd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (ΣPathP (sym (ua Σ-swap-02-≃)  ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      λ i x → glue (λ { (i = i0) → _ ; (i = i1) → _ })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (x (ua-gluePathExt (swap0and2M (h𝔽in xs)) i nothing)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          , (x (ua-gluePathExt (swap0and2M (h𝔽in xs)) i (just nothing))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          , (x (ua-gluePathExt (swap0and2M (h𝔽in xs)) i (just (just nothing))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          , ((F (x ∘ ua-gluePathExt (swap0and2M (h𝔽in xs)) i ∘ just ∘ just ∘ just )))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.hexU* (Rh𝕍 {A = A}) x y z {xs} ((T , F) , E) = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ΣSquarePSet (λ _ _ → isProp→isSet ∘ isPropIsEquiv ∘ snd) _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (ΣSquareP ((λ i j → (hexUΣsq A T) i j) , {!!}))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.hexL* Rh𝕍 = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.trunc* Rh𝕍 xs =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isOfHLevelPlus {n = 0} 3 (isContr-singlTy (𝔽in xs → _))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Rh𝔽in× : ∀ {ℓ'} {B : Type ℓ'} → RElim {A = B}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (λ xs → singlTy (𝔽in xs → A))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.[]* Rh𝔽in→ = (_ , idfun _) , idIsEquiv _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (Rh𝔽in→ {A = A} {B = B} RElim.∷* _) {xs} ((T , F) , E) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ({!!} ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     λ f → Mb.rec (f nothing) {!F (f ∘ just)!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --(λ f → Mb.rec (f nothing) (f ∘ just))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!snd (congMaybeEquiv ?)!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.comm* (Rh𝔽in→ {A = A} {B = B}) _ _ {xs} b =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ΣPathPProp (isPropIsEquiv ∘ snd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (ΣPathP (sym (PCI.p' {B = B} {A = A} xs) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {!preCompInvol*.eq≃ {f = swap0and1Mf ?} A 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (involSwap0and1Mf _) ? !}))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- ΣPathPProp (isPropIsEquiv ∘ snd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --  (ΣPathP (sym (PCI.p' {B = B} {A = A} xs) , PCI.eq≃ {B = B} {A = A} xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.comm-inv* (Rh𝔽in→ {A = A} {B = B}) x y {xs} b = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- ΣSquarePSet (λ _ _ → isProp→isSet ∘ isPropIsEquiv ∘ snd) _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --   λ i j → PCI.pS' {B = B} {A = A} xs (~ i) j ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --     PCI.eq≃Sym' {B = B} {A = A} xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --       (flipSquare ∘ involSwap0and1Mf-coh _) i j

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.hexDiag* (Rh𝔽in→ {A = A} {B = B}) _ _ _ {xs} b = {!!}  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- ΣPathPProp (isPropIsEquiv ∘ snd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --  (ΣPathP (_ , PCI'.eq≃ {B = B} {A = A} xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.hexU* Rh𝔽in→ x y z {xs} b = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- ΣSquarePSet (λ _ _ → isProp→isSet ∘ isPropIsEquiv ∘ snd) _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   (ΣSquareP ((hexUT x y z xs) , {!!}))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   -- λ i i₁ → (hexUT x y z xs i i₁) , {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.hexL* Rh𝔽in→ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.trunc* Rh𝔽in→ xs =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isOfHLevelPlus {n = 0} 3 (isContr-singlTy (𝔽in xs → _))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝔽in→ : ∀ {ℓ'} {B : Type ℓ'} → Type ℓ → (FMSet2 B → Type ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝔽in→ A = fst ∘ fst ∘ RElim.f (Rh𝔽in→ {A = A})

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝔽in→ev : ∀ {ℓ'} {B : Type ℓ'} → (A : Type ℓ) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (∀ xs → (𝔽in {A = B} xs → A) → 𝔽in→ A xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝔽in→ev A = snd ∘ fst ∘ RElim.f (Rh𝔽in→ {A = A})

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝔽in→ev≃ : ∀ {ℓ'} {B : Type ℓ'} → (A : Type ℓ) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (∀ xs → (𝔽in {A = B} xs → A) ≃ 𝔽in→ A xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝔽in→ev≃ A xs = _  , snd ((RElim.f (Rh𝔽in→ {A = A}) xs))


 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝔽in→ev⁻ : ∀ {ℓ'} {B : Type ℓ'} → (A : Type ℓ) (isGroupoidA : isGroupoid A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (∀ xs → 𝔽in→ A xs → (𝔽in {A = B} xs → A))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝔽in→ev⁻ {B = B} A isGroupoidA = RElim.f w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w-comm : ∀ b b' {xs} → PathP
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ i → 𝔽in→ {B = B} A (comm b b' xs i) → 𝔽in (comm b b' xs i) → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ x₁ → x₁) (λ x₁ → x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w-comm b b' {xs} =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (λ i x y → x (involSwap0and1Mf (RRec.f Rh𝔽in xs) y (~ i))) ◁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ i x → unglue (i ∨ ~ i) x ∘
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (swap0and1Mf (RRec.f Rh𝔽in xs)) ∘ (unglue (i ∨ ~ i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ▷ (λ i x y → x (involSwap0and1Mf (RRec.f Rh𝔽in xs) y i))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w-comm-inv' : ∀ b b' {xs} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       SquareP (λ i j →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝔽in→ {B = B} A (comm-inv b b' xs i j) → 𝔽in (comm-inv b b' xs i j) → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ i x → unglue (i ∨ ~ i) x ∘
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (swap0and1Mf (RRec.f Rh𝔽in xs)) ∘ (unglue (i ∨ ~ i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ i x → unglue (i ∨ ~ i) x ∘
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (swap0and1Mf (RRec.f Rh𝔽in xs)) ∘ (unglue (i ∨ ~ i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ j x y → x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (involSwap0and1Mf (RRec.f Rh𝔽in xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (involSwap0and1Mf (RRec.f Rh𝔽in xs) y j) (~ j)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ j x y → x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (swap0and1Mf (RRec.f Rh𝔽in xs) (swap0and1Mf (RRec.f Rh𝔽in xs) y)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w-comm-inv' b b' {xs} j i x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   unglue (j ∨ ~ j) (unglue (i ∨ ~ i) x) ∘
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           unglue (j ∨ ~ j) ∘ (unglue (i ∨ ~ i)) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w-comm-inv : ∀ b b' {xs} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       SquareP (λ i j →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝔽in→ {B = B} A (comm-inv b b' xs i j) → 𝔽in (comm-inv b b' xs i j) → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (w-comm b b' {xs})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (symP (w-comm b' b {xs}))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w-comm-inv b b' {xs} i j x = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hcomp (λ z →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      λ { (j = i0) → λ y → x (involSwap0and1Mf (RRec.f Rh𝔽in xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (involSwap0and1Mf (RRec.f Rh𝔽in xs) y (i ∨ z)) (~ i ∨ z))
            
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ; (j = i1) → λ y → x (involSwap0and1Mf (RRec.f Rh𝔽in xs) y z)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ( unglue (i ∨ ~ i)  (unglue (j ∨ ~ j) x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ∘ unglue (i ∨ ~ i)  ∘ (unglue (j ∨ ~ j)))
           
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w : RElim (λ z → 𝔽in→ A z → 𝔽in z → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.[]* w = idfun _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  (w RElim.∷* a) b x = x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.comm* w b b' {xs} _ = w-comm b b' {xs} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.comm-inv* w b b' {xs} _ = w-comm-inv b b' {xs} 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.hexDiag* w x y z b =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!} ◁ {!!} ▷ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.hexU* w = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.hexL* w = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.trunc* w _ = isGroupoidΠ2 λ _ _ → isGroupoidA

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝔽in→Eval : ∀ {ℓ'} {B : Type ℓ'} → ∀ xs → 𝔽in→ {B = B} A xs → 𝔽in xs → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 𝔽in→Eval {A = A} {B = B} = RElim.f w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  open RElim
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  w : RElim (λ z → 𝔽in→ _ z → 𝔽in z → _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  []* w x ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  (w ∷* x) X b = Mb.rec {!!}  {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  comm* w = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  comm-inv* w = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  hexDiag* w = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  hexU* w = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  hexL* w = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  trunc* w = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module fm2Look {ℓ'} {B : Type ℓ'} (mapF : A → B) (isGroupoidA : isGroupoid A)  where



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  swap-lem : ∀ (xs : FMSet2 B) (a a' : A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (f : 𝔽in {A = B} xs → A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                Mb.rec a (Mb.rec a' f) ∘ (swap0and1Mf (h𝔽in xs)) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 Mb.rec a' (Mb.rec a f)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  swap-lem xs a a' f i nothing = a'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  swap-lem xs a a' f i (just nothing) = a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  swap-lem xs a a' f i (just (just x)) = f x

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  comm*-P : ∀ (a a' : A) (xs : FMSet2 A)  → (f : 𝔽in (fm2Map mapF xs) → A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         PathP (λ i → 𝔽in→ A (fm2Map mapF (comm a a' xs i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (Mb.rec a (Mb.rec a' f))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (Mb.rec a' (Mb.rec a f))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  comm*-P  a a' xs f = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    symP (ua-gluePath _ (swap-lem (fm2Map mapF xs) a' a f)) 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  comm*-P-invo-glueSq : (a a' : A) (xs : FMSet2 A) (b : 𝔽in (fm2Map mapF xs) → A) → Square
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ j → swap-lem (fm2Map mapF xs) a a' b j ∘ swap0and1Mf (h𝔽in (fm2Map mapF xs)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ j → swap-lem (fm2Map mapF xs) a' a b (~ j))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ i y → Mb.rec a (Mb.rec a' b) (involSwap0and1Mf (h𝔽in (fm2Map mapF xs)) y i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  comm*-P-invo-glueSq a a' xs b i j nothing = a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  comm*-P-invo-glueSq a a' xs b i j (just nothing) = a'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  comm*-P-invo-glueSq a a' xs b i j (just (just x)) = b x


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  comm*-P-invo : ∀ (a a' : A) (xs : FMSet2 A) (b : 𝔽in (fm2Map mapF xs) → A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        SquareP (λ i j → PCI.pS' {B = B} {A = A} (fm2Map mapF xs) (~ i) j)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (comm*-P a a' xs b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (symP (comm*-P a' a xs b))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (refl {x = Mb.rec a (Mb.rec a' b)})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (refl {x = Mb.rec a' (Mb.rec a b)})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  comm*-P-invo a a' xs b i j = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         glue 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (λ { (j = i0) → Mb.rec a (Mb.rec a' b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ; (j = i1) → Mb.rec a' (Mb.rec a b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            }) (glue
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ { (i = i0) → swap-lem (fm2Map mapF xs) _ _ b (~ j)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ; (i = i1) → swap-lem (fm2Map mapF xs) _ _ b j
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         }) (comm*-P-invo-glueSq a a' xs b (~ i) j))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RFM2look' : RElim {A = A} (𝔽in→ A ∘ fm2Map mapF)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.[]* RFM2look' ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  (RFM2look' RElim.∷* a) {xs} f =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    Mb.rec a (𝔽in→ev⁻ A isGroupoidA (fm2Map mapF xs) f)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.comm* RFM2look' a a' {xs} b i =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    glue (λ { (i = i0) → _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ; (i = i1) → Mb.rec a' (Mb.rec a ((𝔽in→ev⁻ A isGroupoidA (fm2Map mapF xs)) b)) })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (swap-lem (fm2Map mapF xs) a' a ((𝔽in→ev⁻ A isGroupoidA (fm2Map mapF xs)) b) (~ i))
       
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.comm-inv* (RFM2look') a a' {xs} b =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    comm*-P-invo a a' xs (𝔽in→ev⁻ A isGroupoidA (fm2Map mapF xs) b) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.hexDiag* RFM2look' _ _ _ b =  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    symP (ua-gluePath _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (funExt (Mb.elim _ refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.hexU* RFM2look' = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.hexL* RFM2look' = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElim.trunc* RFM2look' xs =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isOfHLevelRespectEquiv 3
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (𝔽in→ev≃ A (fm2Map mapF xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (isGroupoidΠ λ _ → isGroupoidA)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  fm2look : (xs : FMSet2 A) → (𝔽in→ A ∘ fm2Map mapF) xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  fm2look = RElim.f RFM2look'

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RFM2tab : ∀ {ℓ'} {B : Type ℓ'} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    RElim {A = B} (λ xs → (𝔽in xs → A) → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.[]* RFM2tab _ = []
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (RFM2tab RElim.∷* _) b f = f nothing ∷2 b (f ∘ just)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.comm* (RFM2tab {A = A} {B = B}) _ _ {xs} b i f = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  let z = f ∘' ua-gluePathExt (PCI.e {B = B} {A = A} xs) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  in comm (z nothing) (z (just nothing)) (b (z ∘ just ∘ just)) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.comm-inv* (RFM2tab {A = A}) _ _ {xs} b i j f =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  let z : Maybe (Maybe (𝔽in xs)) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      z = f ∘' λ x → glue
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (λ { (j = i0) → x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 ; (j = i1) → swap0and1Mf (h𝔽in xs) x })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (glue (λ { (i = i0) → swap0and1Mf (h𝔽in xs) x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           ; (i = i1) → _ })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (involSwap0and1Mf (RRec.f Rh𝔽in xs) x (~ j ∧ i)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  in comm-inv (z nothing) (z (just nothing)) (b (z ∘ just ∘ just)) i j
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.hexDiag* (RFM2tab {A = A} {B = B}) _ _ _ {xs} b i f =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  let z = f ∘' ua-gluePathExt (PCI'.e {B = B} {A = A} xs) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  in hexDiag (z nothing) (z (just nothing)) (z (just (just nothing)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (b (z ∘ just ∘ just ∘ just)) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.hexU* RFM2tab = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.hexL* RFM2tab = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.trunc* RFM2tab xs = isGroupoidΠ λ _ → trunc

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fm2tab : ∀ {ℓ'} {B : Type ℓ'} {A : Type ℓ}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  → (xs : FMSet2 B) → (𝔽in xs → A) → FMSet2 A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fm2tab = RElim.f (RFM2tab)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ (isGroupoidA : isGroupoid A)  where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  Rtab∘look≡id : RElimSet' {A = A} λ xs →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          fm2tab (fm2Map (λ _ → _) xs) ((𝔽in→ev⁻ A isGroupoidA (fm2Map (λ _ → _) xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (fm2Look.fm2look {B = Unit} (λ _ → _) isGroupoidA xs)) ≡ xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElimSet'.[]* Rtab∘look≡id = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  (Rtab∘look≡id RElimSet'.∷* x) = cong (x ∷2_) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElimSet'.comm* Rtab∘look≡id x y {xs} b i j =
    
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    hcomp
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (λ z → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (i = i0) → x ∷2 y ∷2 b (z ∧ j) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ;(i = i1) → y ∷2 x ∷2 b (z ∧ j)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ;(j = i0) → comm (compPathRefl {x = x} z i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (compPathRefl {x = y} z i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (fm2tab (fm2Map (λ _ → tt) xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (compPathRefl {x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              𝔽in→ev⁻ A isGroupoidA (fm2Map (λ _ → tt) xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                ((fm2Look.fm2look (λ _ → tt) isGroupoidA xs))} z i)) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ;(j = i1) → comm x y (b z) i })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (comm x y (b i0) i)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  RElimSet'.trunc* Rtab∘look≡id _ = trunc _ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- comm*-P : (X : hSet ℓ-zero) → (a a' : A) → (f : fst X → A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        PathP (λ i → ua (swap0and1M X) i → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (Mb.rec a (Mb.rec a' f))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (Mb.rec a' (Mb.rec a f))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- comm*-P X a a' f =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ua→ (Mb.elim _ refl (Mb.elim _ refl λ _ → refl) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- let z : PathP (λ i₁ → ua (swap0and1M X) i₁ → fst (Mb^ 2 X))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           (fst (swap0and1M X)) (idfun (fst (Mb^ 2 X)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     z = ua-ungluePathExt (swap0and1M X)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  in {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RFM2look : RElim {A = A} (λ z → 𝔽in z → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.[]* RFM2look ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim._∷*_ RFM2look x = Mb.rec x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (RFM2look RElim.∷* a) _ nothing = a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- (RFM2look RElim.∷* _) b (just k) = b k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.comm* RFM2look a a' {xs} b i k = comm*-P (h𝔽in xs) a a' b i k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.comm-inv* RFM2look = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.hexDiag* RFM2look = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.hexU* RFM2look = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.hexL* RFM2look = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RElim.trunc* RFM2look = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- FM2look : (xs : FMSet2 A) → 𝔽in xs → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- FM2look {A = A} = RElim.f RFM2look

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- FM2→Σ𝔽→ : FMSet2 A → Σ𝔽→ A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- FM2→Σ𝔽→ x = {!!}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- FMI : FMSet2 A → hSet ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- FMI =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Elim.f 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (⊥.⊥ , isProp→isSet isProp⊥)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ x {xs} b → Maybe (fst b) , isOfHLevelMaybe zero (snd b) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ x y b → TypeOfHLevel≡ 2 (ua (swap0and1M b)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ x y {xs} b →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (cong ua (equivEq (funExt ((Mb.elim _ refl (Mb.elim _ refl λ _ → refl) ))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∙ uaInvEquiv (swap0and1M b)) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ x y z b → TypeOfHLevel≡ 2 (ua (swap0and2M b)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ x y z {xs} b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        (isInjectiveTransport
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         (funExt (Mb.elim _  refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))))))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ x y z {xs} b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                        (isInjectiveTransport
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         (funExt (Mb.elim _  refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ _ → isGroupoidHSet)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- FMIfin : ∀ (xs : FMSet2 A) → isFinSet (fst (FMI xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- FMIfin xs = (len2 xs) , 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (ElimProp.f {B = λ xs → PT.∥ fst (FMI xs) ≃ F.Fin (len2 xs) ∥₁}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     PT.∣ idEquiv _ ∣₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ _ {_} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       PT.map
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        λ e → congMaybeEquiv e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∙ₑ isoToEquiv
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (iso Maybe→SumUnit
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    SumUnit→Maybe
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    SumUnit→Maybe→SumUnit
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    Maybe→SumUnit→Maybe)
          
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ xs → PT.squash₁) xs)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where open SumUnit

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ×Vec : (A : Type ℓ) → ℕ → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ×Vec A zero = Unit*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ×Vec A (suc n) = A × ×Vec A n

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- tabulate× : ∀ {n} → (fst (Mb^ n (⊥.⊥ , isProp→isSet isProp⊥)) → A) → ×Vec A n
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- tabulate× {n = zero} _ = tt*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- tabulate× {n = suc n} x = x nothing , tabulate× (x ∘ just)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- lookup× : ∀ {n} → ×Vec A n → (fst (Mb^ n (⊥.⊥ , isProp→isSet isProp⊥)) → A) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- lookup× {n = zero} x ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- lookup× {n = suc n} x = Mb.rec (fst x) (lookup× (snd x))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso-tabulate×-lookup× : ∀ {n} → Iso (×Vec A n) (fst (Mb^ n (⊥.⊥ , isProp→isSet isProp⊥)) → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun Iso-tabulate×-lookup× = lookup×
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv Iso-tabulate×-lookup× = tabulate×
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (Iso-tabulate×-lookup× {n = zero}) b i ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (Iso-tabulate×-lookup× {n = suc n}) b i nothing = b nothing
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (Iso-tabulate×-lookup× {n = suc n}) b i (just x) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.rightInv (Iso-tabulate×-lookup× {n = n}) (b ∘ just) i x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (Iso-tabulate×-lookup× {n = zero}) a = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (Iso-tabulate×-lookup× {n = suc n}) a =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ΣPathP (refl ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.leftInv (Iso-tabulate×-lookup× {n = n}) (snd a))



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and1⊎f : {A B C : Type ℓ} → A ⊎ (B ⊎ C) → B ⊎ (A ⊎ C)  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and1⊎f (inl x) = (inr (inl x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and1⊎f (inr (inl x)) = (inl x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and1⊎f (inr (inr x)) = (inr (inr x))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and1⊎fInvol : {A B C : Type ℓ} → ∀ x → swap0and1⊎f (swap0and1⊎f {A = A} {B} {C} x) ≡ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and1⊎fInvol (inl x) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and1⊎fInvol (inr (inl x)) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and1⊎fInvol (inr (inr x)) = refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and1⊎ :  {A B C : Type ℓ} → A ⊎ (B ⊎ C) ≃ B ⊎ (A ⊎ C)  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and1⊎ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isoToEquiv (iso swap0and1⊎f swap0and1⊎f swap0and1⊎fInvol swap0and1⊎fInvol)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and2⊎f : {A B C D : Type ℓ} → A ⊎ (B ⊎ (C ⊎ D)) → C ⊎ (B ⊎ (A ⊎ D))  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and2⊎f (inl x) = (inr (inr (inl x)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and2⊎f (inr (inl x)) = (inr (inl x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and2⊎f (inr (inr (inl x))) = (inl x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and2⊎f (inr (inr (inr x))) = (inr (inr (inr x)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and2⊎fInvol : {A B C D : Type ℓ} → ∀ x → swap0and2⊎f (swap0and2⊎f {A = A} {B} {C} {D} x) ≡ x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and2⊎fInvol (inl x) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and2⊎fInvol (inr (inl x)) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and2⊎fInvol (inr (inr (inl x))) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and2⊎fInvol (inr (inr (inr x))) = refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and2⊎ :  {A B C D : Type ℓ} → A ⊎ (B ⊎ (C ⊎ D)) ≃ C ⊎ (B ⊎ (A ⊎ D))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- swap0and2⊎ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isoToEquiv (iso swap0and2⊎f swap0and2⊎f swap0and2⊎fInvol swap0and2⊎fInvol)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module ∈FMSet2 {A : Type ℓ} (grpA : isGroupoid A) where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   toHSet₃ : ∥ Type ℓ ∥₃ → hSet ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fst (toHSet₃ ∣ x ∣₃) = ∥ x ∥₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   snd (toHSet₃ ∣ x ∣₃) = ST.squash₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   toHSet₃ (squash₃ x x₁ p q r s i i₁ i₂) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     isGroupoidHSet _ _ _ _ (λ j jj → toHSet₃ (r j jj)) (λ j jj → toHSet₃ (s j jj)) i i₁ i₂



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   toTy₃ : ∥ Type ℓ ∥₃ → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   toTy₃ x  = fst (toHSet₃ x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- toTy₃ (squash₃ x x₁ p q r s i i₁ i₂) = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- fromTy₃ : ∀ (A B : Type ℓ) (e : A ≃ B) → (isSetA : isSet A) → (isSetB : isSet B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                → (cong ST.∥_∥₂ (ua e))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                ≡ ua (setTruncIdempotent≃ isSetA ∙ₑ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                   e ∙ₑ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                   invEquiv (setTruncIdempotent≃ isSetB))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- fromTy₃ x y a xs = {!!} 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ua→' : ∀ {ℓ ℓ'} {A₀ A₁ : Type ℓ} {e : A₀ ≃ A₁} {B : Type ℓ'}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (f : A₁ → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → PathP (λ i → ua e i → B) (f ∘ fst e) f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ua→' {e = e} f i a = f ((ua-unglue e i a))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- h ((ua-unglue e i a) ) i

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fromTy₃≡ : ∀ {A B C : Type ℓ} (e : A ≃ B) → (isSetA : isSet A) → (isSetB : isSet B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → (f : A → C)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → (g : B → C)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → PathP (λ i → ua e i → C) f g 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  → PathP (λ i → toTy₃ ∣ ua e i ∣₃ → C)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      (f ∘ fst (setTruncIdempotent≃ isSetA))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      (g ∘ fst (setTruncIdempotent≃ isSetB))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fromTy₃≡ e isSetA isSetB f g p =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     congP {A = λ z → (b : ua e z) → _}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           {B = λ i _ → (a : ∥ ua e i ∥₂) → _} (λ i → _∘ fst (setTruncIdempotent≃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ((_▷_ {A = λ i → isSet (ua e i)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ i → coe0→i (λ i → isSet (ua e i) ) i isSetA) (isPropIsSet _ isSetB)) i))) p

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fromTy₃Sq : ∀ {C : Type ℓ} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (A : I → I → Type ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (isSetA : ∀ i j → isSet (A i j))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    {a₀₀ : A i0 i0 → C} {a₀₁ : A i0 i1 → C} (a₀₋ : PathP (λ j → A i0 j → C) a₀₀ a₀₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    {a₁₀ : A i1 i0 → C} {a₁₁ : A i1 i1 → C} (a₁₋ : PathP (λ j → A i1 j → C) a₁₀ a₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (a₋₀ : PathP (λ i → A i i0 → C) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1 → C) a₀₁ a₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    → (sq : SquareP (λ i j → A i j → C) a₀₋ a₁₋ a₋₀ a₋₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    → (SquareP (λ i j → ∥ A i j ∥₂ → C)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         (λ j → a₀₋ j ∘ fst (setTruncIdempotent≃ (isSetA i0 j)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         (λ j → a₁₋ j ∘ fst (setTruncIdempotent≃ (isSetA i1 j)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         (λ j → a₋₀ j ∘ fst (setTruncIdempotent≃ (isSetA j i0)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                         (λ j → a₋₁ j ∘ fst (setTruncIdempotent≃ (isSetA j i1))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   fromTy₃Sq A isSetA a₀₋ a₁₋ a₋₀ a₋₁ sq i j =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     sq i j ∘ fst (setTruncIdempotent≃ (isSetA i j))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈FM2'' : A → FMSet2 A → ∥ Type ℓ ∥₃ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈FM2'' a = Rec.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      squash₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      ∣ ⊥.⊥* ∣₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (λ x → GT.map λ b → (x ≡ a) ⊎ b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (λ x y → GT.elim (λ _ → isSet→isGroupoid (squash₃ _ _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        λ T → cong ∣_∣₃ (ua swap0and1⊎))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (λ x y → GT.elim (λ _ → isSet→isGroupoid (isProp→isSet (squash₃ _ _ _ _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --             λ T → cong (cong ∣_∣₃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --              ((cong ua (equivEq (funExt (⊎.elim (λ _ → refl) (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                λ _ → refl))))) ∙ uaInvEquiv _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (λ x y z → GT.elim (λ _ → isSet→isGroupoid (squash₃ _ _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                   λ T → cong ∣_∣₃ (ua swap0and2⊎))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      -- (λ x y z → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      --    GT.elim (λ _ → {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      --    λ T i j → ∣ ∙≡∙→square _ _ _ _ {!!} i j ∣₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      --    )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --             -- λ T → {!(isInjectiveTransport
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --             --     ((funExt (⊎.elim (λ _ → refl) (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --             --    (⊎.elim (λ _ → refl) λ _ → refl))))))!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      {!!}  --GT.elim (λ _ → isSet→isGroupoid (isProp→isSet (squash₃ _ _ _ _)))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈FM2'' : ∀ {ℓ'} (B : Type ℓ') (isGrpB : isGroupoid B) → A → FMSet2 A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                  → ∥ Σ (Type ℓ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                        (λ T → B → (A → B) → T → B ) ∥₃ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈FM2'' B isGrpB a = {!!}









-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   swap0and1₃ : {a x y : A} {C : Type ℓ} → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (x ≡ a) ⊎ ∥ (y ≡ a) ⊎ C ∥₂ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (y ≡ a) ⊎ ∥ (x ≡ a) ⊎ C ∥₂ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   swap0and1₃ (inl x) = inr  ∣ inl x ∣₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   swap0and1₃ (inr ∣ inl x ∣₂) = inl x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   swap0and1₃ (inr ∣ inr x ∣₂) = inr ∣ inr x ∣₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   swap0and1₃ (inr (squash₂ x x₁ p q i i₁)) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ⊎.isSet⊎ (grpA _ _) squash₂ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (cong (swap0and1₃ ∘ inr) p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (cong (swap0and1₃ ∘ inr) q) i i₁

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   swap0and1₃invo : {a x y : A} {C : Type ℓ} → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  ∀ b → swap0and1₃ {a = a} {x} {y} {C} (swap0and1₃ b) ≡ b 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   swap0and1₃invo = ⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (λ _ → refl)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   swap0and1Iso₃ : {a x y : A} {C : Type ℓ} → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  Iso ((x ≡ a) ⊎ ∥ (y ≡ a) ⊎ C ∥₂) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      ((y ≡ a) ⊎ ∥ (x ≡ a) ⊎ C ∥₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.fun swap0and1Iso₃ = swap0and1₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.inv swap0and1Iso₃ = swap0and1₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.rightInv swap0and1Iso₃ = swap0and1₃invo
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.leftInv swap0and1Iso₃ = swap0and1₃invo

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   swap0and1≃₃ : {a x y  : A} {C : Type ℓ} → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     ((x ≡ a) ⊎ ∥ (y ≡ a) ⊎ C ∥₂) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                     ≃ ((y ≡ a) ⊎ ∥ (x ≡ a) ⊎ C ∥₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   swap0and1≃₃ = isoToEquiv swap0and1Iso₃



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   swap0and2₃ : {a x y z : A} {C : Type ℓ} → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (x ≡ a) ⊎ ∥ (y ≡ a) ⊎ ∥ (z ≡ a) ⊎ C ∥₂ ∥₂ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (z ≡ a) ⊎ ∥ (y ≡ a) ⊎ ∥ (x ≡ a) ⊎ C ∥₂ ∥₂ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   swap0and2₃  =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ⊎.elim (inr ∘ ∣_∣₂ ∘ inr ∘ ∣_∣₂ ∘ inl )
 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (ST.rec (⊎.isSet⊎ (grpA _ _) squash₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (⊎.rec ( inr ∘ ∣_∣₂ ∘ inl  )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (ST.rec (⊎.isSet⊎ (grpA _ _) squash₂) (⊎.rec inl (inr ∘ ∣_∣₂ ∘ inr ∘ ∣_∣₂ ∘ inr )))))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   swap0and2Iso₃ : {a x y z : A} {C : Type ℓ} → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  Iso ((x ≡ a) ⊎ ∥ (y ≡ a) ⊎ ∥ (z ≡ a) ⊎ C ∥₂ ∥₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      ((z ≡ a) ⊎ ∥ (y ≡ a) ⊎ ∥ (x ≡ a) ⊎ C ∥₂ ∥₂) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.fun swap0and2Iso₃ = swap0and2₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.inv swap0and2Iso₃ = swap0and2₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.rightInv swap0and2Iso₃ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ((ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (⊎.elim (λ _ → refl) (λ _ → refl))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.leftInv swap0and2Iso₃ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ((ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (⊎.elim (λ _ → refl) (λ _ → refl))))))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   swap0and2≃₃ : {a x y z : A} {C : Type ℓ} → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      ((x ≡ a) ⊎ ∥ (y ≡ a) ⊎ ∥ (z ≡ a) ⊎ C ∥₂ ∥₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ≃  ((z ≡ a) ⊎ ∥ (y ≡ a) ⊎ ∥ (x ≡ a) ⊎ C ∥₂ ∥₂) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   swap0and2≃₃ = isoToEquiv swap0and2Iso₃

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- swap0and2≃DiagU : {a x y z : A} {C : Type ℓ} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                       Square 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                         (λ i → (y ≡ a) ⊎ toTy₃ ∣ ua (swap0and1≃₃ {a = a} {x} {z} {C}) i ∣₃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                         (λ i → ua (swap0and2≃₃ {a = a} {x} {y} {z} {C}) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                         (λ i → ua (swap0and1≃₃ {a = a} {y} {x} {∥ (z ≡ a) ⊎ C ∥₂})  i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                         (λ i → ua (swap0and1≃₃ {a = a} {y} {z} {∥ (x ≡ a) ⊎ C ∥₂}) i)
                        
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- -- swap0and2≃DiagU = ∙-∙≡→square
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- --   ( (isInjectiveTransport (funExt (
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- --     ⊎.elim
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- --       (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- --       {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- --       )) ∙ uaCompEquiv _ _) ∙ cong (ua swap0and1≃₃ ∙_)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- --     (uaCompEquiv _ _ ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- --       cong (ua swap0and2≃₃ ∙_) (uaInvEquiv _ )))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∈FM2'' : A → FMSet2 A → ∥ Type ℓ ∥₃ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∈FM2'' a = Rec.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        squash₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ∣ ⊥.⊥* ∣₃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ x xs → ∣ (x ≡ a) ⊎ toTy₃ xs ∣₃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ x y b → cong ∣_∣₃ (ua swap0and1≃₃))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ x y b → cong (cong ∣_∣₃) (cong ua
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (equivEq refl) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            uaInvEquiv
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (swap0and1≃₃ {x = y} {y = x} )))         
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ x y z b → cong ∣_∣₃ (ua swap0and2≃₃))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ x y z b → congSq ∣_∣₃ (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (isInjectiveTransport (funExt (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 ((ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (⊎.elim (λ _ → refl) (λ _ → refl)))))))) )))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ x y z b → congSq ∣_∣₃ (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (isInjectiveTransport (funExt (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 ((ST.elim (λ _ → isProp→isSet (⊎.isSet⊎ (grpA _ _) squash₂ _ _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (⊎.elim (λ _ → refl) (λ _ → refl)))))))) )))

       



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∈FM2'-isSet : (x : A) → (xs : FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     fst (GT.rec (isSet→isGroupoid isSetHProp) (λ x → isOfHLevel 2 x , isPropIsOfHLevel 2)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                (∈FM2'' x xs))  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∈FM2'-isSet x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ElimProp.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (isProp→isSet isProp⊥*)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ x₁ {xs} x₂ → ⊎.isSet⊎ (grpA _ _) (snd (toHSet₃ (∈FM2'' x xs))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       λ xs → snd (GT.rec (isSet→isGroupoid isSetHProp) (λ x → isOfHLevel 2 x , isPropIsOfHLevel 2)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                (∈FM2'' x xs))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   _∈FM2_ : A → FMSet2 A → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   _∈FM2_ a = toTy₃ ∘ ∈FM2'' a

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   l∈ : lockUnit {ℓ-zero} → A → FMSet2 A → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   l∈ unlock a x = a ∈FM2 x

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isSetl∈ : ∀ l a xs →  isSet (l∈ l a xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isSetl∈ unlock a xs = snd (toHSet₃ (∈FM2'' a xs))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∈[] : (a : A) → a ∈FM2 [] → ⊥*  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∈[] a = ST.rec (isProp→isSet isProp⊥*) (idfun _)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∈compute : ∀ x (a : A) (xs : FMSet2 A) → a ∈FM2 (x ∷2 xs) ≃ (x ≡ a) ⊎ (a ∈FM2 xs)  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∈compute x a xs = setTruncIdempotent≃ (⊎.isSet⊎ (grpA _ _) (snd (toHSet₃ (∈FM2'' a xs))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   l∈compute : ∀ l x (a : A) (xs : FMSet2 A) → l∈ l a (x ∷2 xs) ≃ (x ≡ a) ⊎ (l∈ l a xs)  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   l∈compute unlock x a xs =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     setTruncIdempotent≃ (⊎.isSet⊎ (grpA _ _) (snd (toHSet₃ (∈FM2'' a xs))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   l∈compute' : ∀ l x (a : A) (xs : FMSet2 A) → (l∈ l a (x ∷2 xs)) ≃ (∥ (x ≡ a) ⊎ (l∈ l a xs) ∥₂)  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   l∈compute' unlock x a xs = idEquiv _


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈compute' : ∀ x (a : A) (xs : FMSet2 A) → a ∈FM2 (x ∷2 xs) → (x ≡ a) ⊎ (a ∈FM2 xs)  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈compute' x a xs ∣ x₁ ∣₂ = x₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈compute' x a xs (squash₂ x₁ x₂ p q i i₁) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   ⊎.isSet⊎ (grpA _ _) (snd (toHSet₃ (∈FM2'' a xs)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    _ (cong (∈compute' x a xs) p) (cong (∈compute' x a xs) q) i i₁ 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- l∈computeSqTy : (lockUnit {ℓ-zero}) →  (x y a : A) (xs : FMSet2 A) → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- l∈computeSqTy l x₁ y a xs = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- l∈computeSq : ∀ l x y (a : A) (xs : FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --              Path (Path (Type ℓ) (l∈ l a (x ∷2 y ∷2 xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                                  (l∈ l a (y ∷2 x ∷2 xs)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                (λ i → l∈ l a (comm x y xs i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                (ua ( {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                  ∙ₑ (swap0and1≃₃ {a = a} {x = x} {y = y} {C = l∈ l a xs}) ∙ₑ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                  {!!})) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- l∈computeSq x y a xs = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   l∈computeSqSide : ∀ l x y (a : A) (xs : FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        l∈ l a (x ∷2 y ∷2 xs) ≃ ((x ≡ a) ⊎ ∥ (y ≡ a) ⊎ l∈ l a xs ∥₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   l∈computeSqSide l x y a xs =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     l∈compute l x a (y ∷2 xs) ∙ₑ ⊎.⊎-equiv (idEquiv _) (l∈compute' l y a xs)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   l∈computeSqSideP : ∀ l x y (a : A) (xs : FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (b : (l : lockUnit) → l∈ l a xs → FMSet2 A) → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        PathP (λ k → ua (l∈computeSqSide l x y a xs) (~ k) → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (λ q →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   x ∷2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ⊎.rec (λ _ → xs) (λ q₁ → y ∷2 b l q₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (ST.rec (⊎.isSet⊎ (grpA y a) (isSetl∈ l a xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (idfun (Path A y a ⊎ l∈ l a xs)) q))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ q →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                x ∷2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                ⊎.rec (λ _ → xs) (λ q₁ → y ∷2 b l q₁) (fst (l∈compute l y a xs) q))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (fst (l∈compute l x a (y ∷2 xs)) x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   l∈computeSqSideP l x y a xs b =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     symP (ua→ (zz l))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         zz : ∀ l → (a₁ : l∈ l a (x ∷2 y ∷2 xs)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (λ q →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      x ∷2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      ⊎.rec (λ _ → xs) (λ q₁ → y ∷2 b l q₁) (fst (l∈compute l y a xs) q))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (fst (l∈compute l x a (y ∷2 xs)) a₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (λ q →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      x ∷2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      ⊎.rec (λ _ → xs) (λ q₁ → y ∷2 b l q₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                      (ST.rec (⊎.isSet⊎ (grpA y a) (isSetl∈ l a xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       (idfun (Path A y a ⊎ l∈ l a xs)) q))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   (⊎.⊎-equiv (idEquiv (x ≡ a)) (l∈compute' l y a xs) .fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                    (l∈compute l x a (y ∷2 xs) .fst a₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         zz unlock = ST.elim (λ _ → trunc _ _) (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (ST.elim (λ _ → trunc _ _) (⊎.elim (λ _ → refl) λ _ → refl)))
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   l∈computeSq : ∀ l x y (a : A) (xs : FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               Square
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (λ i → l∈ l a (comm x y xs i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (ua (swap0and1≃₃ {a = a} {x = x} {y = y} {C = l∈ l a xs}))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (ua (l∈computeSqSide l x y a xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  (ua (l∈computeSqSide l y x a xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   l∈computeSq unlock x y a xs = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈computeSq' : ∀ x y (a : A) (C : Type ℓ) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                (cong ST.∥_∥₂ (ua (swap0and1≃₃ {a = a} {x = x} {y = y} {C = C})))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                ≡ ua ( (setTruncIdempotent≃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                  (⊎.isSet⊎ (grpA _ _) squash₂)) ∙ₑ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                   (swap0and1≃₃ {a = a} {x = x} {y = y} {C = C}) ∙ₑ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                   invEquiv (setTruncIdempotent≃
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                  (⊎.isSet⊎ (grpA _ _) squash₂)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈computeSq' x y a xs = {!!} 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   involSqLem' :
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (x y : A) {xs : FMSet2 A} → ∀ l → ∀ a →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (b : (l : lockUnit) → l∈ l a xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      PathP (λ i → ua (swap0and1≃₃ {a = a} {x = x} {y = y} {C = l∈ l a xs }) i → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ q →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             x ∷2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → xs) (λ q₁ → y ∷2 b l q₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ((ST.rec (⊎.isSet⊎ (grpA y a) (isSetl∈ l a xs)) (idfun _) q))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (⊎.rec (λ _ → x ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ q →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             y ∷2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → xs) (λ q₁ → x ∷2 b l q₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (ST.rec (⊎.isSet⊎ (grpA x a) (isSetl∈ l a xs)) (idfun _) q)))
         
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   involSqLem' x y l a b = ua→ (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (ST.elim (λ _ → trunc _ _) (⊎.elim (λ _ → refl) λ _ → comm _ _ _)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   involSqLem :
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (x y : A) {xs : FMSet2 A} → ∀ l → ∀ a →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (b : (l : lockUnit) → l∈ l a xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      PathP (λ i → ua (swap0and1≃₃ {a = a} {x = x} {y = y} {C = l∈ l a xs }) i → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ q →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             x ∷2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → xs) (λ q₁ → y ∷2 b l q₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ((ST.rec (⊎.isSet⊎ (grpA y a) (isSetl∈ l a xs)) (idfun _) q))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (⊎.rec (λ _ → x ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ q →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             y ∷2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → xs) (λ q₁ → x ∷2 b l q₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (ST.rec (⊎.isSet⊎ (grpA x a) (isSetl∈ l a xs)) (idfun _) q)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      → PathP (λ z → l∈ l a (comm x y xs z) → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ q →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             x ∷2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → xs) (λ q₁ → y ∷2 b l q₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (fst (l∈compute l y a xs) q))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (fst (l∈compute l x a (y ∷2 xs)) x₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ⊎.rec (λ _ → x ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ q →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             y ∷2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → xs) (λ q₁ → x ∷2 b l q₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (fst (l∈compute l x a xs) q))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (fst (l∈compute l y a (x ∷2 xs)) x₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   involSqLem x y {xs} l a b P i =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     comp (λ k → l∈computeSq l x y a xs (~ k) i → FMSet2 A )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ k → λ {
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (i = i0) → l∈computeSqSideP l x y a xs b k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ;(i = i1) → l∈computeSqSideP l y x a xs b k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            })
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (P i)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   removeFM2 : ∀ a (xs : FMSet2 A) → ∀ l → l∈ l a xs → FMSet2 A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   removeFM2 a = Elim.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ {unlock → ⊥.rec* ∘ ∈[] a})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       -- (λ x {xs} f → ⊎.rec (λ _ → xs) ((x ∷2_) ∘ f) ∘ fst (∈compute x a xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ x y {xs} b → funExt (wP x y {xs} b))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       -- fromTy₃≡ (swap0and1≃₃ {a = a} {x = x} {y = y} {C = a ∈FM2 xs})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       --   _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       --   _ _ _ ((ww x y {xs} b))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        -- )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       -- (λ x y {xs} b →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       --   {! fromTy₃Sq ? ? ? ? ? ? ?!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       --   )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- (λ x y b →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --   congP
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --    (λ j → {!congP (λ i → _∘ fst (setTruncIdempotent≃ ?))!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --      {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      λ _ → isGroupoidΠ2 λ _ _ → trunc

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      w : (x : A) {xs : FMSet2 A} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ((l : lockUnit) → l∈ l a xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (l : lockUnit) → l∈ l a (x ∷2 xs) → FMSet2 A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      w x {xs} x₁ l x₂ = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ⊎.rec (λ _ → xs) (λ q → x ∷2 x₁ l q) (fst (l∈compute l x a xs) x₂)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      wP : (x y : A) {xs : FMSet2 A} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (b : (l : lockUnit) → l∈ l a xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (x₁ : lockUnit) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                PathP (λ z → l∈ x₁ a (comm x y xs z) → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (w x (w y b) x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (w y (w x b) x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      wP x y {xs} b x₁ = involSqLem x y x₁ a b (involSqLem' x y {xs} x₁ a b)
      

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   ww : ∀ x y {xs} (b : a ∈FM2 xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --        PathP (λ i → (xy : ua (swap0and1≃₃ {a = a} {x = x} {y = y} {C = a ∈FM2 xs}) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --             → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --           (⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --             (λ x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --                x ∷2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --                ⊎.rec (λ _ → xs) (λ x₃ → y ∷2 b x₃) (fst (∈compute y a xs) x₂)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --           (⊎.rec (λ _ → x ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --           (λ x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --              y ∷2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --              ⊎.rec (λ _ → xs) (λ x₃ → x ∷2 b x₃) (fst (∈compute x a xs) x₂)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   ww x y {xs} b = ua→ (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --    (ST.elim (λ _ → trunc _ _) (⊎.elim (λ _ → refl) λ _ → comm _ _ _)))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- ww' : ∀ (x y : A) → ∀ {xs} (b : a ∈FM2 xs → FMSet2 A) → _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --    SquareP (λ i j →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --         {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --       {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --       {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --       refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --       refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- ww' x y {xs} b =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --    fromTy₃Sq {C = FMSet2 A}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --      (λ i j → (cong ua
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --      (equivEq refl) ∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --       uaInvEquiv
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --        (swap0and1≃₃ {x = y} {y = x} )) i j)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --        (λ i j → {!!}) (ww x y b) (symP (ww y x b)) refl refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --         {!!}
     
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- ww'F : ∀ x y {xs} --(b : a ∈FM2 xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --          (f : (x ≡ a) ⊎ ∥ (y ≡ a) ⊎ (a ∈FM2 xs) ∥₂ → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --          (g : (y ≡ a) ⊎ ∥ (x ≡ a) ⊎ (a ∈FM2 xs) ∥₂ → FMSet2 A) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --          (isSetP : ∀ i → isSet (ua (swap0and1≃₃ {a = a} {x = y} {y = x} {C = a ∈FM2 xs}) i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --          (isSetP' : ∀ i → isSet (ua (swap0and1≃₃ {a = a} {x = x} {y = y} {C = a ∈FM2 xs}) i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --          → PathP (λ j →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                 PathP (λ i →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                 (cong {x = (swap0and1≃₃ {a = a} {x = y} {y = x} {C = a ∈FM2 xs})}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                                     {y = invEquiv
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                                       ((swap0and1≃₃ {a = a} {x = x} {y = y} {C = a ∈FM2 xs}))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                                     ua (equivEq refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                   ∙ uaInvEquiv (swap0and1≃₃ {a = a} {x = x} {y = y} {C = a ∈FM2 xs}))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                     j i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                  → FMSet2 A )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                  g f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --              → PathP (λ i → ∥ (cong {x = (swap0and1≃₃ {a = a} {x = y} {y = x} {C = a ∈FM2 xs})}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                                     {y = invEquiv
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                                       ((swap0and1≃₃ {a = a} {x = x} {y = y} {C = a ∈FM2 xs}))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                                     ua (equivEq refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                   ∙ uaInvEquiv (swap0and1≃₃ {a = a} {x = x} {y = y} {C = a ∈FM2 xs}))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                     j i ∥₂ → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                (g ∘ fst (setTruncIdempotent≃ (isPropIsSet (isSetP i0) (isSetP' i1) j)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                (f ∘ fst (setTruncIdempotent≃ (isPropIsSet (isSetP i1) (isSetP' i0) j))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --             (congP {A = λ z →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                 (b : ua (swap0and1≃₃ {a = a} {x = y} {y = x} {C = a ∈FM2 xs}) z) → FMSet2 A}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                    {B = λ i _ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                     (a : ∥ ua (swap0and1≃₃ {a = a} {x = y} {y = x} {C = a ∈FM2 xs}) i ∥₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                       → FMSet2 A}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                 (λ i → _∘ fst (setTruncIdempotent≃ (isSetP i))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --             (congP {A = λ z →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                 (b : ua (swap0and1≃₃ {a = a} {x = x} {y = y} {C = a ∈FM2 xs}) (~ z))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                  → FMSet2 A}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                    {B = λ i _ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                     (a : ∥ ua (swap0and1≃₃ {a = a} {x = x} {y = y} {C = a ∈FM2 xs}) (~ i) ∥₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                       → FMSet2 A}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --                 (λ i → _∘ fst (setTruncIdempotent≃ (isSetP' (~ i)))))
                 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- ww'F x y f g isSetP isSetP' j i = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- ww' :  ∀ x y {xs} (b : a ∈FM2 xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --        SquareP (λ i j → a ∈FM2 comm-inv x y xs i j → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --               ?
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --               ?
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --               refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --               refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- ww' = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   module SetRec∈ {ℓ'} {B : Type ℓ'} (isSetB : isSet B) (a : A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (b∷Here : (x : A) → (FMSet2 A) → (x ≡ a) → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (_b∷_ : A → B → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (b∷comm : ∀ x y b → (x b∷ (y b∷ b)) ≡ (y b∷ (x b∷ b))) 
              
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (bComm : ∀ x y xs → (p : x ≡ a) → b∷Here x (y ∷2 xs) p ≡ (y b∷ b∷Here x xs p))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     zz : ∀ x y xs b →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           PathP (λ i → (xy : ua (swap0and1≃₃ {a = a} {x = x} {y = y} {C = a ∈FM2 xs}) i)  → B)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (⊎.rec (b∷Here x (y ∷2 xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             x b∷
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ⊎.rec (b∷Here y xs) (λ x₂ → y b∷ b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (fst (∈compute y a xs) x₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (⊎.rec (b∷Here y (x ∷2 xs)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             y b∷
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ⊎.rec (b∷Here x xs) (λ x₂ → x b∷ b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (fst (∈compute x a xs) x₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     zz x y xs b = ua→
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (⊎.elim (bComm x y xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (ST.elim (λ _ → isProp→isSet (isSetB _ _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (⊎.elim (sym ∘ bComm y x xs) λ _ → b∷comm x y b)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ua→ (⊎.elim {!!} {!!})

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     f : ∀ xs → a ∈FM2 xs → B
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     f = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- f [] x = ⊥.rec* (∈[] a x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- f (x ∷2 xs) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --   ⊎.rec (b∷Here x xs) ((x b∷_) ∘ f xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --   ∘ fst (∈compute x a xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- f (comm x y xs i) v = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- f (comm-inv x₁ y xs i i₁) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- f (hexDiag x₁ y z xs i) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- f (hexU x₁ y z xs i i₁) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- f (hexL x₁ y z xs i i₁) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- f (trunc xs xs₁ x₁ y x₂ y₁ i i₁ x₃) x = {!!}




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   commSqCompute∈ : (a : A) → (x y : A) (xs : FMSet2 A) →

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (xFM yFM : FMSet2 A) → (fFM : a ∈FM2 xs → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       PathP (λ i → a ∈FM2 comm x y xs i → FMSet2 A) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ α → (⊎.rec (λ _ → xFM) (λ β → ⊎.rec (λ _ → yFM) fFM ((fst (∈compute y a xs)) β))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (fst (∈compute x a (y ∷2 xs)) α)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ α → (⊎.rec (λ _ → yFM) (λ β → ⊎.rec (λ _ → xFM) fFM ((fst (∈compute x a xs)) β))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (fst (∈compute y a (x ∷2 xs)) α)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   commSqCompute∈  a x y xs xFM yFM fFM i =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!a ∈FM2 comm x y xs i!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   ss : PathP (λ i → ua (swap0and1⊎ {A = x ≡ a} {B = y ≡ a} {C = a ∈FM2 xs}) i → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --              b0
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --              b1
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   ss = ua→ {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∈[] : (a : A) → a ∈FM2 [] → ⊥*  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∈[] a = ST.rec (isProp→isSet isProp⊥*) (idfun _)
  
  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∈head : ∀ (x) (xs : FMSet2 A) → x ∈FM2 (x ∷2 xs)   
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ∈head x xs = invEq (∈compute x x (xs)) (inl refl)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- bringHead : ∀ a (xs : FMSet2 A) → a ∈FM2 xs → Σ (FMSet2 A) λ xs' → xs ≡ a ∷2 xs' 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- bringHead a = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   removeFM2 : ∀ a (xs : FMSet2 A) → a ∈FM2 xs → FMSet2 A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   removeFM2 a = Elim.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (⊥.rec* ∘ ∈[] a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ x {xs} f → ⊎.rec (λ _ → xs) ((x ∷2_) ∘ f) ∘ fst (∈compute x a xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ww
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!ww'!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      λ _ → isGroupoidΠ λ _ → trunc
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ww : (x y : A) {xs : FMSet2 A} (b : a ∈FM2 xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          PathP (λ i → (cong ST.∥_∥₂ (ua (swap0and1≃₃ {a = a} {x} {y} {C = a ∈FM2 xs}) )) i → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                x ∷2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                ⊎.rec (λ _ → xs) (λ x₃ → y ∷2 b x₃) (fst (∈compute y a xs) x₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (fst (∈compute x a (y ∷2 xs)) x₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → x ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                y ∷2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                ⊎.rec (λ _ → xs) (λ x₃ → x ∷2 b x₃) (fst (∈compute x a xs) x₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (fst (∈compute y a (x ∷2 xs)) x₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ww x y b = toPathP (funExt (ST.elim {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (⊎.elim (λ _ → fromPathP refl) (ST.elim {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           (⊎.elim (λ _ → fromPathP refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            λ _ → cong₂ _∷2_ (transportRefl _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (cong₂ _∷2_ (transportRefl _) (transportRefl _ ∙ cong b (transportRefl _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  ∙ comm _ _ _)))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ww' : (x y z : A) {xs : FMSet2 A} (b : a ∈FM2 xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          PathP (λ i → a ∈FM2 hexDiag x y z xs i → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → y ∷2 z ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                x ∷2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                ⊎.rec (λ _ → z ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (λ x₃ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   y ∷2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ⊎.rec (λ _ → xs) (λ x₄ → z ∷2 b x₄) (fst (∈compute z a xs) x₃))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (fst (∈compute y a (z ∷2 xs)) x₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (fst (∈compute x a (y ∷2 z ∷2 xs)) x₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ⊎.rec (λ _ → y ∷2 x ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (λ x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                z ∷2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                ⊎.rec (λ _ → x ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (λ x₃ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   y ∷2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                   ⊎.rec (λ _ → xs) (λ x₄ → x ∷2 b x₄) (fst (∈compute x a xs) x₃))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (fst (∈compute y a (x ∷2 xs)) x₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (fst (∈compute z a (y ∷2 x ∷2 xs)) x₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ww' x y z b = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   removeLaw : ∀ a (xs : FMSet2 A) → (u : a ∈FM2 xs) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                a ∷2 removeFM2 a xs u ≡ xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   removeLaw a =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ElimSet.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ((⊥.rec* ∘ ∈[] a))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ x {xs} x₁ → {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      λ _ → isSetΠ λ _ → trunc _ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   remove≡ : ∀ a (xs : FMSet2 A) → (u v : a ∈FM2 xs) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                removeFM2 a xs u ≡ removeFM2 a xs v
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   remove≡ a =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ElimSet.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (⊥.rec* ∘ ∈[] a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ x {xs} kk u v →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          zz x {xs} kk (fst (∈compute {x = x} a xs) u)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       (fst (∈compute {x = x} a xs) v))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       λ _ → isSetΠ2 λ _ _ → trunc _ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      zz : (x : A) {xs : FMSet2 A} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ((u v : a ∈FM2 xs) → removeFM2 a xs u ≡ removeFM2 a xs v) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (u v : (x ≡ a) ⊎ (a ∈FM2 xs)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ⊎.rec (λ _ → xs) ((x ∷2_) ∘ removeFM2 a xs) u ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ⊎.rec (λ _ → xs) ((x ∷2_) ∘ removeFM2 a xs) v
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      zz x {xs} kk (inl x₁) (inl x₂) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      zz x {xs} kk (inl x₁) (inr x₂) = sym (removeLaw a xs x₂)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ∙ (λ i → (x₁ (~ i)) ∷2 (removeFM2 a xs x₂)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      zz x {xs} kk (inr x₁) (inl x₂) = (λ i → (x₂ i) ∷2 (removeFM2 a xs x₁)) ∙ removeLaw a xs x₁ 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      zz x {xs} kk (inr x₁) (inr x₂) = cong (x ∷2_) (kk x₁ x₂)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   inj∷2' : (xs ys : FMSet2 A) → (a : A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            → (p : a ∷2 xs ≡ a ∷2 ys) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             → xs ≡ ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   inj∷2' xs ys a p =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ≡⟨ qq ⟩ removeFM2 a (a ∷2 ys) a∈'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ≡⟨ remove≡ a (a ∷2 ys) a∈' (∈head a ys) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ys ∎

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      a∈' = (subst (_∈FM2_ a) p (∈head a xs))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      qq : xs ≡ removeFM2 a (a ∷2 ys) a∈'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      qq i = removeFM2 a (p i) (coe0→i (λ i → a ∈FM2 (p i)) i (∈head a xs))

    
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- removeFM2 a (p i) {!!} 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   zz : (x y : A) {xs : FMSet2 A} (b : a ∈FM2 xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --          PathP (λ i → a ∈FM2 comm x y xs i → FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --          (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --             ⊎.rec (λ _ → y ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --             (λ x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --                x ∷2 ⊎.rec (λ _ → xs) (λ x₃ → y ∷2 b x₃) (fst (∈compute a xs) x₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --             (fst (∈compute a (y ∷2 xs)) x₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --          (λ x₁ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --             ⊎.rec (λ _ → x ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --             (λ x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --                y ∷2 ⊎.rec (λ _ → xs) (λ x₃ → x ∷2 b x₃) (fst (∈compute a xs) x₂))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --             (fst (∈compute a (x ∷2 xs)) x₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --   zz = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈head : ∀ (x) (xs : FMSet2 A) → x ∈FM2 (x ∷2 xs)   
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈head x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   ElimSet.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    ∣ inl refl ∣₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ y {xs} → {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    {!!} 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- _∈FM2'_ : A → FMSet2 A → hSet ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- _∈FM2'_ a = Rec.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      isGroupoidHSet
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (⊥.⊥* , isProp→isSet isProp⊥*)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (λ x b → ((x ≡ a) ⊎ fst b) , ⊎.isSet⊎ (grpA _ _) (snd b))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (λ x y b → TypeOfHLevel≡ 2 (ua (swap0and1⊎ {A = x ≡ a} {B = y ≡ a} {C = fst (b)})))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (λ x y b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                  (cong ua (equivEq (funExt (⊎.elim (λ _ → refl) (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                λ _ → refl))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --               ∙ uaInvEquiv (swap0and1⊎ {A = y ≡ a} {B = x ≡ a} {C = fst (b)})))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (λ x y z b → TypeOfHLevel≡ 2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --        (ua (swap0and2⊎ {A = x ≡ a} {B = y ≡ a} {C = z ≡ a} {D = fst (b)})))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (λ x y z b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            (∙≡∙→square _ _ _ _ (isInjectiveTransport
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                 ((funExt (⊎.elim (λ _ → refl) (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                (⊎.elim (λ _ → refl) λ _ → refl))))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --      (λ x y z b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            (∙≡∙→square _ _ _ _ (isInjectiveTransport
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                 ((funExt (⊎.elim (λ _ → refl) (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                (⊎.elim (λ _ → refl) λ _ → refl))))))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- _∈FM2_ : A → FMSet2 A → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- a ∈FM2 xs = fst (a ∈FM2' xs) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈head : ∀ (x) (xs : FMSet2 A) → x ∈FM2 (x ∷2 xs)   
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈head x xs = inl refl

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈computeTest : ∀ {x} {xs : FMSet2 A} (a : A) → a ∈FM2 (x ∷2 xs) ≃ (x ≡ a) ⊎ (a ∈FM2 xs)  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈computeTest a = idEquiv _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈comm : ∀ {ℓ'} {B : Type ℓ'} → ∀ x → (x₁ y : A) (xs : FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           {b0 : (x₁ ≡ x) ⊎ ((y ≡ x) ⊎ (x ∈FM2 xs)) → B}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         → {b1 : (y ≡ x) ⊎ ((x₁ ≡ x) ⊎ (x ∈FM2 xs)) → B}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           → {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           → {!!} --PathP (λ i → x ∈FM2 comm x₁ y xs i → B) b0 b1
            
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- ∈comm {B = B} a x y xs p =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   ua→ {e = (swap0and1⊎ {A = x ≡ a} {B = y ≡ a} {C = a ∈FM2 xs })}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       {B = λ _ → B} {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- bringHead : ∀ a (xs : FMSet2 A) → a ∈FM2 xs → Σ (FMSet2 A) λ xs' → xs ≡ a ∷2 xs' 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- bringHead a = w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     w : (xs : FMSet2 A) → a ∈FM2 xs → Σ (FMSet2 A) λ xs' → xs ≡ a ∷2 xs' 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     w (_ ∷2 xs') (inl p) = xs' , λ i → p i ∷2 xs'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     w (x' ∷2 xs) (inr x) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       let (xs' , p) = w xs x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       in (x' ∷2 xs') , (cong (x' ∷2_) p ∙ comm _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     w (comm x₁ y xs i) x =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     w (comm-inv x₁ y xs i i₁) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     w (hexDiag x₁ y z xs i) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     w (hexU x₁ y z xs i i₁) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     w (hexL x₁ y z xs i i₁) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --     w (trunc xs xs₁ x₁ y x₂ y₁ i i₁ x₃) x = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- removeFM2 : ∀ (x) (xs : FMSet2 A) → x ∈FM2 xs → FMSet2 A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- removeFM2 x = Elim.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   ⊥.rec*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   w
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   w'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   λ _ → isGroupoidΠ λ _ → trunc
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    w : (x₁ : A) {xs : FMSet2 A} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          (x ∈FM2 xs → FMSet2 A) → x ∈FM2 (x₁ ∷2 xs) → FMSet2 A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    w x {xs} x₁ (inl x₂) = xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    w x x₁ (inr x₂) = x₁ x₂

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    w' : (x₁ y : A) {xs : FMSet2 A} (b : x ∈FM2 xs → FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           PathP (λ i → x ∈FM2 comm x₁ y xs i → FMSet2 A) (w x₁ (w y b))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           (w y (w x₁ b))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    w' x₁ y {xs} b = ua→ ?


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --   w : (xs : FMSet2 A) → x ∈FM2 xs → FMSet2 A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --   w (x₁ ∷2 xs) (inl x) = xs
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --   w (x₁ ∷2 xs) (inr x) = w xs x
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --   w (comm x₁ y xs i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --   w (comm-inv x₁ y xs i i₁) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --   w (hexDiag x₁ y z xs i) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --   w (hexU x₁ y z xs i i₁) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --   w (hexL x₁ y z xs i i₁) x = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --   w (trunc xs xs₁ x₁ y x₂ y₁ i i₁ x₃) x = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- inj∷2' : ∀ n → (xs : FMSet2 A) → len2 xs ≡ n → (ys : FMSet2 A) → (x : A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          → (p : x ∷2 xs ≡ x ∷2 ys) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           → xs ≡ ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- inj∷2' xs ys x p = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- subst (λ z → x ∈FM2 z) (∈head x xs) p 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- let (xs' , px) = bringHead x (x ∷2 ys) (subst (x ∈FM2_) p (∈head x xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --     (ys' , py) = bringHead x (x ∷2 xs) (subst (x ∈FM2_) (sym p) (∈head x ys))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --     cLL : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --     cLL = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- in {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- Elim.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --  ⊥.rec*
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --  (λ x x₁ → {!⊎.rec ? ?!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --  (λ x y b i x₁ → {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --  (λ x y b i j x₁ → {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --  (λ x y z b i x₁ → {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --  (λ x y z b i j x₁ → {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --  (λ x y z b i j x₁ → {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      --  λ _ → isGroupoidΠ λ _ → (isOfHLevelΣ 3 trunc λ _ →  isSet→isGroupoid (trunc _ _))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- _∈FM2_ : FMSet2 A → A → hSet ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- _∈FM2_ = Elim.f 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ _ → (⊥.⊥* , isProp→isSet isProp⊥*))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ x {xs} b a → ((x ≡ a) ⊎ fst (b a)) , ⊎.isSet⊎ (grpA _ _) (snd (b a)) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ x y b → funExt λ a → TypeOfHLevel≡ 2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                         {X = _ , ⊎.isSet⊎ (grpA _ _) (⊎.isSet⊎ (grpA _ _) (snd (b a)))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                         {Y = _ , ⊎.isSet⊎ (grpA _ _) (⊎.isSet⊎ (grpA _ _) (snd (b a)))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                 (ua (swap0and1⊎ {A = x ≡ a} {B = y ≡ a} {C = fst (b a)})))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ x y {xs} b i j a →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --       ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          {p = TypeOfHLevel≡  2 {X = _ , ⊎.isSet⊎ (grpA _ _) (⊎.isSet⊎ (grpA _ _) (snd (b a)))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                                {Y = _ , ⊎.isSet⊎ (grpA _ _) (⊎.isSet⊎ (grpA _ _) (snd (b a)))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --              (ua (swap0and1⊎ {A = x ≡ a} {B = y ≡ a} {C = fst (b a)}))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            {q = refl}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            {r = sym (TypeOfHLevel≡ 2 (ua (swap0and1⊎)))} {s = refl} 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --            (cong ua (equivEq (funExt (⊎.elim (λ _ → refl) (⊎.elim (λ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                λ _ → refl))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --           ∙ uaInvEquiv (swap0and1⊎ {A = y ≡ a} {B = x ≡ a} {C = fst (b a)}))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          i j)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --    ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --      (cong ua (equivEq (funExt ((Mb.elim _ refl (Mb.elim _ refl λ _ → refl) ))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --        ∙ uaInvEquiv (swap0and1M b)) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    {!!} -- (λ x y z b → TypeOfHLevel≡ 2 (ua (swap0and2M b)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    {!!} -- (λ x y z {xs} b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --                    (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --                     (isInjectiveTransport
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --                      (funExt (Mb.elim _  refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))))))


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    {!!} -- (λ x y z {xs} b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --                    (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --                     (isInjectiveTransport
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    --                      (funExt (Mb.elim _  refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --    (λ _ → isGroupoidΠ λ _ → isGroupoidHSet)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ×Vev≃⊎Fin→ : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ×Vev≃⊎Fin→ = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ : ∀ n → GroupHom (Perm n) (SymData n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ zero = Eliminators.recPG (Eli zero) _ (λ ()) (⊥.rec ∘ ¬PermR'zero)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- to≃ (suc n) = Eliminators.recPG (Eli n) _ adjTransposition w 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     w : _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     w (zero invo) = adjTransposition²=idEquiv (+k zero)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     w (zero braid) = adjTranspositionBraid
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     w (zero (comm x)) = commTranspositions' x


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _↔×_ : {A : Type ℓ} → ∀ {n} →  ×Vec A n → ×Vec A n → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _↔×_ {n = zero} x x₁ = ⊥*  
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _↔×_ {n = one} x x₁ = ⊥* 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- _↔×_ {n = suc (suc n)} (x , y , xs) (x' , y' , xs') =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  ((x ≡ y') × (y ≡ x')) ⊎ ((y , xs) ↔× (y' , xs) )




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- mkPaΣ : ∀ {a₀₀ a₀₁ : Σ (hSet ℓ-zero) λ (T , _) → T → A} (a₀₋ : a₀₀ ≡ a₀₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {a₁₀ a₁₁ : Σ (hSet ℓ-zero) λ (T , _) → T → A} (a₁₋ : a₁₀ ≡ a₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    → (s : Square
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong (fst ∘ fst) a₀₋)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong (fst ∘ fst) a₁₋)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong (fst ∘ fst) a₋₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong (fst ∘ fst) a₋₁))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    → SquareP (λ i j → s i j → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (cong (snd) a₀₋)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong (snd) a₁₋)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong (snd) a₋₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong (snd) a₋₁) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    → Square a₀₋ a₁₋ a₋₀ a₋₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- mkPaΣ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- FMI* : (Agrp : isGroupoid A) → FMSet2 A → Σ (hSet ℓ-zero) λ (T , _) → T → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- FMI* Agrp = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Elim.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ((⊥.⊥ , isProp→isSet isProp⊥) , ⊥.elim)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ x {xs} (b , f) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ((Mb^ 1 b) , Mb.elim _ x f) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ x y (b , f) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ΣPathP (TypeOfHLevel≡ 2 (ua (swap0and1M b)) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         toPathP (funExt (Mb.elim _  (transportRefl _) (Mb.elim _ (transportRefl _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            λ _ → transportRefl _ ∙ cong f (transportRefl _))))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ x y (b , f) → mkPaΣ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ((cong ua (equivEq (funExt ((Mb.elim _ refl (Mb.elim _ refl λ _ → refl) ))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∙ uaInvEquiv (swap0and1M b)) )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    λ _ → isGroupoidΣ isGroupoidHSet λ _ → isGroupoidΠ λ _ → Agrp

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- lookupFM2 : (Agrp : isGroupoid A) → (xs : FMSet2 A) → fst (fst (FMI* Agrp xs)) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- lookupFM2 Agrp xs = snd (FMI* Agrp xs)




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- lookupFM2 : (Agrp : isGroupoid A) → (xs : FMSet2 A) → fst (FMI xs) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- lookupFM2 Agrp = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Elim.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ⊥.elim
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ x x₁ → Mb.rec x x₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    λ _ → isGroupoidΠ λ _ → Agrp

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- Elim.f 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  (Fin zero , isSetFin)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  (λ _ {xs} _ → Fin (suc (len2 xs)) , isSetFin)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  (λ x y {xs} _ → TypeOfHLevel≡ 2 (ua swap0and1≃))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  (λ x y {xs} _ → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                   (cong ua swap0and1≃=invEquivSwap0and1 ∙ uaInvEquiv swap0and1≃))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  (λ x y z {xs} _ → TypeOfHLevel≡ 2 (ua swap0and2≃))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  (λ x y z {xs} _ → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                     (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                      (({!!} ∙ {!!}) ∙  uaCompEquiv _ _)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  (λ _ → isGroupoidHSet)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isPropGrpSq : {A : I → I → Type ℓ} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (∀ i j → isGroupoid (A i j))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 → {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               → isProp (SquareP A a₀₋ a₁₋ a₋₀ a₋₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isPropGrpSq x a₀₋ a₁₋ a₋₀ a₋₁ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- emPerm : (xs : FMSet2 A) → EM₁ (SymData (len2 xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- emPerm =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (Elim.f {B = λ xs → EM₁ (SymData (len2 xs))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      embase
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ _ → gh→em₂→ _ (sucPermFDMorphism _))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ x y {xs}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        → elimSet (SymData (len2 xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ _ → emsquash _ _) (emloop swap0and1≃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (lem1 (len2 xs)))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ x y {xs} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        elimProp _ (λ _ → isPropGrpSq (λ i j → emsquash) _ _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (cong emloop swap0and1≃=invEquivSwap0and1 ∙ emloop-sym _ swap0and1≃))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ x y z {xs} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        elimSet (SymData (len2 xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (λ _ → emsquash _ _) (emloop swap0and2≃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ((lem2 (len2 xs))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ x y z {xs} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         elimProp _ (λ _ → isPropGrpSq (λ i j → emsquash) _ _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ((sym (emloop-comp _ _ _) ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 cong emloop (equivEq (refl =→ refl =→ refl =→ refl))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 ∙∙ emloop-comp _ _ _))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ x y z {xs} →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         elimProp _ (λ _ → isPropGrpSq (λ i j → emsquash) _ _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ((sym (emloop-comp _ _ _) ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 cong emloop (equivEq (refl =→ refl =→ refl =→ refl))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 ∙∙ emloop-comp _ _ _))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ _ → emsquash)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      )

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     lem1 : ∀ n → ∀ g → PathP
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (λ i →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (emloop {Group = SymData (suc (suc n))} (sucPerm (sucPerm g)) i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (emloop (sucPerm (sucPerm g)) i))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (emloop swap0and1≃) (emloop swap0and1≃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     lem1 n g =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               (sym (emloop-comp _ _ _) ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 cong emloop (commSwap0and1SucSuc g)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 ∙∙ emloop-comp _ _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     lem2 : ∀ n (g : fst (SymData n)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              Square
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (emloop {Group = (SymData (3 + n))} swap0and2≃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (emloop swap0and2≃)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (emloop (sucPerm (sucPerm (sucPerm g))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                (emloop ((sucPerm (sucPerm (sucPerm g)))))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     lem2 n g = ∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ((sym (emloop-comp _ _ _) ∙∙
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 cong emloop (equivEq (refl =→ refl =→ refl =→ refl))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 ∙∙ emloop-comp _ _ _))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- codes≃ : ∀ n → EM₁ (SymData n) → Σ Type₀ λ A → A ≃ fst (SymData n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- codes≃ n =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   elimSet _ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (_ , idEquiv _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toPerm : (xs : FMSet2 A) → fst (SymData (len2 xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- toPerm xs = {! !}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- paPerm : {xs ys : FMSet2 A} → xs ≡ ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    →   Codes (SymData (len2 xs)) (emPerm xs) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        Codes (SymData (len2 ys)) (emPerm ys)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --Codes (SymData (len2 ys)) (emPerm ys)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- paPerm {xs = xs} {ys} p =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    cong (λ zs → Codes (SymData (len2 zs)) (emPerm zs)) p 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- paPerm' : {xs ys : FMSet2 A} → xs ≡ ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    →   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    --Codes (SymData (len2 ys)) (emPerm ys)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- paPerm' {xs = xs} {ys} p =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!cong (λ zs → Codes (SymData (len2 zs)) (emPerm zs)) p !}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    -- cong (λ zs → Codes (SymData (len2 zs)) (emPerm zs)) p 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     zz : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     zz = decode _ (emPerm ys) {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- emK≃ : ∀ n → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      EM₁ (SymData n) → hSet ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- emK≃ n = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- emF : ∀ {n} → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (x : EM₁ (SymData n)) → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- emF {n} = fst ∘ EMFam.EM₁HFam isSetFin


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- zzz : (Agrp : isGroupoid A) → (xs : FMSet2 A) → (x : A) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → (emF (emPerm xs) → A) → emF (emPerm (x ∷2 xs)) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- zzz Agrp = Elim.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ x _ _ → x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (λ x {xs} f a g → {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      -- {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      λ _ → isGroupoidΠ3 λ _ _ _ → Agrp 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   pp : emPerm (x ∷2 xs) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --         gh→em₂→ _ (sucPermFDMorphism _) (emPerm xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   pp = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   ppp : emF (emPerm (x ∷2 xs)) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --          emF (gh→em₂→ _ (sucPermFDMorphism _) (emPerm xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   ppp = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- lookupEm : (Agrp : isGroupoid A) → (x : FMSet2 A) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → emF (emPerm x) → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- lookupEm Agrp =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Elim.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ ())
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    λ _ → isGroupoidΠ λ _ → Agrp 


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- elimSet _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  (λ x → snd (EMFam.EM₁HFam isSetFin x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --  zero {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- emK' : ∀ n → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (x : EM₁ (SymData (suc n))) → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- emK' n =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   elimSet _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    (λ x → snd (EMFam.EM₁HFam isSetFin x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    zero {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- paK : {xs ys : FMSet2 A} → xs ≡ ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --    → fst (SymData (len2 ys)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- paK {xs = xs} {ys} p = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- zz : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- zz = {!encode (SymData (len2 ys)) ?!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- paUnwind : (x y : A) (xs ys : FMSet2 A) →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (p : x ∷2 xs ≡ y ∷2 ys)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              → Σ (singl xs) λ (xs' , p') → cong (x ∷2_) p' ∙ {!!} ≡ p 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- paUnwind = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- headInsert : (x : A) → (xs : FMSet2 A) → (Fin (len2 xs))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 → singl (x ∷2 xs)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- headInsert = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- paMid : (x y : A) (xs ys : FMSet2 A) → 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              (p : x ∷2 xs ≡ y ∷2 ys)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --              → Σ (Σ (FMSet2 A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  λ zs → (xs ≡ y ∷2 zs) × (x ∷2 zs ≡ ys))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                  λ (zs , (q , r)) → (cong (x ∷2_) q ∙∙ comm x y zs ∙∙ cong (y ∷2_) r) ≡ p
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- paMid = {!!}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   inj∷2 : (xs ys : FMSet2 A) → (x : A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --            → x ∷2 xs ≡ x ∷2 ys → xs ≡ ys
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   inj∷2 = ElimSet.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- (ElimSet.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    (λ _ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    (λ x x₁ x₂ → {!!} ∘ cong len2  )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     --    λ _ → isSetΠ2 λ _ _ → trunc _ _ )
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (λ x {xs} b →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ElimSet.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ x' {ys} b' y' p →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          {!!} {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         λ _ → isSetΠ2 λ _ _ → trunc _ _)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     λ _ → isSetΠ3 λ _ _ _ → trunc _ _ 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Rec.f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --      (isSet→isGroupoid isSetℕ) zero (λ _ → suc)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ _ _ _ → refl) (λ _ _ _ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --        (λ _ _ _ _ → refl) (λ _ _ _ _ → refl) (λ _ _ _ _ → refl)


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- RecSet.f isSetℕ zero (λ _ → suc) (λ _ _ _ → refl) (λ _ _ _ _ → refl)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- open import Cubical.HITs.EilenbergMacLane1 as EM

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ (A : Type ℓ) where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- open import Cubical.Data.List.FinData


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   FMSet2OfLen : ℕ → Type ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   FMSet2OfLen n = Σ (FMSet2 A) λ x → len2 x ≡ n

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module _ {A : Type ℓ} where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- isSetLofLA : ∀ n → isSet (ListOfLen A n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- isSetLofLA n = isOfHLevelListOfLen 0 isSetA n 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   FMSet2OfLen≡ : ∀ {n} → {x y : FMSet2OfLen A n} → fst x ≡ fst y → x ≡ y 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   FMSet2OfLen≡ = Σ≡Prop λ _ → isSetℕ _ _

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isGroupoidFMSet2OfLen : ∀ n → isGroupoid (FMSet2OfLen A n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   isGroupoidFMSet2OfLen n = 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     (isOfHLevelΣ 3 trunc λ _ → isSet→isGroupoid (isProp→isSet (isSetℕ _ _)))

