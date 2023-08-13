{-# OPTIONS --safe #-}
module Cubical.Data.Nat.Order.RecursiveBoolPrim where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Foundations.Path


import Cubical.Functions.Logic as L
open import Cubical.Functions.Involution
open import Cubical.Functions.FunExtEquiv


open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Bool hiding (_≤_ ; isProp≤ ; _≟_)

open import Cubical.Data.Nat.Base as Nat
open import Cubical.Data.Nat.Properties hiding (_!)

open import Cubical.Induction.WellFounded

open import Cubical.Relation.Nullary

open import Cubical.Data.Nat.Order.Recursive

open import Cubical.HITs.PropositionalTruncation as PropTrunc







private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C : Type ℓ

Unit×^ : ∀ m → Unit* {ℓ} ×^ m
Unit×^ zero = tt*
Unit×^ (suc m) = tt* , (Unit×^ m)

zipWith×^ : ∀ n → (A → B → C) → A ×^ n → B ×^ n → C ×^ n
zipWith×^ zero f x₁ x₂ = tt*
zipWith×^ (suc n) f x₁ x₂ =
  f (fst x₁) (fst x₂)  ,  (zipWith×^  n f (snd x₁) (snd x₂))

zipSucWith : ∀ n → (A → B → C) → A ×^ n → B ×^ (suc n) → C ×^ n
zipSucWith zero f x₁ x₂ = tt*
zipSucWith (suc n) f x₁ x₂ =
  f (fst x₁) (fst x₂) , zipSucWith  n f (snd x₁) (snd x₂)

transpose : ∀ n m → (A ×^ m) ×^ n → (A ×^ n) ×^ m
transpose zero m _ = Unit×^ m
transpose (suc n) m x =
  zipWith×^ m _,_ (fst x) (transpose n m (snd x))

pairs : ∀ n → A ×^ (suc n) → (A × A) ×^ n
pairs zero _ = tt*
pairs (suc n) (x , xs@(y , _)) = (x , y) , pairs n xs

adjT'× : ∀ n → Bool ×^ (suc n) → Bool ×^ n → Bool ×^ n
adjT'× n x y =
 let v = zipSucWith n {!!} (snd x) (false , snd x) 
 in {!!}

-- Bool* : Type₁
-- Bool* = Σ (∀ {(A , _) : hSet ℓ-zero} → A → A → A)
--           λ f →
--             ⟨ ((λ {A : hSet ℓ-zero} → f {A})  L.≡ₚ (λ {A : hSet ℓ-zero} x _ → x))
--               L.⊔ ((λ {A : hSet ℓ-zero} → f {A})  L.≡ₚ (λ {A : hSet ℓ-zero} _ x → x)) ⟩


-- isSetBool* : isSet Bool*
-- isSetBool* = isSetΣ (isSetImplicitΠ (λ (A , isSetA) → isSetΠ2 λ _ _ → isSetA))
--                   (isProp→isSet ∘ λ a → squash₁)

-- false* true* : Bool*
-- true* = (λ {A} x _ → x) ,  L.inl ∣ refl ∣₁
-- false* = (λ {A} _ x → x) , (L.inr ∣ refl ∣₁)

-- not* : Bool* → Bool*
-- fst (not* (f , _)) {A} = λ x y → f {A} y x
-- snd (not* (_ , p)) =
--  PropTrunc.map
--   (Sum.map (PropTrunc.map λ x i {A} → λ x₁ x₂ → x i {A} x₂ x₁)
--            (PropTrunc.map λ x i {A} → λ x₁ x₂ → x i {A} x₂ x₁)
--    ∘ equivFun ⊎-swap-≃) p 


-- if*_then_else_ : ∀ {(A , _) : hSet ℓ-zero} → Bool* → A → A → A
-- if*_then_else_ {A} (f , _) x₁ x₂ = f {A} x₁ x₂

-- if-not* : ∀ {A : hSet ℓ-zero} {b} {x y : ⟨ A ⟩} →
--     if*_then_else_ {A} b x y ≡ if* (not* b) then y else x
-- if-not* = refl


Bool' : Type ℓ → Type ℓ
Bool' A =
  Σ (A → A → A)
    λ f → ⟨ (f  L.≡ₚ (λ x _ → x))
              L.⊔ (f  L.≡ₚ (λ _ x → x)) ⟩

false' true' : Bool' A
true' = (λ x _ → x) ,  L.inl ∣ refl ∣₁
false' = (λ _ x → x) , L.inr ∣ refl ∣₁


not' : Bool' A → Bool' A
fst (not' (f , _)) = flip f
snd (not' (_ , p)) =  PropTrunc.map
  (Sum.map (PropTrunc.map λ x i → λ x₁ x₂ → x i x₂ x₁)
           (PropTrunc.map λ x i → λ x₁ x₂ → x i x₂ x₁)
   ∘ equivFun ⊎-swap-≃) p 

not'not' : ∀ x → not' (not' {A = A} x) ≡ x
not'not' x = Σ≡Prop (λ _ → squash₁) refl

_and'_ : Bool' A → Bool' A → Bool' A
(f , p) and' (g , q) =
  (λ x y → f (g x y) y) ,
   PropTrunc.map2
     (Sum.rec
       (λ p → Sum.rec {!!} {!!})
       λ q → Sum.rec {!!} {!!}) p q

LUnitAnd' : ∀ (x : Bool' A) → true' and' x ≡ x
LUnitAnd' x = Σ≡Prop {!!} refl

RUnitAnd' : ∀ (x : Bool' A) → x and' true' ≡ x
RUnitAnd' x = Σ≡Prop {!!} refl


if'_then_else_ : Bool' A  → A → A → A
if'_then_else_ (f , _) x₁ x₂ = f x₁ x₂

if''_then_else_ : Bool' A  → Bool' A → Bool' A → Bool' A
fst (if'' f , _ then g , _ else (h , _)) x y =
  f (g x y) (h x y)
snd (if'' f , _ then g , _ else (h , _)) = {!!}


_or'_ : Bool' A → Bool' A → Bool' A
(f , p) or' (g , q) =
  (λ x y → f x (g x y)) ,
   {!!}


adjHlp : ∀ (v- v v+ get- get+ : Bool' A) →
          Bool' A
adjHlp v- v v+ get- get+ =
  if'' get+
    then v+
    else ((if'' get- then v- else v)) 

-- adjHlp : ∀ (v- v v+ get- get+ : Bool' A) →
--           Bool' A
-- adjHlp v- v v+ get- get+ =
--   (not' v) and' ((v+ and' get+) or' (v- and' get-)) 
--   -- (λ a b → fst v b (fst get- {!!} {!!})) , {!!}
--   -- -- if'' get+
--   -- --   then v+
--   -- --   else ((if'' get- then v- else v)) 


-- lem1Ty : (v-- v- v v+ v++ g-- g- g+ g++ : Bool' A) →
       
--         Type _
-- lem1Ty v-- v- v v+ v++ g-- g- g+ g++ =
--       adjHlp 
--            (adjHlp v-- v- v g-- g-)
--            (adjHlp v- v v+ g- g+)
--            (adjHlp v v+ v++ g+ g++)
--            g- g+ ≡ v

-- lem1 : ∀ v-- v- v v+ v++ g- g g+ →
--          lem1Ty {A = A} v-- v- v v+ v++ false' true' false' false' 
    
-- lem1 v-- v- v v+ v++ g- g g+ =
--  Σ≡Prop {!!} refl

-- if'inl : ∀ {b} {a0 a1 : A} (isSetA : isSet A) p →
--        if' b , ∣ inl p ∣₁ then a1 else a0 ≡ a1
-- if'inl {a0 = a0} {a1 = a1} isSetA =
--  PropTrunc.rec (isSetA _ _) λ p i → p i a1 a0

-- record Sep (A : Type ℓ) : Type ℓ where
--  field
--   a0 a1 : A
--   isSetA : isSet A
--   a0≢a1 : ¬ a0 ≡ a1

-- isSetBool' : Sep A → isSet (Bool' A) 
-- isSetBool' x = isSetΣ (isSetΠ2 λ _ _ → isSetA) (isProp→isSet ∘ λ a → squash₁)
--  where
--  open Sep x


-- SepBool : Sep Bool
-- Sep.a0 SepBool = false
-- Sep.a1 SepBool = true
-- Sep.isSetA SepBool = isSetBool
-- Sep.a0≢a1 SepBool = false≢true

-- -- IsoBool'[Bool]Bool : Iso (Bool' Bool) Bool 
-- -- IsoBool'[Bool]Bool = w
-- --  where
 

-- --  open Iso
-- --  w : Iso (Bool' _) Bool
-- --  fun w = if'_then true else false
-- --  inv w = if_then true' else false'
-- --  rightInv w false = refl
-- --  rightInv w true = refl
-- --  leftInv w =
-- --    uncurry λ f →
-- --      PropTrunc.elim (λ _ → isSetBool' SepBool _ _)
-- --       (Sum.elim
-- --         (PropTrunc.elim (λ _ → isSetBool' SepBool _ _)
-- --           (Σ≡Prop (λ _ → squash₁) ∘
-- --               λ a →
-- --                (λ i → fst (if (if'inl {b = f} {false} {true} isSetBool ∣ a ∣₁ i)
-- --                        then true' else false'))
-- --                        ∙ sym a))
-- --         (PropTrunc.elim (λ _ → isSetBool' SepBool _ _)
-- --           (Σ≡Prop (λ _ → squash₁) ∘ {!!}))

-- --         )


-- SndFin×→ : ∀ n → (Bool ×^ n → Bool) → hProp ℓ-zero
-- SndFin×→ zero x = L.⊥
-- SndFin×→ (suc n) x =
--   (L.∀[ xs ] L.∀[ b ]  (x (b , xs) ≡ b) , isSetBool _ _ )
--   L.⊔ (L.∀[ b ] SndFin×→ n (x ∘ (b ,_)))

-- Fin×→ : ℕ → Type
-- Fin×→ n = Σ (Bool ×^ n → Bool) (fst ∘ SndFin×→ n)


-- -- isSetBool' : Sep A → Iso (Bool' Bool) Bool 
-- -- isSetBool' x = w
-- --  where
-- --  open Sep x
-- --  open Iso
-- --  w : Iso (Bool' _) Bool
-- --  fun w b = if' {!b!} then true else false
-- --  inv w = {!!}
-- --  rightInv w = {!!}
-- --  leftInv w = {!!}

-- -- -- isoBB'sec : ∀ a → (if if' a then true else false then true' else false') ≡ a
-- -- -- isoBB'sec a = {!!}
-- -- --  where
-- -- --  w : ∀ b → (if' a then true else false ≡ b) → (if b then
-- -- --        (λ {A} x _ → x) , ∣ inl ∣ (λ _ {A} x _ → x) ∣₁ ∣₁ else
-- -- --        (λ {A} _ x → x) , ∣ inr ∣ (λ _ {A} _ x → x) ∣₁ ∣₁)
-- -- --       ≡ a
-- -- --  w false p = {!!}
-- -- --  w true p = {!!}

-- -- -- isoBB' : Iso Bool' Bool
-- -- -- Iso.fun isoBB' = if'_then true else false
-- -- -- Iso.inv isoBB' = if_then true' else false'
-- -- -- Iso.rightInv isoBB' false = refl
-- -- -- Iso.rightInv isoBB' true = refl
-- -- -- Iso.leftInv isoBB' a = {!!}
-- -- -- -- Σ≡Prop (λ _ → squash₁) {!!}

-- -- -- -- data Bool' : Type where
-- -- -- --  true : Bool'
-- -- -- --  ! : Bool' → Bool'
-- -- -- --  ‼true : ! (! true) ≡ true

-- -- -- -- ‼ : ∀ x → ! (! x) ≡ x
-- -- -- -- ‼ true = ‼true
-- -- -- -- ‼ (! x) = cong ! (‼ x)
-- -- -- -- ‼ (‼true i) j = {!! (! (‼true (j ∨ i)))!}

-- -- -- -- -- !equiv : isEquiv !
-- -- -- -- -- !equiv = snd (involEquiv ‼)

-- -- -- -- -- B→B' : Bool → Bool'
-- -- -- -- -- B→B' false = ! true
-- -- -- -- -- B→B' true = true

-- -- -- -- -- B'→B : Bool' → Bool
-- -- -- -- -- B'→B true = true
-- -- -- -- -- B'→B (! x) = not (B'→B x)
-- -- -- -- -- B'→B (‼ x i) = notnot (B'→B x) i

-- -- -- -- -- BB'lem : ∀ x → B→B' (not x) ≡ ! (B→B' x)
-- -- -- -- -- BB'lem false = sym (‼ true)
-- -- -- -- -- BB'lem true = refl

-- -- -- -- -- -- j = i0 ⊢ B→B' (notnot (B'→B b) i)
-- -- -- -- -- -- j = i1 ⊢ ‼ b i
-- -- -- -- -- -- i = i0 ⊢ (BB'lem (not (B'→B b)) ∙
-- -- -- -- -- --           (λ i₁ → ! ((BB'lem (B'→B b) ∙ (λ i₂ → ! (bb'sec b i₂))) i₁)))
-- -- -- -- -- --          j
-- -- -- -- -- -- i = i1 ⊢ bb'sec b j

-- -- -- -- -- bb'sec : section B→B' B'→B
-- -- -- -- -- bb'sec true = refl
-- -- -- -- -- bb'sec (! b) = BB'lem (B'→B b) ∙ cong ! (bb'sec b)
-- -- -- -- -- bb'sec (‼ b i) j =
-- -- -- -- --   hcomp
-- -- -- -- --     (λ k → λ { (i = i1) → {!!}
-- -- -- -- --              ; (j = i0) → {!BB'lem ? (~ k)!}
-- -- -- -- --              ; (j = i1) → hcomp
-- -- -- -- --                            (λ k' → λ {
-- -- -- -- --                               (i = i0) → {!!}
-- -- -- -- --                              ;(i = i1) → {!! ?!}
-- -- -- -- --                              ;(k = i0) → {!!}
-- -- -- -- --                              ;(k = i1) → ‼ (bb'sec b k') i
-- -- -- -- --                              })
-- -- -- -- --                            {!!}
-- -- -- -- --              })
-- -- -- -- --               {!!}
-- -- -- -- --           -- (! (compPath-filler (BB'lem (B'→B b))
-- -- -- -- --           --       (cong ! (bb'sec b)) (~ i) j))


-- -- -- -- -- IsoBB' : Iso Bool Bool'
-- -- -- -- -- Iso.fun IsoBB' = B→B'
-- -- -- -- -- Iso.inv IsoBB' = B'→B
-- -- -- -- -- Iso.rightInv IsoBB' = {!!}
-- -- -- -- -- -- Iso.rightInv IsoBB' (! b) = BB'lem (B'→B b) ∙ {!!}
-- -- -- -- -- -- Iso.rightInv IsoBB' (‼ b i) = {!!}
-- -- -- -- -- Iso.leftInv IsoBB' false = refl
-- -- -- -- -- Iso.leftInv IsoBB' true = refl

-- -- -- -- -- -- private
-- -- -- -- -- --   variable
-- -- -- -- -- --     ℓ : Level

-- -- -- -- -- -- maybeFunExt : ∀ {ℓ ℓ'} {A : I → Type ℓ} {B : I → Type ℓ'}
-- -- -- -- -- --     → ∀ {f₀ f₁}
-- -- -- -- -- --     → PathP (λ i → B i) (f₀ nothing) (f₁ nothing)
-- -- -- -- -- --     → PathP (λ i → A i → B i) (f₀ ∘ just) (f₁ ∘ just)
-- -- -- -- -- --     → PathP (λ i → Maybe (A i) → B i) f₀ f₁
-- -- -- -- -- -- maybeFunExt p _ i nothing = p i
-- -- -- -- -- -- maybeFunExt _ p i (just x) = p i x

-- -- -- -- -- -- ΣProp→≡hlp : ∀ {ℓ' ℓ''} {A : I → Type ℓ} → {Bi0 : A i0 → Type ℓ'}
-- -- -- -- -- --               {Bi1 : A i1 → Type ℓ'}
              
-- -- -- -- -- --              (Ci0 : ∀ a → isProp (Bi0 a))
-- -- -- -- -- --              (Ci1 : ∀ a → isProp (Bi1 a))
-- -- -- -- -- --              {D : Type ℓ''}
             
-- -- -- -- -- --              (bP₀ bP₁ : PathP (λ i → A i → Type ℓ' ) (Bi0) (Bi1))
-- -- -- -- -- --              (cP₀ : PathP (λ i → ∀ a → isProp (bP₀ i a)) (Ci0) (Ci1))
-- -- -- -- -- --              (cP₁ : PathP (λ i → ∀ a → isProp (bP₁ i a)) (Ci0) (Ci1))
             
-- -- -- -- -- --              → Square
-- -- -- -- -- --                 (λ i → Σ (A i) (bP₀ i) → D)
-- -- -- -- -- --                 (λ i → Σ (A i) (bP₁ i) → D)
-- -- -- -- -- --                 refl
-- -- -- -- -- --                 refl
-- -- -- -- -- -- ΣProp→≡hlp {ℓ = ℓ} {ℓ' = ℓ'} {A = A} {Bi0} {Bi1} Ci0 Ci1 {D} bP₀ bP₁ cP₀ cP₁ =
-- -- -- -- -- --   λ j i → Σ (A i) (ss j i) → D
-- -- -- -- -- --  where
-- -- -- -- -- --   ss : SquareP
-- -- -- -- -- --         (λ _ i → A i → Type ℓ')
-- -- -- -- -- --         bP₀
-- -- -- -- -- --         bP₁
-- -- -- -- -- --         refl
-- -- -- -- -- --         refl
-- -- -- -- -- --   ss = congSqP {A = λ _ i → A i → hProp ℓ'}
-- -- -- -- -- --                {B = λ _ i → A i → Type ℓ' }
-- -- -- -- -- --                (λ _ i → (fst ∘_))
-- -- -- -- -- --           (isOfHLevel→isOfHLevelDep 2
-- -- -- -- -- --             {B = λ T → T → hProp ℓ'}
-- -- -- -- -- --             (λ _ → isSet→ (isSetHProp {ℓ'})) _ _
-- -- -- -- -- --               (λ i a → bP₀ i a , cP₀ i a)
-- -- -- -- -- --               (λ i a → bP₁ i a , cP₁ i a) refl)
        


-- -- -- -- -- -- -- congSqP : ∀ {ℓ ℓ'} {A : I → I → Type ℓ} {B : I → I → Type ℓ'}
-- -- -- -- -- -- --   {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁}
-- -- -- -- -- -- --   {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} {a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁}
-- -- -- -- -- -- --   {a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀} {a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁}
-- -- -- -- -- -- --   → (f : ∀ i j → A i j → B i j)
-- -- -- -- -- -- --   → SquareP A a₀₋ a₁₋ a₋₀ a₋₁
-- -- -- -- -- -- --   → SquareP B (congP (f i0) a₀₋) (congP (f i1) a₁₋)
-- -- -- -- -- -- --               (congP (λ i → f i i0) a₋₀) (congP (λ i → f i i1) a₋₁)
-- -- -- -- -- -- -- congSqP f sq i j = f i j (sq i j)
-- -- -- -- -- -- -- {-# INLINE congSqP #-}


-- -- -- -- -- -- -- congSq' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} → {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
-- -- -- -- -- -- --   {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
-- -- -- -- -- -- --   {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁} (f : ∀ a → B a)
-- -- -- -- -- -- --   → (sq : Square (a₀₋) (a₁₋) (a₋₀) (a₋₁))
-- -- -- -- -- -- --   → SquareP (λ i j → B (sq i j)) (cong f a₀₋) (cong f a₁₋) (cong f a₋₀) (cong f a₋₁)
-- -- -- -- -- -- -- congSq' {a₀₋ = a₀₋} {a₁₋ = a₁₋} {a₋₀ = a₋₀} {a₋₁ = a₋₁}  f sq i j = f (sq i j)
-- -- -- -- -- -- -- {-# INLINE congSq' #-}


-- -- -- -- -- -- isProp→PathPPartial : ∀ {ℓ'} → ∀ j →
-- -- -- -- -- --              {A : I → Type ℓ} →
-- -- -- -- -- --              (a : ∀ i →  Partial ((i ∨ ~ i) ∨ j) (A i))
-- -- -- -- -- --              {B : ∀ i → A i → Type ℓ'} → 
-- -- -- -- -- --              (∀ i → (a : A i) → isProp (B i a))
-- -- -- -- -- --              → (b₀ : B i0 (a i0 1=1))
-- -- -- -- -- --              → (b₁ : B i1 (a i1 1=1))
-- -- -- -- -- --               → ∀ i  → PartialP ((i ∨ ~ i) ∨ j)
-- -- -- -- -- --                   (λ o → B i (a i o))
-- -- -- -- -- -- isProp→PathPPartial j a x b₀ b₁ i = 
-- -- -- -- -- --    λ { (i = i0) → b₀
-- -- -- -- -- --      ; (i = i1) → b₁
-- -- -- -- -- --      ; (j = i1) → isProp→PathP (λ i → x i (a i 1=1)) (b₀) (b₁) i
-- -- -- -- -- --      }


-- -- -- -- -- -- GlueCyl : ∀ j →
-- -- -- -- -- --            {A : I → Type ℓ} →
-- -- -- -- -- --            (T : ∀ i →  Partial ((i ∨ ~ i) ∨ j) (Σ (Type ℓ) λ T → T → A i))
-- -- -- -- -- --            (isE₀ : isEquiv (snd (T i0 1=1)))
-- -- -- -- -- --            (isE₁ : isEquiv (snd (T i1 1=1)))
-- -- -- -- -- --            → I → Type ℓ
              
-- -- -- -- -- -- GlueCyl j {A} T isE₀ isE₁ i =
-- -- -- -- -- --   Glue' (A i) (T i)
-- -- -- -- -- --     (isProp→PathPPartial j
-- -- -- -- -- --       T (λ _ → isPropIsEquiv ∘ snd)
-- -- -- -- -- --        isE₀ isE₁ i)



-- -- -- -- -- -- GlueCyl' : ∀ j →
-- -- -- -- -- --            {A : I → Type ℓ} →
-- -- -- -- -- --            (Ty : ∀ i →  Partial ((i ∨ ~ i) ∨ j) (Type ℓ))
-- -- -- -- -- --            → (e₀ : Ty i0 1=1 ≃ A i0)
-- -- -- -- -- --            → (e₁ : Ty i1 1=1 ≃ A i1)
-- -- -- -- -- --            → (PartialP {ℓ} (j)
-- -- -- -- -- --               (λ {(j = i1) → PathP (λ i → Ty i 1=1 → A i)
-- -- -- -- -- --                  (fst e₀)
-- -- -- -- -- --                  (fst e₁)}))
-- -- -- -- -- --            → I → Type ℓ
              
-- -- -- -- -- -- GlueCyl' j {A} Ty e₀ e₁ e =
-- -- -- -- -- --   GlueCyl j {A = A}
-- -- -- -- -- --     (λ i → λ { (i = i1) → _ , fst e₁
-- -- -- -- -- --       ; (i = i0) → _ , fst e₀
-- -- -- -- -- --       ; (j = i1) → Ty i 1=1 , e 1=1 i
-- -- -- -- -- --       })
-- -- -- -- -- --     (snd e₀) (snd e₁)

-- -- -- -- -- -- GlueCyl'' : ∀ j →
-- -- -- -- -- --            {A : I → Type ℓ} →
-- -- -- -- -- --              (e₀ : Σ (Type ℓ) λ T → T ≃ A i0)
-- -- -- -- -- --            → (e₁ : Σ (Type ℓ) λ T → T ≃ A i1)
-- -- -- -- -- --            → (e : Partial (j) (PathP (λ i →  Σ (Type ℓ) λ T → T →  A i)
-- -- -- -- -- --                   (fst e₀ , fst (snd e₀))
-- -- -- -- -- --                   (fst e₁ , fst (snd e₁))) )
           
-- -- -- -- -- --            → I → Type ℓ
              
-- -- -- -- -- -- GlueCyl'' j {A} e₀ e₁ e =
-- -- -- -- -- --     GlueCyl j {A = A}
-- -- -- -- -- --     (λ i → λ { (i = i0) → (fst e₀ , fst (snd e₀))
-- -- -- -- -- --       ; (i = i1) → (fst e₁ , fst (snd e₁))
-- -- -- -- -- --       ; (j = i1) → e 1=1 i
-- -- -- -- -- --       })
-- -- -- -- -- --     (snd (snd e₀)) (snd (snd e₁))



-- -- -- -- -- -- -- injFin×→ℕ : ∀ {n} x y → Fin×→ℕ n x ≡ Fin×→ℕ n y → x ≡ y  
-- -- -- -- -- -- -- injFin×→ℕ {n} x y x₁ = {!!}


-- -- -- -- -- -- rot201Mb : ∀ n → Maybe (Fin× (2 + n)) → Maybe (Fin× (2 + n))
-- -- -- -- -- -- rot201Mb n = Mb.rec (just (sucFin× Fin×0))
-- -- -- -- -- --              (Fin×cases nothing
-- -- -- -- -- --                (just ∘ Fin×cases Fin×0 (sucFin× ∘ sucFin×)))
-- -- -- -- -- -- -- nothing = just (sucFin× Fin×0)
-- -- -- -- -- -- -- rot312Mb n (just x) = {!Fin×cases!}

-- -- -- -- -- -- rot120Mb : ∀ n → Maybe (Fin× (2 + n)) → Maybe (Fin× (2 + n))
-- -- -- -- -- -- rot120Mb n = Mb.rec
-- -- -- -- -- --   (just Fin×0)
-- -- -- -- -- --   (Fin×cases (just (sucFin× Fin×0))
-- -- -- -- -- --     (Fin×cases nothing (just ∘ sucFin× ∘ sucFin×)))

-- -- -- -- -- -- ℕ≟Split : ℕ → ℕ → Type
-- -- -- -- -- -- ℕ≟Split zero zero = Unit
-- -- -- -- -- -- ℕ≟Split zero (suc m) = ⊥
-- -- -- -- -- -- ℕ≟Split (suc n) zero = ⊥
-- -- -- -- -- -- ℕ≟Split (suc n) (suc m) = ℕ≟Split n m

-- -- -- -- -- -- ℕ≟split : ∀ {n m} → n ≡ m → ℕ≟Split n m
-- -- -- -- -- -- ℕ≟split {zero} {zero} x = tt
-- -- -- -- -- -- ℕ≟split {zero} {suc m} x = znots x
-- -- -- -- -- -- ℕ≟split {suc n} {zero} x = snotz x
-- -- -- -- -- -- ℕ≟split {suc n} {suc m} x = ℕ≟split (injSuc x)

-- -- -- -- -- -- injFin×→ℕ' : ∀ {n} (x y : Fin× n) → 
-- -- -- -- -- --     ℕ≟Split (Fin×→ℕ n (fst x)) (Fin×→ℕ n (fst y)) → fst x ≡ fst y  
-- -- -- -- -- -- injFin×→ℕ' {suc n} (x'@(x , xs) , X) (y'@(y , ys) , Y) p with x | y
-- -- -- -- -- -- ... | false | false = cong (false ,_) (injFin×→ℕ' {n} (xs , X) (ys , Y) p)
-- -- -- -- -- -- ... | true | true = cong (true ,_) (allFalse-≡ n xs ys X Y)

-- -- -- -- -- -- injFin×→ℕ : ∀ {n} (x y : Fin× n) → Fin×→ℕ n (fst x) ≡ Fin×→ℕ n (fst y) → x ≡ y  
-- -- -- -- -- -- injFin×→ℕ x y =
-- -- -- -- -- --   Σ≡Prop (snd ∘ Fin×Snd _)
-- -- -- -- -- --     ∘ injFin×→ℕ' x y
-- -- -- -- -- --     ∘ ℕ≟split 


-- -- -- -- -- -- rot201Mb-rot120Mb : ∀ n → section (rot201Mb n) (rot120Mb n)
-- -- -- -- -- -- rot201Mb-rot120Mb n =
-- -- -- -- -- --  Mb.elim _ refl
-- -- -- -- -- --    (uncurry (uncurry
-- -- -- -- -- --     λ { false → uncurry
-- -- -- -- -- --          λ { false → λ _ _ → refl
-- -- -- -- -- --             ; true _ _ → cong just (injFin×→ℕ _ _ refl)
-- -- -- -- -- --             }
-- -- -- -- -- --       ; true _ _ → cong just (injFin×→ℕ _ _ refl)
-- -- -- -- -- --       }))

-- -- -- -- -- -- rot120Mb-rot201Mb : ∀ n → retract (rot201Mb n) (rot120Mb n)
-- -- -- -- -- -- rot120Mb-rot201Mb n =
-- -- -- -- -- --   Mb.elim _ refl
-- -- -- -- -- --      (uncurry (uncurry
-- -- -- -- -- --        λ { false → uncurry
-- -- -- -- -- --          λ { false → λ _ _ → refl
-- -- -- -- -- --             ; true _ _ → cong just (injFin×→ℕ _ _ refl)
-- -- -- -- -- --             }
-- -- -- -- -- --       ; true _ _ → cong just (injFin×→ℕ _ _ refl)
-- -- -- -- -- --       }))


-- -- -- -- -- -- swap02MbIso : ∀ n → Iso
-- -- -- -- -- --    (Maybe (Fin× (suc (suc n))))
-- -- -- -- -- --    (Maybe (Fin× (suc (suc n))))
-- -- -- -- -- -- Iso.fun (swap02MbIso n) = rot201Mb n
-- -- -- -- -- -- Iso.inv (swap02MbIso n) = rot120Mb n
-- -- -- -- -- -- Iso.rightInv (swap02MbIso n) = rot201Mb-rot120Mb n
-- -- -- -- -- -- Iso.leftInv (swap02MbIso n) = rot120Mb-rot201Mb n


-- -- -- -- -- -- swap02Mb≃ : ∀ n → Maybe (Fin× (suc (suc n))) ≃ Maybe (Fin× (suc (suc n)))
-- -- -- -- -- -- swap02Mb≃ = isoToEquiv ∘ swap02MbIso


-- -- -- -- -- -- -- zzss' : ∀ {ℓ} {a₀₀ a₀₁ : Type ℓ} (a₀₋ : a₀₀ ≡ a₀₁)
-- -- -- -- -- -- --   {a₁₀ a₁₁ : Type ℓ} (a₁₋ : a₁₀ ≡ a₁₁)
-- -- -- -- -- -- --   (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
-- -- -- -- -- -- --   → Square a₀₋ a₁₋ a₋₀ a₋₁
-- -- -- -- -- -- --   → {!!}
-- -- -- -- -- -- --    -- PathP (λ i → a₋₀ i → a₋₁ i) (transport a₀₋) (transport a₁₋)
  
-- -- -- -- -- -- -- zzss' a₀₋ a₁₋ a₋₀ a₋₁ s =
-- -- -- -- -- -- --   {! congP (λ _ → transport) (flipSquare (PathP∙∙→compPathR' s))!}


-- -- -- -- -- -- -- zzss : ∀ {ℓ} {a₀₀ a₀₁ : Type ℓ} (a₀₋ : a₀₀ ≡ a₀₁)
-- -- -- -- -- -- --   {a₁₀ a₁₁ : Type ℓ} (a₁₋ : a₁₀ ≡ a₁₁)
-- -- -- -- -- -- --   (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
-- -- -- -- -- -- --   → PathP (λ i → a₋₀ i → a₋₁ i) (transport a₀₋) (transport a₁₋)
-- -- -- -- -- -- --   → Square a₀₋ a₁₋ a₋₀ a₋₁
-- -- -- -- -- -- -- zzss = {!!}


-- -- -- -- -- -- congP' : ∀ {ℓ'} {A : I → Type ℓ} {B : (i : I) → Type ℓ'}
-- -- -- -- -- --   (f : (i : I) → A i → B i) {x : A i0} {y : A i1}
-- -- -- -- -- --   (p : PathP A x y) → PathP (λ i → B i) (f i0 x) (f i1 y)
-- -- -- -- -- -- congP' f p i = f i (p i)
-- -- -- -- -- -- {-# INLINE congP' #-}

-- -- -- -- -- -- congPapp : ∀ {ℓ'} {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ'}
-- -- -- -- -- --   {f₀ : ∀ a → B i0 a } {f₁ : ∀ a → B i1 a}
-- -- -- -- -- --   (f : PathP (λ i → ∀ a → B i a) f₀ f₁) {x : A i0} {y : A i1}
-- -- -- -- -- --   (p : PathP A x y) → PathP (λ i → B i (p i)) (f i0 x) (f i1 y)
-- -- -- -- -- -- congPapp f p i = f i (p i)
-- -- -- -- -- -- {-# INLINE congPapp #-}


-- -- -- -- -- -- congSqP' : ∀ {ℓ ℓ'} {A : I → I → Type ℓ} {B : I → I → Type ℓ'}
-- -- -- -- -- --   {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁}
-- -- -- -- -- --   {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} {a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁}
-- -- -- -- -- --   {a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀} {a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁}
-- -- -- -- -- --   → let F = λ i j → A i j → B i j in 
-- -- -- -- -- --   {f₀₀ : F i0 i0} {f₀₁ : F i0 i1} {f₀₋ : PathP (λ j → F i0 j) f₀₀ f₀₁}
-- -- -- -- -- --   {f₁₀ : F i1 i0} {f₁₁ : F i1 i1} {f₁₋ : PathP (λ j → F i1 j) f₁₀ f₁₁}
-- -- -- -- -- --   {f₋₀ : PathP (λ i → F i i0) f₀₀ f₁₀} {f₋₁ : PathP (λ i → F i i1) f₀₁ f₁₁}
-- -- -- -- -- --   → SquareP F f₀₋ f₁₋ f₋₀ f₋₁
-- -- -- -- -- --   → SquareP A a₀₋ a₁₋ a₋₀ a₋₁
-- -- -- -- -- --   → SquareP B (congPapp (f₀₋) a₀₋) (congPapp (f₁₋) a₁₋)
-- -- -- -- -- --               (congPapp (f₋₀) a₋₀) (congPapp (f₋₁) a₋₁)
-- -- -- -- -- -- congSqP' f sq i j = f i j (sq i j)
-- -- -- -- -- -- {-# INLINE congSqP' #-}


-- -- -- -- -- -- module _ {A : Type ℓ} where

-- -- -- -- -- --  open Tab× {ℓ} {A}


-- -- -- -- -- --  tab×biAdjT×'<-lem-f : ∀ n →
-- -- -- -- -- --    PathP (λ j →
-- -- -- -- -- --      (F×biAdjT≡ {n = 3 + n} (zero , tt) (1 , tt) (~ j) → A) →
-- -- -- -- -- --       (𝑮-refl {B = A × A × A × tab×≡ (n) i0}
-- -- -- -- -- --       ((≃-× (idEquiv _) Σ-swap-01-≃))
-- -- -- -- -- --        (Σ-swap-01-≃) (j)))

-- -- -- -- -- --       (λ f → f Fin×0
-- -- -- -- -- --           , (f (sucFin× Fin×0) ,
-- -- -- -- -- --             (f (sucFin× (sucFin× Fin×0)) , (f ∘ sucFin× ∘ sucFin× ∘ sucFin×))))
-- -- -- -- -- --       (λ f → f Fin×0 ,
-- -- -- -- -- --             (f (sucFin× Fin×0) ,
-- -- -- -- -- --             (f (sucFin× (sucFin× Fin×0)) , (f ∘ sucFin× ∘ sucFin× ∘ sucFin×))))
      

-- -- -- -- -- --  tab×biAdjT×'<-lem-f n j f =
-- -- -- -- -- --    let x' : PathP (λ j →
-- -- -- -- -- --                Fin× (3 + n) → F×biAdjT≡ {n = 3 + n} (zero , tt) (1 , tt) (~ j))
-- -- -- -- -- --                _ _ 
-- -- -- -- -- --        x' = funExt λ (y , y') →
-- -- -- -- -- --               Fin×PathP (3 + n)
-- -- -- -- -- --                 _ _
-- -- -- -- -- --                 {y₀ = Fin×Snd∘adjT× (3 + n) 1  y y'}
-- -- -- -- -- --                 {y₁ = Fin×Snd∘adjT× (3 + n) 0  y y'}
-- -- -- -- -- --                 λ i → glueBiAdjT×< n i y
                
-- -- -- -- -- --        f' = f ∘' x' j
-- -- -- -- -- --    in 
-- -- -- -- -- --        glue
-- -- -- -- -- --        (λ { (j = i1) → 
-- -- -- -- -- --            f _ ,
-- -- -- -- -- --             (f (_) ,
-- -- -- -- -- --             (f (_) , (f ∘ sucFin× ∘ sucFin× ∘ sucFin×)))
-- -- -- -- -- --           ; (j = i0) → 
-- -- -- -- -- --            f (_)
-- -- -- -- -- --           , (f _ ,
-- -- -- -- -- --             (f _ , (f ∘ sucFin× ∘ sucFin× ∘ sucFin×)))
-- -- -- -- -- --           })
-- -- -- -- -- --          (f' Fin×0 ,
-- -- -- -- -- --            (f' (sucFin× Fin×0) ,
-- -- -- -- -- --            (f' (sucFin× (sucFin× Fin×0)) ,
-- -- -- -- -- --             f' ∘ sucFin× ∘ sucFin× ∘ sucFin×)))


-- -- -- -- -- --  tab×biAdjT×'<-lem-f+2 : ∀ n k l< → 
-- -- -- -- -- --    PathP (λ j →
-- -- -- -- -- --      (F×biAdjT≡ {n = 2 + n} (zero , tt) (suc (suc k) , l<) j → A) →
-- -- -- -- -- --       ua (Σ-swap-01-≃ {A = A} {A} {tab×adjT× n (k , l<) (~ j) i0}) j)
-- -- -- -- -- --      (λ f → f Fin×0 , (f (sucFin× Fin×0) , f ∘ sucFin× ∘ sucFin×))
-- -- -- -- -- --      λ f → f Fin×0 , (f (sucFin× Fin×0) , f ∘ sucFin× ∘ sucFin×)
-- -- -- -- -- --  tab×biAdjT×'<-lem-f+2 n k l< j f =
-- -- -- -- -- --    let x' : PathP (λ j →
-- -- -- -- -- --                F×adjT≡ {n = n} k (~ j) →
-- -- -- -- -- --                  F×biAdjT≡ {n = 2 + n} (zero , tt) (suc (suc k) , l<) j)
-- -- -- -- -- --                (sucFin× ∘ sucFin×)
-- -- -- -- -- --                (sucFin× ∘ sucFin×) 
-- -- -- -- -- --        x' j y =
-- -- -- -- -- --          (glue (λ { (j = i0) → false , fst (sucFin× y)
-- -- -- -- -- --                   ; (j = i1) → false , fst (sucFin× y)
-- -- -- -- -- --                   })
-- -- -- -- -- --                (false , false , fst y))
-- -- -- -- -- --           , let z = congP (λ _ → (snd ∘_) ∘ snd )  (F×biAdjT≡' {n = 2 + n}
-- -- -- -- -- --                        (zero , tt) (suc (suc k) , l<))
-- -- -- -- -- --              in isProp→PathP (λ j → isPropΠ {A = F×adjT≡ {n = n} k (~ j)}
-- -- -- -- -- --                         (λ y → (z j
-- -- -- -- -- --                      ( ((glue (λ { (j = i0) → false , fst (sucFin× y)
-- -- -- -- -- --                   ; (j = i1) → false , fst (sucFin× y)
-- -- -- -- -- --                   })
-- -- -- -- -- --                (false , false , fst y)))) )))
-- -- -- -- -- --                    (snd ∘ (sucFin× ∘ sucFin× {n = n}))
-- -- -- -- -- --                    ((snd ∘ (sucFin× ∘ sucFin× {n = n}))) j
-- -- -- -- -- --                     y
                    
-- -- -- -- -- --        x'0 : PathP (λ j → F×biAdjT≡
-- -- -- -- -- --                  {n = 2 + n} (zero , tt) (suc (suc k) , l<) j)
-- -- -- -- -- --                  (sucFin× Fin×0)
-- -- -- -- -- --                  Fin×0
-- -- -- -- -- --        x'0 = Fin×PathP' (2 + n)
-- -- -- -- -- --         (F×biAdjT≡' {2 + n} (zero , tt) (suc (suc k) , l<))
-- -- -- -- -- --           (𝑮-gluePath (adjT×^≃ {n = 2 + n} zero)
-- -- -- -- -- --              _ (idEquiv (Bool ×^ (2 + n)))
-- -- -- -- -- --                  (congP' {B = λ i →
-- -- -- -- -- --                     Bool × Bool × adjT×^≡ {A = Bool} {n = n} k (~ i)}
-- -- -- -- -- --                       (λ _ → (true ,_) ∘' (false ,_))
-- -- -- -- -- --                  (symP-fromGoal (glue-repeat-false (n) k))))

-- -- -- -- -- --        x'1 : PathP (λ j → F×biAdjT≡
-- -- -- -- -- --                  {n = 2 + n} (zero , tt) (suc (suc k) , l<) j)
-- -- -- -- -- --                  Fin×0
-- -- -- -- -- --                  (sucFin× Fin×0)
-- -- -- -- -- --        x'1 = Fin×PathP' (2 + n)
-- -- -- -- -- --         (F×biAdjT≡' {2 + n} (zero , tt) (suc (suc k) , l<))
-- -- -- -- -- --           (𝑮-gluePath (adjT×^≃ {n = 2 + n} zero)
-- -- -- -- -- --              _ (idEquiv (Bool ×^ (2 + n)))
-- -- -- -- -- --                  (congP' {B = λ i →
-- -- -- -- -- --                     Bool × Bool × adjT×^≡ {A = Bool} {n = n} k (~ i)}
-- -- -- -- -- --                       (λ _ → (false ,_) ∘' (true ,_))
-- -- -- -- -- --                  (symP-fromGoal (glue-repeat-false (n) k))))

-- -- -- -- -- --    in 
-- -- -- -- -- --        glue
-- -- -- -- -- --        (λ { (j = i1) → 
-- -- -- -- -- --            f _ ,
-- -- -- -- -- --             (f _ ,
-- -- -- -- -- --             ( (f ∘ sucFin× ∘ sucFin×)))
-- -- -- -- -- --           ; (j = i0) → 
-- -- -- -- -- --            f (_)
-- -- -- -- -- --           , (f _ ,
-- -- -- -- -- --             ( (f ∘ sucFin× ∘ sucFin×)))
-- -- -- -- -- --           })
-- -- -- -- -- --          (f (x'0 j) ,
-- -- -- -- -- --            (f (x'1 j) ,
-- -- -- -- -- --            f ∘ x' j))
 
-- -- -- -- -- --  tab×biAdjT×'< : ∀ l →
-- -- -- -- -- --    (n : ℕ) (k< : 1 < suc n) (l< : suc (suc l) < suc n) →
-- -- -- -- -- --       Square (tab×≡ (suc n)) (tab×≡ (suc n))
-- -- -- -- -- --       (λ i → F×biAdjT≡ {n = suc n} (zero , k<) (suc l , l<) (i) → A)
-- -- -- -- -- --       (λ i → biAdjT×^≡< {A = A} {n = suc n} (l , l<) (~ i))
-- -- -- -- -- --  tab×biAdjT×'< zero (suc (suc n)) k< l< j i =
-- -- -- -- -- --    let e = tab×≡-ungluing-equiv' 3 n i
-- -- -- -- -- --    in Glue' (𝑮-refl {B = A × A × A × tab×≡ (n) i}
-- -- -- -- -- --       ((≃-× (idEquiv _) Σ-swap-01-≃))
-- -- -- -- -- --        (Σ-swap-01-≃) (~ j))
-- -- -- -- -- --          (λ { (i = i0) → (F×biAdjT≡ {n = 3 + n} (zero , _) (1 , l<) (j) → A)
-- -- -- -- -- --               , tab×biAdjT×'<-lem-f n (~ j)  
-- -- -- -- -- --             ; (i = i1) → biAdjT×^≡< {A = A} {n = 3 + n} (zero , l<) (~ j) ,
-- -- -- -- -- --                 λ x → x
-- -- -- -- -- --             ; (j = i0) → _ 
-- -- -- -- -- --             ; (j = i1) → _
-- -- -- -- -- --             })
-- -- -- -- -- --          λ { (i = i0) → isProp→PathP
-- -- -- -- -- --               (λ j → isPropIsEquiv
-- -- -- -- -- --                 (tab×biAdjT×'<-lem-f n (~ j)))
-- -- -- -- -- --                   (snd e) (snd e) j
-- -- -- -- -- --             ; (i = i1) →
-- -- -- -- -- --                 isProp→PathP
-- -- -- -- -- --               (λ j → isPropIsEquiv
-- -- -- -- -- --                 (idfun (biAdjT×^≡< {A = A} {n = 3 + n} (zero , l<) (~ j))))
-- -- -- -- -- --                   (snd e) (snd e) j
-- -- -- -- -- --             ; (j = i0) → snd e
-- -- -- -- -- --             ; (j = i1) → snd e
-- -- -- -- -- --             }
-- -- -- -- -- --  tab×biAdjT×'< (suc k) (suc n) k< l< j i =
-- -- -- -- -- --    let e = tab×adjT×0'-lem {n} i
-- -- -- -- -- --    in Glue'
-- -- -- -- -- --          (ua (Σ-swap-01-≃ {A = A} {A} {tab×adjT× n (k , l<) (~ j) i}) j)
-- -- -- -- -- --          ((λ { (i = i0) →
-- -- -- -- -- --             ((F×biAdjT≡ {n = 2 + n} (zero , k<) (suc (suc k) , l<) j → A))
-- -- -- -- -- --                   , tab×biAdjT×'<-lem-f+2 n k l< j 
-- -- -- -- -- --                 ; (i = i1) →
-- -- -- -- -- --                    (ua (Σ-swap-01-≃ {A = A} {A}
-- -- -- -- -- --                      {tab×adjT× n (k , l<) (~ j) (i)}) j) ,
-- -- -- -- -- --                     idfun _
-- -- -- -- -- --                 ; (j = i0) → tab×≡ (2 + n) i , fst e
-- -- -- -- -- --                 ; (j = i1) → tab×≡ (2 + n) i , fst e
-- -- -- -- -- --                 }))
-- -- -- -- -- --          (λ { (i = i0) → isProp→PathP
-- -- -- -- -- --               (λ j → isPropIsEquiv (tab×biAdjT×'<-lem-f+2 n k l< j))
-- -- -- -- -- --                  (snd e) (snd e) j
-- -- -- -- -- --                 ; (i = i1) → isProp→PathP
-- -- -- -- -- --               (λ j → isPropIsEquiv (idfun ((ua (Σ-swap-01-≃ {A = A} {A}
-- -- -- -- -- --                      {tab×adjT× n (k , l<) (~ j) (i)}) j)))) (snd e) (snd e) j
-- -- -- -- -- --                 ; (j = i0) → snd e
-- -- -- -- -- --                 ; (j = i1) → snd e
-- -- -- -- -- --                 })
         
-- -- -- -- -- --  lem-tab×biAdjT×' : ∀ n k (k< : suc k < n) (l< : 1 < suc n) → 
-- -- -- -- -- --          Square
-- -- -- -- -- --        (λ i → F×biAdjT≡  {n = 1 + n} (suc k , k<) (zero , l<) i → A)
-- -- -- -- -- --         (λ i → F×biAdjT≡ {n = 1 + n} (zero , l<) (suc k , k<) (~ i) → A)
-- -- -- -- -- --         refl
-- -- -- -- -- --         refl
-- -- -- -- -- --  lem-tab×biAdjT×' n k k< l< =
-- -- -- -- -- --     cong {x = F×biAdjT≡' {1 + n} (suc k , k<) (zero , l<)}
-- -- -- -- -- --          {y = sym (F×biAdjT≡' {1 + n} (zero , l<) (suc k , k<))}
-- -- -- -- -- --       (cong {A = (Σ Type λ X → X → hProp ℓ-zero)}
-- -- -- -- -- --       ((λ X → X → A) ∘ (λ a → Σ (fst a) (fst ∘ snd a))))
-- -- -- -- -- --      (ΣSquareSet (λ _ → isSet→ isSetHProp) refl)
 
-- -- -- -- -- --  tab×biAdjT×' : ∀ k l n → ∀ k< l< →
-- -- -- -- -- --       Square
-- -- -- -- -- --         (tab×≡ n) (tab×≡ n)
-- -- -- -- -- --         (λ i → (F×biAdjT≡ {n} (k , k<) (l , l<) (i) → A))
-- -- -- -- -- --         (biAdjT×^≡ {A = A} {n} (k , k<) (l , l<))
        
-- -- -- -- -- --  tab×biAdjT×' =
-- -- -- -- -- --    Nat.elim
-- -- -- -- -- --       (Nat.cases
-- -- -- -- -- --         (λ n k< l< → refl)
-- -- -- -- -- --         (λ l → Nat.cases (λ ())
-- -- -- -- -- --           (tab×biAdjT×'< l)))
-- -- -- -- -- --       λ k X → Nat.cases
-- -- -- -- -- --         (Nat.cases (λ ())
-- -- -- -- -- --            (λ n k< l< →
-- -- -- -- -- --               flipSquare
-- -- -- -- -- --                  ( lem-tab×biAdjT×' n k k< l<
-- -- -- -- -- --                   ◁
-- -- -- -- -- --                 flipSquare (symP-fromGoal (tab×biAdjT×'< k n l< k<)))
-- -- -- -- -- --              -- {!
-- -- -- -- -- --              --  symP-fromGoal (tab×biAdjT×'< k n l< k<)!}
-- -- -- -- -- --               ))
-- -- -- -- -- --       λ l →
-- -- -- -- -- --           Nat.elim (λ ())
-- -- -- -- -- --            λ n Z k< l< →
-- -- -- -- -- --              congP₃ (λ i → tab×≡-suc) 
-- -- -- -- -- --          {Maybe∘Fin×≃Fin×∘suc n} {Maybe∘Fin×≃Fin×∘suc n}
-- -- -- -- -- --           (equivPathP 
-- -- -- -- -- --             (zzz n k l k< l<)
-- -- -- -- -- --             _ _)
-- -- -- -- -- --           (X l n k< l<)
-- -- -- -- -- --           λ _ → idEquiv _  

-- -- -- -- -- --    where
-- -- -- -- -- --     zzz : ∀ n k l → ∀ k< l< → PathP
-- -- -- -- -- --       (λ i →
-- -- -- -- -- --          Maybe (F×biAdjT≡ {n = n} (k , k<) (l , l<) (i)) →
-- -- -- -- -- --          F×biAdjT≡ {n = suc n} (suc k , k<) (suc l , l<) (i))
-- -- -- -- -- --       (λ z → IsoMaybe∘Fin×Fin×∘suc n .Iso.fun z)
-- -- -- -- -- --       (λ z → IsoMaybe∘Fin×Fin×∘suc n .Iso.fun z)
-- -- -- -- -- --     zzz n k l k< l< = 
-- -- -- -- -- --       maybeFunExt
-- -- -- -- -- --       (toPathP (invEq (congEquiv Σ-assoc-≃)
-- -- -- -- -- --         (cong′ (true ,_) (sym (snd (isContrΣallFalse n) _)) )))
-- -- -- -- -- --         (toPathP (funExt λ z →
-- -- -- -- -- --           Σ≡Prop (snd ∘ Fin×Snd (1 + n))
-- -- -- -- -- --             (cong′ (false ,_)
-- -- -- -- -- --             (transportTransport⁻ (biAdjT×^≡ (k , k<) (l , l<)) (fst z))
-- -- -- -- -- --             )))

-- -- -- -- -- --  tab×biAdjT× :
-- -- -- -- -- --    ∀ n (k l : Fin₋₁ n) →
-- -- -- -- -- --       PathP (λ i → (F×biAdjT≡ {n} k l i → A)
-- -- -- -- -- --          ≡ biAdjT×^≡ {A = A} {n} k l i)
-- -- -- -- -- --       (tab×≡ n) (tab×≡ n)
-- -- -- -- -- --  tab×biAdjT× n k l = tab×biAdjT×' (fst k) (fst l) n (snd k) (snd l) 


       
-- -- -- -- -- --  tab×adjT×-invol0-cyl : ∀ n →
-- -- -- -- -- --        (p : ∀ n (k : Fin₋₁ n) →
-- -- -- -- -- --               SquareP (λ j i → adjT×^≡-invol {A = Bool} n (fst k) j (i) →
-- -- -- -- -- --                 hProp ℓ-zero)
-- -- -- -- -- --                  ((F×adjSnd {n} (fst k)))
-- -- -- -- -- --                  (symP  (F×adjSnd {n} (fst k)))
-- -- -- -- -- --                  (λ _ → Fin×Snd n)
-- -- -- -- -- --                  (λ _ → Fin×Snd n))
-- -- -- -- -- --      → ∀ i jj →
-- -- -- -- -- --        PartialP (i ∨ ~ i ∨ jj ∨ ~ jj)
-- -- -- -- -- --           λ o → PathP (λ j → Σ (Type ℓ) λ T → T →
-- -- -- -- -- --             Σ-swap-01-≡-invol-ua {A = A} {B = tab×≡ n jj} j i)
-- -- -- -- -- --                (fst (tab×adjT×0'-sides n i jj o) ,
-- -- -- -- -- --                  fst (snd (tab×adjT×0'-sides n i jj o)))
-- -- -- -- -- --                ((fst (tab×adjT×0'-sides n (~ i) jj o) ,
-- -- -- -- -- --                  fst (snd (tab×adjT×0'-sides n (~ i) jj o))))
-- -- -- -- -- --  tab×adjT×-invol0-cyl n p i jj =
-- -- -- -- -- --      (λ { (i =  i0) → λ j → tab×≡ (suc (suc n)) jj , fst (tab×≡-ungluing-equiv'2 n jj)
-- -- -- -- -- --         ; (i = i1) → λ j → tab×≡ (suc (suc n)) jj , fst (tab×≡-ungluing-equiv'2 n jj)
-- -- -- -- -- --         ; (jj = i0) → λ j → (Σ (Σ-swap-01-≡-invol-ua j i)
-- -- -- -- -- --                         (fst ∘ p (suc (suc n)) (zero , tt) j i) →
-- -- -- -- -- --                         A) , tab×adjT×-invol0-jj0 n p i j
-- -- -- -- -- --         ; (jj = i1) → λ j →  _ , idfun _
-- -- -- -- -- --         })


-- -- -- -- -- --  tab×adjT×-invol0 : ∀ n →
-- -- -- -- -- --    (p : ∀ n (k : Fin₋₁ n) →
-- -- -- -- -- --                SquareP (λ j i → adjT×^≡-invol {A = Bool} n (fst k) j (i) → hProp ℓ-zero)
-- -- -- -- -- --                   ((F×adjSnd {n} (fst k)))
-- -- -- -- -- --                   (symP  (F×adjSnd {n} (fst k)))
-- -- -- -- -- --                   (λ _ → Fin×Snd n)
-- -- -- -- -- --                   (λ _ → Fin×Snd n))
-- -- -- -- -- --     → SquareP
-- -- -- -- -- --       (λ j i →
-- -- -- -- -- --          (Σ (adjT×^≡-invol (suc (suc n)) zero j (i))
-- -- -- -- -- --           (fst ∘ p (suc (suc n)) (zero , _) j i) →
-- -- -- -- -- --           A)
-- -- -- -- -- --          ≡ adjT×^≡-invol {A = A} (suc (suc n)) zero j i)
-- -- -- -- -- --       (tab×adjT×0' (suc n) tt)
-- -- -- -- -- --       (symP (tab×adjT×0' (suc n) _))
-- -- -- -- -- --        (refl {x = tab×≡ (suc (suc n))})
-- -- -- -- -- --        refl
-- -- -- -- -- --  tab×adjT×-invol0 n p j i jj =
-- -- -- -- -- --    Glue (Σ-swap-01-≡-invol-ua {A = A} {B = tab×≡ n jj} j i)
-- -- -- -- -- --      λ o → fst Σ-assoc-≃ (ΣPathPProp
-- -- -- -- -- --                {A = λ j → Σ (Type ℓ)
-- -- -- -- -- --                     λ T → T →
-- -- -- -- -- --                      Σ-swap-01-≡-invol-ua {A = A} {B = tab×≡ n jj} j i }
-- -- -- -- -- --                {B = λ _ → isEquiv ∘ snd}
-- -- -- -- -- --               {u = Iso.inv Σ-assoc-Iso (tab×adjT×0'-sides n i jj o) }
-- -- -- -- -- --               {v = Iso.inv Σ-assoc-Iso (tab×adjT×0'-sides n (~ i) jj o)}
-- -- -- -- -- --          (isPropIsEquiv ∘ snd) (tab×adjT×-invol0-cyl n p i jj o) j)
   

-- -- -- -- -- --  tab×adjT×-invol :
-- -- -- -- -- --    ∀ n (k : Fin₋₁ n) →
-- -- -- -- -- --      (p : ∀ n (k : Fin₋₁ n) →
-- -- -- -- -- --                SquareP (λ j i → adjT×^≡-invol {A = Bool} n (fst k) j i  → hProp ℓ-zero)
-- -- -- -- -- --                   (F×adjSnd {n} (fst k))
-- -- -- -- -- --                   (symP  (F×adjSnd {n} (fst k)))
-- -- -- -- -- --                   (λ _ → Fin×Snd n)
-- -- -- -- -- --                   (λ _ → Fin×Snd n)) →    
-- -- -- -- -- --      SquareP (λ j i → (Σ (adjT×^≡-invol {A = Bool} n (fst k) j i)
-- -- -- -- -- --          (fst ∘ p n k j i)
-- -- -- -- -- --           → A)
-- -- -- -- -- --           ≡ adjT×^≡-invol {A = A} n (fst k) j i)
-- -- -- -- -- --       (tab×adjT× n k)
-- -- -- -- -- --       (symP (tab×adjT× n k))
-- -- -- -- -- --       refl 
-- -- -- -- -- --       refl


-- -- -- -- -- --  tab×adjT×-invol = Nat.cases (λ ())
-- -- -- -- -- --    (Nat.cases (λ ())
-- -- -- -- -- --      (uncurry ∘ flip (Nat.elim
-- -- -- -- -- --       (λ n _ → tab×adjT×-invol0 n)
-- -- -- -- -- --       λ k X → Nat.cases (λ ())
-- -- -- -- -- --        λ n k< p →
-- -- -- -- -- --          congSqP'
-- -- -- -- -- --           {A = λ jj j →
-- -- -- -- -- --              Maybe
-- -- -- -- -- --                (Σ (adjT×^≡-invol (suc (suc n)) k jj j)
-- -- -- -- -- --                 (fst ∘ p (suc (suc n)) (k , k<) jj j))
-- -- -- -- -- --                ≃
-- -- -- -- -- --                Σ (Bool × adjT×^≡-invol (suc (suc n)) k jj j)
-- -- -- -- -- --                (fst ∘ p (suc (suc (suc n))) (suc k , k<) jj j)}
-- -- -- -- -- --           (λ jj j P →
-- -- -- -- -- --              𝑮 (preCompEquiv P ∙ₑ ≃MaybeFunProd)
-- -- -- -- -- --                (λ i → A × (X (n) k< p jj j i)) (idEquiv _))
-- -- -- -- -- --            (ΣSquarePSet
-- -- -- -- -- --               (λ _ _ → isProp→isSet ∘ isPropIsEquiv)
-- -- -- -- -- --               _ _ _ _
-- -- -- -- -- --                 (isSet→SquareP
-- -- -- -- -- --                   (λ jj j → isSet→ (isProp→PathP (λ j →
-- -- -- -- -- --                     isPropIsSet {A = Σ (Bool × adjT×^≡-invol (suc (suc n)) k jj j)
-- -- -- -- -- --                (fst ∘ p (suc (suc (suc n))) (suc k , k<) jj j)})
-- -- -- -- -- --                     (isSetFin× _) (isSetFin× _) j))
-- -- -- -- -- --                   _ _ _ _))
                             
-- -- -- -- -- --           )))

-- -- -- -- -- --  tab×BiadjT×≃< : ∀ k l n → (k< : suc k < suc n) → (l< : suc l < suc n) →
-- -- -- -- -- --                l < k → l < 1 → 
-- -- -- -- -- --               (p : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- --                 SquareP (λ i j →
-- -- -- -- -- --                  biAdjT×^≡-comp {A = Bool} {n = n} k l i j → hProp ℓ-zero)
-- -- -- -- -- --                    (F×adjSnd {n} (fst k))
-- -- -- -- -- --                    (F×adjSnd {n} (fst l))
-- -- -- -- -- --                    (cong snd (F×biAdjT≡' {n = n} k l))
-- -- -- -- -- --                    λ _ → Fin×Snd n)
-- -- -- -- -- --                → 
-- -- -- -- -- --               SquareP
-- -- -- -- -- --               (λ i j → (Σ (biAdjT×^≡-comp
-- -- -- -- -- --                    {A = Bool} {n = suc n} (k , k<) (l , l<) i j)
-- -- -- -- -- --                           (fst ∘ p (suc n) (k , k<) (l , l<) i j) → A ) →
-- -- -- -- -- --                            biAdjT×^≡-comp {A = A} {n = (suc n)} (k , k<) (l , l<) i j)
-- -- -- -- -- --               {!!}
-- -- -- -- -- --               {!!}
-- -- -- -- -- --               {!!}
-- -- -- -- -- --               {!!}
-- -- -- -- -- --               -- (tab×adjT× (suc n) (k , k<))
-- -- -- -- -- --               -- (tab×adjT× (suc n) (l , l<))
-- -- -- -- -- --               -- (tab×biAdjT× (suc n) (k , k<) (l , l<))
-- -- -- -- -- --               -- (refl {x = tab×≡ (suc n)})
-- -- -- -- -- --  tab×BiadjT×≃< = {!!}

-- -- -- -- -- --  -- tab×BiadjT×'<0 : ∀ k l n → (k< : suc k < suc n) → (l< : suc l < suc n) →
-- -- -- -- -- --  --               l < k → l < 1 → 
-- -- -- -- -- --  --              (p : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- --  --                SquareP (λ i j →
-- -- -- -- -- --  --                 biAdjT×^≡-comp {A = Bool} {n = n} k l i j → hProp ℓ-zero)
-- -- -- -- -- --  --                   (F×adjSnd {n} (fst k))
-- -- -- -- -- --  --                   (F×adjSnd {n} (fst l))
-- -- -- -- -- --  --                   (cong snd (F×biAdjT≡' {n = n} k l))
-- -- -- -- -- --  --                   λ _ → Fin×Snd n)
-- -- -- -- -- --  --     → ∀ i jj →
-- -- -- -- -- --  --       PartialP (i ∨ ~ i ∨ jj ∨ ~ jj)
-- -- -- -- -- --  --          λ o → PathP (λ j → Σ (Type ℓ) λ T → T →
-- -- -- -- -- --  --            Σ-swap-01-≡-invol-ua {A = A} {B = tab×≡ n jj} j i)
-- -- -- -- -- --  --               {!!}
-- -- -- -- -- --  --               {!!}
-- -- -- -- -- --  -- tab×BiadjT×'<0 k l n k< l< _ _ p i jj = {!!}
-- -- -- -- -- --  --     -- (λ { (i =  i0) → λ j → tab×≡ (suc (suc n)) jj , fst (tab×≡-ungluing-equiv'2 n jj)
-- -- -- -- -- --  --     --    ; (i = i1) → λ j → tab×≡ (suc (suc n)) jj , fst (tab×≡-ungluing-equiv'2 n jj)
-- -- -- -- -- --  --     --    ; (jj = i0) → λ j → (Σ (Σ-swap-01-≡-invol-ua j i)
-- -- -- -- -- --  --     --                    (fst ∘ p (suc (suc n)) (zero , tt) j i) →
-- -- -- -- -- --  --     --                    A) , tab×adjT×-invol0-jj0 n p i j
-- -- -- -- -- --  --     --    ; (jj = i1) → λ j →  _ , idfun _
-- -- -- -- -- --  --     --    })


-- -- -- -- -- -- --  tab×BiadjT×'< : ∀ k l n → (k< : suc k < suc n) → (l< : suc l < suc n) →
-- -- -- -- -- -- --                l < k → l < 1 → 
-- -- -- -- -- -- --               (p : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- --                 SquareP (λ i j →
-- -- -- -- -- -- --                  biAdjT×^≡-comp {A = Bool} {n = n} k l i j → hProp ℓ-zero)
-- -- -- -- -- -- --                    (F×adjSnd {n} (fst k))
-- -- -- -- -- -- --                    (F×adjSnd {n} (fst l))
-- -- -- -- -- -- --                    (cong snd (F×biAdjT≡' {n = n} k l))
-- -- -- -- -- -- --                    λ _ → Fin×Snd n)
-- -- -- -- -- -- --                → 
-- -- -- -- -- -- --               SquareP
-- -- -- -- -- -- --               (λ i j → (Σ (biAdjT×^≡-comp
-- -- -- -- -- -- --                    {A = Bool} {n = suc n} (k , k<) (l , l<) i j)
-- -- -- -- -- -- --                           (fst ∘ p (suc n) (k , k<) (l , l<) i j) → A ) ≡
-- -- -- -- -- -- --                            biAdjT×^≡-comp {A = A} {n = (suc n)} (k , k<) (l , l<) i j)
-- -- -- -- -- -- --               (tab×adjT× (suc n) (k , k<))
-- -- -- -- -- -- --               (tab×adjT× (suc n) (l , l<))
-- -- -- -- -- -- --               (tab×biAdjT× (suc n) (k , k<) (l , l<))
-- -- -- -- -- -- --               (refl {x = tab×≡ (suc n)})
-- -- -- -- -- -- --  tab×BiadjT×'< (suc zero) zero (suc (suc n)) k< l< x x₁ p =
-- -- -- -- -- -- --    {!!}
-- -- -- -- -- -- --    -- λ i j jj → Glue'
-- -- -- -- -- -- --    --      (Σ-swap-012-≡-comp-ua (λ _ → A × A × A × tab×≡ n jj) i j)
-- -- -- -- -- -- --    --      ?
-- -- -- -- -- -- --    --      -- (primPOr (~ i)
-- -- -- -- -- -- --    --      --          _
-- -- -- -- -- -- --    --      --           (λ _ → tab×adjT× (3 + n) (1 , _) j jj , {!!})
-- -- -- -- -- -- --    --      --          -- (λ { (i = i0) → tab×adjT× (3 + n) (1 , _) j jj ,
-- -- -- -- -- -- --    --      --          --   {!!}
-- -- -- -- -- -- --    --      --          -- ; (i = i1) → tab×adjT× (3 + n) (zero , _) j jj ,
-- -- -- -- -- -- --    --      --          --   {!!} ∘' unglue (j ∨ ~ j ∨ jj ∨ ~ jj)
-- -- -- -- -- -- --    --      --          --   })
-- -- -- -- -- -- --    --      --          (primPOr (j ∨ ~ j) (jj ∨ ~ jj)
-- -- -- -- -- -- --    --      --           (λ { (j = i0) →
-- -- -- -- -- -- --    --      --             tab×biAdjT× (3 + n) (1 , _) (zero , _) i jj , {!!}
-- -- -- -- -- -- --    --      --           ; (j = i1) → tab×≡ (3 + n) jj , {!!} })
-- -- -- -- -- -- --    --      --           (λ { (jj = i0) →
-- -- -- -- -- -- --    --      --             ((Σ (biAdjT×^≡-comp
-- -- -- -- -- -- --    --      --            {A = Bool} {n = 3 + n} (1 , _) (0 , _) i j)
-- -- -- -- -- -- --    --      --                   (fst ∘ p (3 + n) (1 , _) (0 , _) i j) → A )) ,
-- -- -- -- -- -- --    --      --                   {!!}
-- -- -- -- -- -- --    --      --           ; (jj = i1) →
-- -- -- -- -- -- --    --      --            Σ-swap-012-≡-comp-ua (λ _ → A × A × A × (A ×^ n)) i j ,
-- -- -- -- -- -- --    --      --              {!λ x → x!} })))
-- -- -- -- -- -- --    --      -- (λ { (jj = i0) → {!!} , {!!}
-- -- -- -- -- -- --    --      --    ; (jj = i1) → {!!} , {!!}
-- -- -- -- -- -- --    --      --      -- (Σ-swap-012-≡-comp-ua (λ _ → A × A × A × (A ×^ n)) i j)
-- -- -- -- -- -- --    --      --      --   , {!λ x → x!}
-- -- -- -- -- -- --    --      --    ; (j = i0) → tab×biAdjT× (3 + n) (1 , _) (zero , _) i jj , {!!}
-- -- -- -- -- -- --    --      --    ; (j = i1) → tab×≡ (3 + n) jj , {!!}
-- -- -- -- -- -- --    --      --    ; (i = i0) → tab×adjT× (3 + n) (1 , _) j jj , {!!}
-- -- -- -- -- -- --    --      --    ; (i = i1) → tab×adjT× (3 + n) (zero , _) j jj , {!!}
-- -- -- -- -- -- --    --      --    })
-- -- -- -- -- -- --    --        {!!}
-- -- -- -- -- -- --    --      -- λ { (jj = i0) → {!!}
-- -- -- -- -- -- --    --      --    ; (jj = i1) → ?
-- -- -- -- -- -- --    --      --    ; (j = i0) → {!!}
-- -- -- -- -- -- --    --      --    ; (j = i1) → ?
-- -- -- -- -- -- --    --      --    ; (i = i0) → {!!}
-- -- -- -- -- -- --    --      --    ; (i = i1) → {!!}
-- -- -- -- -- -- --    --      --    }
-- -- -- -- -- -- --  tab×BiadjT×'< (suc (suc k)) zero n k< l< x x₁ p = {!!}
 
-- -- -- -- -- -- -- --  tab×BiadjT×' : ∀ k l n → (k< : suc k < suc n) → (l< : suc l < suc n) →
-- -- -- -- -- -- -- --               (p : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- -- --                 SquareP (λ i j →
-- -- -- -- -- -- -- --                  biAdjT×^≡-comp {A = Bool} {n = n} k l i j → hProp ℓ-zero)
-- -- -- -- -- -- -- --                    (F×adjSnd {n} (fst k))
-- -- -- -- -- -- -- --                    (F×adjSnd {n} (fst l))
-- -- -- -- -- -- -- --                    (cong snd (F×biAdjT≡' {n = n} k l))
-- -- -- -- -- -- -- --                    λ _ → Fin×Snd n)
-- -- -- -- -- -- -- --                → 
-- -- -- -- -- -- -- --               SquareP
-- -- -- -- -- -- -- --               (λ i j → (Σ (biAdjT×^≡-comp
-- -- -- -- -- -- -- --                    {A = Bool} {n = suc n} (k , k<) (l , l<) i j)
-- -- -- -- -- -- -- --                           (fst ∘ p (suc n) (k , k<) (l , l<) i j) → A ) ≡
-- -- -- -- -- -- -- --                            biAdjT×^≡-comp {A = A} {n = (suc n)} (k , k<) (l , l<) i j)
-- -- -- -- -- -- -- --               (tab×adjT× (suc n) (k , k<))
-- -- -- -- -- -- -- --               (tab×adjT× (suc n) (l , l<))
-- -- -- -- -- -- -- --               (tab×biAdjT× (suc n) (k , k<) (l , l<))
-- -- -- -- -- -- -- --               refl
-- -- -- -- -- -- -- --  tab×BiadjT×' =
-- -- -- -- -- -- -- --    Nat.elim
-- -- -- -- -- -- -- --      (Nat.cases (Nat.cases (λ ())
-- -- -- -- -- -- -- --       (λ n _ _ p i j jj →
-- -- -- -- -- -- -- --           let q = tab×adjT× (suc (suc n)) (zero , tt)
-- -- -- -- -- -- -- --           in hcomp
-- -- -- -- -- -- -- --              (λ z → primPOr
-- -- -- -- -- -- -- --                (~ jj)
-- -- -- -- -- -- -- --                (i ∨ ~ i ∨ j ∨ ~ j ∨ jj )
-- -- -- -- -- -- -- --                (λ { (jj = i0) →
-- -- -- -- -- -- -- --                  (Σ (biAdjT×^≡-comp
-- -- -- -- -- -- -- --                    {A = Bool} {n = suc (suc n)} (zero , _) (zero , _) i j)
-- -- -- -- -- -- -- --                     (fst ∘
-- -- -- -- -- -- -- --                       ((isSet→SquareP {A = λ i j →
-- -- -- -- -- -- -- --                        Path ((biAdjT×^≡-comp
-- -- -- -- -- -- -- --                    {A = Bool} {n = suc (suc n)} (zero , _) (zero , _) i j)
-- -- -- -- -- -- -- --                     → hProp ℓ-zero)
-- -- -- -- -- -- -- --                        (F×adjSnd {suc (suc n)} zero j)
-- -- -- -- -- -- -- --                          (p (suc (suc n)) (zero , _) (zero , _) i j)}
-- -- -- -- -- -- -- --                         (λ i j → isOfHLevelPath 2
-- -- -- -- -- -- -- --                             (isSet→ isSetHProp) _ _)
-- -- -- -- -- -- -- --                         (λ _ → refl)
-- -- -- -- -- -- -- --                         (λ _ → refl)
-- -- -- -- -- -- -- --                         (λ _ → refl)
-- -- -- -- -- -- -- --                         (λ _ → refl)
-- -- -- -- -- -- -- --                         i j) z))
                 
-- -- -- -- -- -- -- --                   ) → A })
-- -- -- -- -- -- -- --                λ _ → q j jj )
-- -- -- -- -- -- -- --              (q j jj)))
-- -- -- -- -- -- -- --        (λ l → {!!}))
-- -- -- -- -- -- -- --      λ k X → Nat.cases
-- -- -- -- -- -- -- --       {!!}
-- -- -- -- -- -- -- --      λ l → (Nat.cases
-- -- -- -- -- -- -- --        (λ ())
-- -- -- -- -- -- -- --        λ n k< l< p →
-- -- -- -- -- -- -- --         --  let X' = {!X l n k< l< p  !}
-- -- -- -- -- -- -- --         --  in {!!}
-- -- -- -- -- -- -- --         --  )
-- -- -- -- -- -- -- --         congSqP'
-- -- -- -- -- -- -- --           {A = λ jj j →
-- -- -- -- -- -- -- --              Maybe
-- -- -- -- -- -- -- --                (Σ _
-- -- -- -- -- -- -- --                 (fst ∘ p (suc n) (k , k<) (l , l<) jj j))
-- -- -- -- -- -- -- --                ≃
-- -- -- -- -- -- -- --                Σ (Bool ×
-- -- -- -- -- -- -- --                  biAdjT×^≡-comp {A = Bool} {n = suc n} (k , k<) (l , l<) jj j)
-- -- -- -- -- -- -- --                (fst ∘ p (suc (suc n)) (suc k , k<) (suc l , l<) jj j)}
-- -- -- -- -- -- -- --           (λ jj j P →
-- -- -- -- -- -- -- --              𝑮 (preCompEquiv P ∙ₑ ≃MaybeFunProd)
-- -- -- -- -- -- -- --                (λ i → A × X l n k< l< p jj j i) (idEquiv _))
-- -- -- -- -- -- -- --                (ΣSquarePSet
-- -- -- -- -- -- -- --                  (λ i j → isProp→isSet ∘ isPropIsEquiv)
-- -- -- -- -- -- -- --                  _ _ _ _
-- -- -- -- -- -- -- --                   (isSet→SquareP
-- -- -- -- -- -- -- --                     (λ i j → isSet→
-- -- -- -- -- -- -- --                       (isSetΣ {!!}
-- -- -- -- -- -- -- --                         (isProp→isSet ∘
-- -- -- -- -- -- -- --                           snd ∘ (p (suc (suc n)) (suc k , k<) (suc l , l<) i j))))
-- -- -- -- -- -- -- --                     _ _ _ _)))



-- -- -- -- -- -- -- -- -- -- -- -- -- --  tab×BiadjT× : ∀ n → (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- --               (p : ∀ n (k l : Σ ℕ (λ k₁ → suc k₁ < n)) →
-- -- -- -- -- -- -- -- -- -- -- -- -- --                 SquareP (λ i j →
-- -- -- -- -- -- -- -- -- -- -- -- -- --                  biAdjT×^≡-comp {A = Bool} {n = n} k l i j → hProp ℓ-zero)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                    (F×adjSnd {n} (fst k))
-- -- -- -- -- -- -- -- -- -- -- -- -- --                    (F×adjSnd {n} (fst l))
-- -- -- -- -- -- -- -- -- -- -- -- -- --                    (cong snd (F×biAdjT≡' {n = n} k l))
-- -- -- -- -- -- -- -- -- -- -- -- -- --                    λ _ → Fin×Snd n)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                → 
-- -- -- -- -- -- -- -- -- -- -- -- -- --               SquareP
-- -- -- -- -- -- -- -- -- -- -- -- -- --               (λ i j → (Σ (biAdjT×^≡-comp {A = Bool} {n = n} k l i j)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                           (fst ∘ p n k l i j) → A ) ≡
-- -- -- -- -- -- -- -- -- -- -- -- -- --                            biAdjT×^≡-comp {A = A} {n = n} k l i j)
-- -- -- -- -- -- -- -- -- -- -- -- -- --               (tab×adjT× n k)
-- -- -- -- -- -- -- -- -- -- -- -- -- --               (tab×adjT× n l)
-- -- -- -- -- -- -- -- -- -- -- -- -- --               (tab×biAdjT× n k l)
-- -- -- -- -- -- -- -- -- -- -- -- -- --               refl
-- -- -- -- -- -- -- -- -- -- -- -- -- --  tab×BiadjT× (suc n) k l p = tab×BiadjT×' (fst k) (fst l) n (snd k) (snd l) p

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- tab×adjT×-invol (suc (suc (suc n))) (suc k , k<) p jj j i =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --   Glue
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --           (A × tab×adjT×-invol (suc (suc n)) (k , k<) {!p!} jj j i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --           λ { (i = i0) → {!!} , {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --              -- (F×adjT≡ {n = suc (suc n)} (suc k) (~ j) → A) ,
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --              --     preCompEquiv (MaybeFin×AdjTSq≃ (suc n) k (~ j))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --              --       ∙ₑ ≃MaybeFunProd
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --             ; (i = i1) → _ , idEquiv _ }
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- tab×adjT×-invol (suc (suc n)) (zero , k<) p = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- tab×biAdjT× :
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --   ∀ n (k l : Fin₋₁ n) → PathP (λ i → (F×biAdjT≡ {n} k l i → A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --         ≡ biAdjT×^≡ {A = A} {n} l k i)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --      (tab×≡ n) (tab×≡ n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- tab×biAdjT× (suc (suc n)) (suc k , k<) (suc l , l<) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  --   {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- tab×biAdjT× (suc (suc n)) (zero , k<) (zero , l<) = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- tab×biAdjT× (suc (suc n)) (zero , k<) (suc l , l<) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  -- tab×biAdjT× (suc (suc n)) (suc k , k<) (zero , l<) = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isEquivF×adjT : ∀ {n} → ∀ k → isEquiv (F×adjT {n} k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isEquivF×adjT {zero} k = idIsEquiv _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isEquivF×adjT {suc n} (suc k) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isEquivF×adjT {suc zero} zero = idIsEquiv _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isEquivF×adjT {suc (suc n)} zero = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- F×adjT≃ : ∀ {n} → ℕ → (Fin× n) ≃ (Fin× n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- F×adjT≃ k = F×adjT k , {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unglueAdjT× : ∀ n k → PathP (λ i → ua (F×adjT≃ k) i → Fin× n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (fst (F×adjT≃ k)) (idfun (Fin× n))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unglueAdjT× n k = ua-ungluePathExt (F×adjT≃ {n} k) 

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unglueAdjT×' : ∀ n k → PathP (λ i → ua (F×adjT≃ {n} k) i → Fin× n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                 (idfun (Fin× n)) (fst (F×adjT≃ k))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- unglueAdjT×' = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- invol : ∀ {n} → ∀ k → isInvolution (F×adjT {n} k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sectionF×adjT² = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sectionF×adjT² : ∀ {n} → ∀ k → isInvolution (F×adjT {n} k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- sectionF×adjT² = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- isInvol-F×adjT : ∀ {n} → ∀ k → isInvolution (F×adjT {n} k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- fst (isInvol-F×adjT {n} k x i) = {!secEq (adjT×^≃ k) (fst x)!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- snd (isInvol-F×adjT k x i) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- F×adjT≃ : ∀ {n} → ℕ → Iso (Fin× n) (Fin× n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- F×adjT≃ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- F×adjTIso : ∀ {n} → ℕ → Iso (Fin× n) (Fin× n)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.fun (F×adjTIso k) = F×adjT k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.inv (F×adjTIso k) = F×adjT k
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (F×adjTIso k) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (F×adjTIso k) = {!!}
