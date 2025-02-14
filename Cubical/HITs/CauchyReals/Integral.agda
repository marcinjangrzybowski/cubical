module Cubical.HITs.CauchyReals.Integral where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Fin

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ;_ℚ^ⁿ_;_ℚ₊^ⁿ_)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Lems
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative

  -- foldl : ∀ {ℓ'} {B : Type ℓ'} → (B → A → B) → B → List A → B


private
  variable
    ℓ : Level
    A B : Type ℓ


foldlFin : ∀ {n} → (B → A → B) → B → (Fin n → A) → B
foldlFin {n = zero} f b v = b
foldlFin {n = suc n} f b v = foldlFin {n = n} f (f b (v fzero)) (v ∘ fsuc)

record Partition[_,_] (a b : ℝ) : Type₀ where 
 field
  len : ℕ
  pts : Fin (1 ℕ.+ len) → ℝ
  a≤pts : ∀ k → a ≤ᵣ pts k 
  pts≤b : ∀ k → pts k ≤ᵣ b
  pts≤pts : (k : Fin len) → pts (finj k) ≤ᵣ pts (fsuc k)

 diffs : Fin len → Σ ℝ (0 ≤ᵣ_) 
 diffs k = _ , x≤y→0≤y-x (pts (finj k)) _ (pts≤pts k)
 
 mesh : ℝ
 mesh = foldlFin maxᵣ 0 (fst ∘ diffs)

 record Sample : Type₀ where
  field
   samples : Fin len → ℝ
   ≤samples : (k : Fin len) → pts (finj k) ≤ᵣ samples k
   samples≤ : (k : Fin len) → samples k ≤ᵣ pts (fsuc k)
   
  samplesΣ : Fin len → Σ[ t ∈ ℝ ] (a ≤ᵣ t ) × (t ≤ᵣ b)
  samplesΣ k = (samples k) ,
    ((isTrans≤ᵣ a _ _ (a≤pts (finj k)) (≤samples k))
           , isTrans≤ᵣ (samples k) _ _ (samples≤ k) (pts≤b (fsuc k)))
  
  riemannSum : (∀ r → a ≤ᵣ r → r ≤ᵣ b → ℝ) → ℝ
  riemannSum f = foldlFin
    (λ S ((t , a≤t , t≤b) , b-a) → S +ᵣ b-a ·ᵣ (f t a≤t t≤b) ) 0
     (λ k →  samplesΣ k , pts (fsuc k) -ᵣ pts (finj k))

  riemannSum' : (ℝ → ℝ) → ℝ
  riemannSum' f = foldlFin
    (λ S ((t , a≤t , t≤b) , b-a) → S +ᵣ b-a ·ᵣ (f t) ) 0
     (λ k →  samplesΣ k , pts (fsuc k) -ᵣ pts (finj k))

 open Sample public
open Partition[_,_] 

TaggedPartition[_,_] : ℝ → ℝ → Type
TaggedPartition[ a , b ] = Σ (Partition[ a , b ]) Sample


on[_,_]IntegralOf_is_ : ∀ a b → (∀ r → a ≤ᵣ r → r ≤ᵣ b → ℝ) → ℝ → Type
on[ a , b ]IntegralOf f is s =
   ∀ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
     ∀ ((p , t) : TaggedPartition[ a , b ]) →
     (mesh p <ᵣ rat (fst δ) →
       absᵣ (riemannSum t f -ᵣ s) <ᵣ rat (fst ε))

on[_,_]IntegralOf_is'_ : ∀ a b → (ℝ → ℝ) → ℝ → Type
on[ a , b ]IntegralOf f is' s =  
   ∀ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
     ∀ ((p , t) : TaggedPartition[ a , b ]) →
     (mesh p <ᵣ rat (fst δ) →
       absᵣ (riemannSum' t f -ᵣ s) <ᵣ rat (fst ε))

-- Integral'-additive : ∀ a b c f s s' →
--   on[ a , b ]IntegralOf f is' s →
--   on[ b , c ]IntegralOf f is' s' →
--   on[ a , c ]IntegralOf f is' (s +ᵣ s')
-- Integral'-additive a b c f s s' S S' ε =
--   let P = S  (/2₊ ε)
--       P' = S' (/2₊ ε)
--   in PT.map2 {!!} P P'
     


-- FTOC : ∀ x₀ (f F : ℝ → ℝ)
--                  → (∀ x → x₀ ≤ᵣ x → on[ x₀ , x ]IntegralOf f is' F x)
--                  → ∀ x → x₀ ≤ᵣ x → derivativeOf F at x is' f x
-- FTOC x₀ f F D x x₀≤x ε =
--   PT.map2 (λ (δ , X) (δ' , X') →
--    let δ* = ℚ.min₊ (ℚ.min₊ δ δ') ε
--        ((tp , tp') , (tpm , tpm')) = tps x (ε) δ*
--        z : absᵣ ((riemannSum' (snd tp) f -ᵣ F x)
--              +ᵣ ((F (x +ᵣ rat (fst ε))) -ᵣ riemannSum' (snd tp') f))  <ᵣ rat (fst (ε ℚ₊· ε))
--        z = isTrans≤<ᵣ
--               (absᵣ ((riemannSum' (snd tp) f -ᵣ F x)
--              +ᵣ ((F (x +ᵣ rat (fst ε))) -ᵣ riemannSum' (snd tp') f)))
--               _ _ (absᵣ-triangle
--                (riemannSum' (snd tp) f -ᵣ F x)
--                 ((F (x +ᵣ rat (fst ε))) -ᵣ riemannSum' (snd tp') f))
--              (isTrans<≡ᵣ (absᵣ (((riemannSum' (snd tp) f -ᵣ F x)))
--                      +ᵣ absᵣ (((F (x +ᵣ rat (fst ε))
--                  -ᵣ (riemannSum' (snd tp') f))))) _ _
--             (<ᵣMonotone+ᵣ
--               (absᵣ ((riemannSum' (snd tp) f -ᵣ F x))) _
--                (absᵣ ((F (x +ᵣ rat (fst ε))
--                  -ᵣ (riemannSum' (snd tp') f)))) _
--                 (X tp (isTrans<≤ᵣ (mesh (fst tp)) _ _ tpm
--                    (( (
--                       (≤ℚ→≤ᵣ (fst δ*) (fst δ)
--                        (ℚ.isTrans≤ (fst δ*) _ (fst δ)
--                         ((ℚ.min≤ (ℚ.min (fst δ)  (fst δ') ) (fst ε)))
--                          (ℚ.min≤ (fst δ) (fst δ'))))))) ))
--                 ((isTrans≡<ᵣ _ _ _
--                   (minusComm-absᵣ (F (x +ᵣ rat (fst ε)))
--                    (riemannSum' (snd tp') f)) (X' tp'
--                      (isTrans<≤ᵣ (mesh (fst tp')) _ _ tpm' (
--                       (≤ℚ→≤ᵣ (fst δ*) (fst δ')
--                        (ℚ.isTrans≤ (fst δ*) _ (fst δ')
--                         ((ℚ.min≤ (ℚ.min (fst δ)  (fst δ') ) (fst ε)))
--                          (ℚ.min≤' (fst δ) (fst δ'))))))))))
--              (cong rat (ℚ.ε/2+ε/2≡ε _)))
--        z' = subst2 {x = rat (fst (invℚ₊ ε))
--                  ·ᵣ (absᵣ ((riemannSum' (snd tp) f -ᵣ F x)
--              +ᵣ ((F (x +ᵣ rat (fst ε))) -ᵣ riemannSum' (snd tp') f)))}
--               {absᵣ
--                (f x -ᵣ differenceAt F x (rat (fst ε)) (inl {!!})) }
--                  _<ᵣ_
--               ({!!}) (sym (rat·ᵣrat _ _) ∙
--                       cong rat (ℚ.[y·x]/y ε _) )
--               (<ᵣ-o·ᵣ
--                 (absᵣ ((riemannSum' (snd tp) f -ᵣ F x)
--              +ᵣ ((F (x +ᵣ rat (fst ε))) -ᵣ riemannSum' (snd tp') f)))
--                 _ (ℚ₊→ℝ₊ (invℚ₊ ε)) z)
--        zz' = {!z!}
--    in δ* ,
--       λ h → ⊎.elim
--        (λ 0<h h<δ* →
--          let zz : absᵣ (h ·ᵣ f x -ᵣ
--                         (F (x +ᵣ h) -ᵣ F x)
--                         )
--                       <ᵣ h ·ᵣ rat (fst ε)
--              zz = {!z!}     
--          in {!!})
--        {!!})
--     (D x x₀≤x (/2₊ (ε ℚ₊· ε))) (D (x +ᵣ rat (fst ε)) {!!} (/2₊ (ε ℚ₊· ε)))

--  where
--   tps : ∀ x (ε δ : ℚ₊) → Σ (TaggedPartition[ x₀ , x ]
--               × TaggedPartition[ x₀ , x +ᵣ rat (fst ε)  ])
--                 λ (tp ,  tp') → (mesh (fst tp) <ᵣ rat (fst δ))
--                      × (mesh (fst tp') <ᵣ rat (fst δ))
--   tps x h δ = {!!}
  
--   -- PT.map (λ (δ , X)
--   --   → let δ' = {!!}
--   --     in δ' ,
--   --         (λ h → ⊎.elim
--   --           (λ 0<h h<δ' →
--   --             let rs : Σ Partition[ x , x +ᵣ fst η ] Sample
--   --                 rs = {!!} , {!!}
--   --                 z = X rs {!X!}
--   --                 z' =
--   --                     isTrans≡<ᵣ _
--   --                        ((absᵣ (riemannSum' (snd rs) f -ᵣ G η)
--   --                          ·ᵣ invℝ h (inl 0<h)) ·ᵣ invℝ h (inl 0<h)) _
--   --                        (cong absᵣ (sym (·DistR+ (riemannSum' (snd rs) f)
--   --                          (G η) _)) ∙
--   --                          (·absᵣ (riemannSum' {_} {_} {fst rs} (snd rs) f -ᵣ G η) (invℝ h (inl 0<h)) ∙
--   --                           cong ((absᵣ (riemannSum' (snd rs) f -ᵣ G η)
--   --                          ·ᵣ invℝ h (inl 0<h)) ·ᵣ_) ((absᵣPos
--   --                           (invℝ h (inl 0<h))
--   --                             (invℝ-pos h 0<h)))))
--   --                         ((<ᵣ-·ᵣo
--   --                         (absᵣ (riemannSum' (snd rs) f -ᵣ G η))
--   --                          (rat (fst θ)) (invℝ h (inl 0<h) , invℝ-pos h 0<h) z))
--   --             in {!z'!})
--   --           {!!}))
--   --   (G= η θ)

--  -- where

--  -- η = {!!}

--  -- θ = {!!}

--  -- G : ∀ (h : ℝ₊) → ℝ 
--  -- G h = F (x +ᵣ fst h) -ᵣ F x

--  -- G= : ∀ (h : ℝ₊) → on[ x , x +ᵣ fst h ]IntegralOf f is' (G h)
--  -- G= = {!!}
 
--  -- difF : ∀ h 0<h  → differenceAt F x h (inl 0<h) ·ᵣ h ≡
--  --                     G (h , 0<h)
--  -- difF h 0＃h = {!!}
 
-- -- -- derivativeOf_at_is_






-- -- -- private
-- -- --   variable
-- -- --     ℓ : Level
-- -- --     A B : Type ℓ


-- -- -- foldlFin : ∀ {n} → (B → A → B) → B → (Fin n → A) → B
-- -- -- foldlFin {n = zero} f b v = b
-- -- -- foldlFin {n = suc n} f b v = foldlFin {n = n} f (f b (v fzero)) (v ∘ fsuc)

-- -- -- record Partition[_,_] (a b : ℝ) : Type₀ where 
-- -- --  field
-- -- --   len : ℕ
-- -- --   pts : Fin (1 ℕ.+ len) → ℝ
-- -- --   a≤pts : ∀ k → a ≤ᵣ pts k 
-- -- --   pts≤b : ∀ k → pts k ≤ᵣ b
-- -- --   pts≤pts : (k : Fin len) → pts (finj k) ≤ᵣ pts (fsuc k)

-- -- --  diffs : Fin len → Σ ℝ (0 ≤ᵣ_) 
-- -- --  diffs k = _ , x≤y→0≤y-x (pts (finj k)) _ (pts≤pts k)
 
-- -- --  mesh : ℝ
-- -- --  mesh = foldlFin maxᵣ 0 (fst ∘ diffs)

-- -- --  record Sample : Type₀ where
-- -- --   field
-- -- --    samples : Fin len → ℝ
-- -- --    ≤samples : (k : Fin len) → pts (finj k) ≤ᵣ samples k
-- -- --    samples≤ : (k : Fin len) → samples k ≤ᵣ pts (fsuc k)
   
-- -- --   samplesΣ : Fin len → Σ[ t ∈ ℝ ] (a ≤ᵣ t ) × (t ≤ᵣ b)
-- -- --   samplesΣ = {!!}
  
-- -- --   riemannSum : (∀ r → a ≤ᵣ r → r ≤ᵣ b → ℝ) → ℝ
-- -- --   riemannSum f = foldlFin
-- -- --     (λ S ((t , a≤t , t≤b) , b-a) → S +ᵣ b-a ·ᵣ (f t a≤t t≤b) ) 0
-- -- --      (λ k →  samplesΣ k , pts (fsuc k) -ᵣ pts (finj k))

-- -- --  open Sample public
-- -- -- open Partition[_,_] 

-- -- -- TaggedPartition[_,_] : ℝ → ℝ → Type
-- -- -- TaggedPartition[ a , b ] = Σ (Partition[ a , b ]) Sample


-- -- -- on[_,_]IntegralOf_is_ : ∀ a b → (∀ r → a ≤ᵣ r → r ≤ᵣ b → ℝ) → ℝ → Type
-- -- -- on[ a , b ]IntegralOf f is s =
-- -- --   ∀ ((p , t) : TaggedPartition[ a , b ]) →
-- -- --    ∀ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
-- -- --      (mesh p <ᵣ rat (fst δ) →
-- -- --        absᵣ (riemannSum t f -ᵣ s) <ᵣ rat (fst ε))


-- -- -- FTOC : ∀ a b (f F : ∀ r → a ≤ᵣ r → r ≤ᵣ b → ℝ)
-- -- --                  → (∀ x → (≤x : a ≤ᵣ x) → (x≤ : x ≤ᵣ b)
-- -- --                      → on[ a , x ]IntegralOf
-- -- --                          (λ r ≤r r≤ → f r ≤r (isTrans≤ᵣ r _ _ r≤ x≤))
-- -- --                            is F x ≤x x≤)
-- -- --                  → ∀ x → (≤x : a ≤ᵣ x) → (x≤ : x ≤ᵣ b) →
-- -- --                      {!derivativeOf F at ? is ?!}
-- -- -- FTOC = {!!}

-- -- -- -- derivativeOf_at_is_
