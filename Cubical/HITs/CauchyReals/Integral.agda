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

 a≤b : a ≤ᵣ b
 a≤b = isTrans≤ᵣ a _ _ (a≤pts fzero) (pts≤b fzero)
 
 pts'Σ : Fin (3 ℕ.+ len) → Σ[ p ∈ ℝ ] (a ≤ᵣ p) × (p ≤ᵣ b)
 pts'Σ (zero , l , p) = a , ≤ᵣ-refl a , a≤b
 pts'Σ (suc k , zero , p) = b , a≤b , ≤ᵣ-refl b
 pts'Σ (suc k , suc l , p) = pts (k , l , cong (predℕ ∘ predℕ)
   (sym (ℕ.+-suc (suc l) (suc k)) ∙ p)) , a≤pts _ , pts≤b _

 pts' : Fin (3 ℕ.+ len) → ℝ
 pts' = fst ∘ pts'Σ

 a≤pts' : ∀ k → a ≤ᵣ pts' k
 a≤pts' = fst ∘ snd ∘ pts'Σ
 
 pts'≤b : ∀ k → pts' k ≤ᵣ b
 pts'≤b = snd ∘ snd ∘ pts'Σ

 pts'≤pts' : ∀ k → pts' (finj k) ≤ᵣ pts' (fsuc k)
 pts'≤pts' (zero , l , p) = a≤pts' (1 , l , +-suc _ _ ∙ cong suc p)
 pts'≤pts' k'@(suc k , zero , p) =
  let z = pts'≤b (suc k , 1 , cong suc p)      
  in isTrans≡≤ᵣ (pts' (finj k'))
        (pts' (suc k , 1 , (λ i → suc (p i))))
        _ (cong {x = finj k'}
                {(suc k , 1 , cong suc p)} pts'
                 (toℕ-injective refl)) z
 pts'≤pts' (suc k , suc l , p) =
   let k' = k , l , cong (predℕ ∘ predℕ)
               (sym (ℕ.+-suc (suc l) (suc k)) ∙ p) 
   in subst2 _≤ᵣ_ 
         (cong (λ u → pts (k , l ℕ.+ (suc zero) , u))
           (isSetℕ _ _ _ _))
         (cong (λ u → pts (suc k , l , u))
           (isSetℕ _ _ _ _))
         (pts≤pts k')


 record Sample : Type₀ where
  field
   samples : Fin (2 ℕ.+ len) → ℝ
   pts'≤samples : (k : Fin _) → pts' (finj k) ≤ᵣ samples k 
   samples≤pts' : (k : Fin _) → samples k ≤ᵣ pts' (fsuc k)


  a≤samples : ∀ k → a  ≤ᵣ samples k
  a≤samples k = isTrans≤ᵣ a _ _ (a≤pts' (finj k)) (pts'≤samples k)

  samples≤b : ∀ k → samples k ≤ᵣ b
  samples≤b k = isTrans≤ᵣ (samples k) _ b (samples≤pts' k) (pts'≤b (fsuc k))
  
  samplesΣ : Fin (2 ℕ.+ len) → Σ[ t ∈ ℝ ] (a ≤ᵣ t ) × (t ≤ᵣ b)
  samplesΣ k = samples k , a≤samples k , samples≤b k
  
  riemannSum : (∀ r → a ≤ᵣ r → r ≤ᵣ b → ℝ) → ℝ
  riemannSum f = foldlFin
    (λ S ((t , a≤t , t≤b) , b-a) → S +ᵣ b-a ·ᵣ (f t a≤t t≤b) ) 0
     (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))

  riemannSum' : (ℝ → ℝ) → ℝ
  riemannSum' f = foldlFin
    (λ S ((t , a≤t , t≤b) , b-a) → S +ᵣ b-a ·ᵣ (f t) ) 0
     (λ k →  samplesΣ k , pts' (fsuc k) -ᵣ pts' (finj k))

 open Sample public
 
 leftSample : Sample
 leftSample .samples = pts' ∘ finj
 leftSample .pts'≤samples = ≤ᵣ-refl ∘ pts' ∘ finj 
 leftSample .samples≤pts' = pts'≤pts'

 rightSample : Sample
 rightSample .samples = pts' ∘ fsuc
 rightSample .pts'≤samples = pts'≤pts'
 rightSample .samples≤pts' = ≤ᵣ-refl ∘ pts' ∘ fsuc 


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


0≤pos/ : ∀ {p q} → 0 ℚ.≤ [ pos p / q ] 
0≤pos/ {p} {q} =
  subst (0 ℤ.≤_) (sym (ℤ.·IdR _))
    (ℤ.ℕ≤→pos-≤-pos 0 p ℕ.zero-≤)


module _ a b (a≤b : a ≤ᵣ b) where


 Δ : ℝ
 Δ = b -ᵣ a

 0≤Δ : 0 ≤ᵣ Δ
 0≤Δ = x≤y→0≤y-x a _ a≤b 
 

 uContMesh : ∀ f → IsUContinuous f →
        ∀ (ε₊ : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
                  (∀ ((p , t) : TaggedPartition[ a , b ]) →
                     (mesh p <ᵣ rat (fst δ) →
                       absᵣ (riemannSum' t f -ᵣ
                             riemannSum' (leftSample p) f)
                          <ᵣ Δ ·ᵣ rat (fst ε₊)))
 uContMesh = {!!}

 module _ (n : ℕ) where

  t : Fin (suc n) → ℚ
  t (k , _) = [ pos k / 1+ n ]

  0≤t : ∀ k → 0 ≤ᵣ rat (t k)
  0≤t k = ≤ℚ→≤ᵣ 0 (t k) (0≤pos/ {fst k} {1+ n})

  t≤1 : ∀ k → rat (t k) ≤ᵣ 1
  t≤1 k = ≤ℚ→≤ᵣ (t k) 1 w 
   where
   w : pos (k .fst) ℤ.· ℚ.ℕ₊₁→ℤ 1 ℤ.≤ pos 1 ℤ.· ℚ.ℕ₊₁→ℤ (1+ n)
   w = subst2 ℤ._≤_ (sym (ℤ.·IdR _)) (sym (ℤ.·IdL _))
          (ℤ.ℕ≤→pos-≤-pos (fst k) _ (ℕ.≤-suc $ ℕ.predℕ-≤-predℕ (snd k)))

  tIncr : ∀ k → t (finj k) ℚ.≤ t (fsuc k)
  tIncr k = ℤ.≤-·o {m = pos (toℕ k)} {n = pos (suc (toℕ k))} {k = suc n}
            (ℤ.ℕ≤→pos-≤-pos _ _ ℕ.≤-sucℕ)

  equalPartition : Partition[ a , b ] 
  equalPartition .len = n
  equalPartition .pts k = a +ᵣ Δ ·ᵣ (rat (t k)) 
  equalPartition .a≤pts k =
    isTrans≡≤ᵣ a (a +ᵣ Δ ·ᵣ 0) _ 
      (sym (𝐑'.+IdR' _ _ (𝐑'.0RightAnnihilates _)))
       (≤ᵣ-o+ (Δ ·ᵣ 0) (Δ ·ᵣ (rat (t k))) a
         (≤ᵣ-o·ᵣ 0 (rat (t k)) Δ  0≤Δ (0≤t k))) 
  equalPartition .pts≤b k = 
    isTrans≤≡ᵣ (a +ᵣ Δ ·ᵣ rat (t k)) (a +ᵣ Δ) b
    (≤ᵣ-o+ _ _ a
     (isTrans≤≡ᵣ (Δ ·ᵣ rat (t k)) (Δ ·ᵣ 1) Δ
      (≤ᵣ-o·ᵣ (rat (t k)) 1 Δ  0≤Δ (t≤1 k)) (·IdR Δ)))
      (L𝐑.lem--05 {a} {b})
  equalPartition .pts≤pts k =
     ≤ᵣ-o+ _ _ a (≤ᵣ-o·ᵣ (rat (t (finj k))) (rat (t (fsuc k))) Δ  0≤Δ
      (≤ℚ→≤ᵣ (t (finj k)) _ (tIncr k)))




Integrate-UContinuous : ∀ a b → a ≤ᵣ b → ∀ f → IsUContinuous f → ℝ
Integrate-UContinuous a b a≤b f ucf =
 fromCauchySequence s c

 where
 s : Seq
 s n = riemannSum'
        (leftSample (equalPartition a b a≤b n))
         f

 c : IsCauchySequence s
 c ε = {!!}
 

-- -- Integral'-additive : ∀ a b c f s s' →
-- --   on[ a , b ]IntegralOf f is' s →
-- --   on[ b , c ]IntegralOf f is' s' →
-- --   on[ a , c ]IntegralOf f is' (s +ᵣ s')
-- -- Integral'-additive a b c f s s' S S' ε =
-- --   let P = S  (/2₊ ε)
-- --       P' = S' (/2₊ ε)
-- --   in PT.map2 {!!} P P'
     


-- -- FTOC : ∀ x₀ (f F : ℝ → ℝ)
-- --                  → (∀ x → x₀ ≤ᵣ x → on[ x₀ , x ]IntegralOf f is' F x)
-- --                  → ∀ x → x₀ ≤ᵣ x → derivativeOf F at x is' f x
-- -- FTOC x₀ f F D x x₀≤x ε =
-- --   PT.map2 (λ (δ , X) (δ' , X') →
-- --    let δ* = ℚ.min₊ (ℚ.min₊ δ δ') ε
-- --        ((tp , tp') , (tpm , tpm')) = tps x (ε) δ*
-- --        z : absᵣ ((riemannSum' (snd tp) f -ᵣ F x)
-- --              +ᵣ ((F (x +ᵣ rat (fst ε))) -ᵣ riemannSum' (snd tp') f))  <ᵣ rat (fst (ε ℚ₊· ε))
-- --        z = isTrans≤<ᵣ
-- --               (absᵣ ((riemannSum' (snd tp) f -ᵣ F x)
-- --              +ᵣ ((F (x +ᵣ rat (fst ε))) -ᵣ riemannSum' (snd tp') f)))
-- --               _ _ (absᵣ-triangle
-- --                (riemannSum' (snd tp) f -ᵣ F x)
-- --                 ((F (x +ᵣ rat (fst ε))) -ᵣ riemannSum' (snd tp') f))
-- --              (isTrans<≡ᵣ (absᵣ (((riemannSum' (snd tp) f -ᵣ F x)))
-- --                      +ᵣ absᵣ (((F (x +ᵣ rat (fst ε))
-- --                  -ᵣ (riemannSum' (snd tp') f))))) _ _
-- --             (<ᵣMonotone+ᵣ
-- --               (absᵣ ((riemannSum' (snd tp) f -ᵣ F x))) _
-- --                (absᵣ ((F (x +ᵣ rat (fst ε))
-- --                  -ᵣ (riemannSum' (snd tp') f)))) _
-- --                 (X tp (isTrans<≤ᵣ (mesh (fst tp)) _ _ tpm
-- --                    (( (
-- --                       (≤ℚ→≤ᵣ (fst δ*) (fst δ)
-- --                        (ℚ.isTrans≤ (fst δ*) _ (fst δ)
-- --                         ((ℚ.min≤ (ℚ.min (fst δ)  (fst δ') ) (fst ε)))
-- --                          (ℚ.min≤ (fst δ) (fst δ'))))))) ))
-- --                 ((isTrans≡<ᵣ _ _ _
-- --                   (minusComm-absᵣ (F (x +ᵣ rat (fst ε)))
-- --                    (riemannSum' (snd tp') f)) (X' tp'
-- --                      (isTrans<≤ᵣ (mesh (fst tp')) _ _ tpm' (
-- --                       (≤ℚ→≤ᵣ (fst δ*) (fst δ')
-- --                        (ℚ.isTrans≤ (fst δ*) _ (fst δ')
-- --                         ((ℚ.min≤ (ℚ.min (fst δ)  (fst δ') ) (fst ε)))
-- --                          (ℚ.min≤' (fst δ) (fst δ'))))))))))
-- --              (cong rat (ℚ.ε/2+ε/2≡ε _)))
-- --        z' = subst2 {x = rat (fst (invℚ₊ ε))
-- --                  ·ᵣ (absᵣ ((riemannSum' (snd tp) f -ᵣ F x)
-- --              +ᵣ ((F (x +ᵣ rat (fst ε))) -ᵣ riemannSum' (snd tp') f)))}
-- --               {absᵣ
-- --                (f x -ᵣ differenceAt F x (rat (fst ε)) (inl {!!})) }
-- --                  _<ᵣ_
-- --               ({!!}) (sym (rat·ᵣrat _ _) ∙
-- --                       cong rat (ℚ.[y·x]/y ε _) )
-- --               (<ᵣ-o·ᵣ
-- --                 (absᵣ ((riemannSum' (snd tp) f -ᵣ F x)
-- --              +ᵣ ((F (x +ᵣ rat (fst ε))) -ᵣ riemannSum' (snd tp') f)))
-- --                 _ (ℚ₊→ℝ₊ (invℚ₊ ε)) z)
-- --        zz' = {!z!}
-- --    in δ* ,
-- --       λ h → ⊎.elim
-- --        (λ 0<h h<δ* →
-- --          let zz : absᵣ (h ·ᵣ f x -ᵣ
-- --                         (F (x +ᵣ h) -ᵣ F x)
-- --                         )
-- --                       <ᵣ h ·ᵣ rat (fst ε)
-- --              zz = {!z!}     
-- --          in {!!})
-- --        {!!})
-- --     (D x x₀≤x (/2₊ (ε ℚ₊· ε))) (D (x +ᵣ rat (fst ε)) {!!} (/2₊ (ε ℚ₊· ε)))

-- --  where
-- --   tps : ∀ x (ε δ : ℚ₊) → Σ (TaggedPartition[ x₀ , x ]
-- --               × TaggedPartition[ x₀ , x +ᵣ rat (fst ε)  ])
-- --                 λ (tp ,  tp') → (mesh (fst tp) <ᵣ rat (fst δ))
-- --                      × (mesh (fst tp') <ᵣ rat (fst δ))
-- --   tps x h δ = {!!}
  
-- --   -- PT.map (λ (δ , X)
-- --   --   → let δ' = {!!}
-- --   --     in δ' ,
-- --   --         (λ h → ⊎.elim
-- --   --           (λ 0<h h<δ' →
-- --   --             let rs : Σ Partition[ x , x +ᵣ fst η ] Sample
-- --   --                 rs = {!!} , {!!}
-- --   --                 z = X rs {!X!}
-- --   --                 z' =
-- --   --                     isTrans≡<ᵣ _
-- --   --                        ((absᵣ (riemannSum' (snd rs) f -ᵣ G η)
-- --   --                          ·ᵣ invℝ h (inl 0<h)) ·ᵣ invℝ h (inl 0<h)) _
-- --   --                        (cong absᵣ (sym (·DistR+ (riemannSum' (snd rs) f)
-- --   --                          (G η) _)) ∙
-- --   --                          (·absᵣ (riemannSum' {_} {_} {fst rs} (snd rs) f -ᵣ G η) (invℝ h (inl 0<h)) ∙
-- --   --                           cong ((absᵣ (riemannSum' (snd rs) f -ᵣ G η)
-- --   --                          ·ᵣ invℝ h (inl 0<h)) ·ᵣ_) ((absᵣPos
-- --   --                           (invℝ h (inl 0<h))
-- --   --                             (invℝ-pos h 0<h)))))
-- --   --                         ((<ᵣ-·ᵣo
-- --   --                         (absᵣ (riemannSum' (snd rs) f -ᵣ G η))
-- --   --                          (rat (fst θ)) (invℝ h (inl 0<h) , invℝ-pos h 0<h) z))
-- --   --             in {!z'!})
-- --   --           {!!}))
-- --   --   (G= η θ)

-- --  -- where

-- --  -- η = {!!}

-- --  -- θ = {!!}

-- --  -- G : ∀ (h : ℝ₊) → ℝ 
-- --  -- G h = F (x +ᵣ fst h) -ᵣ F x

-- --  -- G= : ∀ (h : ℝ₊) → on[ x , x +ᵣ fst h ]IntegralOf f is' (G h)
-- --  -- G= = {!!}
 
-- --  -- difF : ∀ h 0<h  → differenceAt F x h (inl 0<h) ·ᵣ h ≡
-- --  --                     G (h , 0<h)
-- --  -- difF h 0＃h = {!!}
 
-- -- -- -- derivativeOf_at_is_






-- -- -- -- private
-- -- -- --   variable
-- -- -- --     ℓ : Level
-- -- -- --     A B : Type ℓ


-- -- -- -- foldlFin : ∀ {n} → (B → A → B) → B → (Fin n → A) → B
-- -- -- -- foldlFin {n = zero} f b v = b
-- -- -- -- foldlFin {n = suc n} f b v = foldlFin {n = n} f (f b (v fzero)) (v ∘ fsuc)

-- -- -- -- record Partition[_,_] (a b : ℝ) : Type₀ where 
-- -- -- --  field
-- -- -- --   len : ℕ
-- -- -- --   pts : Fin (1 ℕ.+ len) → ℝ
-- -- -- --   a≤pts : ∀ k → a ≤ᵣ pts k 
-- -- -- --   pts≤b : ∀ k → pts k ≤ᵣ b
-- -- -- --   pts≤pts : (k : Fin len) → pts (finj k) ≤ᵣ pts (fsuc k)

-- -- -- --  diffs : Fin len → Σ ℝ (0 ≤ᵣ_) 
-- -- -- --  diffs k = _ , x≤y→0≤y-x (pts (finj k)) _ (pts≤pts k)
 
-- -- -- --  mesh : ℝ
-- -- -- --  mesh = foldlFin maxᵣ 0 (fst ∘ diffs)

-- -- -- --  record Sample : Type₀ where
-- -- -- --   field
-- -- -- --    samples : Fin len → ℝ
-- -- -- --    ≤samples : (k : Fin len) → pts (finj k) ≤ᵣ samples k
-- -- -- --    samples≤ : (k : Fin len) → samples k ≤ᵣ pts (fsuc k)
   
-- -- -- --   samplesΣ : Fin len → Σ[ t ∈ ℝ ] (a ≤ᵣ t ) × (t ≤ᵣ b)
-- -- -- --   samplesΣ = {!!}
  
-- -- -- --   riemannSum : (∀ r → a ≤ᵣ r → r ≤ᵣ b → ℝ) → ℝ
-- -- -- --   riemannSum f = foldlFin
-- -- -- --     (λ S ((t , a≤t , t≤b) , b-a) → S +ᵣ b-a ·ᵣ (f t a≤t t≤b) ) 0
-- -- -- --      (λ k →  samplesΣ k , pts (fsuc k) -ᵣ pts (finj k))

-- -- -- --  open Sample public
-- -- -- -- open Partition[_,_] 

-- -- -- -- TaggedPartition[_,_] : ℝ → ℝ → Type
-- -- -- -- TaggedPartition[ a , b ] = Σ (Partition[ a , b ]) Sample


-- -- -- -- on[_,_]IntegralOf_is_ : ∀ a b → (∀ r → a ≤ᵣ r → r ≤ᵣ b → ℝ) → ℝ → Type
-- -- -- -- on[ a , b ]IntegralOf f is s =
-- -- -- --   ∀ ((p , t) : TaggedPartition[ a , b ]) →
-- -- -- --    ∀ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
-- -- -- --      (mesh p <ᵣ rat (fst δ) →
-- -- -- --        absᵣ (riemannSum t f -ᵣ s) <ᵣ rat (fst ε))


-- -- -- -- FTOC : ∀ a b (f F : ∀ r → a ≤ᵣ r → r ≤ᵣ b → ℝ)
-- -- -- --                  → (∀ x → (≤x : a ≤ᵣ x) → (x≤ : x ≤ᵣ b)
-- -- -- --                      → on[ a , x ]IntegralOf
-- -- -- --                          (λ r ≤r r≤ → f r ≤r (isTrans≤ᵣ r _ _ r≤ x≤))
-- -- -- --                            is F x ≤x x≤)
-- -- -- --                  → ∀ x → (≤x : a ≤ᵣ x) → (x≤ : x ≤ᵣ b) →
-- -- -- --                      {!derivativeOf F at ? is ?!}
-- -- -- -- FTOC = {!!}

-- -- -- -- -- derivativeOf_at_is_
