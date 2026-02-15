module Cubical.HITs.CauchyReals.Summation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Powerset
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
import Cubical.Data.Nat.Order.Inductive as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Fin

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals.Fast as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Fast.Order as ℚ using
  ( _ℚ₊+_ ; 0<_ ; ℚ₊ ; _ℚ₊·_ ; ℚ₊≡)
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚ
 using (invℚ₊;/2₊;/3₊;/4₊;x/2<x;invℚ;_ℚ^ⁿ_;_ℚ₊^ⁿ_)


open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Derivative

open import Cubical.Tactics.CommRingSolverFast.RationalsReflection
open import Cubical.Tactics.CommRingSolverFast.FastRationalsReflection
open import Cubical.Tactics.CommRingSolverFast.IntReflection
open import Cubical.HITs.CauchyReals.LiftingExpr
open import Cubical.Tactics.CommRingSolverFast.RealsReflection

private
  variable
    ℓ : Level
    A A' B B' : Type ℓ

clampCases : ∀ a b → a ℚ.≤ b → ∀ u v → u ℚ.≤ v →
            (ℚ.clamp a b v ℚ.- ℚ.clamp a b u ≡ 0)
              ⊎ ((a ℚ.≤ v) × (u ℚ.≤ b))
clampCases a b a≤b u v u≤v =
  ⊎.rec (λ a≤v →
     ⊎.rec (λ u≤b → inr (a≤v , u≤b))
       (λ b<u → inl
            (cong (ℚ._-_ (ℚ.clamp a b v)) (sym (ℚ.minComm (ℚ.max a v) b ∙∙
           ℚ.≤→min _ (ℚ.max a v) ((ℚ.isTrans≤ b u _ (ℚ.<Weaken≤ b u b<u)
            (ℚ.isTrans≤ u v _ u≤v (ℚ.≤max' a v )))) ∙
            sym (ℚ.≤→min b (ℚ.max a u)
              ((ℚ.isTrans≤ b u _ (ℚ.<Weaken≤ b u b<u)
            ((ℚ.≤max' a u )))))
             ∙∙ ℚ.minComm b (ℚ.max a u))) ∙ ℚ!))
      (ℚ.Dichotomyℚ u b))
   (λ v<a → inl
         (cong (ℚ._-_ (ℚ.clamp a b v)) (sym ((ℚ.minComm (ℚ.max a v) b ∙∙
        cong (ℚ.min b) (ℚ.maxComm a v ∙ ℚ.≤→max v a (ℚ.<Weaken≤ v a v<a) ∙
          sym (ℚ.≤→max u a (ℚ.isTrans≤  u v _ u≤v (ℚ.<Weaken≤ v a v<a)))
           ∙ ℚ.maxComm u a )
       ∙∙ ℚ.minComm b (ℚ.max a u)))) ∙ ℚ!))
   (ℚ.Dichotomyℚ a v)


⊎-⊎-×-rec : A ⊎ B → A' ⊎ B' → (A ⊎ A') ⊎ (B × B')
⊎-⊎-×-rec (inl x) _ = inl (inl x)
⊎-⊎-×-rec (inr _) (inl x) = inl (inr x)
⊎-⊎-×-rec (inr x) (inr x₁) = inr (x , x₁)

≤x→clamp : ∀ L L' x → L' ℚ.≤ x → ℚ.clamp L L' x ≡ L'
≤x→clamp L L' x L'≤x = ℚ.minComm (ℚ.max L x) L'
  ∙ ℚ.≤→min L' (ℚ.max L x) (ℚ.isTrans≤ L' x _ L'≤x (ℚ.≤max' L x))

x≤→clamp : ∀ L L' x → L ℚ.≤ L' → x ℚ.≤ L → ℚ.clamp L L' x ≡ L
x≤→clamp L L' x L≤L' x≤L = ℚ.≤→min (ℚ.max L x) L'
  (subst (ℚ.max L x ℚ.≤_) (ℚ.maxIdem L')
   (ℚ.≤MonotoneMax L L' x L' L≤L' (ℚ.isTrans≤ x L L' x≤L L≤L')) ) ∙
  ℚ.maxComm L x ∙ ℚ.≤→max x L x≤L


clampDegen : ∀ a b x → b ℚ.≤ a → ℚ.clamp a b x ≡ b
clampDegen a b x b≤a =
  ℚ.minComm (ℚ.max a x) b ∙
   ℚ.≤→min _ _ (ℚ.isTrans≤ b a _ b≤a (ℚ.≤max a x))



ℚclampInterval-delta : ∀ a b a' b'
          → a  ℚ.≤ b
          → a' ℚ.≤ b'
               → ℚ.clamp a  b  b' ℚ.- ℚ.clamp a  b  a'
               ≡ ℚ.clamp a' b' b  ℚ.- ℚ.clamp a' b' a
ℚclampInterval-delta a b a' b' a≤b a'≤b' =
 ⊎.rec (⊎.rec
         (hhh a b a' b' a≤b a'≤b'  )
         (sym ∘ hhh a' b' a b a'≤b' a≤b))
       (λ (a≤b' , a'≤b) →
          hhh' a b a' b' a≤b a'≤b' a≤b' a'≤b
           ∙∙ cong₂ ℚ._-_ (ℚ.minComm b' b) (ℚ.maxComm a a') ∙∙
           sym (hhh' a' b' a b a'≤b' a≤b a'≤b a≤b') )
       (⊎-⊎-×-rec
          (ℚ.≤cases b' a)
          (ℚ.≤cases b a'))

  where

  hhh' : ∀ a b a' b'
         → a  ℚ.≤ b
         → a' ℚ.≤ b'
         → a ℚ.≤ b' → a' ℚ.≤ b
              → ℚ.clamp a  b  b' ℚ.- ℚ.clamp a  b  a'
              ≡ ℚ.min b' b ℚ.- ℚ.max a a'
  hhh' a b a' b' a≤b a'≤b' a≤b' a'≤b =
    cong₂ ℚ._-_ (cong (flip ℚ.min b) (ℚ.≤→max a b' a≤b'))
            (ℚ.≤→min (ℚ.max a a') b
             (subst (ℚ.max a a' ℚ.≤_) (ℚ.maxIdem b)
              (ℚ.≤MonotoneMax a b a' b a≤b a'≤b)) )



  hhh : ∀ a b a' b'
         → a  ℚ.≤ b
         → a' ℚ.≤ b'
         → b' ℚ.≤ a
              → ℚ.clamp a  b  b' ℚ.- ℚ.clamp a  b  a'
              ≡ ℚ.clamp a' b' b  ℚ.- ℚ.clamp a' b' a
  hhh a b a' b' a≤b a'≤b' b'≤a =
     cong₂ ℚ._-_ (x≤→clamp a b b' a≤b b'≤a)
                 (x≤→clamp a b a' a≤b (ℚ.isTrans≤ a' b' a a'≤b' b'≤a))
      ∙∙ ℚ.+InvR a ∙ sym (ℚ.+InvR b') ∙∙
      cong₂ ℚ._-_
        (sym (≤x→clamp a' b' b (ℚ.isTrans≤ b' a b b'≤a a≤b)))
        (sym (≤x→clamp a' b' a b'≤a))

clamp-dist : ∀ a b x y →
  ℚ.abs (ℚ.clamp a b x ℚ.- ℚ.clamp a b y) ℚ.≤ ℚ.abs (b ℚ.- a)
clamp-dist a b =
  ⊎.rec
    (λ a≤b →
      ℚ.elimBy≤
       (λ x y X →
         subst (ℚ._≤ ℚ.abs (b ℚ.- a))
          (ℚ.absComm- (ℚ.clamp a b x) (ℚ.clamp a b y)) X)
       λ x y x≤y →
         subst (ℚ._≤ ℚ.abs (b ℚ.- a))
           (cong ℚ.abs
             (sym (ℚclampInterval-delta a b x y a≤b x≤y))
           ∙ ℚ.absComm- (ℚ.clamp a b y) (ℚ.clamp a b x))
           (ℚ.clampDist x y a b))
    (λ b≤a x y →
      subst (ℚ._≤ ℚ.abs (b ℚ.- a))
       (cong {x = 0} ℚ.abs (ℚ! ∙ cong (ℚ._-_ (ℚ.clamp a b x) ) (clampDegen a b x b≤a ∙ sym (clampDegen a b y b≤a))))
       
       (ℚ.0≤abs (b ℚ.- a)) )
   (ℚ.≤cases a b)

opaque
 unfolding minᵣ
 clampᵣ-dist : ∀ a b x y → absᵣ (clampᵣ a b x -ᵣ clampᵣ a b y) ≤ᵣ absᵣ (b -ᵣ a)
 clampᵣ-dist a b x y = ≤Cont₂
  {f₀ x y} {λ a b → absᵣ (b -ᵣ a)}
  (cont∘₂ IsContinuousAbsᵣ
         (IsContinuous-₂∘ (IsContinuousClamp₂ _) (IsContinuousClamp₂ _)))
    ((cont∘₂ IsContinuousAbsᵣ
         (IsContinuous-₂∘

           ((λ _ → IsContinuousId) , ((λ _ → IsContinuousConst _)))
           (((λ _ → IsContinuousConst _)) ,
             (λ _ → IsContinuousId))) ))
   (λ aℚ bℚ →  let a = (rat aℚ) ; b = (rat bℚ) in
     ≤Cont₂ {λ x y → f₀ x y a b} {λ _ _ → absᵣ (b -ᵣ a)}
       (cont∘₂ IsContinuousAbsᵣ
         (IsContinuous-₂∘
           (((λ _ → IsContinuousConst _)) ,
             (λ _ → IsContinuousClamp a b))
           ((λ _ → IsContinuousClamp a b) , ((λ _ → IsContinuousConst _)))) )
         ((λ _ → IsContinuousConst _) , (λ _ → IsContinuousConst _))
       (λ x y → subst2 _≤ᵣ_
         (sym (absᵣ-rat _) ∙
            cong absᵣ (sym (-ᵣ-rat₂ _ _) ))
         (sym (absᵣ-rat _) ∙ cong absᵣ (sym (-ᵣ-rat₂ _ _) ))
         (≤ℚ→≤ᵣ _ _ (clamp-dist aℚ bℚ x y))) x y)
  a b
  where
  f₀ : ℝ → ℝ → ℝ → ℝ → ℝ
  f₀ x y a b  = absᵣ (clampᵣ a b x -ᵣ clampᵣ a b y)


ℕ₊₁→ℕ-lem : ∀ n m → n ≡ ℕ₊₁→ℕ m → (1+ predℕ n) ≡ m
ℕ₊₁→ℕ-lem zero m x = ⊥.rec (ℕ.znots x )
ℕ₊₁→ℕ-lem (suc n) m x = cong 1+_ (ℕ.injSuc x)






substFin : ∀ {n} {m} → n ≡ m → Fin n → Fin m
substFin p = map-snd (subst (_ ℕ.<ᵗ_) p)

foldFin+ᵣ : ∀ n V (f : A → ℝ) x x' →
  foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) (x +ᵣ x') V ≡
   x +ᵣ foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) x' V
foldFin+ᵣ zero V f x x' = refl
foldFin+ᵣ (suc n) V f x x' =
  foldFin+ᵣ n (V ∘ fsuc) _ (x +ᵣ x') (f (V fzero)) ∙
   sym (+ᵣAssoc x _ _) ∙
   cong (x +ᵣ_) (sym (foldFin+ᵣ n (V ∘ fsuc) f x' (f (V fzero))))

foldFin+0ᵣ : ∀ n V (f : A → ℝ) x →
  foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) x V ≡
   x +ᵣ foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) 0 V
foldFin+0ᵣ n V f x =
 cong (λ x → foldlFin {n = n} (λ a y → a +ᵣ f y) x V) (sym (+IdR _))
 ∙ foldFin+ᵣ n V f x 0


-- zip-foldFin+ᵣ : ∀ n V V' (f : A → ℝ) (f' : A' → ℝ) x x' →
--   foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) x V
--     +ᵣ foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f' y) x' V' ≡
--    foldlFin {B = ℝ} {n = n} (λ a (y , y') → a +ᵣ (f y +ᵣ f' y')) (x +ᵣ x')
--     λ x → V x , V' x
-- zip-foldFin+ᵣ zero V V' f f' _ _ = refl
-- zip-foldFin+ᵣ (suc n) V V' f f' x x' =
--   zip-foldFin+ᵣ n (V ∘ fsuc) (V' ∘ fsuc) f f'
--      (x +ᵣ f (V fzero)) (x' +ᵣ f' (V' fzero))
--    ∙ cong (λ xx → foldlFin {n = n}
--       _
--       xx
--       (λ x₁ → V (fsuc x₁) , V' (fsuc x₁)))
--       ℝ!

-- zip-foldFin+ᵣ' : ∀ n V (f : A → ℝ) (f' : A → ℝ) x x' →
--   foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) x V
--     +ᵣ foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f' y) x' V ≡
--    foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ (f y +ᵣ f' y)) (x +ᵣ x')
--     V
-- zip-foldFin+ᵣ' zero V f f' _ _ = refl
-- zip-foldFin+ᵣ' (suc n) V  f f' x x' =
--   zip-foldFin+ᵣ' n (V ∘ fsuc) f f'
--      (x +ᵣ f (V fzero)) (x' +ᵣ f' (V fzero))
--    ∙ cong (λ xx → foldlFin {n = n}
--       _
--       xx
--       (V ∘ fsuc) )
--       ℝ!


-- foldFin·DistL : ∀ n (f : A → ℝ) α x V →
--   foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ α ·ᵣ f y) (α ·ᵣ x) V
--       ≡ α ·ᵣ foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) (x) V
-- foldFin·DistL zero f α x V = refl
-- foldFin·DistL (suc n) f α x V =
--   cong (λ z → foldlFin {n = n} (λ a y → a +ᵣ α ·ᵣ f y) z
--       (λ x₁ → V (fsuc x₁)))
--        (sym (·DistL+ _ _ _))
--   ∙ foldFin·DistL n f α (x +ᵣ f (V fzero)) (V ∘ fsuc)


foldFin+map : ∀ n x (f : A → ℝ) (g : B → A) V →
  foldlFin {B = ℝ} {A = A} {n = n} (λ a y → a +ᵣ f y) x (g ∘ V)
    ≡ foldlFin {B = ℝ} {A = B} {n = n} (λ a y → a +ᵣ f (g y)) x V
foldFin+map zero x f g V = refl
foldFin+map (suc n) x f g V =
 foldFin+map n (x +ᵣ f ((g ∘ V) fzero)) f g (V ∘ fsuc)


-- foldFin+transpose : ∀ n n' (f : Fin n → Fin n' → ℝ) x →
--   foldlFin {B = ℝ} {n = n} (λ a k → a +ᵣ
--       foldlFin {B = ℝ} {n = n'} (λ a k' → a +ᵣ
--       f k k') (fromNat zero) (idfun _)) x (idfun _)
--       ≡ foldlFin {B = ℝ} {n = n'} (λ a k' → a +ᵣ
--            foldlFin {B = ℝ} {n = n} (λ a k → a +ᵣ
--            f k k') (fromNat zero) (idfun _)) x (idfun _)
-- foldFin+transpose zero zero f x = refl
-- foldFin+transpose (suc n) zero f x =
--    foldFin+map n (x +ᵣ 0) _ fsuc (idfun _) ∙
--     foldFin+transpose n zero (f ∘ fsuc) _ ∙ +IdR x
-- foldFin+transpose n (suc n') f x =
--      ((cong (foldlFin {n = n})
--         (funExt₂ λ a k →
--            cong (a +ᵣ_)
--             ((λ i → foldFin+map n' (+IdL (f k (idfun (Fin (suc n')) fzero)) i)
--              (λ k' → f k k') fsuc (idfun _) i)
--               ∙ foldFin+0ᵣ n' (idfun _) _ _))
--          ≡$ x) ≡$ (idfun (Fin n)))
--    ∙ ((λ i → foldFin+map n (+IdL x (~ i))
--      (λ z →
--         f (z .fst) 0 +ᵣ
--         foldlFin {n = n'} (λ a₁ k' → a₁ +ᵣ f (z .snd) (fsuc k')) 0 (idfun (Fin n')))
--      (λ x → x , x) (idfun _) (~ i))
--    ∙ sym (zip-foldFin+ᵣ n _ _ _ _ 0 x)
--    ∙ sym (foldFin+ᵣ n _ _
--       (foldlFin {n = n} (λ a k → a +ᵣ f k 0) 0 (idfun _)) x))
--     ∙ (cong (foldlFin {n = n}
--        (λ a k →
--           a +ᵣ
--           foldlFin {n = n'} (λ a₁ k' → a₁ +ᵣ f k (fsuc k')) 0
--           (idfun _)))
--            (+ᵣComm _ _) ≡$ (idfun (Fin n)))
--   ∙ foldFin+transpose n n' _ _
--   ∙ sym (foldFin+map n' _ _ fsuc (idfun _))



-- foldFin·DistL' : ∀ n (f : A → ℝ) α V →
--   foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ α ·ᵣ f y) 0 V
--       ≡ α ·ᵣ foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) 0 V
-- foldFin·DistL' n f α V =
--  cong  (λ x →   foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ α ·ᵣ f y) x V)
--      (sym (𝐑'.0RightAnnihilates _))
--  ∙ foldFin·DistL n f α 0 V



-- zip-foldFin-ᵣ : ∀ n V V' (f : A → ℝ) (f' : A' → ℝ) x x' →
--   foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) x V
--     -ᵣ foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f' y) x' V' ≡
--    foldlFin {B = ℝ} {n = n} (λ a (y , y') → a +ᵣ (f y -ᵣ f' y')) (x -ᵣ x')
--     λ x → V x , V' x
-- zip-foldFin-ᵣ n V V' f f' x x' =
--  cong ((foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) x V) +ᵣ_)
--   (-ᵣ≡[-1·ᵣ] (foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f' y) x' V')
--    ∙ sym (foldFin·DistL n _ (-1) _ _)) ∙
--   zip-foldFin+ᵣ n V V' f _ _ _ ∙
--    ((cong₂ (foldlFin {n = n}) (funExt₂ λ a u → cong ((a +ᵣ_) ∘ (f (fst u) +ᵣ_))
--     (sym (-ᵣ≡[-1·ᵣ] _)))
--      (cong (x +ᵣ_) (sym (-ᵣ≡[-1·ᵣ] _)))) ≡$ (λ x₁ → V x₁ , V' x₁))


-- foldFin+≤ : ∀ n x x' (f : A → ℝ) (f' : A' → ℝ) V V' →
--    x ≤ᵣ x' →
--   (∀ k → f (V k) ≤ᵣ f' (V' k)) →
--   foldlFin {B = ℝ} {A = A} {n = n} (λ a y → a +ᵣ f y) x V
--     ≤ᵣ foldlFin {B = ℝ} {A = A'} {n = n} (λ a y → a +ᵣ f' y) x' V'

-- foldFin+≤ zero x x' f f' V V' x≤x' f≤f' = x≤x'
-- foldFin+≤ (suc n) x x' f f' V V' x≤x' f≤f' =
--   foldFin+≤ n _ _ f f' (V ∘ fsuc) (V' ∘ fsuc)
--     (≤ᵣMonotone+ᵣ _ _ _ _ x≤x' (f≤f' fzero)) (f≤f' ∘ fsuc)


-- foldFin+< : ∀ n x x' (f : A → ℝ) (f' : A' → ℝ) V V' →
--    x ≤ᵣ x' →
--   (∀ k → f (V k) <ᵣ f' (V' k)) →
--   foldlFin {B = ℝ} {A = A} {n = (suc n)} (λ a y → a +ᵣ f y) x V
--     <ᵣ foldlFin {B = ℝ} {A = A'} {n = (suc n)} (λ a y → a +ᵣ f' y) x' V'

-- foldFin+< zero x x' f f' V V' x≤x' X = ≤<ᵣMonotone+ᵣ _ _ _ _ x≤x' (X fzero)
-- foldFin+< (suc n) x x' f f' V V' x≤x' X =
--  foldFin+< n _ _ f f' (V ∘ fsuc) (V' ∘ fsuc)
--           (≤ᵣMonotone+ᵣ _ _ _ _ x≤x' (<ᵣWeaken≤ᵣ _ _ $ X fzero)) (X ∘ fsuc)


-- foldFin+<-abs : ∀ n → zero ℕ.< n → ∀ x x' (f : A → ℝ) (f' : A' → ℝ) V V'  →
--    absᵣ x ≤ᵣ x' →
--   (∀ k → absᵣ (f (V k)) <ᵣ f' (V' k)) →
--   absᵣ (foldlFin {B = ℝ} {A = A} {n = n} (λ a y → a +ᵣ f y) x V)
--     <ᵣ foldlFin {B = ℝ} {A = A'} {n = n} (λ a y → a +ᵣ f' y) x' V'

-- foldFin+<-abs zero 0<n x x' f f' V V' x≤x' X = ⊥.rec (ℕ.¬-<-zero 0<n)

-- foldFin+<-abs (suc zero) 0<n x x' f f' V V' x≤x' X =
--  isTrans≤<ᵣ _ _ _ (absᵣ-triangle _ _) (≤<ᵣMonotone+ᵣ _ _ _ _ x≤x' (X fzero))
-- foldFin+<-abs (suc (suc n)) 0<n x x' f f' V V' x₁ X =
--   foldFin+<-abs (suc n) ℕ.zero-<-suc (x +ᵣ f (V fzero)) (x' +ᵣ f' (V' fzero))
--     f f' (V ∘ fsuc) (V' ∘ fsuc)
--      (isTrans≤ᵣ _ _ _ (absᵣ-triangle _ _)
--        (≤ᵣMonotone+ᵣ _ _ _ _ x₁ (<ᵣWeaken≤ᵣ _ _ $ X fzero)))
--        (X ∘ fsuc)

-- foldFin+≤-abs : ∀ n → ∀ x x' (f : A → ℝ) (f' : A' → ℝ) V V'  →
--    absᵣ x ≤ᵣ x' →
--   (∀ k → absᵣ (f (V k)) ≤ᵣ f' (V' k)) →
--   absᵣ (foldlFin {B = ℝ} {A = A} {n = n} (λ a y → a +ᵣ f y) x V)
--     ≤ᵣ foldlFin {B = ℝ} {A = A'} {n = n} (λ a y → a +ᵣ f' y) x' V'

-- foldFin+≤-abs zero x x' f f' V V' x≤x' X = x≤x'

-- foldFin+≤-abs (suc zero) x x' f f' V V' x≤x' X =
--  isTrans≤ᵣ _ _ _ (absᵣ-triangle _ _) (≤ᵣMonotone+ᵣ _ _ _ _ x≤x' (X fzero))
-- foldFin+≤-abs (suc (suc n)) x x' f f' V V' x₁ X =
--   foldFin+≤-abs (suc n)  (x +ᵣ f (V fzero)) (x' +ᵣ f' (V' fzero))
--     f f' (V ∘ fsuc) (V' ∘ fsuc)
--      (isTrans≤ᵣ _ _ _ (absᵣ-triangle _ _)
--        (≤ᵣMonotone+ᵣ _ _ _ _ x₁ (X fzero)))
--        (X ∘ fsuc)


-- foldFin+Const : ∀ n x V →
--   foldlFin {B = ℝ} {A = A} {n = n} (λ a y → a +ᵣ x) 0 V
--     ≡ fromNat n ·ᵣ x
-- foldFin+Const zero x V = sym (𝐑'.0LeftAnnihilates _)
-- foldFin+Const (suc n) x V =
--       (λ i → foldFin+0ᵣ n (V ∘ fsuc) (λ _ → x) (+IdL x i) i)
--    ∙∙ cong₂ (_+ᵣ_) (sym (·IdL x)) (foldFin+Const n x (V ∘ fsuc))
--    ∙∙ (sym (·DistR+ 1 (fromNat n) x)
--       ∙ cong (_·ᵣ x) (+ᵣ-rat _ _  ∙ cong rat (ℚ.ℕ+→ℚ+ 1 n )))

-- foldlFin-substN : ∀ {n n'} → (p : n ≡ n') → ∀ f b v →
--             foldlFin {B = B} {A = A} {n} f b v ≡
--               foldlFin {B = B} {A = A} {n'} f b (v ∘ substFin (sym p))
-- foldlFin-substN {n = n} = J (λ n' p → ∀ f b v →
--             foldlFin {n = n} f b v ≡
--               foldlFin {n = n'}  f b (v ∘ substFin (sym p)))
--                λ f b v → cong (foldlFin {n = n} f b)
--                  (funExt λ x → cong v (sym (transportRefl _)))


-- deltas-sum : ∀ n (f : Fin (suc n) → ℝ) →
--  foldlFin {n = n} (λ a k → a +ᵣ (f (fsuc k) -ᵣ f (finj k))) 0 (idfun _) ≡
--    f flast -ᵣ f fzero
-- deltas-sum zero f = ℝ!
-- deltas-sum (suc n) f =
--  foldFin+0ᵣ n (fsuc) _ _
--   ∙ cong₂ _+ᵣ_
--     (+IdL _)
--     (foldFin+map n 0 _ fsuc (idfun _)
--      ∙ deltas-sum n (f ∘ fsuc))
--   ∙ ℝ!


-- ℕ^+ : ∀ k n m → k ℕ.^ (n ℕ.+ m) ≡ (k ℕ.^ n) ℕ.· (k ℕ.^ m)
-- ℕ^+ k zero m = sym (ℕ.+-zero _)
-- ℕ^+ k (suc n) m = cong (k ℕ.·_) (ℕ^+ k n m) ∙ ℕ.·-assoc k _ _


-- 2^ : ℕ → ℕ
-- 2^ zero = 1
-- 2^ (suc x) = (2^ x) ℕ.+ (2^ x)

-- 2^-^ : ∀ n → 2^ n ≡ 2 ^ n
-- 2^-^ zero = refl
-- 2^-^ (suc n) = cong₂ ℕ._+_ (2^-^ n) (2^-^ n)
--  ∙ cong ((2 ^ n) ℕ.+_) (sym (ℕ.+-zero _))

-- 2^+ : ∀ n m → 2^ (n ℕ.+ m) ≡ (2^ n) ℕ.· (2^ m)
-- 2^+ zero m = sym (ℕ.+-zero (2^ m))
-- 2^+ (suc n) m = cong₂ ℕ._+_ (2^+ n m) (2^+ n m)
--  ∙ ·-distribʳ (2^ n) _ (2^ m)

-- injectFin+ : {m n : ℕ} → Fin m → Fin (n ℕ.+ m)
-- injectFin+ {n = n} x = (n ℕ.+ fst x) ,  ℕ.<→<ᵗ (ℕ.<-k+ {k = n} (ℕ.<ᵗ→< (snd x)))
-- -- injectFin+ {n = suc n} x = fsuc (injectFin+ x)


-- injectFin+' : {m n : ℕ} → Fin n → Fin (n ℕ.+ m)
-- injectFin+' {m} {n = n} x = fst x , ℕ.<→<ᵗ {fst x}  (ℕ.<≤-trans {fst x} (ℕ.<ᵗ→< {fst x} {n} (snd x)) ℕ.≤SumLeft) 

-- fsuc∘inj' : {n m : ℕ} → ∀ x → fsuc  {n ℕ.+ (suc m)} (injectFin+' {suc m} {n} x) ≡
--                  injectFin+' {suc m} {suc n} (fsuc x)
-- fsuc∘inj' {n} {m} x = toℕ-injective {(suc n) ℕ.+ (suc m)} refl

-- finj∘inj' : {n m : ℕ} → ∀ x → finj (injectFin+' {m} {n} x) ≡
--             injectFin+' {m} {suc n} (finj x)
-- finj∘inj' {n} {m} x = toℕ-injective {(suc n) ℕ.+ m} refl


-- fsuc∘inj : {n m : ℕ} → ∀ x p →
--                  fsuc {n ℕ.+ m} (injectFin+ {m} {n} x) ≡
--                  (fst (injectFin+ {suc m} {n} (fsuc x))
--                    , p)
-- fsuc∘inj {n} {m} x p = toℕ-injective {suc (n ℕ.+ m)} (sym (+-suc _ _))

-- finj∘inj : {n m : ℕ} → ∀ x p → finj {n ℕ.+ m} (injectFin+ {m} {n} x) ≡
--             (fst (injectFin+ {suc m} {n} (finj x)) , p)
-- finj∘inj {n} {m} x p = toℕ-injective {suc (n ℕ.+ m)} refl




-- Fin+→⊎ : ∀ n m → Fin (n ℕ.+ m) → (Fin n ⊎ Fin m)
-- Fin+→⊎ zero m = inr
-- Fin+→⊎ (suc n) m (zero , snd₁) = inl fzero
-- Fin+→⊎ (suc n) m (suc k , p) = ⊎.map fsuc
--   (idfun _) (Fin+→⊎ n m (k , p))


-- rec⊎-injectFin+' : ∀ {A : Type} {m} {n} f g x →
--   ⊎.rec {C = A} f g (Fin+→⊎ n m (injectFin+' {m} {n} x))
--                        ≡ f x
-- rec⊎-injectFin+' {n = zero} f g x = ⊥.rec (¬Fin0 x)
-- rec⊎-injectFin+' {n = suc n} f g (zero , snd₁) = refl 
-- rec⊎-injectFin+' {m = m} {n = suc n} f g (suc k , p) = (cong (λ k → ⊎.rec f g
--       (⊎.map fsuc (λ x → x)
--        (Fin+→⊎ n m k))) (toℕ-injective {n ℕ.+ m} refl)
--        ∙ (rec-map f g fsuc (idfun _) (Fin+→⊎ n m (injectFin+' {n = n} (k , p)))))
--     ∙ rec⊎-injectFin+' {n = n} (f ∘ fsuc) g (k , p)



-- Fin+→⊎∘injectFin+' : ∀ n m x → inl x ≡ Fin+→⊎ n m (injectFin+' {m} {n} x)
-- Fin+→⊎∘injectFin+' zero m x = ⊥.rec (¬Fin0 x)
-- Fin+→⊎∘injectFin+' (suc n) m (zero , _) = refl
--   -- cong inl (toℕ-injective refl)
-- Fin+→⊎∘injectFin+' (suc n) m (suc k , p) =
--   cong (⊎.map fsuc (λ x → x))
--     (Fin+→⊎∘injectFin+' n m (k , p))
--     ∙ cong (λ p → ⊎.map (fsuc {n}) (λ x → x) (Fin+→⊎ n m ((k , p))))
--         (ℕ.isProp<ᵗ {k} {n ℕ.+ m} (snd ((injectFin+' {m = m} {n = n} (k , p))))
--            (injectFin+'  {m = m} {n = suc n} (suc k , p) .snd))

-- Fin+→⊎∘injectFin+ : ∀ n m x → inr x ≡ Fin+→⊎ n m (injectFin+ {m} {n} x)
-- Fin+→⊎∘injectFin+ zero m x = cong inr (toℕ-injective {m} refl)
-- Fin+→⊎∘injectFin+ (suc n) m x =
--   cong (⊎.map fsuc (λ x → x)) (Fin+→⊎∘injectFin+ n m x
--    ∙ cong (Fin+→⊎ n m) (toℕ-injective {n ℕ.+ m} refl)
--    )

-- rec⊎-injectFin+ : ∀ {A : Type} {m} {n} f g x →
--   ⊎.rec {C = A} f g (Fin+→⊎ n m (injectFin+ {m} {n} x))
--                        ≡ g x
-- rec⊎-injectFin+ {m = m} {n = zero}  f g x = cong g (toℕ-injective {m} refl)
-- rec⊎-injectFin+ {m = m} {n = suc n} f g x =

--   cong (λ k → ⊎.rec f g
--       (⊎.map fsuc (λ x₁ → x₁)
--        (Fin+→⊎ n m k))) (toℕ-injective {n ℕ.+ m} refl)
--    ∙ (rec-map f g fsuc (idfun _) (Fin+→⊎ n m (injectFin+ {m} {n} x)))
--   ∙ rec⊎-injectFin+ {n = n} (f ∘ fsuc) g x

-- injectFin+'-flast : ∀ n m k p p' →
--   Fin+→⊎ n m (injectFin+' {m} {n} (k , p)) ≡
--     inl (k , p')

-- injectFin+'-flast zero m k () p'
-- injectFin+'-flast (suc n) m zero p p' = refl
-- injectFin+'-flast (suc n) m (suc k) p p' =
--   cong (⊎.map fsuc (λ x → x))
--     (cong (Fin+→⊎ n m)  (toℕ-injective {n ℕ.+ m} refl)
--      ∙ injectFin+'-flast n m k p p')
   


-- Iso-Fin+⊎-leftInv : ∀ n m a → ⊎.rec (injectFin+' {m} {n}) (injectFin+ {m} {n}) (Fin+→⊎ n m a) ≡ a
-- Iso-Fin+⊎-leftInv zero m a = toℕ-injective {m} refl
-- Iso-Fin+⊎-leftInv (suc n) m (zero , p) = toℕ-injective {suc n ℕ.+ m} refl
-- Iso-Fin+⊎-leftInv (suc n) m (suc k ,  p) = 
--      h
--        (Fin+→⊎ n m
--         (k , p))
--   ∙ cong fsuc
--      (Iso-Fin+⊎-leftInv n m (k , p))
  
--  where

--  h : ∀ x →
--        ⊎.rec (injectFin+' {m} {suc n}) (injectFin+ {m} {suc n})
--            (⊎.map fsuc (idfun (Fin m)) x)
--        ≡
--        fsuc (⊎.rec (injectFin+' {m} {n}) (injectFin+ {m} {n}) x)
--  h (inl x) = toℕ-injective {suc n ℕ.+ m} refl
--  h (inr x) = toℕ-injective {suc n ℕ.+ m} refl

-- Iso-Fin+⊎ : ∀ n m → Iso (Fin (n ℕ.+ m)) (Fin n ⊎ Fin m)
-- Iso-Fin+⊎ n m .Iso.fun = Fin+→⊎ n m
-- Iso-Fin+⊎ n m .Iso.inv = ⊎.rec (injectFin+' {m} {n}) (injectFin+ {m} {n})
-- Iso-Fin+⊎ n m .Iso.sec (inl x) = sym (Fin+→⊎∘injectFin+' n m _)
-- Iso-Fin+⊎ n m .Iso.sec (inr x) = sym (Fin+→⊎∘injectFin+ n m _)
-- Iso-Fin+⊎ n m .Iso.ret = Iso-Fin+⊎-leftInv n m

-- injectFin+'-flast≡injectFin+-fzero :
--  ∀ n m →
--   fst (injectFin+' {m} {suc n} flast) ≡
--   fst (injectFin+ {suc m} {n} fzero)
-- injectFin+'-flast≡injectFin+-fzero n m = sym (+-zero _)

-- injectFin+'-flast-S : ∀ n m k p →
--      inr fzero ≡ Fin+→⊎ (suc n) (suc (suc m))
--        (k , p)
-- injectFin+'-flast-S n m zero p = {!!}
--   -- ⊥.rec (ℕ.znots {n}
--   --  (ℕ.inj-+m {m = suc (suc m)} (cong suc (sym (+-comm m 1)) ∙ p)))
-- injectFin+'-flast-S zero m (suc zero) p = {!!}
--  -- cong inr (toℕ-injective refl)
-- injectFin+'-flast-S zero m (suc (suc k)) p = {!!}
--  -- ⊥.rec (ℕ.snotz {k} (ℕ.inj-+m {m = suc (suc (suc m))}
--  --       (cong suc (
--  --         (ℕ.+-assoc k 3 m ∙
--  --          cong (ℕ._+ m) (+-comm k 3))
--  --        ∙ +-comm (suc (suc (suc k))) m) ∙ p)))

-- injectFin+'-flast-S (suc n) m (suc k) p = {!!}
--  -- cong (⊎.map fsuc (λ x → x)) (injectFin+'-flast-S n m k _)

-- foldFin·2 : ∀ n m → (f : B → A → B) → (b : B) →
--               (V : Fin (n ℕ.+ m) → A) →
--              foldlFin {n = n ℕ.+ m} f b V ≡
--                foldlFin {n = m} f
--                  (foldlFin {n = n} f b (V ∘ injectFin+'))
--                   (V ∘ injectFin+)
-- foldFin·2 zero m f b V =
--  cong (foldlFin {n = m} f b)
--   (funExt λ x → cong V (toℕ-injective refl) )
-- foldFin·2 {B = B} {A = A} (suc n) m f b V =
--  foldFin·2 n m f (f b (V fzero)) (V ∘ fsuc)
--   ∙ cong₂ (foldlFin {_} {B} {_} {A} {m} f)
--     (cong₂ (foldlFin {_} {B} {_} {A} {n} f)
--       (cong (f b) (cong V (toℕ-injective refl)))
--         (funExt λ x → cong V (toℕ-injective refl)))
--      (funExt λ x → cong V (toℕ-injective refl))


-- foldFin-sum-concat : ∀ n m → (f : Fin (n ℕ.+ m) → ℝ) →
--      foldlFin (λ a y → a +ᵣ f y) 0 (idfun _)
--       ≡ foldlFin (λ a y → a +ᵣ f (injectFin+' {m} {n} y)) 0 (idfun _)
--       +ᵣ foldlFin (λ a y → a +ᵣ f (injectFin+ {m} {n} y)) 0 (idfun _)

-- foldFin-sum-concat n m f =
--   foldFin·2 n m (λ a y → a +ᵣ f y) 0 (idfun _)
--    ∙ foldFin+0ᵣ m (idfun _  ∘ injectFin+) f _
--    ∙ cong₂ _+ᵣ_
--      (foldFin+map n _ _ injectFin+' (idfun _))
--      (foldFin+map m _ _ injectFin+ (idfun _))

-- 0<2^ : ∀ n → 0 ℕ.< 2^ n
-- 0<2^ zero = ℕ.zero-<-suc
-- 0<2^ (suc n) = ℕ.<-+-< (0<2^ n) (0<2^ n)


-- Fin^2· : ∀ n m → (Fin (2^ n) × Fin (2^ m))
--                       → (Fin (2^ (n ℕ.+ m)))
-- Fin^2· n m ((l , l<) , (k , k<)) = {!!}
--  -- (((2^ m) ℕ.· l) ℕ.+ k) ,
--  --  (2^ m ℕ.· l ℕ.+ k
--  --      <≤⟨ ℕ.<-k+ {k = 2^ m ℕ.· l} k< ⟩
--  --     _ ≡≤⟨ (λ i → ℕ.+-comm (ℕ.·-comm (2^ m) l i) (2^ m) i) ⟩
--  --    _ ≤≡⟨ ℕ.≤-·k {k = 2^ m} l< ⟩
--  --         sym (2^+ n m))

--  -- where open ℕ.<-Reasoning

-- Fin^2·-injectFin+' : ∀ n m x y →
--   (injectFin+' (Fin^2· n m (x , y))) ≡
--     (Fin^2· (suc n) m (injectFin+' x , y))
-- Fin^2·-injectFin+' n m (fst₁ , snd₁) y = toℕ-injective refl

-- Fin^2·-injectFin+ : ∀ n m x y → (injectFin+ (Fin^2· n m (x , y)))
--     ≡ (Fin^2· (suc n) m (injectFin+ x , y))
-- Fin^2·-injectFin+ n m x y =
--  toℕ-injective
--   (cong (ℕ._+ (2^ m ℕ.· x .fst ℕ.+ y .fst)) (2^+ n m ∙ ℕ.·-comm (2^ n) (2^ m) )
--     ∙ (ℕ.+-assoc (2^ m ℕ.· 2^ n) _ (fst y) ∙
--       cong (ℕ._+ fst y) (·-distribˡ (2^ m) _ _)))

-- foldFin·2^ : ∀ n m → (f : B → A → B) → (b : B) →
--               (V : Fin (2^ (n ℕ.+ m)) → A) →
--              foldlFin f b V ≡
--                foldlFin {n = 2^ n} (foldlFin {n = 2^ m} f)
--                  b (curry (V ∘ Fin^2· n m ))
-- foldFin·2^ zero m f b V = cong (foldlFin {n = 2^ m} f b)
--   (funExt λ x → cong V (toℕ-injective
--     (cong (ℕ._+ fst x) (ℕ.0≡m·0 (2^ m)))))
-- foldFin·2^ (suc n) m f b V =
--   foldFin·2 (2^ (n ℕ.+ m)) (2^ (n ℕ.+ m)) f b V
--    ∙ foldFin·2^ n m _ _ _
--     ∙ cong {x = (foldlFin {n = 2^ (n ℕ.+ m)}
--             f b (V ∘ injectFin+'))} (λ z → foldlFin (foldlFin f) z
--          (curry ((V ∘ injectFin+) ∘ Fin^2· n m)))
--          (foldFin·2^ n m _ _ _)

--     ∙ (λ i → foldlFin {n = 2^ n} ff'
--        (foldlFin {n = 2^ n} ff' b
--         (λ x y → V (Fin^2·-injectFin+' n m x y i)))
--        (λ x y → V (Fin^2·-injectFin+ n m x y i))) ∙
--       sym (foldFin·2 (2^ n) (2^ n) ff' _ _)
--  where
--  ff' = (foldlFin {n = 2^ m} f)


-- record ElimFinSS (A : Type) (n : ℕ) : Type where
--  no-eta-equality
--  field
--   a₀ : A
--   f : Fin n → A
--   aₙ : A

--  go : Fin (2 ℕ.+ n) → A
--  go (zero , _) = a₀
--  go (suc k , p) = {!!}
--  -- go (suc k , zero , p) = aₙ
--  -- go (suc k , suc l , p) =
--  --   f (k , l , cong (predℕ ∘ predℕ) (sym (ℕ.+-suc (suc l) (suc k)) ∙ p))
