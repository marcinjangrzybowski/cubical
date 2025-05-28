module Cubical.HITs.CauchyReals.Integral where

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



ℕ₊₁→ℕ-lem : ∀ n m → n ≡ ℕ₊₁→ℕ m → (1+ predℕ n) ≡ m
ℕ₊₁→ℕ-lem zero m x = ⊥.rec (ℕ.znots x )
ℕ₊₁→ℕ-lem (suc n) m x = cong 1+_ (ℕ.injSuc x)

private
  variable
    ℓ : Level
    A A' B : Type ℓ


foldlFin : ∀ {n} → (B → A → B) → B → (Fin n → A) → B
foldlFin {n = zero} f b v = b
foldlFin {n = suc n} f b v = foldlFin {n = n} f (f b (v fzero)) (v ∘ fsuc)

substFin : ∀ {n} {m} → n ≡ m → Fin n → Fin m 
substFin p = map-snd (subst (_ ℕ.<_) p)

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
 cong (λ x → foldlFin (λ a y → a +ᵣ f y) x V) (sym (+IdR _))
 ∙ foldFin+ᵣ n V f x 0
   

zip-foldFin+ᵣ : ∀ n V V' (f : A → ℝ) (f' : A' → ℝ) x x' →
  foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) x V
    +ᵣ foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f' y) x' V' ≡
   foldlFin {B = ℝ} {n = n} (λ a (y , y') → a +ᵣ (f y +ᵣ f' y')) (x +ᵣ x')
    λ x → V x , V' x
zip-foldFin+ᵣ zero V V' f f' _ _ = refl
zip-foldFin+ᵣ (suc n) V V' f f' x x' =
  zip-foldFin+ᵣ n (V ∘ fsuc) (V' ∘ fsuc) f f'
     (x +ᵣ f (V fzero)) (x' +ᵣ f' (V' fzero))
   ∙ cong (λ xx → foldlFin
      _
      xx
      (λ x₁ → V (fsuc x₁) , V' (fsuc x₁)))
      (L𝐑.lem--087 {x} {f (V fzero)} {x'} {f' (V' fzero)})


foldFin·DistL : ∀ n (f : A → ℝ) α x V → 
  foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ α ·ᵣ f y) (α ·ᵣ x) V
      ≡ α ·ᵣ foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) (x) V
foldFin·DistL zero f α x V = refl
foldFin·DistL (suc n) f α x V =
  cong (λ z → foldlFin (λ a y → a +ᵣ α ·ᵣ f y) z
      (λ x₁ → V (fsuc x₁)))
       (sym (·DistL+ _ _ _))
  ∙ foldFin·DistL n f α (x +ᵣ f (V fzero)) (V ∘ fsuc)


zip-foldFin-ᵣ : ∀ n V V' (f : A → ℝ) (f' : A' → ℝ) x x' →
  foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) x V
    -ᵣ foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f' y) x' V' ≡
   foldlFin {B = ℝ} {n = n} (λ a (y , y') → a +ᵣ (f y -ᵣ f' y')) (x -ᵣ x')
    λ x → V x , V' x 
zip-foldFin-ᵣ n V V' f f' x x' = 
 cong ((foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f y) x V) +ᵣ_)
  (-ᵣ≡[-1·ᵣ] (foldlFin {B = ℝ} {n = n} (λ a y → a +ᵣ f' y) x' V')
   ∙ sym (foldFin·DistL n _ (-1) _ _)) ∙
  zip-foldFin+ᵣ n V V' f _ _ _ ∙
   ((cong₂ foldlFin (funExt₂ λ a u → cong ((a +ᵣ_) ∘ (f (fst u) +ᵣ_))
    (sym (-ᵣ≡[-1·ᵣ] _)))
     (cong (x +ᵣ_) (sym (-ᵣ≡[-1·ᵣ] _)))) ≡$ (λ x₁ → V x₁ , V' x₁))

foldFin+< : ∀ n x x' (f : A → ℝ) (f' : A' → ℝ) V V' →
   x ≤ᵣ x' →
  (∀ k → f (V k) <ᵣ f' (V' k)) → 
  foldlFin {B = ℝ} {A = A} {n = (suc n)} (λ a y → a +ᵣ f y) x V
    <ᵣ foldlFin {B = ℝ} {A = A'} {n = (suc n)} (λ a y → a +ᵣ f' y) x' V'
    
foldFin+< zero x x' f f' V V' x≤x' X = ≤<ᵣMonotone+ᵣ _ _ _ _ x≤x' (X fzero)
foldFin+< (suc n) x x' f f' V V' x≤x' X =
 foldFin+< n _ _ f f' (V ∘ fsuc) (V' ∘ fsuc)
          (≤ᵣMonotone+ᵣ _ _ _ _ x≤x' (<ᵣWeaken≤ᵣ _ _ $ X fzero)) (X ∘ fsuc)

foldFin+<-abs : ∀ n → zero ℕ.< n → ∀ x x' (f : A → ℝ) (f' : A' → ℝ) V V'  →
   absᵣ x ≤ᵣ x' →
  (∀ k → absᵣ (f (V k)) <ᵣ f' (V' k)) → 
  absᵣ (foldlFin {B = ℝ} {A = A} {n = n} (λ a y → a +ᵣ f y) x V)
    <ᵣ foldlFin {B = ℝ} {A = A'} {n = n} (λ a y → a +ᵣ f' y) x' V'
    
foldFin+<-abs zero 0<n x x' f f' V V' x≤x' X = ⊥.rec (ℕ.¬-<-zero 0<n)
  
foldFin+<-abs (suc zero) 0<n x x' f f' V V' x≤x' X =
 isTrans≤<ᵣ _ _ _ (absᵣ-triangle _ _) (≤<ᵣMonotone+ᵣ _ _ _ _ x≤x' (X fzero))
foldFin+<-abs (suc (suc n)) 0<n x x' f f' V V' x₁ X =
  foldFin+<-abs (suc n) ℕ.zero-<-suc (x +ᵣ f (V fzero)) (x' +ᵣ f' (V' fzero))
    f f' (V ∘ fsuc) (V' ∘ fsuc)
     (isTrans≤ᵣ _ _ _ (absᵣ-triangle _ _)
       (≤ᵣMonotone+ᵣ _ _ _ _ x₁ (<ᵣWeaken≤ᵣ _ _ $ X fzero)))
       (X ∘ fsuc)


foldFin+Const : ∀ n x V → 
  foldlFin {B = ℝ} {A = A} {n = n} (λ a y → a +ᵣ x) 0 V
    ≡ fromNat n ·ᵣ x
foldFin+Const zero x V = sym (𝐑'.0LeftAnnihilates _)
foldFin+Const (suc n) x V =
      (λ i → foldFin+0ᵣ n (V ∘ fsuc) (λ _ → x) (+IdL x i) i) 
   ∙∙ cong₂ (_+ᵣ_) (sym (·IdL x)) (foldFin+Const n x (V ∘ fsuc))
   ∙∙ (sym (·DistR+ 1 (fromNat n) x)
      ∙ cong (_·ᵣ x) (+ᵣ-rat _ _  ∙ cong rat (ℚ.ℕ+→ℚ+ 1 n )))

foldlFin-substN : ∀ {n n'} → (p : n ≡ n') → ∀ f b v →
            foldlFin {B = B} {A = A} {n} f b v ≡
              foldlFin {B = B} {A = A} {n'} f b (v ∘ substFin (sym p))
foldlFin-substN {n = n} = J (λ n' p → ∀ f b v →
            foldlFin f b v ≡
              foldlFin f b (v ∘ substFin (sym p)))
               λ f b v → cong (foldlFin {n = n} f b)
                 (funExt λ x → cong v (sym (transportRefl _)))

ℕ^+ : ∀ k n m → k ℕ.^ (n ℕ.+ m) ≡ (k ℕ.^ n) ℕ.· (k ℕ.^ m)
ℕ^+ k zero m = sym (ℕ.+-zero _)
ℕ^+ k (suc n) m = cong (k ℕ.·_) (ℕ^+ k n m) ∙ ℕ.·-assoc k _ _


2^ : ℕ → ℕ
2^ zero = 1
2^ (suc x) = (2^ x) ℕ.+ (2^ x)

2^-^ : ∀ n → 2^ n ≡ 2 ^ n
2^-^ zero = refl
2^-^ (suc n) = cong₂ ℕ._+_ (2^-^ n) (2^-^ n)
 ∙ cong ((2 ^ n) ℕ.+_) (sym (ℕ.+-zero _)) 

2^+ : ∀ n m → 2^ (n ℕ.+ m) ≡ (2^ n) ℕ.· (2^ m)
2^+ zero m = sym (ℕ.+-zero (2^ m))
2^+ (suc n) m = cong₂ ℕ._+_ (2^+ n m) (2^+ n m)
 ∙ ·-distribʳ (2^ n) _ (2^ m)

injectFin+ : {m n : ℕ} → Fin m → Fin (n ℕ.+ m)
injectFin+ {n = n} x = (n ℕ.+ fst x) ,  ℕ.<-k+ {k = n} (snd x)
-- injectFin+ {n = suc n} x = fsuc (injectFin+ x)


injectFin+' : {m n : ℕ} → Fin n → Fin (n ℕ.+ m)
injectFin+' {m} {n = n} x = fst x , ℕ.<≤-trans (snd x) ℕ.≤SumLeft 


foldFin·2 : ∀ n m → (f : B → A → B) → (b : B) →
              (V : Fin (n ℕ.+ m) → A) → 
             foldlFin {n = n ℕ.+ m} f b V ≡
               foldlFin {n = m} f
                 (foldlFin {n = n} f b (V ∘ injectFin+'))
                  (V ∘ injectFin+)
foldFin·2 zero m f b V =
 cong (foldlFin {n = m} f b)
  (funExt λ x → cong V (toℕ-injective refl) )
foldFin·2 {B = B} {A = A} (suc n) m f b V = 
 foldFin·2 n m f (f b (V fzero)) (V ∘ fsuc)
  ∙ cong₂ (foldlFin {_} {B} {_} {A} {m} f)
    (cong₂ (foldlFin {_} {B} {_} {A} {n} f)
      (cong (f b) (cong V (toℕ-injective refl)))
        (funExt λ x → cong V (toℕ-injective refl)))
     (funExt λ x → cong V (toℕ-injective refl))


0<2^ : ∀ n → 0 ℕ.< 2^ n
0<2^ zero = ℕ.zero-<-suc
0<2^ (suc n) = ℕ.<-+-< (0<2^ n) (0<2^ n)


Fin^2· : ∀ n m → (Fin (2^ n) × Fin (2^ m))
                      → (Fin (2^ (n ℕ.+ m)))
Fin^2· n m ((l , l<) , (k , k<)) =
 (((2^ m) ℕ.· l) ℕ.+ k) ,
  (2^ m ℕ.· l ℕ.+ k
      <≤⟨ ℕ.<-k+ {k = 2^ m ℕ.· l} k< ⟩
     _ ≡≤⟨ (λ i → ℕ.+-comm (ℕ.·-comm (2^ m) l i) (2^ m) i) ⟩
    _ ≤≡⟨ ℕ.≤-·k {k = 2^ m} l< ⟩
         sym (2^+ n m))

 where open ℕ.<-Reasoning

Fin^2·-injectFin+' : ∀ n m x y →
  (injectFin+' (Fin^2· n m (x , y))) ≡
    (Fin^2· (suc n) m (injectFin+' x , y))
Fin^2·-injectFin+' n m (fst₁ , snd₁) y = toℕ-injective refl

Fin^2·-injectFin+ : ∀ n m x y → (injectFin+ (Fin^2· n m (x , y)))
    ≡ (Fin^2· (suc n) m (injectFin+ x , y))
Fin^2·-injectFin+ n m x y =
 toℕ-injective
  (cong (ℕ._+ (2^ m ℕ.· x .fst ℕ.+ y .fst)) (2^+ n m ∙ ℕ.·-comm (2^ n) (2^ m) )
    ∙ (ℕ.+-assoc (2^ m ℕ.· 2^ n) _ (fst y) ∙
      cong (ℕ._+ fst y) (·-distribˡ (2^ m) _ _)))

foldFin·2^ : ∀ n m → (f : B → A → B) → (b : B) →
              (V : Fin (2^ (n ℕ.+ m)) → A) → 
             foldlFin f b V ≡
               foldlFin {n = 2^ n} (foldlFin {n = 2^ m} f)
                 b (curry (V ∘ Fin^2· n m ))
foldFin·2^ zero m f b V = cong (foldlFin {n = 2^ m} f b)
  (funExt λ x → cong V (toℕ-injective
    (cong (ℕ._+ fst x) (ℕ.0≡m·0 (2^ m)))))
foldFin·2^ (suc n) m f b V =
  foldFin·2 (2^ (n ℕ.+ m)) (2^ (n ℕ.+ m)) f b V
   ∙ foldFin·2^ n m _ _ _
    ∙ cong {x = (foldlFin {n = 2^ (n ℕ.+ m)}
            f b (V ∘ injectFin+'))} (λ z → foldlFin (foldlFin f) z
         (curry ((V ∘ injectFin+) ∘ Fin^2· n m)))
         (foldFin·2^ n m _ _ _)
      
    ∙ (λ i → foldlFin {n = 2^ n} ff'
       (foldlFin {n = 2^ n} ff' b
        (λ x y → V (Fin^2·-injectFin+' n m x y i)))
       (λ x y → V (Fin^2·-injectFin+ n m x y i))) ∙
      sym (foldFin·2 (2^ n) (2^ n) ff' _ _)
 where
 ff' = (foldlFin {n = 2^ m} f)



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
  riemannSum' f = foldlFin {n = 2 ℕ.+ len}
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


-- clampDeltaᵣ : ∀ L L' x → clampᵣ L L' x ≡
--                (x +ᵣ clampᵣ (L -ᵣ x) (L' -ᵣ x) 0)
-- clampDeltaᵣ L L' x = {!!}


clampDeltaSplitℚ : ∀ L L' x y → L ℚ.≤ L' → x ℚ.≤ y
            → (y ℚ.- x) ≡
              (ℚ.min L y ℚ.- ℚ.min L x)
               ℚ.+ (ℚ.clamp L L' y ℚ.- ℚ.clamp L L' x)
               ℚ.+ (ℚ.max L' y ℚ.- ℚ.max L' x)
clampDeltaSplitℚ = {!!}


clamp-Δ-·f : ∀ a b → a ≤ᵣ b → ∀ f
     → IsContinuous f
     → ∀ (δ : ℚ₊)
     → ∀ u v → u ≤ᵣ v
     → v -ᵣ u ≤ᵣ rat (fst δ)
     → (∀ aℚ bℚ → ( u ∈ intervalℙ (rat aℚ) (rat bℚ)) ⊎
                     ((u <ᵣ rat aℚ) ⊎ (rat bℚ <ᵣ u)))
     → (clampᵣ a b v -ᵣ clampᵣ a b u) ·ᵣ f u
       ≡ (clampᵣ a b v -ᵣ clampᵣ a b u)
         ·ᵣ f (clampᵣ (a -ᵣ rat (fst δ)) (b) u)
clamp-Δ-·f a b a≤b f cf δ u v u≤v v∼u X =
  {!!}


clamp-interval-Δ-swap : ∀ a b a' b'
           → a  ≤ᵣ b
           → a' ≤ᵣ b'
                → clampᵣ a  b  b' -ᵣ clampᵣ a  b  a'
                ≡ clampᵣ a' b' b  -ᵣ clampᵣ a' b' a
clamp-interval-Δ-swap a b a' b' a≤b a'≤b' =
  {!!}



open Partition[_,_] 

TaggedPartition[_,_] : ℝ → ℝ → Type
TaggedPartition[ a , b ] = Σ (Partition[ a , b ]) Sample


-- concatTaggedPartition : ∀ a b c → TaggedPartition[ a , b ] → TaggedPartition[ b , c ]
--                 → TaggedPartition[ a , c ]
-- concatTaggedPartition = {!!}



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


module Integration a b (a≤b : a ≤ᵣ b) where


 Δ : ℝ
 Δ = b -ᵣ a

 0≤Δ : 0 ≤ᵣ Δ
 0≤Δ = x≤y→0≤y-x a _ a≤b 
 

 -- uContMesh : ∀ f → IsUContinuous f →
 --        ∀ (ε₊ : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
 --                  (∀ ((p , t) : TaggedPartition[ a , b ]) →
 --                     (mesh p <ᵣ rat (fst δ) →
 --                       absᵣ (riemannSum' t f -ᵣ
 --                             riemannSum' (leftSample p) f)
 --                          <ᵣ Δ ·ᵣ rat (fst ε₊)))
 -- uContMesh d iucf ε₊ = {!!}

 module _ (n : ℕ) where

  t : ℕ → ℚ
  t k = [ pos (suc k) / 2+ n  ]

  0≤t : ∀ k → 0 ≤ᵣ rat (t k)
  0≤t k = ≤ℚ→≤ᵣ 0 (t k) (0≤pos/ {suc k} {2+ n})

  t≤1 : ∀ (k : Fin (1 ℕ.+ n)) → rat (t (fst k)) ≤ᵣ 1
  t≤1 k = ≤ℚ→≤ᵣ (t (fst k)) 1 w 
   where
   w : pos (suc (k .fst)) ℤ.· ℚ.ℕ₊₁→ℤ 1 ℤ.≤ pos 1 ℤ.· ℚ.ℕ₊₁→ℤ (2+ n)
   w = subst2 ℤ._≤_ (sym (ℤ.·IdR _)) (sym (ℤ.·IdL _))
          (ℤ.ℕ≤→pos-≤-pos (suc (fst k))
           _ (ℕ.suc-≤-suc $ ℕ.≤-suc $ ℕ.predℕ-≤-predℕ (snd k)))

  tIncr : ∀ k → t k ℚ.≤ t (suc k)
  tIncr k = ℤ.≤-·o {m = pos (suc k)} {n = pos (suc (suc k))} {k = suc (suc n)}
            (ℤ.ℕ≤→pos-≤-pos _ _ ℕ.≤-sucℕ)

  equalPartition : Partition[ a , b ] 
  equalPartition .len = n
  equalPartition .pts k = a +ᵣ Δ ·ᵣ (rat (t (fst k))) 
  equalPartition .a≤pts k =
    isTrans≡≤ᵣ a (a +ᵣ Δ ·ᵣ 0) _ 
      (sym (𝐑'.+IdR' _ _ (𝐑'.0RightAnnihilates _)))
       (≤ᵣ-o+ (Δ ·ᵣ 0) (Δ ·ᵣ (rat (t (fst k)))) a
         (≤ᵣ-o·ᵣ 0 (rat (t (fst k))) Δ  0≤Δ (0≤t (fst k)))) 
  equalPartition .pts≤b k = 
    isTrans≤≡ᵣ (a +ᵣ Δ ·ᵣ rat (t (fst k))) (a +ᵣ Δ) b
    (≤ᵣ-o+ _ _ a
     (isTrans≤≡ᵣ (Δ ·ᵣ rat (t (fst k))) (Δ ·ᵣ 1) Δ
      (≤ᵣ-o·ᵣ (rat (t (fst k))) 1 Δ  0≤Δ (t≤1 k)) (·IdR Δ)))
      (L𝐑.lem--05 {a} {b})
  equalPartition .pts≤pts k =
     ≤ᵣ-o+ _ _ a (≤ᵣ-o·ᵣ (rat (t ( (fst k)))) (rat (t (suc (fst k)))) Δ  0≤Δ
      (≤ℚ→≤ᵣ (t (fst k)) _ (tIncr (fst k))))


  equalPartitionPts' : ∀ k → pts' equalPartition k ≡
        a +ᵣ Δ ·ᵣ rat [ pos (fst k) / 2+ n  ]
  equalPartitionPts' (zero , zero , p) = ⊥.rec (ℕ.znots (cong predℕ p))
  equalPartitionPts' (zero , suc l , p) =
   sym (𝐑'.+IdR' _ _ (𝐑'.0RightAnnihilates' _ _ (cong rat (ℚ.[0/n]≡[0/m] _ _))))
  equalPartitionPts' (suc k , zero , p) =
    sym (L𝐑.lem--05 {a} {b}) ∙
      cong (a +ᵣ_) (sym (𝐑'.·IdR' _ _ (cong (rat ∘ [_/ 2+ n ])
       (cong (pos ∘ predℕ) p)
       ∙ (cong rat $ ℚ.[n/n]≡[m/m] (suc n) 0))))
  equalPartitionPts' (suc k , suc l , p) = refl
 
  equalPartitionΔ : ∀ k →
    pts' equalPartition (fsuc k) -ᵣ pts' equalPartition (finj k)
    ≡ Δ ·ᵣ rat [ 1 / 2+ n ]
  equalPartitionΔ (zero , zero , snd₁) = ⊥.rec (ℕ.znots (cong predℕ snd₁))
  equalPartitionΔ (zero , suc fst₂ , snd₁) =
   L𝐑.lem--063 {a}
  equalPartitionΔ (suc fst₁ , zero , snd₁) =
    L𝐑.lem--089 {b} {a} {Δ ·ᵣ rat [ pos (suc fst₁) / 2+ n ]}
     ∙ cong₂ (_-ᵣ_)
       (sym (·IdR Δ)) (cong (Δ ·ᵣ_) (cong (rat ∘ [_/ 2+ n ])
         (cong (pos ∘ predℕ) snd₁)))
       ∙ sym (𝐑'.·DistR- _ _ _) ∙
        cong (Δ ·ᵣ_)
         (cong₂ {x = 1}
          {rat [ pos (suc (suc n)) / 2+ n ]}
          _-ᵣ_ (cong rat (ℚ.[n/n]≡[m/m] 0 (suc n)))
          {rat [ pos (suc n) / 2+ n ]}
          {rat [ pos (suc n) / 2+ n ]}
          refl
          ∙ -ᵣ-rat₂ [ (pos (suc (suc n))) / 2+ n ] [ pos (suc n) / 2+ n ]
           ∙ cong rat
               (ℚ.n/k-m/k (pos (suc (suc n))) (pos (suc n)) (2+ n) ∙
                  cong [_/ 2+ n ] (cong (ℤ._- pos (suc n))
                      (ℤ.pos+ 1 (suc n)) ∙ ℤ.plusMinus (pos (suc n)) 1)))
                      
  equalPartitionΔ (suc k , suc l , p) =
   L𝐑.lem--088 {a} ∙
       sym (𝐑'.·DistR- _ _ _) ∙
         cong (Δ ·ᵣ_) zz
    where
    zz : rat (t (suc k)) -ᵣ rat (t k) ≡ rat [ 1 / 2+ n ]
    zz = cong₂ {x = rat (t (suc k))}
          {rat [ pos (suc (suc k)) / 2+ n ]}
          _-ᵣ_ refl {rat (t k)} {rat [ pos (suc k) / (2+ n) ]}
           refl  ∙ -ᵣ-rat₂ 
          ([ pos (suc (suc k)) / 2+ n ]) ([ pos (suc k) / 2+ n ]) ∙
           cong
             {x = [ pos (suc (suc k)) / 2+ n ] ℚ.- [ pos (suc k) / 2+ n ]}
             {y = [ 1 / 2+ n ]}
             rat (ℚ.n/k-m/k (pos (suc (suc k))) (pos (suc k)) (2+ n)  ∙
                cong [_/ 2+ n ] (cong (ℤ._- pos (suc k)) (ℤ.pos+ 1 (suc k))
                
                 ∙ ℤ.plusMinus (pos (suc k)) 1))
                 
 equalPartition-2ⁿ : ℕ → Partition[ a , b ] 
 equalPartition-2ⁿ n = equalPartition (predℕ (predℕ (2^ (suc n))))


llll : absᵣ (rat [ pos 0 / 1+ 0 ] -ᵣ rat [ pos 0 / 1+ 0 ]) ≤ᵣ
      rat [ pos 0 / 1+ 0 ]
llll = ≡ᵣWeaken≤ᵣ _ _
   (cong absᵣ (-ᵣ-rat₂ _ _) ∙ absᵣ0
     ∙ cong {x = zero} (λ z → rat [ pos z / 1+ z ]) refl )
  
0<2^-ℚ : ∀ n → ℚ.0< [ pos (2^ n) / 1+ 0 ]
0<2^-ℚ n = ℚ.<→0< [ pos (2^ n) / 1+ 0 ] (ℚ.<ℤ→<ℚ 0 (pos (2^ n))
 (invEq (ℤ.pos-<-pos≃ℕ< 0 _) (0<2^ n) ))

2^-mon : ∀ n → 2^ n ℕ.< 2^ (suc n)
2^-mon zero = ℕ.≤-solver 2 2
2^-mon (suc n) = ℕ.<-+-< (2^-mon n) (2^-mon n) 

lemXX : ∀ n → 2 ℕ.+ predℕ (predℕ (2^ (suc n))) ≡ 2^ (suc n)
lemXX n = ℕ.k+predℕₖ {2} {2^ (suc n)} (ℕ.≤-+-≤ {1} {2^ n} {1} {2^ n}
 (0<2^ n) (0<2^ n))

invℚ₊-inj : ∀ a b → fst (invℚ₊ a) ≡ fst (invℚ₊ b) → fst a ≡ fst b 
invℚ₊-inj a b x =
  sym (ℚ.invℚ₊-invol _)
  ∙∙ cong (fst ∘ invℚ₊) (ℚ₊≡ x) ∙∙
  ℚ.invℚ₊-invol _


module Resample where

 clampDeltaSplit : ∀ L L' x y → L ≤ᵣ L' → x ≤ᵣ y
             → (y -ᵣ x) ≡
               (minᵣ L y -ᵣ minᵣ L x)
                +ᵣ (clampᵣ L L' y -ᵣ clampᵣ L L' x)
                +ᵣ (maxᵣ L' y -ᵣ maxᵣ L' x)
 clampDeltaSplit = {!!}

 resampledRiemannSum' : ∀ a b →  (ℝ → ℝ)
   → (pa pa' : Partition[ a , b ])
    (s : Sample pa) → ℝ
 resampledRiemannSum' a b f pa pa' sa =
   foldlFin {n = 2 ℕ.+ P'.len}
      (λ s  k →
        let  a' = P'.pts' (finj k)
             b' = P'.pts' (fsuc k)
        in s +ᵣ
            foldlFin {n = 2 ℕ.+ P.len}
            (λ s ((t , a≤t , t≤b) , b-a) → s +ᵣ
              b-a ·ᵣ (f t) ) 0
                (λ k →  S.samplesΣ k ,
                 clampᵣ a' b' (P.pts' (fsuc k))
                  -ᵣ clampᵣ a' b' (P.pts' (finj k)))
        )
      0
      (idfun _)

  where
  module P = Partition[_,_] pa
  module P' = Partition[_,_] pa'
  module S = Sample sa


 resampledRiemannSum : ∀ a b → a ≤ᵣ b →  (∀ r → a ≤ᵣ r → r ≤ᵣ b → ℝ)
   → (pa pa' : Partition[ a , b ])
    (s : Sample pa) → ℝ
 resampledRiemannSum a b a≤b f pa pa' sa =
   foldlFin {n = 2 ℕ.+ P'.len}
      (λ s  k →
        let  a' = P'.pts' (finj k)
             b' = P'.pts' (fsuc k)
        in s +ᵣ
            foldlFin {n = 2 ℕ.+ P.len}
            (λ s ((t , a≤t , t≤b) , b-a) → s +ᵣ
              b-a ·ᵣ (f (clampᵣ a' b' t)
                (isTrans≤ᵣ _ _ _ (P'.a≤pts' (finj k))
                  (≤clampᵣ a' b' t (P'.pts'≤pts' k)))
                (isTrans≤ᵣ _ _ _ (clamp≤ᵣ a' b' t) (P'.pts'≤b (fsuc k)))) ) 0
                (λ k →  S.samplesΣ k , P.pts' (fsuc k) -ᵣ P.pts' (finj k))
        )
      0
      (idfun _)
      
      -- (λ k →  k (P'.pts' (fsuc k) , P'.pts' (finj k)))
  -- foldlFin {n = 2 ℕ.+ P.len}
  --    (λ s ((t , a≤t , t≤b) , b-a) → s +ᵣ
  --      b-a ·ᵣ (f t a≤t t≤b) ) 0
  --        (λ k →  S.samplesΣ k , P.pts' (fsuc k) -ᵣ P.pts' (finj k))
  where
  module P = Partition[_,_] pa
  module P' = Partition[_,_] pa'
  module S = Sample sa
  
 resample : ∀ a b → a ≤ᵣ b → (pa pa' : Partition[ a , b ])
    (sa : Sample pa)  → ∀ f 
    → resampledRiemannSum' a b f pa pa' sa
       ≡ riemannSum' sa f
 resample = {!!}

 partitionClamp : ∀ a b → a <ᵣ b → ∀ a' b' → a' ≤ᵣ b'
   → a ≤ᵣ a' →  b' ≤ᵣ b →  
   (pa : Partition[ a , b ]) →
    b' -ᵣ a' ≡
         foldlFin {n = 2 ℕ.+ len pa}
      (λ s  k →
        let  a* = pts' pa (finj k)
             b* = pts' pa (fsuc k)
        in s +ᵣ
            ((clampᵣ a' b' b* -ᵣ clampᵣ a' b' a*))
        )
      0
      (idfun _) 
 partitionClamp = {!!}
 
 resampleΔ-UC : ∀ a b → a <ᵣ b → (pa pa' : Partition[ a , b ])
    (sa : Sample pa)  → ∀ f → IsUContinuous f → (ε : ℚ₊)  
    → ∃[ δ ∈ ℚ₊ ]
     (mesh pa <ᵣ rat (fst δ) → mesh pa' <ᵣ rat (fst δ) →
      absᵣ (riemannSum' sa f -ᵣ riemannSum' (leftSample pa') f) <ᵣ
     rat (fst ε))
 resampleΔ-UC a b a<b pa pa' sa f fcu ε =
   PT.map
     (map-snd (λ {δ} X m-pa< m-pa'< → 
       isTrans≡<ᵣ _ _ _
        (cong absᵣ
         (cong (_-ᵣ_ (S.riemannSum' f))
           (sym (resample a b (<ᵣWeaken≤ᵣ _ _ a<b) pa' pa (leftSample pa') f))
           ∙ zip-foldFin-ᵣ (2 ℕ.+ len pa)
             
             (λ k →  S.samplesΣ k , P.pts' (fsuc k) -ᵣ P.pts' (finj k))
             (idfun _)
             _ _ _ _))
        (isTrans<≡ᵣ _ _ _
          
          (foldFin+<-abs (2 ℕ.+ len pa) ℕ.zero-<-suc _ 0
            _ (λ k → (pts' pa (fsuc k) -ᵣ pts' pa (finj k)) ·ᵣ
                         fst η)
                          (λ k →
                            (S.samplesΣ k ,
                             P.pts' (fsuc k) -ᵣ P.pts' (finj k)) , k)
                          (idfun _)
           llll
           {!ruc!} 
           )
          {!!})

       ))
    (IsUContinuous-εᵣ f fcu
     (ℚ₊→ℝ₊ ε ₊·ᵣ invℝ₊ (_ , x<y→0<y-x _ _ a<b)))

  where
    η : ℝ₊
    η = (ℚ₊→ℝ₊ ε ₊·ᵣ invℝ₊ (_ , x<y→0<y-x _ _ a<b))
    module P = Partition[_,_] pa
    module P' = Partition[_,_] pa'
    module S = Sample sa

    ruc : ∀ k →
        absᵣ
      ((P.pts' (fsuc k) -ᵣ P.pts' (finj k)) ·ᵣ f (S.samplesΣ k .fst) -ᵣ
       foldlFin
       (λ s ((t , a≤t , t≤b) , b-a) → s +ᵣ b-a ·ᵣ f t) 0
       (λ k₁ →
          P'.samplesΣ P'.leftSample k₁ ,
          clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' (fsuc k₁))
          -ᵣ clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' (finj k₁))))
      <ᵣ
      (P.pts' (fsuc k) -ᵣ P.pts' (finj k))
      ·ᵣ fst η
    ruc k = 
      isTrans≡<ᵣ _ _ _
        (cong (absᵣ ∘ (_-ᵣ (foldlFin
       (λ s ((t , a≤t , t≤b) , b-a) → s +ᵣ b-a ·ᵣ f t) 0
       (λ k₁ →
          P'.samplesΣ P'.leftSample k₁ ,
          clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' (fsuc k₁))
          -ᵣ clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k)) (P'.pts' (finj k₁))
          ))))
           (cong (_·ᵣ f (S.samplesΣ k .fst))
             (partitionClamp a b a<b
               (P.pts' (finj k))
               (P.pts' (fsuc k))
                (P.pts'≤pts' k)
               (P.a≤pts' (finj k)) (P.pts'≤b (fsuc k)) pa'
               ) ∙ ·ᵣComm _ _ ∙
                sym (foldFin·DistL (2 ℕ.+ len pa') _ _ _
                 (idfun _))) ∙
                cong absᵣ
                 (zip-foldFin-ᵣ (2 ℕ.+ len pa')
                 (idfun _)
                  (λ k₁ →
                    (samplesΣ P'.leftSample k₁ ,
                        clampᵣ (P.pts' (finj k))
                         (P.pts' (fsuc k)) (P'.pts' (fsuc k₁))
                     -ᵣ clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k))
                         (P'.pts' (finj k₁))))
                    _ _ _
                  0))
           (isTrans<≡ᵣ _ _ _
            (foldFin+<-abs (2 ℕ.+ len pa')
              ℕ.zero-<-suc _ 0 _
                (λ kk → 
                 (clampᵣ (P.pts' (finj k)) ((P.pts' (fsuc k)))
                  (P'.pts' (fsuc kk)) -ᵣ
                   clampᵣ (P.pts' (finj k)) ((P.pts' (fsuc k)))
                    (P'.pts' (finj kk)))
                         ·ᵣ fst η)
                ((λ k₁ → k₁ ,
                    (samplesΣ P'.leftSample k₁ ,
                       clampᵣ (P.pts' (finj k))
                        (P.pts' (fsuc k)) (P'.pts' (fsuc k₁))
                          -ᵣ clampᵣ (P.pts' (finj k)) (P.pts' (fsuc k))
                          (P'.pts' (finj k₁)))))
                (idfun _)
                {!!}
              {!!})
            {!!} )

-- Integrate-UContinuous : ∀ (a b : ℚ) → a ℚ.< b → ∀ f → IsUContinuous f →
--  Σ ℝ λ R → on[ (rat a) , (rat b) ]IntegralOf f is' R 
-- Integrate-UContinuous a b a<b f ucf =
--  (lim (s ∘ fst ∘ z) λ δ ε →
--   invEq (∼≃abs<ε ((s (fst (z δ)))) (s (fst (z ε))) (δ ℚ₊+ ε)) (z-C δ ε))
--   , isI
--  where

--  Δ : ℚ₊
--  Δ = ℚ.<→ℚ₊ a b a<b

--  open Integration (rat a) (rat b) (<ᵣWeaken≤ᵣ _ _ (<ℚ→<ᵣ _ _ a<b)) hiding (Δ)

--  s : ℕ → ℝ
--  s n = riemannSum' (leftSample (equalPartition-2ⁿ n)) f

--  zTySnd : ℚ₊ → ℕ → Type
--  zTySnd ε =
--    (λ n → (u v : ℝ) → absᵣ (u -ᵣ v)
--        <ᵣ rat (fst Δ ℚ.· fst (invℚ₊ ([ pos (2^ (suc n)) / one ]
--         , 0<2^-ℚ (suc n)))) →
--         absᵣ (f u -ᵣ f v) <ᵣ rat (fst (ε ℚ₊· invℚ₊ Δ)))
--  z : (ε : ℚ₊) → Σ ℕ (zTySnd ε)
--  z ε =
--   let (δ , X) = ucf (ε ℚ₊· invℚ₊ Δ)
--       ((m , u) , p , (0≤u , _)) = ℚ.ceil-[1-frac]ℚ₊ (Δ ℚ₊· invℚ₊ δ)
--       (n , (N , _)) = log2ℕ m
--       ppp : _
--       ppp = ℚ.≤ℤ→≤ℚ _ _ (invEq (ℤ.pos-≤-pos≃ℕ≤ _ _)
--                   (ℕ.<-weaken  (ℕ.<-trans (subst (m ℕ.<_) (sym (2^-^ n)) N)
--                    (2^-mon n))))
--       qq : (fst (Δ ℚ₊· invℚ₊ δ)) ℚ.≤ [ pos m / one ]
--       qq = subst2 (ℚ._≤_) (ℚ.+IdR (fst (Δ ℚ₊· invℚ₊ δ))) p
--             (ℚ.≤-o+ _ _ (fst (Δ ℚ₊· invℚ₊ δ)) 0≤u)
--       p' : (fst (Δ ℚ₊· invℚ₊ δ)) ℚ.≤ ([ pos (2^ (suc n)) / one ])
--       p' = ℚ.isTrans≤ (fst (Δ ℚ₊· invℚ₊ δ)) _ _ qq ppp
--       Δ/2^n<δ : (fst Δ ℚ.· _) ℚ.≤ (fst δ)
--       Δ/2^n<δ = ℚ.x≤y·z→x·invℚ₊y≤z (fst Δ) (fst δ)
--          ([ pos (2^ (suc n)) / one ] , 0<2^-ℚ (suc n))
--           (subst ((fst Δ) ℚ.≤_ )
--            (ℚ.·Comm (fst δ) [ pos (2^ (suc n)) / one ])
--             (ℚ.x·invℚ₊y≤z→x≤y·z (fst Δ) [ pos (2^ (suc n)) / one ] δ p')  )
          
--       xzx : (u v : ℝ) → absᵣ (u -ᵣ v)
--        <ᵣ rat (fst Δ ℚ.· fst (invℚ₊ ([ pos (2^ (suc n)) / one ] , 0<2^-ℚ (suc n)))) →
--         absᵣ (f u -ᵣ f v) <ᵣ rat (fst (ε ℚ₊· invℚ₊ Δ))
--       xzx u v =
--         fst (∼≃abs<ε _ _ _)
--          ∘ X u v ∘ invEq (∼≃abs<ε _ _ _)
--           ∘ flip (isTrans<≤ᵣ _
--            (rat ( (fst Δ ℚ.·
--               (fst (invℚ₊ ([ pos (2^ (suc n)) / 1+ zero ] , 0<2^-ℚ (suc n))))))) _)
--                (≤ℚ→≤ᵣ _ _ Δ/2^n<δ) 
   
--   in (n , xzx)


--  c-C : ∀ (ε : ℚ₊) n m 
--           → ((u v : ℝ) → absᵣ (u -ᵣ v) <ᵣ
--             rat (fst Δ ℚ.·
--              fst (invℚ₊ ([ pos (2^ (suc n)) / one ] , 0<2^-ℚ (suc n))))
--                 → absᵣ (f u -ᵣ f v) <ᵣ rat (fst (ε ℚ₊· invℚ₊ Δ)))
         
--           → absᵣ (s (n ℕ.+ m) -ᵣ s n) <ᵣ rat (fst ε) 
--  c-C ε n m X =
--    isTrans<≡ᵣ _ _ _ (isTrans≡<ᵣ _ _ _
--      (cong absᵣ zzz'')
--       ((foldFin+<-abs (2^ (suc n)) (0<2^ (suc n)) _ 0 _
--         (λ _ → rat (fst ε) ·ᵣ
--             (rat (fst (invℚ₊ ([ pos (2^ (suc n)) / 1+ zero ] , 0<2^-ℚ (suc n))))))
--              _ (λ _ → tt)
--         llll uuzz)))
--       ((foldFin+Const (2^ (suc n)) _ (λ _ → tt) ∙
--            ·ᵣComm _ _
--            ∙ sym (·ᵣAssoc _ _ _)
--            ∙ 𝐑'.·IdR' _ _
--             (sym (rat·ᵣrat _ _)
--              ∙ cong rat
--              (ℚ.invℚ₊[x]·x ([ pos (2^ (suc n)) / one ] , 0<2^-ℚ (suc n))) )))
--   where
--   ss' :  Fin (2 ℕ.+ predℕ (predℕ (2^ (suc (n))))) →
--         Σ (Σ ℝ (λ t₁ → (rat a ≤ᵣ t₁) × (t₁ ≤ᵣ rat b))) (λ v → ℝ)
--   ss' k = EP.samplesΣ EP.leftSample k ,
--         EP.pts'  (fsuc k) -ᵣ EP.pts'  (finj k)
--    where 
--    module EP = Partition[_,_] (equalPartition (predℕ (predℕ (2^ (suc n)))))


--   ss : Fin (2 ℕ.+ predℕ (predℕ (2^ (suc (n ℕ.+ m))))) →
--         Σ (Σ ℝ (λ t₁ → (rat a ≤ᵣ t₁) × (t₁ ≤ᵣ rat b))) (λ v → ℝ)
--   ss k = EP.samplesΣ EP.leftSample k ,
--         EP.pts'  (fsuc k) -ᵣ EP.pts'  (finj k)
--    where 
--    module EP = Partition[_,_] (equalPartition (predℕ (predℕ (2^ (suc n ℕ.+ m)))))

--   fp : 2 ℕ.+ predℕ (predℕ (2^ (suc (n ℕ.+ m)))) ≡ 2^ (suc (n ℕ.+ m))
--   fp = lemXX (n ℕ.+ m)

--   fp' : 2 ℕ.+ predℕ (predℕ (2^ (suc n))) ≡ 2^ (suc n)
--   fp' = lemXX n


--   aaa : _
--   aaa = _

--   zz : s (n ℕ.+ m) ≡ foldlFin {n = 2^ (suc n)} (foldlFin {n = 2^ m} aaa)
--                       (rat [ pos 0 / 1+ 0 ])
--                       (curry ((ss ∘ substFin (sym fp)) ∘ Fin^2· (suc n) m))
--   zz = foldlFin-substN
--       {n = 2 ℕ.+ predℕ (predℕ (2^ (suc (n ℕ.+ m))))}
--       {n' = 2^ (suc (n ℕ.+ m))}
--       fp (λ S ((t , a≤t , t≤b) , b-a) → S +ᵣ b-a ·ᵣ (f t) )
--         0 ss
--      ∙ foldFin·2^ (suc n) m _ 0 _


--   zz' : foldlFin {n = 2^ (suc n)} (foldlFin {n = 2^ m} aaa)
--                       (rat [ pos 0 / 1+ 0 ])
--                       (curry ((ss ∘ substFin (sym fp)) ∘ Fin^2· (suc n) m))
--                ≡ _
--   zz' = cong (λ ff → foldlFin {n = 2^ (suc n)} ff
--                       (rat [ pos 0 / 1+ 0 ])
--                       (curry ((ss ∘ substFin (sym fp)) ∘ Fin^2· (suc n) m)))
--               (funExt₂
--                  λ xx y → foldFin+0ᵣ (2^ m) _ _ xx)
                 
--   zzz'' : s (n ℕ.+ m) -ᵣ s n ≡
--      foldlFin {n = 2^ (suc n)} _
--          (0 -ᵣ 0)
--          _
--   zzz'' = cong₂ _-ᵣ_ (zz ∙ zz')
--          (foldlFin-substN
--       {n = 2 ℕ.+ predℕ (predℕ (2^ (suc n)))}
--       {n' = 2^ (suc n)}
--       fp' (λ S ((t , a≤t , t≤b) , b-a) → S +ᵣ b-a ·ᵣ (f t) )
--         0 ss')
--          ∙
--        zip-foldFin-ᵣ (2^ (suc n)) _ _ _ _
--         0 0


--   uuzzz : (k : Fin (2^ (suc n))) (k' : Fin (2^ m)) →
--      absᵣ
--       ((ss (substFin (λ i → fp (~ i)) (Fin^2· (suc n) m (k , k')))) 
--        .snd
--        ·ᵣ
--        f ((ss (substFin (λ i → fp (~ i)) (Fin^2· (suc n) m (k , k')))) 
--         .fst .fst)
--        -ᵣ
--        rat (fst (invℚ₊ ([ pos (2^ m) / 1+ 0 ] , 0<2^-ℚ m))) ·ᵣ
--        (ss' (substFin (sym fp') k) .snd ·ᵣ
--         f (ss' (substFin (sym fp') k) .fst .fst))) <ᵣ
--          rat (fst ε) ·ᵣ rat (fst (invℚ₊ ([ pos (2^ (suc n)) / one ] ,
--           (0<2^-ℚ (suc n)))))
--            ·ᵣ rat (fst (invℚ₊ ([ pos (2^ m) / one ] , 0<2^-ℚ m)))
--   uuzzz k k' = isTrans<≡ᵣ _ _ _
--     (isTrans≡<ᵣ _ _ _
--     (zzz)
--     (<ᵣ-o·ᵣ _ _ (absᵣ
--                  (Δ''
--                   ·ᵣ rat [ 1 / 2+ predℕ (predℕ (2^ (suc n ℕ.+ m))) ])
--                  , isTrans<≤ᵣ _ _ _
--                     (snd ((_ , x<y→0<y-x _ _ (<ℚ→<ᵣ _ _ a<b))
--                     ₊·ᵣ ℚ₊→ℝ₊ _)) (≤absᵣ _))
--                   (X _ _
--                     (isTrans<≡ᵣ _ _ _ (isTrans≡<ᵣ _ _ _
--                      (cong absᵣ
--                       L𝐑.lem--063)
--                      (isTrans≡<ᵣ _ _ _
--                       (absᵣNonNeg _
--                         (NonNeg·ᵣ _ _ 
--                             ((<ᵣWeaken≤ᵣ _ _
--                              (x<y→0<y-x _ _ (<ℚ→<ᵣ _ _ a<b))))
--                               ((≤ℚ→≤ᵣ _ _
--                               (ℚ.0≤pos (fst k')
--                               (2+ predℕ (predℕ (2^ (n ℕ.+ m)
--                               ℕ.+ 2^ (n ℕ.+ m)))))))))
--                       (isTrans≡<ᵣ _ _ _
--                        (cong (_·ᵣ
--                 rat [ pos (fst k')
--                   / 2+ predℕ (predℕ (2^ (n ℕ.+ m) ℕ.+ 2^ (n ℕ.+ m))) ])
--                    (-ᵣ-rat₂ _ _)
--                  ∙ sym (rat·ᵣrat _ _))
--                   (<ℚ→<ᵣ _ _
--                      (ℚ.<-o· _ [ pos (2^ m) / _ ] (b ℚ.- a)
--                     (ℚ.-< a b a<b)
--                    (ℚ.[k/n]<[k'/n] (pos (fst k')) _
--                      (2+ predℕ (predℕ (2^ (n ℕ.+ m) ℕ.+ 2^ (n ℕ.+ m))))
--                     (invEq (ℤ.pos-<-pos≃ℕ< _ _) (snd k'))))))))
--                      (cong rat (cong (fst Δ ℚ.·_)
--                       (cong [_/ (2+ predℕ (predℕ (2^ (n ℕ.+ m) ℕ.+ 2^ (n ℕ.+ m)))) ]
--                        (cong pos (sym (ℕ.·-identityʳ _)))
--                       ∙ qqquuu 1 ∙
--                        cong [ 1 /_]
--                        (cong (1+_ ∘ predℕ) (lemXX n)
--                          ∙ ℕ₊₁→ℕ-lem _ _ (ℤ.injPos $
--                            (snd (ℤ.0<→ℕ₊₁ (pos (2^ (suc n)))
--                              (0<2^-ℚ (suc n))))))))) ))
--                     ))
--                       (cong₂ _·ᵣ_ (absᵣNonNeg _
--                        (NonNeg·ᵣ _ _
--                         (<ᵣWeaken≤ᵣ _ _ (x<y→0<y-x _ _ (<ℚ→<ᵣ _ _ a<b)))
--                          (≤ℚ→≤ᵣ _ _
--                           ((ℚ.0≤pos 1
--                            (2+ predℕ (predℕ (2^ (n ℕ.+ m) ℕ.+ 2^ (n ℕ.+ m)))))))))
--                         refl
--                         -- (cong rat (ℚ.·Comm (fst ε) (fst (invℚ₊ Δ))))
--                        ∙ (cong₂ _·ᵣ_
--                          (cong₂ _·ᵣ_
--                            (-ᵣ-rat₂ _ _)
--                            (cong rat
--                              (cong
--                                  {x = [
--                                    pos (2 ℕ.+ predℕ (predℕ (2^ (suc n ℕ.+ m))))
--                                     / 1 ] , _}
--                                  {y = (([ pos (2^ n ℕ.+ 2^ n) / one ]
--                                   , 0<2^-ℚ (suc n)) ℚ₊·
--                              ([ pos (2^ m) / one ] , 0<2^-ℚ m))}
--                              (fst ∘ invℚ₊)
--                                (ℚ₊≡ (cong [_/ 1 ]
--                                 (cong pos (lemXX (n ℕ.+ m)
--                                   ∙ 2^+ (suc n) m)
--                                     ∙ ℤ.pos·pos (2^ (suc n)) (2^ m) )))
--                               ∙ cong fst
--                                (sym (ℚ.invℚ₊Dist·
--                                 ([ pos (2^ n ℕ.+ 2^ n) / one ] , 0<2^-ℚ (suc n))
--                                 ([ pos (2^ m) / one ] , 0<2^-ℚ m)))) ∙
--                              rat·ᵣrat _ _))
--                          (rat·ᵣrat _ _ ∙
--                           cong (rat (fst ε) ·ᵣ_)
--                             (sym (invℝ₊-rat _)) )
--                          ∙∙ L𝐑.lem--090
--                          ∙∙ [x·yᵣ]/₊y _ (ℚ₊→ℝ₊ Δ)))

--    where

   

--     Δ'' = Integration.Δ (rat a) (rat b)
--         (<ᵣWeaken≤ᵣ (rat a) (rat b) (<ℚ→<ᵣ a b a<b))

--     k* = substFin (sym fp') k
--     kk = (substFin (λ i → fp (~ i)) (Fin^2· (suc n) m (k , k')))

--     qqquuu : ∀ l → ℚ.[
--               pos (2^ m ℕ.· l) ,
--               (2+ predℕ (predℕ (2^ (n ℕ.+ m) ℕ.+ 2^ (n ℕ.+ m))))
--               ]
--               ≡ ℚ.[ pos (l) , (2+ predℕ (predℕ (2^ (suc n)))) ]
--     qqquuu l = (ℚ.eq/ _ _
--                     (cong₂ ℤ._·_
--                      (ℤ.pos·pos (2^ m) l ∙
--                        ℤ.·Comm (pos (2^ m)) (pos l))
--                       ((sym (snd (ℤ.0<→ℕ₊₁ _ (tt)))) ∙
--                         cong pos (lemXX n))
--                      ∙ sym (ℤ.·Assoc (pos l) _ _)
--                       ∙ cong (pos l ℤ.·_)
--                        (ℤ.·Comm (pos (2^ m)) _
--                         ∙ (sym (ℤ.pos·pos (2^ (suc n)) (2^ m)) ∙
--                          cong pos (sym (2^+ (suc n) m)))
--                           ∙ cong (pos) (sym (lemXX (n ℕ.+ m))))))

--     zzz : absᵣ (ss (substFin (λ i → fp (~ i)) (Fin^2· (suc n) m (k , k'))) .snd
--             ·ᵣ
--             f
--             (ss (substFin (λ i → fp (~ i)) (Fin^2· (suc n) m (k , k'))) .fst
--              .fst)
--             -ᵣ
--             rat (fst (invℚ₊ ([ pos (2^ m) / 1+ 0 ] , 0<2^-ℚ m))) ·ᵣ
--             (ss' (substFin (sym fp') k) .snd ·ᵣ
--              f (ss' (substFin (sym fp') k) .fst .fst)))
--            ≡ _

--     zzz = cong absᵣ (cong₂ _-ᵣ_
--         (cong₂ _·ᵣ_ (equalPartitionΔ
--          (predℕ (predℕ (2^ (suc n ℕ.+ m)))) kk)
--           (cong f ((equalPartitionPts'
--          (predℕ (predℕ (2^ (suc n ℕ.+ m)))) (finj kk) ∙
--           cong (rat a +ᵣ_) (cong (Δ'' ·ᵣ_) (cong rat
--            (cong [_/ (2+ predℕ (predℕ (2^ (suc n ℕ.+ m)))) ]
--             (ℤ.pos+ (2^ m ℕ.· fst k) (fst k'))
--              ∙ sym (ℚ.n/k+m/k (pos (2^ m ℕ.· fst k)) (pos (fst k')) _))
--              ∙ sym (+ᵣ-rat
--                [ (pos (2^ m ℕ.· fst k)) / (2+ predℕ (predℕ (2^ (suc n ℕ.+ m)))) ]
--                [ (pos (fst k')) / (2+ predℕ (predℕ (2^ (suc n ℕ.+ m)))) ]
--                ))
--               ∙ ·DistL+ _ _ _) ∙
--             +ᵣAssoc _ _ _
--             ∙ cong₂ _+ᵣ_ (cong (rat a +ᵣ_)
--                 (cong {y = rat [ pos (fst (finj k*))
--                   / 2+ predℕ (predℕ (2^ (suc n))) ]} (Δ'' ·ᵣ_)
--                   (cong rat (qqquuu (fst k)))))
--                    refl))))
--         (cong (rat (fst (invℚ₊ ([ pos (2^ m) / 1+ 0 ] , 0<2^-ℚ m)))
--              ·ᵣ_)
--               (cong₂ _·ᵣ_  ((equalPartitionΔ
--          (predℕ (predℕ (2^ (suc n)))) k*))
--                 (cong f
--                  (equalPartitionPts'
--          (predℕ (predℕ (2^ (suc n)))) (finj k*)))
--             ) ∙ ·ᵣAssoc _ _ _ ∙ cong₂ _·ᵣ_
--              (·ᵣComm _ _ ∙ sym (·ᵣAssoc _ _ _) ∙
--               cong {y = rat [ 1 / 2+ predℕ (predℕ (2^ (suc n ℕ.+ m))) ]}
--                (Δ'' ·ᵣ_) (sym (rat·ᵣrat _ _) ∙
--                 cong rat (ℚ.[1/n]·[1/m]≡[1/n·m]
--                   (2+ predℕ (predℕ (2^ (suc n))))
--                   _ ∙ invℚ₊-inj _ _ (cong [_/ one ]
--                    (cong (pos) (cong₂ (ℕ._·_) (lemXX n)
--                    (cong ℤ.abs (sym (snd (ℤ.0<→ℕ₊₁ _ ((0<2^-ℚ m))))))
--                     ∙∙ sym (2^+ (suc n) m) ∙∙
--                     sym (lemXX (n ℕ.+ m))
--                      ))) ))) refl  )
--          ∙ sym (𝐑'.·DistR- _ _ _))
--          ∙ ·absᵣ _ _ 
     
--   uuzz : (k : Fin (2^ (suc n))) →
--           absᵣ
--           (foldlFin (λ a₁ y → a₁ +ᵣ y .snd ·ᵣ f (y .fst .fst)) 0
--            (curry
--             (λ x₁ → ss (substFin (λ i → fp (~ i)) (Fin^2· (suc n) m x₁))) k)
--            -ᵣ
--            (ss' (substFin (sym fp') k)) .snd
--            ·ᵣ
--            f ((ss' (substFin (sym fp') k)) .fst .fst))
--           <ᵣ
--           rat (fst ε) ·ᵣ rat (fst (invℚ₊ ([ pos (2^ (suc n)) / one ] , _)))
--   uuzz k = isTrans≡<ᵣ _ _ _
--     (cong absᵣ
--      (cong (_-ᵣ_ (foldlFin (λ a₁ y → a₁ +ᵣ y .snd ·ᵣ f (y .fst .fst)) 0
--            (curry
--             (λ x₁ → ss (substFin (λ i → fp (~ i)) (Fin^2· (suc n) m x₁))) k))
--              ) (((sym (𝐑'.·IdL' _ _
--                (sym (rat·ᵣrat _
--                 ((fst (invℚ₊ (([ pos (2^ m) / 1+ 0 ] ,
--                   0<2^-ℚ m))))))
--                  ∙ cong rat (ℚ.x·invℚ₊[x] ([ pos (2^ m) / 1+ 0 ] ,
--                   0<2^-ℚ m)))))
--               ∙ sym (·ᵣAssoc _ _ _)) ∙
--                sym (foldFin+Const (2^ m) _ (λ _ → tt)))
--                ∙
--                zip-foldFin-ᵣ (2^ m) _ _ _ _ _ _)
--                )
--     (isTrans<≡ᵣ _ _ _
--        (foldFin+<-abs (2^ m) (0<2^ m) _ 0 _
--          (λ _ → rat (fst ε) ·ᵣ rat (fst (invℚ₊ ([ pos (2^ (suc n)) / one ] ,
--           (0<2^-ℚ (suc n)))))
--            ·ᵣ rat (fst (invℚ₊ ([ pos (2^ m) / one ] , 0<2^-ℚ m)))) _
--            (λ _ → tt)
--          llll (uuzzz k))
--        (foldFin+Const (2^ m) _ (λ _ → tt) ∙
--            ·ᵣComm _ _
--            ∙ sym (·ᵣAssoc _ _ _)
--            ∙ 𝐑'.·IdR' _ _
--             (sym (rat·ᵣrat _ _)
--              ∙ cong rat (ℚ.invℚ₊[x]·x ([ pos (2^ m) / one ] , 0<2^-ℚ m))))) 
  
--  z-C : (δ ε : ℚ₊) → absᵣ (s (fst (z δ)) -ᵣ s (fst (z ε))) <ᵣ rat (fst (δ ℚ₊+ ε))
--  z-C δ ε = 
--       ℕ.elimBy≤+ {A = λ n n' → ∀ δ ε  
--        → zTySnd δ n
--        → zTySnd ε n'
--        → absᵣ (s n -ᵣ s n') <ᵣ rat (fst (δ ℚ₊+ ε))}
--       (λ x y X δ ε x' y' → 
--        subst2 _<ᵣ_
--          (minusComm-absᵣ _ _)
--          (cong rat (ℚ.+Comm (fst ε) (fst δ) ))
--          (X ε δ y' x'))
--       (λ x y δ ε X _ →
--         isTrans≡<ᵣ _ _ _
--           ((λ i → absᵣ (s x -ᵣ s (ℕ.+-comm y x i)))
--             ∙ minusComm-absᵣ _ _)
--           (isTrans<≤ᵣ _ _ _
--            (c-C δ x y X)
--            (≤ℚ→≤ᵣ _ _ (ℚ.≤+ℚ₊ (fst δ) (fst δ) ε (ℚ.isRefl≤ (fst δ))))))
--       (fst (z δ)) (fst (z ε)) δ ε (snd (z δ)) (snd (z ε))


--  isI-lem : ∀ (ε : ℚ₊) (n : ℕ) →
--            ∀ ((p , t) : TaggedPartition[ (rat a) , (rat b) ]) →
--             (mesh p <ᵣ rat (fst ?) →
--               absᵣ (riemannSum' t f -ᵣ s) <ᵣ rat (fst ε))

--  isI-lem = {!!}
 
--  isI : on[ rat a , rat b ]IntegralOf f is'
--         lim (λ x → s (fst (z x)))
--         (λ δ ε →
--            invEq (∼≃abs<ε (s (fst (z δ))) (s (fst (z ε))) (δ ℚ₊+ ε))
--            (z-C δ ε))
--  isI ε =
--    let (δ , Xδ) = ucf (ε ℚ₊· invℚ₊ Δ)
--    in ∣ δ , {!!} ∣₁

-- -- IntegralOf-UContinuous : ∀ a b a≤b f iucf
-- --    → on[ (rat a) , (rat b) ]IntegralOf f is'
-- --      (Integrate-UContinuous a b a≤b f iucf) 
-- -- IntegralOf-UContinuous a b a≤b₁ f iucf ε =
-- --   {!!}


-- -- -- Integral'-additive : ∀ a b c f s s' →
-- -- --   on[ a , b ]IntegralOf f is' s →
-- -- --   on[ b , c ]IntegralOf f is' s' →
-- -- --   on[ a , c ]IntegralOf f is' (s +ᵣ s')
-- -- -- Integral'-additive a b c f s s' S S' ε =
-- -- --   let P = S  (/2₊ ε)
-- -- --       P' = S' (/2₊ ε)
-- -- --   in PT.map2 {!!} P P'
     
-- -- -- meanLemma : ∀ f x → IsContinuous f →
-- -- --   ∀ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]  
-- -- --     (∀ y → absᵣ (x -ᵣ y) <ᵣ (rat (fst δ))
-- -- --       → ∀ tp s → absᵣ (riemannSum' {a = x} {b = y} {tp} s f -ᵣ absᵣ (x -ᵣ y) ·ᵣ f x) <ᵣ absᵣ (x -ᵣ y) ·ᵣ (rat (fst ε)) )
-- -- -- meanLemma = {!riemannSum'!}


-- -- -- -- FTOC : ∀ x₀ (f g F : ℝ → ℝ) → IsContinuous f → IsContinuous F
-- -- -- --                  → (∀ x → x₀ ≤ᵣ x → on[ x₀ , x ]IntegralOf f is' F x)
-- -- -- --                  → (∀ x → x₀ ≤ᵣ x → derivativeOf F at x is' g x)
-- -- -- --                  → (∀ x → x₀ ≤ᵣ x → f x ≡ g x)
-- -- -- -- FTOC x₀ f F fC FC  D x x₀≤x ε' = {!!}


-- -- -- FTOC : ∀ x₀ (f F : ℝ → ℝ) → IsContinuous f → IsContinuous F
-- -- --                  → (∀ x → x₀ ≤ᵣ x → on[ x₀ , x ]IntegralOf f is' F x)
-- -- --                  → ∀ x → x₀ ≤ᵣ x → derivativeOf F at x is' f x
-- -- -- FTOC x₀ f F fC FC  D x x₀≤x ε' =  
-- -- --  PT.rec squash₁
-- -- --      (λ (η , Y)  →
-- -- --      let ε = ℚ.min₊ (/2₊ η) (/2₊ ε')
-- -- --      in 
-- -- --       PT.map2 (λ (δ , X) (δ' , X') →
-- -- --           let δ* = ℚ.min₊ (ℚ.min₊ δ δ') ε
-- -- --               ((tp , tp*) , (tpm , tpm*)) = tps x (ε) δ*
-- -- --               tp' = concatTaggedPartition _ _ _ tp tp*
-- -- --               tpm' : mesh (fst tp') <ᵣ rat (fst δ*)
-- -- --               tpm' = {!!}
-- -- --               z : absᵣ ((riemannSum' (snd tp) f -ᵣ F x)
-- -- --                     +ᵣ ((F (x +ᵣ rat (fst ε))) -ᵣ riemannSum' (snd tp') f))  <ᵣ rat (fst (ε ℚ₊· ε))
-- -- --               z = isTrans≤<ᵣ
-- -- --                      (absᵣ ((riemannSum' (snd tp) f -ᵣ F x)
-- -- --                     +ᵣ ((F (x +ᵣ rat (fst ε))) -ᵣ riemannSum' (snd tp') f)))
-- -- --                      _ _ (absᵣ-triangle
-- -- --                       (riemannSum' (snd tp) f -ᵣ F x)
-- -- --                        ((F (x +ᵣ rat (fst ε))) -ᵣ riemannSum' (snd tp') f))
-- -- --                     (isTrans<≡ᵣ (absᵣ (((riemannSum' (snd tp) f -ᵣ F x)))
-- -- --                             +ᵣ absᵣ (((F (x +ᵣ rat (fst ε))
-- -- --                         -ᵣ (riemannSum' (snd tp') f))))) _ _
-- -- --                    (<ᵣMonotone+ᵣ
-- -- --                      (absᵣ ((riemannSum' (snd tp) f -ᵣ F x))) _
-- -- --                       (absᵣ ((F (x +ᵣ rat (fst ε))
-- -- --                         -ᵣ (riemannSum' (snd tp') f)))) _
-- -- --                        (X tp (isTrans<≤ᵣ (mesh (fst tp)) _ _ tpm
-- -- --                           (( (
-- -- --                              (≤ℚ→≤ᵣ (fst δ*) (fst δ)
-- -- --                               (ℚ.isTrans≤ (fst δ*) _ (fst δ)
-- -- --                                ((ℚ.min≤ (ℚ.min (fst δ)  (fst δ') ) (fst ε)))
-- -- --                                 (ℚ.min≤ (fst δ) (fst δ'))))))) ))
-- -- --                        ((isTrans≡<ᵣ _ _ _
-- -- --                          (minusComm-absᵣ (F (x +ᵣ rat (fst ε)))
-- -- --                           (riemannSum' (snd tp') f)) (X' tp'
-- -- --                             (isTrans<≤ᵣ (mesh (fst tp')) _ _ tpm' (
-- -- --                              (≤ℚ→≤ᵣ (fst δ*) (fst δ')
-- -- --                               (ℚ.isTrans≤ (fst δ*) _ (fst δ')
-- -- --                                ((ℚ.min≤ (ℚ.min (fst δ)  (fst δ') ) (fst ε)))
-- -- --                                 (ℚ.min≤' (fst δ) (fst δ'))))))))))
-- -- --                     (cong rat (ℚ.ε/2+ε/2≡ε _)))
-- -- --               -- zzX : {!!}
-- -- --               -- xxX = {!!}
-- -- --               zz' : absᵣ ((riemannSum' (snd tp*) f)
-- -- --                        -ᵣ rat (fst ε) ·ᵣ differenceAt F x (rat (fst ε)) (inl (snd (ℚ₊→ℝ₊ ε))))
-- -- --                     <ᵣ rat (fst (ε ℚ₊· ε))
-- -- --               zz' = {!!}
-- -- --               -- z' : absᵣ (f x -ᵣ differenceAt F x (rat (fst ε)) (inl (snd (ℚ₊→ℝ₊ ε))))
-- -- --               --       <ᵣ rat (fst ε)      
-- -- --               -- z' = subst2 {x = rat (fst (invℚ₊ ε))
-- -- --               --           ·ᵣ (absᵣ ((riemannSum' (snd tp) f -ᵣ F x)
-- -- --               --       +ᵣ ((F (x +ᵣ rat (fst ε))) -ᵣ riemannSum' (snd tp') f)))}
-- -- --               --        {absᵣ
-- -- --               --         (f x -ᵣ differenceAt F x (rat (fst ε)) (inl (snd (ℚ₊→ℝ₊ ε)))) }
-- -- --               --           _<ᵣ_
-- -- --               --        ({!!}) (sym (rat·ᵣrat _ _) ∙
-- -- --               --                cong rat (ℚ.[y·x]/y ε _) )
-- -- --               --        (<ᵣ-o·ᵣ
-- -- --               --          (absᵣ ((riemannSum' (snd tp) f -ᵣ F x)
-- -- --               --       +ᵣ ((F (x +ᵣ rat (fst ε))) -ᵣ riemannSum' (snd tp') f)))
-- -- --               --          _ (ℚ₊→ℝ₊ (invℚ₊ ε)) z)

-- -- --               -- zz' = {!!}
-- -- --           in δ* ,
-- -- --              λ h → ⊎.elim
-- -- --               (λ 0<h h<δ* →
-- -- --                 let
-- -- --                     zz : absᵣ
-- -- --                           (riemannSum' (snd tp*) f -ᵣ absᵣ (x -ᵣ (x +ᵣ rat (fst ε))) ·ᵣ f x)
-- -- --                           <ᵣ absᵣ (x -ᵣ (x +ᵣ rat (fst ε))) ·ᵣ rat (fst (/4₊ (ε'))) 
-- -- --                     zz = Y (x +ᵣ (rat (fst ε)))
-- -- --                         {!!}
-- -- --                         (fst tp*)
-- -- --                         (snd tp*)
-- -- --                     tph : TaggedPartition[ x , x +ᵣ h ]
-- -- --                     tph = {!!}
-- -- --                     zzz* : absᵣ (riemannSum' (snd tph) f -ᵣ absᵣ h ·ᵣ f x) <ᵣ
-- -- --                            absᵣ h ·ᵣ rat (fst (/4₊ (ε')))
-- -- --                     zzz* =
-- -- --                      let uuuu = Y (x +ᵣ h) {!!} {!!} (snd tph) 
-- -- --                      in {!uuuu!}
                      
-- -- --                     zzz : absᵣ (f x -ᵣ differenceAt F x h (inl 0<h)) <ᵣ rat (fst ε')
-- -- --                     zzz = {!!}
-- -- --                 in zzz)
-- -- --               {!!})
-- -- --        (D x x₀≤x (/2₊ (ε ℚ₊· ε))) (D (x +ᵣ rat (fst ε)) {!!} (/2₊ (ε ℚ₊· ε))))
-- -- --        -- (FC x (/4₊ (ε' ℚ₊· ε')))
-- -- --        (meanLemma f x fC (/4₊ (ε')))

-- -- --  where
-- -- --   tps : ∀ x (ε δ : ℚ₊) → Σ (TaggedPartition[ x₀ , x ]
-- -- --               × TaggedPartition[ x , x +ᵣ rat (fst ε)  ])
-- -- --                 λ (tp ,  tp') → (mesh (fst tp) <ᵣ rat (fst δ))
-- -- --                      × (mesh (fst tp') <ᵣ rat (fst δ))
-- -- --   tps x h δ = {!!}
  
-- -- --   -- PT.map (λ (δ , X)
-- -- --   --   → let δ' = {!!}
-- -- --   --     in δ' ,
-- -- --   --         (λ h → ⊎.elim
-- -- --   --           (λ 0<h h<δ' →
-- -- --   --             let rs : Σ Partition[ x , x +ᵣ fst η ] Sample
-- -- --   --                 rs = {!!} , {!!}
-- -- --   --                 z = X rs {!X!}
-- -- --   --                 z' =
-- -- --   --                     isTrans≡<ᵣ _
-- -- --   --                        ((absᵣ (riemannSum' (snd rs) f -ᵣ G η)
-- -- --   --                          ·ᵣ invℝ h (inl 0<h)) ·ᵣ invℝ h (inl 0<h)) _
-- -- --   --                        (cong absᵣ (sym (·DistR+ (riemannSum' (snd rs) f)
-- -- --   --                          (G η) _)) ∙
-- -- --   --                          (·absᵣ (riemannSum' {_} {_} {fst rs} (snd rs) f -ᵣ G η) (invℝ h (inl 0<h)) ∙
-- -- --   --                           cong ((absᵣ (riemannSum' (snd rs) f -ᵣ G η)
-- -- --   --                          ·ᵣ invℝ h (inl 0<h)) ·ᵣ_) ((absᵣPos
-- -- --   --                           (invℝ h (inl 0<h))
-- -- --   --                             (invℝ-pos h 0<h)))))
-- -- --   --                         ((<ᵣ-·ᵣo
-- -- --   --                         (absᵣ (riemannSum' (snd rs) f -ᵣ G η))
-- -- --   --                          (rat (fst θ)) (invℝ h (inl 0<h) , invℝ-pos h 0<h) z))
-- -- --   --             in {!z'!})
-- -- --   --           {!!}))
-- -- --   --   (G= η θ)

-- -- --  -- where

-- -- --  -- η = {!!}

-- -- --  -- θ = {!!}

-- -- --  -- G : ∀ (h : ℝ₊) → ℝ 
-- -- --  -- G h = F (x +ᵣ fst h) -ᵣ F x

-- -- --  -- G= : ∀ (h : ℝ₊) → on[ x , x +ᵣ fst h ]IntegralOf f is' (G h)
-- -- --  -- G= = {!!}
 
-- -- --  -- difF : ∀ h 0<h  → differenceAt F x h (inl 0<h) ·ᵣ h ≡
-- -- --  --                     G (h , 0<h)
-- -- --  -- difF h 0＃h = {!!}
 
-- -- -- -- -- derivativeOf_at_is_






-- -- -- -- -- private
-- -- -- -- --   variable
-- -- -- -- --     ℓ : Level
-- -- -- -- --     A B : Type ℓ


-- -- -- -- -- foldlFin : ∀ {n} → (B → A → B) → B → (Fin n → A) → B
-- -- -- -- -- foldlFin {n = zero} f b v = b
-- -- -- -- -- foldlFin {n = suc n} f b v = foldlFin {n = n} f (f b (v fzero)) (v ∘ fsuc)

-- -- -- -- -- record Partition[_,_] (a b : ℝ) : Type₀ where 
-- -- -- -- --  field
-- -- -- -- --   len : ℕ
-- -- -- -- --   pts : Fin (1 ℕ.+ len) → ℝ
-- -- -- -- --   a≤pts : ∀ k → a ≤ᵣ pts k 
-- -- -- -- --   pts≤b : ∀ k → pts k ≤ᵣ b
-- -- -- -- --   pts≤pts : (k : Fin len) → pts (finj k) ≤ᵣ pts (fsuc k)

-- -- -- -- --  diffs : Fin len → Σ ℝ (0 ≤ᵣ_) 
-- -- -- -- --  diffs k = _ , x≤y→0≤y-x (pts (finj k)) _ (pts≤pts k)
 
-- -- -- -- --  mesh : ℝ
-- -- -- -- --  mesh = foldlFin maxᵣ 0 (fst ∘ diffs)

-- -- -- -- --  record Sample : Type₀ where
-- -- -- -- --   field
-- -- -- -- --    samples : Fin len → ℝ
-- -- -- -- --    ≤samples : (k : Fin len) → pts (finj k) ≤ᵣ samples k
-- -- -- -- --    samples≤ : (k : Fin len) → samples k ≤ᵣ pts (fsuc k)
   
-- -- -- -- --   samplesΣ : Fin len → Σ[ t ∈ ℝ ] (a ≤ᵣ t ) × (t ≤ᵣ b)
-- -- -- -- --   samplesΣ = {!!}
  
-- -- -- -- --   riemannSum : (∀ r → a ≤ᵣ r → r ≤ᵣ b → ℝ) → ℝ
-- -- -- -- --   riemannSum f = foldlFin
-- -- -- -- --     (λ S ((t , a≤t , t≤b) , b-a) → S +ᵣ b-a ·ᵣ (f t a≤t t≤b) ) 0
-- -- -- -- --      (λ k →  samplesΣ k , pts (fsuc k) -ᵣ pts (finj k))

-- -- -- -- --  open Sample public
-- -- -- -- -- open Partition[_,_] 

-- -- -- -- -- TaggedPartition[_,_] : ℝ → ℝ → Type
-- -- -- -- -- TaggedPartition[ a , b ] = Σ (Partition[ a , b ]) Sample


-- -- -- -- -- on[_,_]IntegralOf_is_ : ∀ a b → (∀ r → a ≤ᵣ r → r ≤ᵣ b → ℝ) → ℝ → Type
-- -- -- -- -- on[ a , b ]IntegralOf f is s =
-- -- -- -- --   ∀ ((p , t) : TaggedPartition[ a , b ]) →
-- -- -- -- --    ∀ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
-- -- -- -- --      (mesh p <ᵣ rat (fst δ) →
-- -- -- -- --        absᵣ (riemannSum t f -ᵣ s) <ᵣ rat (fst ε))


-- -- -- -- -- FTOC : ∀ a b (f F : ∀ r → a ≤ᵣ r → r ≤ᵣ b → ℝ)
-- -- -- -- --                  → (∀ x → (≤x : a ≤ᵣ x) → (x≤ : x ≤ᵣ b)
-- -- -- -- --                      → on[ a , x ]IntegralOf
-- -- -- -- --                          (λ r ≤r r≤ → f r ≤r (isTrans≤ᵣ r _ _ r≤ x≤))
-- -- -- -- --                            is F x ≤x x≤)
-- -- -- -- --                  → ∀ x → (≤x : a ≤ᵣ x) → (x≤ : x ≤ᵣ b) →
-- -- -- -- --                      {!derivativeOf F at ? is ?!}
-- -- -- -- -- FTOC = {!!}

-- -- -- -- -- -- derivativeOf_at_is_
