{-# OPTIONS --safe #-}
module Cubical.Functions.FunExtEquiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport

open import Cubical.Data.Vec.Base
open import Cubical.Data.Vec.NAry
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Reflection.StrictEquiv

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level

-- Function extensionality is an equivalence
module _ {A : Type ℓ} {B : A → I → Type ℓ₁}
  {f : (x : A) → B x i0} {g : (x : A) → B x i1} where

  funExtEquiv : (∀ x → PathP (B x) (f x) (g x)) ≃ PathP (λ i → ∀ x → B x i) f g
  unquoteDef funExtEquiv = defStrictEquiv funExtEquiv funExt funExt⁻

  funExtPath : (∀ x → PathP (B x) (f x) (g x)) ≡ PathP (λ i → ∀ x → B x i) f g
  funExtPath = ua funExtEquiv

  funExtIso : Iso (∀ x → PathP (B x) (f x) (g x)) (PathP (λ i → ∀ x → B x i) f g)
  funExtIso = iso funExt funExt⁻ (λ x → refl {x = x}) (λ x → refl {x = x})

-- Function extensionality for binary functions
funExt₂ : {A : Type ℓ} {B : A → Type ℓ₁} {C : (x : A) → B x → I → Type ℓ₂}
          {f : (x : A) → (y : B x) → C x y i0}
          {g : (x : A) → (y : B x) → C x y i1}
          → ((x : A) (y : B x) → PathP (C x y) (f x y) (g x y))
          → PathP (λ i → ∀ x y → C x y i) f g
funExt₂ p i x y = p x y i

-- Function extensionality for binary functions is an equivalence
module _ {A : Type ℓ} {B : A → Type ℓ₁} {C : (x : A) → B x → I → Type ℓ₂}
         {f : (x : A) → (y : B x) → C x y i0}
         {g : (x : A) → (y : B x) → C x y i1} where
  private
    appl₂ : PathP (λ i → ∀ x y → C x y i) f g → ∀ x y → PathP (C x y) (f x y) (g x y)
    appl₂ eq x y i = eq i x y

  funExt₂Equiv : (∀ x y → PathP (C x y) (f x y) (g x y)) ≃ (PathP (λ i → ∀ x y → C x y i) f g)
  unquoteDef funExt₂Equiv = defStrictEquiv funExt₂Equiv funExt₂ appl₂

  funExt₂Path : (∀ x y → PathP (C x y) (f x y) (g x y)) ≡ (PathP (λ i → ∀ x y → C x y i) f g)
  funExt₂Path = ua funExt₂Equiv


-- Function extensionality for ternary functions
funExt₃ : {A : Type ℓ} {B : A → Type ℓ₁} {C : (x : A) → B x → Type ℓ₂}
          {D : (x : A) → (y : B x) → C x y → I → Type ℓ₃}
          {f : (x : A) → (y : B x) → (z : C x y) → D x y z i0}
          {g : (x : A) → (y : B x) → (z : C x y) → D x y z i1}
        → ((x : A) (y : B x) (z : C x y) → PathP (D x y z) (f x y z) (g x y z))
        → PathP (λ i → ∀ x y z → D x y z i) f g
funExt₃ p i x y z = p x y z i

-- Function extensionality for ternary functions is an equivalence
module _ {A : Type ℓ} {B : A → Type ℓ₁} {C : (x : A) → B x → Type ℓ₂}
         {D : (x : A) → (y : B x) → C x y → I → Type ℓ₃}
         {f : (x : A) → (y : B x) → (z : C x y) → D x y z i0}
         {g : (x : A) → (y : B x) → (z : C x y) → D x y z i1} where
  private
    appl₃ : PathP (λ i → ∀ x y z → D x y z i) f g → ∀ x y z → PathP (D x y z) (f x y z) (g x y z)
    appl₃ eq x y z i = eq i x y z

  funExt₃Equiv : (∀ x y z → PathP (D x y z) (f x y z) (g x y z)) ≃ (PathP (λ i → ∀ x y z → D x y z i) f g)
  unquoteDef funExt₃Equiv = defStrictEquiv funExt₃Equiv funExt₃ appl₃

  funExt₃Path : (∀ x y z → PathP (D x y z) (f x y z) (g x y z)) ≡ (PathP (λ i → ∀ x y z → D x y z i) f g)
  funExt₃Path = ua funExt₃Equiv


-- n-ary non-dependent funext
nAryFunExt : {X : Type ℓ} {Y : I → Type ℓ₁} (n : ℕ) (fX : nAryOp n X (Y i0)) (fY : nAryOp n X (Y i1))
           → ((xs : Vec X n) → PathP Y (fX $ⁿ xs) (fY $ⁿ map (λ x → x) xs))
           → PathP (λ i → nAryOp n X (Y i)) fX fY
nAryFunExt zero fX fY p        = p []
nAryFunExt (suc n) fX fY p i x = nAryFunExt n (fX x) (fY x) (λ xs → p (x ∷ xs)) i

-- n-ary funext⁻
nAryFunExt⁻ : (n : ℕ) {X : Type ℓ} {Y : I → Type ℓ₁} (fX : nAryOp n X (Y i0)) (fY : nAryOp n X (Y i1))
           → PathP (λ i → nAryOp n X (Y i)) fX fY
           → ((xs : Vec X n) → PathP Y (fX $ⁿ xs) (fY $ⁿ map (λ x → x) xs))
nAryFunExt⁻ zero fX fY p [] = p
nAryFunExt⁻ (suc n) fX fY p (x ∷ xs) = nAryFunExt⁻ n (fX x) (fY x) (λ i → p i x) xs

nAryFunExtEquiv : (n : ℕ) {X : Type ℓ} {Y : I → Type ℓ₁} (fX : nAryOp n X (Y i0)) (fY : nAryOp n X (Y i1))
  → ((xs : Vec X n) → PathP Y (fX $ⁿ xs) (fY $ⁿ map (λ x → x) xs)) ≃ PathP (λ i → nAryOp n X (Y i)) fX fY
nAryFunExtEquiv n {X} {Y} fX fY = isoToEquiv (iso (nAryFunExt n fX fY) (nAryFunExt⁻ n fX fY)
                                              (linv n fX fY) (rinv n fX fY))
  where
  linv : (n : ℕ) (fX : nAryOp n X (Y i0)) (fY : nAryOp n X (Y i1))
    (p : PathP (λ i → nAryOp n X (Y i)) fX fY)
    → nAryFunExt n fX fY (nAryFunExt⁻ n fX fY p) ≡ p
  linv zero fX fY p          = refl
  linv (suc n) fX fY p i j x = linv n (fX x) (fY x) (λ k → p k x) i j

  rinv : (n : ℕ) (fX : nAryOp n X (Y i0)) (fY : nAryOp n X (Y i1))
         (p : (xs : Vec X n) → PathP Y (fX $ⁿ xs) (fY $ⁿ map (λ x → x) xs))
       → nAryFunExt⁻ n fX fY (nAryFunExt n fX fY p) ≡ p
  rinv zero fX fY p i []          = p []
  rinv (suc n) fX fY p i (x ∷ xs) = rinv n (fX x) (fY x) (λ ys i → p (x ∷ ys) i) i xs

-- Funext when the domain also depends on the interval

funExtDepTy : (A : I → Type ℓ) (B : (i : I) → A i → Type ℓ₁)
              (f : (x : A i0) → B i0 x) (g : (x : A i1) → B i1 x) → Type (ℓ-max ℓ ℓ₁)
funExtDepTy A B f g =  
  ({x₀ : A i0} {x₁ : A i1} (p : PathP A x₀ x₁) → PathP (λ i → B i (p i)) (f x₀) (g x₁))
  → PathP (λ i → (x : A i) → B i x) f g

funExtDep : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
  {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}
  → ({x₀ : A i0} {x₁ : A i1} (p : PathP A x₀ x₁) → PathP (λ i → B i (p i)) (f x₀) (g x₁))
  → PathP (λ i → (x : A i) → B i x) f g
funExtDep {A = A} {B} {f} {g} h i x =
  comp
    (λ k → B i (coei→i A i x k))
    (λ k → λ
      { (i = i0) → f (coei→i A i0 x k)
      ; (i = i1) → g (coei→i A i1 x k)
      })
    (h (λ j → coei→j A i j x) i)

funExtDep⁻ : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
  {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}
  → PathP (λ i → (x : A i) → B i x) f g
  → ({x₀ : A i0} {x₁ : A i1} (p : PathP A x₀ x₁) → PathP (λ i → B i (p i)) (f x₀) (g x₁))
funExtDep⁻ q p i = q i (p i)

funExtDepEquiv : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
  {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}
  → ({x₀ : A i0} {x₁ : A i1} (p : PathP A x₀ x₁) → PathP (λ i → B i (p i)) (f x₀) (g x₁))
  ≃ PathP (λ i → (x : A i) → B i x) f g
funExtDepEquiv {A = A} {B} {f} {g} = isoToEquiv isom
  where
  open Iso
  isom : Iso _ _
  isom .fun = funExtDep
  isom .inv = funExtDep⁻
  isom .rightInv q m i x =
    comp
      (λ k → B i (coei→i A i x (k ∨ m)))
      (λ k → λ
        { (i = i0) → f (coei→i A i0 x (k ∨ m))
        ; (i = i1) → g (coei→i A i1 x (k ∨ m))
        ; (m = i1) → q i x
        })
      (q i (coei→i A i x m))
  isom .leftInv h m p i =
    comp
      (λ k → B i (lemi→i m k))
      (λ k → λ
        { (i = i0) → f (lemi→i m k)
        ; (i = i1) → g (lemi→i m k)
        ; (m = i1) → h p i
        })
      (h (λ j → lemi→j j m) i)
    where
    lemi→j : ∀ j → coei→j A i j (p i) ≡ p j
    lemi→j j =
      coei→j (λ k → coei→j A i k (p i) ≡ p k) i j (coei→i A i (p i))

    lemi→i : PathP (λ m → lemi→j i m ≡ p i) (coei→i A i (p i)) refl
    lemi→i =
      sym (coei→i (λ k → coei→j A i k (p i) ≡ p k) i (coei→i A i (p i)))
      ◁ λ m k → lemi→j i (m ∨ k)

heteroHomotopy≃Homotopy : {A : I → Type ℓ} {B : (i : I) → Type ℓ₁}
  {f : A i0 → B i0} {g : A i1 → B i1}
  → ({x₀ : A i0} {x₁ : A i1} → PathP A x₀ x₁ → PathP B (f x₀) (g x₁))
  ≃ ((x₀ : A i0) → PathP B (f x₀) (g (transport (λ i → A i) x₀)))
heteroHomotopy≃Homotopy {A = A} {B} {f} {g} = isoToEquiv isom
  where
  open Iso
  isom : Iso _ _
  isom .fun h x₀ = h (isContrSinglP A x₀ .fst .snd)
  isom .inv k {x₀} {x₁} p =
    subst (λ fib → PathP B (f x₀) (g (fib .fst))) (isContrSinglP A x₀ .snd (x₁ , p)) (k x₀)
  isom .rightInv k = funExt λ x₀ →
    cong (λ α → subst (λ fib → PathP B (f x₀) (g (fib .fst))) α (k x₀))
      (isProp→isSet isPropSinglP (isContrSinglP A x₀ .fst) _
        (isContrSinglP A x₀ .snd (isContrSinglP A x₀ .fst))
        refl)
    ∙ transportRefl (k x₀)
  isom .leftInv h j {x₀} {x₁} p =
    transp
      (λ i → PathP B (f x₀) (g (isContrSinglP A x₀ .snd (x₁ , p) (i ∨ j) .fst)))
      j
      (h (isContrSinglP A x₀ .snd (x₁ , p) j .snd))

uncurryIIE : ∀ {ℓ₁} {A A' : Type ℓ} {B : A → A' → Type ℓ}
    {C : {a : A} {a' : A'} → B a a' → Type ℓ₁}
  → (∀ {a a'} → (b : B a a') → C b) →
      ((aab : Σ A (λ a → Σ (A') (λ a' → B a a'))) → C (snd (snd aab)))   
uncurryIIE x = x ∘ snd ∘ snd

curryIIE' : ∀ {ℓ₁} {A A' : Type ℓ} {B : A → A' → Type ℓ}
    {C : {a : A} {a' : A'} → B a a' → Type ℓ₁}
   → ((aab : Σ A (λ a → Σ (A') (λ a' → B a a'))) → C (snd (snd aab)))
   → (∀ {a a'} → (b : B a a') → C b)
curryIIE' f x = f (_ , _ , x)

curryIIE'-Iso :
  ∀ {ℓ₁} {A A' : Type ℓ} {B : A → A' → Type ℓ}
    {C : {a : A} {a' : A'} → B a a' → Type ℓ₁}
  → Iso (∀ {a a'} → (b : B a a') → C b)
      ((aab : Σ A (λ a → Σ (A') (λ a' → B a a'))) → C (snd (snd aab)))
Iso.fun curryIIE'-Iso = uncurryIIE
Iso.inv curryIIE'-Iso = curryIIE'
Iso.rightInv curryIIE'-Iso _ = refl
Iso.leftInv curryIIE'-Iso _ = refl
-- --   -- unquoteDecl ΣPathP≃PathPΣ = declStrictIsoToEquiv ΣPathP≃PathPΣ ΣPathPIsoPathPΣ

-- --   -- ΣPathP≡PathPΣ = ua ΣPathP≃PathPΣ

heteroHomotopyIsoHomotopy' : ∀ {ℓ₁} {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
  {f : (a : A i0) → B i0 a} {g : (a : A i1) → B i1 a}
  →  ({x₀ : A i0} {x₁ : A i1} → (p : PathP A x₀ x₁) →
        PathP (λ i → B i (p i)) (f x₀) (g x₁)) ≃
    -- ((x₀ : A i0) →  {!!})
    ((x₀ : A i0) → PathP (λ i → B i (transp (λ i₁ → A (i₁ ∧ i)) (~ i) x₀))
        (f x₀) (g (transport (λ i → A i) x₀)))
heteroHomotopyIsoHomotopy' {ℓ} {ℓ₁} {A = A} {B} {f} {g} =
  isoToEquiv curryIIE'-Iso ∙ₑ
    -- pathToEquiv {!!}
    equivΠ (
         Σ-contractSnd (isContrSinglP _))
          ((pathToEquiv ∘ sym) ∘ uncurry h)

 where
  h : ∀ (a₀ : A i0) (s : singlP A a₀) →
        PathP (λ i → B i (transp (λ j → A (i ∧ j)) (~ i) a₀)) (f a₀)
          (g (transp (λ i → A i) i0 a₀))
          ≡ PathP (λ i → B i (snd s i)) (f a₀) (g (fst s))
  h a₀ s = cong {A = singlP A a₀} 
            {B = λ _ → Type ℓ₁} {y = s}
             (λ (a₁ , p) → PathP (λ i → B i (p i)) (f a₀) (g a₁))
              (snd (isContrSinglP A a₀) s)

funExtDep' : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
  {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}
  → ((x₀ : A i0) → PathP (λ i → B i (transp (λ i₁ → A (i₁ ∧ i)) (~ i) x₀))
        (f x₀) (g (transport (λ i → A i) x₀)))
  → PathP (λ i → (x : A i) → B i x) f g
funExtDep' {B = B} = funExtDep ∘ invEq (heteroHomotopyIsoHomotopy' {B = B})

funExtDep'≃ : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
  {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}
  → ((x₀ : A i0) → PathP (λ i → B i (transp (λ i₁ → A (i₁ ∧ i)) (~ i) x₀))
        (f x₀) (g (transport (λ i → A i) x₀)))
  ≃ PathP (λ i → (x : A i) → B i x) f g
funExtDep'≃ {B = B} =
   (invEquiv (heteroHomotopyIsoHomotopy' {B = B})) ∙ₑ funExtDepEquiv



funExtDep≡' : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
  {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}
  →  PathP (λ i → (x₀ : A i0) → B i (transp (λ i₁ → A (i₁ ∧ i)) (~ i) x₀))
              f (g ∘ transport (λ i → A i))
   ≡ PathP (λ i → (x : A i) → B i x) f g
funExtDep≡' {A = A} {B = B} {f} {g} j =
   PathP (λ i → (x : A (i ∧ j)) →
      B i ((transp (λ i₁ → A (((i₁ ∨ j) ∧ i))) (~ i ∨ j) x))) f
        (g ∘ λ x → transp (λ i → A (i ∨ j)) (j) x)

funExtDep'≡ : {A : I → Type ℓ} {B : Type ℓ₁}
  {f : A i0 → B} {g : A i1 → B}
  →  PathP (λ i → A i0 → B)
              f (g ∘ transport (λ i → A i))
   ≡ PathP (λ i → (x : A i) → B) f g
funExtDep'≡ {A = A} {B = B} {f} {g} j =
   PathP (λ i → (x : A (i ∧ j)) → B) f
        (g ∘ λ x → transp (λ i → A (i ∨ j)) (j) x)



funExtDep'→ : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
  {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}
  →  PathP (λ i → (x₀ : A i0) → B i (transp (λ i₁ → A (i₁ ∧ i)) (~ i) x₀))
              f (g ∘ transport (λ i → A i))
   → PathP (λ i → (x : A i) → B i x) f g
funExtDep'→ {A = A} {B = B} {f} {g} =
  transport (funExtDep≡' {A = A} {B = B} {f} {g})
   -- PathP (λ i → (x : A (i ∧ j)) →
   --    B i ((transp (λ i₁ → A (((i₁ ∨ j) ∧ i))) (~ i ∨ j) x))) f
   --      (g ∘ λ x → transp (λ i → A (i ∨ j)) (j) x)

funExtDep'→⁻ : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
  {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}
  → PathP (λ i → (x : A i) → B i x) f g
  →  PathP (λ i → (x₀ : A i0) → B i (transp (λ i₁ → A (i₁ ∧ i)) (~ i) x₀))
              f (g ∘ transport (λ i → A i))
   
funExtDep'→⁻ {A = A} {B = B} {f} {g} =
  transport (sym (funExtDep≡' {A = A} {B = B} {f} {g}))

funExtDep'' : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
  {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}
  → ((x₀ : A i0) → PathP (λ i → B i (transp (λ i₁ → A (i₁ ∧ i)) (~ i) x₀))
        (f x₀) (g (transport (λ i → A i) x₀)))
   ≃ PathP (λ i → (x : A i) → B i x) f g
funExtDep'' {A = A} {B = B} =
   funExtEquiv ∙ₑ pathToEquiv funExtDep≡'


module _ {A B : Type ℓ} (e : A ≃ B)
        {C : (i : I) → ua e i → Type ℓ₁}
        {f : (x : A) → C i0 x} {g : (x : B) → C i1 x}
        where

  -- funExtDep'UaSi-Iso :
  --     Iso ((a : A) → PathP (λ i → C i (ua-gluePath e (λ _ → e .fst a) i))
  --         (f a) (g (e .fst a)))
  --    ((abp : Σ _ (ua-singl e)) →
  --          PathP (λ i → C i (snd (snd abp) i))
  --         (f (fst abp)) (g (fst (snd abp))))
  -- funExtDep'UaSi-Iso =
  --   {!codomainIsoDep ? ?!}


  ua∨ : Square refl (ua e)  refl  (ua e)
  ua∨ j i =
    Glue (ua e i)
          λ { (j = i0) → A ,
               ΣPathPProp {A = λ i → A → ua e i} {B = λ i → isEquiv} 
                  {u = idEquiv A} {v = e} isPropIsEquiv
                    (ua-gluePathExt e) i
            ; (i = i0) → A , idEquiv _
            ; (i = i1) → ua e j , ua-unglueEquiv e j
            ; (j = i1) → (ua e i) , idEquiv _} 
        
  funExtDep≡'ua : 
      (PathP (λ i → (a : A) → C i ((ua-gluePath e (λ _ → e .fst a) i)))
                f (g ∘ fst e))
     ≡ PathP (λ i → (p : ua e i) → C i p) f g
  funExtDep≡'ua j =
     PathP (λ i → (p : ua∨ j i) → C i (unglue (j ∨ ~ j ∨ i ∨ ~ i) p))
        f (g ∘ ua-unglue e j)
  
     -- PathP (λ i → (x : A (i ∧ j)) →
     --    B i ((transp (λ i₁ → A (((i₁ ∨ j) ∧ i))) (~ i ∨ j) x))) f
     --      (g ∘ λ x → transp (λ i → A (i ∨ j)) (j) x)


  funExtDep'Ua≃ :
      ((a : A) → PathP (λ i → C i (ua-gluePath e (λ _ → e .fst a) i))
          (f a) (g (e .fst a)))
     ≃ PathP (λ i → (x : ua e i) → C i x)
         f g
  funExtDep'Ua≃ = funExtEquiv ∙ₑ pathToEquiv funExtDep≡'ua


  
funExtSq : {A : Type ℓ} {B : A → I → I → Type ℓ₁}
  {f₀₀ : (x : A) → B x i0 i0}
  {f₀₁ : (x : A) → B x i0 i1}
  {f₁₀ : (x : A) → B x i1 i0}
  {f₁₁ : (x : A) → B x i1 i1}
  (f₀₋ : PathP (λ j → (x : A) → B x i0 j) f₀₀ f₀₁)
  (f₁₋ : PathP (λ j → (x : A) → B x i1 j) f₁₀ f₁₁)
  (f₋₀ : PathP (λ i → (x : A) → B x i i0) f₀₀ f₁₀)
  (f₋₁ : PathP (λ i → (x : A) → B x i i1) f₀₁ f₁₁)  
  → (∀ a → SquareP (λ i j → B a i j)
              (funExt⁻ f₀₋ a)
              (funExt⁻ f₁₋ a)
              (funExt⁻ f₋₀ a)
              (funExt⁻ f₋₁ a))
  → SquareP (λ i j → ∀ a → B a i j)
        f₀₋
        f₁₋
        f₋₀
        f₋₁ 
funExtSq f₀₋ f₁₋ f₋₀ f₋₁ x i j a = x a i j

implicitFunExtSq : {A : Type ℓ} {B : A → I → I → Type ℓ₁}
  {f₀₀ : {x : A} → B x i0 i0}
  {f₀₁ : {x : A} → B x i0 i1}
  {f₁₀ : {x : A} → B x i1 i0}
  {f₁₁ : {x : A} → B x i1 i1}
  (f₀₋ : PathP (λ j → {x : A} → B x i0 j) f₀₀ f₀₁)
  (f₁₋ : PathP (λ j → {x : A} → B x i1 j) f₁₀ f₁₁)
  (f₋₀ : PathP (λ i → {x : A} → B x i i0) f₀₀ f₁₀)
  (f₋₁ : PathP (λ i → {x : A} → B x i i1) f₀₁ f₁₁)  
  → (∀ a → SquareP (λ i j → B a i j)
              (implicitFunExt⁻ f₀₋)
              (implicitFunExt⁻ f₁₋)
              (implicitFunExt⁻ f₋₀)
              (implicitFunExt⁻ f₋₁))
  → SquareP (λ i j → ∀ {a} → B a i j)
        f₀₋
        f₁₋
        f₋₀
        f₋₁ 
implicitFunExtSq f₀₋ f₁₋ f₋₀ f₋₁ x i j {a} = x a i j


module _ {A : I → I → Type ℓ} {B : Type ℓ₁}
  {f₀₀ : (x : A i0 i0) → B}
  {f₀₁ : (x : A i0 i1) → B}
  {f₁₀ : (x : A i1 i0) → B}
  {f₁₁ : (x : A i1 i1) → B}
  (f₀₋ : PathP (λ j → (x : A i0 j) → B) f₀₀ f₀₁)
  (f₁₋ : PathP (λ j → (x : A i1 j) → B) f₁₀ f₁₁)
  (f₋₀ : PathP (λ i → (x : A i i0) → B) f₀₀ f₁₀)
  (f₋₁ : PathP (λ i → (x : A i i1) → B) f₀₁ f₁₁)
     where
 SQ≡hlp :
    (Square {A = A i0 i0 → B}
        (λ j x → f₀₋ j (transport-fillerExt⁻ (λ z → A i0 (z ∧ j)) i0 x))
        (λ j x → f₁₋ j (transport-fillerExt⁻ (λ z → A z (z ∧ j)) i0 x))
        (λ i x → f₋₀ i (transport-fillerExt⁻ (λ z → A (z ∧ i) i0) i0 x))
        λ i x → f₋₁ i (transport-fillerExt⁻ (λ z → A (z ∧ i) z) i0 x))
      ≡
    (SquareP (λ i j → A i j → B)
        {f₀₀} {f₀₁}
        f₀₋
        {f₁₀} {f₁₁}
        f₁₋
        f₋₀
        f₋₁)
 SQ≡hlp = (λ z → 
   SquareP (λ i j → A (z ∧ i) (z ∧ j) → B)
       (λ j → f₀₋ j ∘ transport-fillerExt⁻ (λ z → A i0 (z ∧ j)) z)      
       (λ j → f₁₋ j ∘ transport-fillerExt⁻ (λ z → A z (z ∧ j)) z)
       (λ i → f₋₀ i ∘ transport-fillerExt⁻ (λ z → A (z ∧ i) i0) z)
       (λ i → f₋₁ i ∘ transport-fillerExt⁻ (λ z → A (z ∧ i) z) z))


 SQ≡hlp-comp :
    (Square {A = A i0 i0 → B}
        (λ j x → f₀₋ j (transport-fillerExt⁻ (λ z → A i0 (z ∧ j)) i0 x))
        (λ j x → f₁₋ j (transport-fillerExt⁻ (λ z → A z (z ∧ j)) i0 x))
        (λ i x → f₋₀ i (transport-fillerExt⁻ (λ z → A (z ∧ i) i0) i0 x))
        λ i x → f₋₁ i (transport-fillerExt⁻ (λ z → A (z ∧ i) z) i0 x))
      →
    (SquareP (λ i j → A i j → B)
        {f₀₀} {f₀₁}
        f₀₋
        {f₁₀} {f₁₁}
        f₁₋
        f₋₀
        f₋₁)
 SQ≡hlp-comp s i j =
  -- let x' : ∀ z → A (z ∧ i) (z ∧ j) → A i0 i0
  --     x' = coei→0 (λ z → A (z ∧ i) (z ∧ j)) 
  -- in hcomp
  --     (λ z →
  --     λ { (i = i0) → f₀₋ j {!!}
  --       ; (i = i1) → f₁₋ j {!!}
  --       ; (j = i0) → f₋₀ i {!!}
  --       ; (j = i1) → f₋₁ i {!!}
  --       })
  --     (s i j {!x' i0 !})
   comp (λ z → A (z ∧ i) (z ∧ j) → B)
     (λ z →
      λ { (i = i0) → f₀₋ j ∘ transport-fillerExt⁻ (λ z → A i0 (z ∧ j)) z
        ; (i = i1) → f₁₋ j ∘ transport-fillerExt⁻ (λ z → A z (z ∧ j)) z
        ; (j = i0) → f₋₀ i ∘ transport-fillerExt⁻ (λ z → A (z ∧ i) i0) z
        ; (j = i1) → f₋₁ i ∘ transport-fillerExt⁻ (λ z → A (z ∧ i) z) z
        })
     (s i j) 


 SQ-cu : Cube (λ _ _ → A i0 i0) (λ i j → A i j)
      (λ z j → A (i0) (z ∧ j))
      (λ z j → A (z) (z ∧ j))
      (λ z i → A (z ∧ i) (i0))
      λ z i → A (z ∧ i) (z)
 SQ-cu z i j = A (z ∧ i) (z ∧ j)

 funExtSqDep :
   ((a : A i0 i0) →
     Square
      (λ i → f₀₋ i (transp (λ i₁ → A i0 (i₁ ∧ i)) i0 a))
      (λ i → f₁₋ i (transp (λ i₁ → A i₁ (i₁ ∧ i)) i0 a))
      (λ i → f₋₀ i (transp (λ i₁ → A (i₁ ∧ i) i0) i0 a))
      (λ i → f₋₁ i (transp (λ i₁ → A (i₁ ∧ i) i₁) i0 a)))
  → SquareP (λ i j → A i j → B)
        f₀₋
        f₁₋
        f₋₀
        f₋₁ 
 funExtSqDep = SQ≡hlp-comp ∘ funExtSq _ _ _ _ 


-- module _ {A : I → I → Type ℓ} {B : Type ℓ₁} where

-- module _{A : I → I → Type ℓ} {B : ∀ i j → A i j → Type ℓ₁}
--   {f₀₀ : (x : A i0 i0) → B i0 i0 x}
--   {f₀₁ : (x : A i0 i1) → B i0 i1 x}
--   {f₁₀ : (x : A i1 i0) → B i1 i0 x}
--   {f₁₁ : (x : A i1 i1) → B i1 i1 x}
--   (f₀₋ : PathP (λ j → (x : A i0 j) → B i0 j x) f₀₀ f₀₁)
--   (f₁₋ : PathP (λ j → (x : A i1 j) → B i1 j x) f₁₀ f₁₁)
--   (f₋₀ : PathP (λ i → (x : A i i0) → B i i0 x) f₀₀ f₁₀)
--   (f₋₁ : PathP (λ i → (x : A i i1) → B i i1 x) f₀₁ f₁₁)
--      where
--  SQ≡hlp :
--     (SquareP (λ i j → ∀ a → B i j a)
--         f₀₋
--         f₁₋
--         f₋₀
--         f₋₁) ≡ {!!}
--  SQ≡hlp = {!!}

-- -- funExtSqDep : {A : I → I → Type ℓ} {B : ∀ i j → A i j → Type ℓ₁}
-- --   {f₀₀ : (x : A i0 i0) → B i0 i0 x}
-- --   {f₀₁ : (x : A i0 i1) → B i0 i1 x}
-- --   {f₁₀ : (x : A i1 i0) → B i1 i0 x}
-- --   {f₁₁ : (x : A i1 i1) → B i1 i1 x}
-- --   (f₀₋ : PathP (λ j → (x : A i0 j) → B i0 j x) f₀₀ f₀₁)
-- --   (f₁₋ : PathP (λ j → (x : A i1 j) → B i1 j x) f₁₀ f₁₁)
-- --   (f₋₀ : PathP (λ i → (x : A i i0) → B i i0 x) f₀₀ f₁₀)
-- --   (f₋₁ : PathP (λ i → (x : A i i1) → B i i1 x) f₀₁ f₁₁)
-- --   → (  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
-- --   {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
-- --   (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
-- --    → (p : SquareP A a₀₋ a₁₋ a₋₀ a₋₁) →
-- --      SquareP ((λ i j → B i j (p i j)))
-- --          (funExtDep⁻ f₀₋ a₀₋)
-- --          (funExtDep⁻ f₁₋ a₁₋)
-- --          (funExtDep⁻ f₋₀ a₋₀)
-- --          (funExtDep⁻ f₋₁ a₋₁))

-- --   → SquareP (λ i j → ∀ a → B i j a)
-- --         f₀₋
-- --         f₁₋
-- --         f₋₀
-- --         f₋₁ 
-- -- funExtSqDep f₀₋ f₁₋ f₋₀ f₋₁ x = {!!}
  


-- -- --   → ((x : A) → PathP (B x) (f x) (g x))
-- -- --   → PathP (λ i → (x : A) → B x i) f g
-- -- -- funExtSq = {!!} funExt

-- -- --   funExtDep'UaSi :
-- -- --       ((a : A) → PathP (λ i → C i (ua-gluePath e (λ _ → e .fst a) i))
-- -- --           (f a) (g (e .fst a)))
-- -- --      ≃ ((abp : Σ _ (ua-singl e)) →
-- -- --            PathP (λ i → C i (snd (snd abp) i))
-- -- --           (f (fst abp)) (g (fst (snd abp))))
-- -- --   funExtDep'UaSi =     
-- -- --      (equivΠ (isoToEquiv (ua-singl-Iso e))
-- -- --          λ _ → idEquiv _)


-- -- --   zzzqqq : Iso (PathP (λ i → (x : Σ A (ua-singl e)) → C i (snd (snd x) i))
-- -- --               (λ x → f (fst x)) (λ x → g (fst (snd x))))
-- -- --               (PathP (λ i → ∀ a a' → (p : PathP (λ i → ua e i) a a') → C i (p i))
-- -- --               (λ a _ _ → f a) λ _ a' _ → g a')
-- -- --   Iso.fun zzzqqq x i a a' p = x i (a , a' , p)
-- -- --   Iso.inv zzzqqq x i (a , a' , p) = x i a a' p
-- -- --   Iso.rightInv zzzqqq _ = refl
-- -- --   Iso.leftInv zzzqqq _ = refl

-- -- --   -- qqqzzz : Iso
-- -- --   --            ((x : A) (y : B) →
-- -- --   --             PathP (λ z → (p : PathP (λ i → ua e i) x y) → C z (p z))
-- -- --   --             (λ _ → f x) (λ _ → g y))
-- -- --   --            (PathP (λ i → (p : ua e i) → C i
-- -- --   --                ((glue
-- -- --   --             (λ { (i = i0) → invEq e (fst e p)
-- -- --   --                ; (i = i1) → p
-- -- --   --                })
-- -- --   --             (secEq e (ua-unglue e i p) i))))
-- -- --   --               (f ∘ λ a → snd e .equiv-proof (fst e a) .fst .fst) g)
-- -- --   -- Iso.fun qqqzzz X i p = X (invEq e (ua-unglue e i p)) (ua-unglue e i p) i
-- -- --   --      λ j → glue
-- -- --   --         (λ { (j = i0) → invEq e (ua-unglue e i p)
-- -- --   --            ; (j = i1) → ua-unglue e i p
-- -- --   --            })
-- -- --   --         (secEq e (ua-unglue e i p) j)
-- -- --   -- Iso.inv qqqzzz X a b = {!!}
-- -- --   --   -- let z = fromPathP X
-- -- --   --   -- in toPathP (funExt λ x → {!!} ∙ funExt⁻ z b)
-- -- --   -- Iso.rightInv qqqzzz = {!!}
-- -- --   -- Iso.leftInv qqqzzz = {!!}

-- -- --   -- qqqzzz' : Iso
-- -- --   --            ((x : A) (y : B) →
-- -- --   --             PathP (λ z → (p : PathP (λ i → ua e i) x y) → C z (p z))
-- -- --   --             (λ _ → f x) (λ _ → g y))
-- -- --   --            (PathP (λ i → (p : ua e i) → C i p) f g)
-- -- --   -- Iso.fun qqqzzz' X = {!!}
-- -- --   --   ◁ {!!}  ▷
-- -- --   --                    {!!}
-- -- --   -- Iso.inv qqqzzz' = {!!}
-- -- --   -- Iso.rightInv qqqzzz' = {!!}
-- -- --   -- Iso.leftInv qqqzzz' = {!!}

-- -- --   -- funExtDep'Ua :
-- -- --   --     ((a : A) → PathP (λ i → C i (ua-gluePath e (λ _ → e .fst a) i))
-- -- --   --         (f a) (g (e .fst a)))
-- -- --   --    ≃ PathP (λ i → (x : ua e i) → C i {!!})
-- -- --   --        (f ∘ invEq e ∘ fst e) g
-- -- --   -- funExtDep'Ua =
-- -- --   --    funExtDep'UaSi ∙ₑ funExtEquiv ∙ₑ
-- -- --   --     isoToEquiv zzzqqq ∙ₑ
-- -- --   --      invEquiv funExt₂Equiv ∙ₑ
-- -- --   --       isoToEquiv qqqzzz --wwqqzz


-- -- --   -- qweqwe : Iso ((x : A) (y : B) →
-- -- --   --      PathP (λ z → (p : PathP (λ i → ua e i) x y) → C z (p z))
-- -- --   --      (λ _ → f x) (λ _ → g y))
-- -- --   --      (PathP (λ i → (p : ua e i) → C i p) f g)
-- -- --   -- Iso.fun qweqwe X = {!!}
-- -- --   --   -- X {!!} {!!} i {!!}
-- -- --   --   -- where
-- -- --   --   --   ss : SquareP (λ i j → ua e i → B)
-- -- --   --   --          {!!}
-- -- --   --   --          {!!}
-- -- --   --   --          {!!}
-- -- --   --   --          {!!}
-- -- --   --   --   ss i j x = {!!}
-- -- --   -- Iso.inv qweqwe = {!!}
-- -- --   -- Iso.rightInv qweqwe = {!!}
-- -- --   -- Iso.leftInv qweqwe = {!!}
  
-- -- --   -- funExtDep'Ua' :
-- -- --   --     ((a : A) → PathP (λ i → C i (ua-gluePath e (λ _ → e .fst a) i))
-- -- --   --         (f a) (g (e .fst a)))
-- -- --   --    ≃ PathP (λ i → (p : ua e i) → C i p)
-- -- --   --        (f) g
-- -- --   -- funExtDep'Ua' =
-- -- --   --    funExtDep'UaSi ∙ₑ funExtEquiv ∙ₑ
-- -- --   --     isoToEquiv zzzqqq ∙ₑ
-- -- --   --      invEquiv funExt₂Equiv ∙ₑ isoToEquiv qweqwe

-- -- --      -- funExtDep'UaSi ∙ₑ
-- -- --      --  isoToEquiv (invIso curryIIE'-Iso) ∙ₑ
-- -- --      --   {!!} 

-- -- -- -- module _ {A B : Type ℓ} (e : A ≃ B)
-- -- -- --         {C : Type ℓ₁}
-- -- -- --         {f : A → C} {g : B → C}
-- -- -- --         where

-- -- -- --  funExtDep'Ua→ :
-- -- -- --       ((a : A) → (f a) ≡ (g (e .fst a)))
-- -- -- --      ≃ PathP (λ i → (x : ua (invEquiv e) i) → C) g f
-- -- -- --  funExtDep'Ua→ =
-- -- -- --     funExtDep'UaSi e {C = λ _ _ → C} {f} {g} ∙ₑ
-- -- -- --       isoToEquiv {!!} 
-- -- -- --   where
-- -- -- --    w : Iso ((abp : Σ A (ua-singl e)) → f (fst abp) ≡ g (fst (snd abp)))
-- -- -- --          (PathP (λ i → ua (invEquiv e) i → C) {!!} f)
-- -- -- --    Iso.fun w X i u = X ((ua-unglue (invEquiv e) i u) ,
-- -- -- --      ({!!} , λ j →
-- -- -- --        glue (λ {(j = i0) → (ua-unglue (invEquiv e) i u)
-- -- -- --                ;(j = i1) → fst e (ua-unglue (invEquiv e) i u)
-- -- -- --                }) (fst e (ua-unglue (invEquiv e) i u)))) (~ i)
-- -- -- --    Iso.inv w X abp = {!!}
-- -- -- --    -- {!fromPath!}
-- -- -- --    --   ∙ λ i →  fromPathP X i (ua-ungluePath e (snd (snd abp)) i)
-- -- -- --    Iso.rightInv w = {!!}
-- -- -- --    Iso.leftInv w = {!!}
-- -- -- -- -- funExtDep'Iso : {A : I → Type ℓ} {B : Type ℓ₁}
-- -- -- -- --   {f : A i0 → B} {g : A i1 → B}
-- -- -- -- --   → Iso ((x₀ : A i0) → (f x₀) ≡ (g (transport (λ i → A i) x₀)))
-- -- -- -- --     (PathP (λ i → (x : A i) → B) f g)
-- -- -- -- -- funExtDep'Iso {A = A} {B = B} {f} {g} = w
-- -- -- -- --   where
-- -- -- -- --   w : Iso _ _
-- -- -- -- --   Iso.fun w = transport (funExtDep'≡) ∘ funExt
-- -- -- -- --   Iso.inv w p x₀ i = p i (transp (λ i₁ → A (i₁ ∧ i)) (~ i) x₀)
-- -- -- -- --   Iso.rightInv w b = {!!}
-- -- -- -- --    -- congP (λ _ → {!fst funExtDep''!}) {!!}
-- -- -- -- --   Iso.leftInv w a i x = {!!}

-- -- -- -- -- funExtDep''≃ : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
-- -- -- -- --   {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}
-- -- -- -- --   → ((x₀ : A i0) → PathP (λ i → B i (transp (λ i₁ → A (i₁ ∧ i)) (~ i) x₀))
-- -- -- -- --         (f x₀) (g (transport (λ i → A i) x₀)))
-- -- -- -- --   ≃ PathP (λ i → (x : A i) → B i x) f g
-- -- -- -- -- funExtDep''≃ = {!!}
-- -- -- -- -- -- funExtDepSq {A = A} {B = B} f0- f1- f-0 f-1 h =
-- -- -- -- -- --   {!!} ◁ congP (λ _ → funExtDep ∘ curryIIE)
-- -- -- -- -- --       (funExtDep
-- -- -- -- -- --    ({!!})
-- -- -- -- -- --       ) ▷ {!!}
-- -- -- -- --   -- {!!} ◁ ({!λ i j → h!} ) ▷ {!!}

-- -- -- -- -- --  where
-- -- -- -- -- --   p0 : PathP (λ i → funExtDepTy (A i) (B i) (f-0 i) (f-1 i))
-- -- -- -- -- --           (λ _ → f0-) λ _ → f1-
-- -- -- -- -- --   p0 = {!!} ◁ (funExtDep λ {x₀} {x₁} p →
-- -- -- -- -- --         let p' = h {!!}
-- -- -- -- -- --        -- h 
-- -- -- -- -- --        --         λ {?} {?} {?} {?} {?} {?} i₁ i₂ → {!!}
-- -- -- -- -- --      in {! !}) ▷ {!!}

  
-- -- -- -- --   -- funExtDep {B = {!!}} {f = λ i → {!f-0 x!}} {g = {!!}}
-- -- -- -- --   --  ((funExtDep {B = λ i → ? → PathP ? ? ?}
-- -- -- -- --   --    {f = λ x i₁ → f0- i₁ (x i₁)} {g = λ x i₁ → f1- i₁ (x i₁)} h) j) i
-- -- -- -- --   -- comp
-- -- -- -- --   --   (λ k → B i j x)
-- -- -- -- --   --    (λ k → λ
-- -- -- -- --   --     { (i = i0) → {!!}
-- -- -- -- --   --     ; (i = i1) → {!!}
-- -- -- -- --   --     ; (j = i0) → {!!}
-- -- -- -- --   --     ; (j = i1) → {!!}
-- -- -- -- --   --     })
-- -- -- -- --   --   (h {!!} i j)



-- -- -- -- -- -- funExtDep : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
-- -- -- -- -- --   {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}
-- -- -- -- -- --   → ({x₀ : A i0} {x₁ : A i1} (p : PathP A x₀ x₁) → PathP (λ i → B i (p i)) (f x₀) (g x₁))
-- -- -- -- -- --   → PathP (λ i → (x : A i) → B i x) f g
-- -- -- -- -- -- funExtDep {A = A} {B} {f} {g} h i x =
-- -- -- -- -- --   comp
-- -- -- -- -- --     (λ k → B i (coei→i A i x k))
-- -- -- -- -- --     (λ k → λ
-- -- -- -- -- --       { (i = i0) → f (coei→i A i0 x k)
-- -- -- -- -- --       ; (i = i1) → g (coei→i A i1 x k)
-- -- -- -- -- --       })
-- -- -- -- -- --     (h (λ j → coei→j A i j x) i)
