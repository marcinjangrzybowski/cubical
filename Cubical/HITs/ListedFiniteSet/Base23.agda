{-# OPTIONS --safe --experimental-lossy-unification  #-} 
module Cubical.HITs.ListedFiniteSet.Base23 where

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

-- open import Cubical.Functions.Logic
open import Cubical.Foundations.Function

open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism


open import Cubical.Foundations.Univalence


open import Cubical.HITs.EilenbergMacLane1

open import Cubical.Data.FinData

import Cubical.Data.SumFin as F


open import Cubical.HITs.ListedFiniteSet.Base2

open import Cubical.Data.FinData.GTrun

import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Functions.Involution

open import Cubical.Homotopy.EilenbergMacLane.Properties

open import Cubical.Data.FinSet


open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.SymmetricGroup
open import Cubical.Algebra.Group.Generators

open import Cubical.HITs.ListedFiniteSet.Base22

private
  variable
    ℓ : Level
    A B : Type ℓ

module Rem∈ {A : Type ℓ} (grpA : isGroupoid A)
      (_∈FM2_ : A → FMSet2 A → Type ℓ)
      (∈FM2[] : ∀ x → x ∈FM2 [] → ⊥)
      (∈compute : ∀ {x} {xs : FMSet2 A} (a : A) → a ∈FM2 (x ∷2 xs) ≃ (x ≡ a) ⊎ (a ∈FM2 xs))
    where
  -- open ∈FMSet2 {A = A} grpA

  removeFM2 : ∀ (x) (xs : FMSet2 A) → x ∈FM2 xs → FMSet2 A
  removeFM2 x = 
     Elim.f
    (⊥.rec ∘ (∈FM2[] _))
    w
    {!!}
    {!!}
    {!!}
    {!!}
    {!!}
    λ _ → isGroupoidΠ λ _ → trunc
   where
     w : (x₁ : A) {xs : FMSet2 A} →
           (x ∈FM2 xs → FMSet2 A) → x ∈FM2 (x₁ ∷2 xs) → FMSet2 A
     w x₁ {xs} b =
       ⊎.rec (λ _ → xs) ((x ∷2_) ∘ b)
       ∘ equivFun (∈compute x)

     w' : (x₁ y : A) {xs : FMSet2 A} (b : x ∈FM2 xs → FMSet2 A) →
            PathP (λ i → x ∈FM2 comm x₁ y xs i → FMSet2 A) (w x₁ (w y b))
            (w y (w x₁ b))
     w' x₁ y {xs} b = {!!}
        

   -- zzz : ?


-- -- lemSucUA : ∀ {n} → (e : Fin n ≃ Fin n) → ua (sucPerm e) ≡
-- --                       {!ua e!} 
-- -- lemSucUA = {!!}

-- -- Mb^ : ℕ → (hSet ℓ-zero) → (hSet ℓ-zero) 
-- -- Mb^ zero x₁ = x₁
-- -- Mb^ (suc x) b' =
-- --   let b = Mb^ x b'
-- --   in Maybe (fst b) , isOfHLevelMaybe zero (snd b)

-- -- swap0and1Mf : (b : hSet ℓ-zero) → fst (Mb^ 2 b) → fst (Mb^ 2 b)  
-- -- swap0and1Mf b nothing = just nothing
-- -- swap0and1Mf b (just nothing) = nothing
-- -- swap0and1Mf b (just (just x)) = (just (just x))

-- -- swap0and1M : (b : hSet ℓ-zero) → fst (Mb^ 2 b) ≃ fst (Mb^ 2 b)  
-- -- swap0and1M b = involEquiv {f = swap0and1Mf b}
-- --    (Mb.elim _ refl (Mb.elim _ refl λ _ → refl) )

-- -- swap0and2Mf : (b : hSet ℓ-zero) → fst (Mb^ 3 b) → fst (Mb^ 3 b)  
-- -- swap0and2Mf b nothing = (just (just nothing))
-- -- swap0and2Mf b (just nothing) = just nothing
-- -- swap0and2Mf b (just (just nothing)) = nothing
-- -- swap0and2Mf b (just (just (just x))) = (just (just (just x)))

-- -- swap0and2M : (b : hSet ℓ-zero) → fst (Mb^ 3 b) ≃ fst (Mb^ 3 b)  
-- -- swap0and2M b = involEquiv {f = swap0and2Mf b}
-- --    (Mb.elim _ refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)) )

-- -- congMUA : (b : hSet ℓ-zero) →
-- --              cong Maybe (ua (swap0and1M b)) ≡
-- --               ua (congMaybeEquiv (swap0and1M b)) 
-- -- congMUA b = isInjectiveTransport
-- --   (funExt (Mb.elim _ refl λ _ → refl))

-- -- FMI : FMSet2 A → hSet ℓ-zero
-- -- FMI =
-- --   Elim.f 
-- --    (⊥.⊥ , isProp→isSet isProp⊥)
-- --    (λ x {xs} b → Maybe (fst b) , isOfHLevelMaybe zero (snd b) )
-- --    (λ x y b → TypeOfHLevel≡ 2 (ua (swap0and1M b)))
-- --    (λ x y {xs} b →
-- --       ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- --         (cong ua (equivEq (funExt ((Mb.elim _ refl (Mb.elim _ refl λ _ → refl) ))))
-- --           ∙ uaInvEquiv (swap0and1M b)) )
-- --    (λ x y z b → TypeOfHLevel≡ 2 (ua (swap0and2M b)))
-- --    (λ x y z {xs} b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- --                       (∙≡∙→square _ _ _ _
-- --                        (isInjectiveTransport
-- --                         (funExt (Mb.elim _  refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))))))


-- --    (λ x y z {xs} b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- --                       (∙≡∙→square _ _ _ _
-- --                        (isInjectiveTransport
-- --                         (funExt (Mb.elim _  refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))))))
-- --    (λ _ → isGroupoidHSet)

-- -- FMIfin : ∀ (xs : FMSet2 A) → isFinSet (fst (FMI xs))
-- -- FMIfin xs = (len2 xs) , 
-- --   (ElimProp.f {B = λ xs → PT.∥ fst (FMI xs) ≃ F.Fin (len2 xs) ∥₁}
-- --     PT.∣ idEquiv _ ∣₁
-- --      (λ _ {_} →
-- --       PT.map
-- --        λ e → congMaybeEquiv e
-- --           ∙ₑ isoToEquiv
-- --               (iso Maybe→SumUnit
-- --                    SumUnit→Maybe
-- --                    SumUnit→Maybe→SumUnit
-- --                    Maybe→SumUnit→Maybe)
          
-- --           )
-- --        (λ xs → PT.squash₁) xs)

-- --   where open SumUnit

-- -- ×Vec : (A : Type ℓ) → ℕ → Type ℓ
-- -- ×Vec A zero = Unit*
-- -- ×Vec A (suc n) = A × ×Vec A n

-- -- tabulate× : ∀ {n} → (fst (Mb^ n (⊥.⊥ , isProp→isSet isProp⊥)) → A) → ×Vec A n
-- -- tabulate× {n = zero} _ = tt*
-- -- tabulate× {n = suc n} x = x nothing , tabulate× (x ∘ just)

-- -- lookup× : ∀ {n} → ×Vec A n → (fst (Mb^ n (⊥.⊥ , isProp→isSet isProp⊥)) → A) 
-- -- lookup× {n = zero} x ()
-- -- lookup× {n = suc n} x = Mb.rec (fst x) (lookup× (snd x))

-- -- Iso-tabulate×-lookup× : ∀ {n} → Iso (×Vec A n) (fst (Mb^ n (⊥.⊥ , isProp→isSet isProp⊥)) → A)
-- -- Iso.fun Iso-tabulate×-lookup× = lookup×
-- -- Iso.inv Iso-tabulate×-lookup× = tabulate×
-- -- Iso.rightInv (Iso-tabulate×-lookup× {n = zero}) b i ()
-- -- Iso.rightInv (Iso-tabulate×-lookup× {n = suc n}) b i nothing = b nothing
-- -- Iso.rightInv (Iso-tabulate×-lookup× {n = suc n}) b i (just x) =
-- --   Iso.rightInv (Iso-tabulate×-lookup× {n = n}) (b ∘ just) i x
-- -- Iso.leftInv (Iso-tabulate×-lookup× {n = zero}) a = refl
-- -- Iso.leftInv (Iso-tabulate×-lookup× {n = suc n}) a =
-- --  ΣPathP (refl ,
-- --   Iso.leftInv (Iso-tabulate×-lookup× {n = n}) (snd a))



-- swap0and1⊎f : {A B C : Type ℓ} → A ⊎ (B ⊎ C) → B ⊎ (A ⊎ C)  
-- swap0and1⊎f (inl x) = (inr (inl x))
-- swap0and1⊎f (inr (inl x)) = (inl x)
-- swap0and1⊎f (inr (inr x)) = (inr (inr x))

-- swap0and1⊎fInvol : {A B C : Type ℓ} → ∀ x → swap0and1⊎f (swap0and1⊎f {A = A} {B} {C} x) ≡ x
-- swap0and1⊎fInvol (inl x) = refl
-- swap0and1⊎fInvol (inr (inl x)) = refl
-- swap0and1⊎fInvol (inr (inr x)) = refl

-- swap0and1⊎ :  {A B C : Type ℓ} → A ⊎ (B ⊎ C) ≃ B ⊎ (A ⊎ C)  
-- swap0and1⊎ =
--   isoToEquiv (iso swap0and1⊎f swap0and1⊎f swap0and1⊎fInvol swap0and1⊎fInvol)


-- swap0and2⊎f : {A B C D : Type ℓ} → A ⊎ (B ⊎ (C ⊎ D)) → C ⊎ (B ⊎ (A ⊎ D))  
-- swap0and2⊎f (inl x) = (inr (inr (inl x)))
-- swap0and2⊎f (inr (inl x)) = (inr (inl x))
-- swap0and2⊎f (inr (inr (inl x))) = (inl x)
-- swap0and2⊎f (inr (inr (inr x))) = (inr (inr (inr x)))

-- swap0and2⊎fInvol : {A B C D : Type ℓ} → ∀ x → swap0and2⊎f (swap0and2⊎f {A = A} {B} {C} {D} x) ≡ x
-- swap0and2⊎fInvol (inl x) = refl
-- swap0and2⊎fInvol (inr (inl x)) = refl
-- swap0and2⊎fInvol (inr (inr (inl x))) = refl
-- swap0and2⊎fInvol (inr (inr (inr x))) = refl

-- swap0and2⊎ :  {A B C D : Type ℓ} → A ⊎ (B ⊎ (C ⊎ D)) ≃ C ⊎ (B ⊎ (A ⊎ D))
-- swap0and2⊎ =
--   isoToEquiv (iso swap0and2⊎f swap0and2⊎f swap0and2⊎fInvol swap0and2⊎fInvol)


-- module _ {A : Type ℓ} (grpA : isGroupoid A) where

--   _∈FM2'_ : A → FMSet2 A → hSet ℓ
--   _∈FM2'_ a = Rec.f
--        isGroupoidHSet
--        (⊥.⊥* , isProp→isSet isProp⊥*)
--        (λ x b → ((x ≡ a) ⊎ fst b) , ⊎.isSet⊎ (grpA _ _) (snd b))
--        (λ x y b → TypeOfHLevel≡ 2 (ua (swap0and1⊎ {A = x ≡ a} {B = y ≡ a} {C = fst (b)})))
--        (λ x y b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
--                    (cong ua (equivEq (funExt (⊎.elim (λ _ → refl) (⊎.elim (λ _ → refl)
--                  λ _ → refl))))
--                 ∙ uaInvEquiv (swap0and1⊎ {A = y ≡ a} {B = x ≡ a} {C = fst (b)})))
--        (λ x y z b → TypeOfHLevel≡ 2
--          (ua (swap0and2⊎ {A = x ≡ a} {B = y ≡ a} {C = z ≡ a} {D = fst (b)})))
--        (λ x y z b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
--              (∙≡∙→square _ _ _ _ (isInjectiveTransport
--                   ((funExt (⊎.elim (λ _ → refl) (⊎.elim (λ _ → refl)
--                  (⊎.elim (λ _ → refl) λ _ → refl))))))))
--        (λ x y z b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
--              (∙≡∙→square _ _ _ _ (isInjectiveTransport
--                   ((funExt (⊎.elim (λ _ → refl) (⊎.elim (λ _ → refl)
--                  (⊎.elim (λ _ → refl) λ _ → refl))))))))

--   _∈FM2_ : A → FMSet2 A → Type ℓ
--   a ∈FM2 xs = fst (a ∈FM2' xs) 

--   ∈head : ∀ (x) (xs : FMSet2 A) → x ∈FM2 (x ∷2 xs)   
--   ∈head x xs = inl refl

--   ∈computeTest : ∀ {x} {xs : FMSet2 A} (a : A) → a ∈FM2 (x ∷2 xs) ≃ (x ≡ a) ⊎ (a ∈FM2 xs)  
--   ∈computeTest a = idEquiv _

--   -- bringHead : ∀ a (xs : FMSet2 A) → a ∈FM2 xs → Σ (FMSet2 A) λ xs' → xs ≡ a ∷2 xs' 
--   -- bringHead a = w
--   --   where
--   --     w : (xs : FMSet2 A) → a ∈FM2 xs → Σ (FMSet2 A) λ xs' → xs ≡ a ∷2 xs' 
--   --     w (_ ∷2 xs') (inl p) = xs' , λ i → p i ∷2 xs'
--   --     w (x' ∷2 xs) (inr x) =
--   --       let (xs' , p) = w xs x
--   --       in (x' ∷2 xs') , (cong (x' ∷2_) p ∙ comm _ _ _)
--   --     w (comm x₁ y xs i) x =
--   --       {!!}
--   --     w (comm-inv x₁ y xs i i₁) x = {!!}
--   --     w (hexDiag x₁ y z xs i) x = {!!}
--   --     w (hexU x₁ y z xs i i₁) x = {!!}
--   --     w (hexL x₁ y z xs i i₁) x = {!!}
--   --     w (trunc xs xs₁ x₁ y x₂ y₁ i i₁ x₃) x = {!!}

--   -- removeFM2 : ∀ (x) (xs : FMSet2 A) → x ∈FM2 xs → FMSet2 A
--   -- removeFM2 x = Elim.f
--   --   ⊥.rec*
--   --   w
--   --   w'
--   --   {!!}
--   --   {!!}
--   --   {!!}
--   --   {!!}
--   --   λ _ → isGroupoidΠ λ _ → trunc
--   --  where
--   --    w : (x₁ : A) {xs : FMSet2 A} →
--   --          (x ∈FM2 xs → FMSet2 A) → x ∈FM2 (x₁ ∷2 xs) → FMSet2 A
--   --    w x {xs} x₁ (inl x₂) = xs
--   --    w x x₁ (inr x₂) = x₁ x₂

--   --    w' : (x₁ y : A) {xs : FMSet2 A} (b : x ∈FM2 xs → FMSet2 A) →
--   --           PathP (λ i → x ∈FM2 comm x₁ y xs i → FMSet2 A) (w x₁ (w y b))
--   --           (w y (w x₁ b))
--   --    w' x₁ y {xs} b = ua→ ?


--     -- where
--     --   w : (xs : FMSet2 A) → x ∈FM2 xs → FMSet2 A
--     --   w (x₁ ∷2 xs) (inl x) = xs
--     --   w (x₁ ∷2 xs) (inr x) = w xs x
--     --   w (comm x₁ y xs i) = {!!}
--     --   w (comm-inv x₁ y xs i i₁) x = {!!}
--     --   w (hexDiag x₁ y z xs i) x = {!!}
--     --   w (hexU x₁ y z xs i i₁) x = {!!}
--     --   w (hexL x₁ y z xs i i₁) x = {!!}
--     --   w (trunc xs xs₁ x₁ y x₂ y₁ i i₁ x₃) x = {!!}

--   -- inj∷2' : ∀ n → (xs : FMSet2 A) → len2 xs ≡ n → (ys : FMSet2 A) → (x : A)
--   --          → (p : x ∷2 xs ≡ x ∷2 ys) 
--   --           → xs ≡ ys
--   -- inj∷2' xs ys x p = {!!}

-- -- subst (λ z → x ∈FM2 z) (∈head x xs) p 

--     -- let (xs' , px) = bringHead x (x ∷2 ys) (subst (x ∈FM2_) p (∈head x xs))
--     --     (ys' , py) = bringHead x (x ∷2 xs) (subst (x ∈FM2_) (sym p) (∈head x ys))

--     --     cLL : {!!}
--     --     cLL = {!!}
--     -- in {!!}

--      -- Elim.f
--      --  ⊥.rec*
--      --  (λ x x₁ → {!⊎.rec ? ?!})
--      --  (λ x y b i x₁ → {!!})
--      --  (λ x y b i j x₁ → {!!})
--      --  (λ x y z b i x₁ → {!!})
--      --  (λ x y z b i j x₁ → {!!})
--      --  (λ x y z b i j x₁ → {!!})
--      --  λ _ → isGroupoidΠ λ _ → (isOfHLevelΣ 3 trunc λ _ →  isSet→isGroupoid (trunc _ _))

--   -- _∈FM2_ : FMSet2 A → A → hSet ℓ
--   -- _∈FM2_ = Elim.f 
--   --    (λ _ → (⊥.⊥* , isProp→isSet isProp⊥*))
--   --    (λ x {xs} b a → ((x ≡ a) ⊎ fst (b a)) , ⊎.isSet⊎ (grpA _ _) (snd (b a)) )
--   --    (λ x y b → funExt λ a → TypeOfHLevel≡ 2
--   --                         {X = _ , ⊎.isSet⊎ (grpA _ _) (⊎.isSet⊎ (grpA _ _) (snd (b a)))}
--   --                         {Y = _ , ⊎.isSet⊎ (grpA _ _) (⊎.isSet⊎ (grpA _ _) (snd (b a)))}
--   --                 (ua (swap0and1⊎ {A = x ≡ a} {B = y ≡ a} {C = fst (b a)})))
--   --    (λ x y {xs} b i j a →
--   --       ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
--   --          {p = TypeOfHLevel≡  2 {X = _ , ⊎.isSet⊎ (grpA _ _) (⊎.isSet⊎ (grpA _ _) (snd (b a)))}
--   --                                {Y = _ , ⊎.isSet⊎ (grpA _ _) (⊎.isSet⊎ (grpA _ _) (snd (b a)))}
--   --              (ua (swap0and1⊎ {A = x ≡ a} {B = y ≡ a} {C = fst (b a)}))}
--   --            {q = refl}
--   --            {r = sym (TypeOfHLevel≡ 2 (ua (swap0and1⊎)))} {s = refl} 
--   --            (cong ua (equivEq (funExt (⊎.elim (λ _ → refl) (⊎.elim (λ _ → refl)
--   --                λ _ → refl))))
--   --           ∙ uaInvEquiv (swap0and1⊎ {A = y ≡ a} {B = x ≡ a} {C = fst (b a)}))
--   --          i j)
--   --    --    ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
--   --    --      (cong ua (equivEq (funExt ((Mb.elim _ refl (Mb.elim _ refl λ _ → refl) ))))
--   --    --        ∙ uaInvEquiv (swap0and1M b)) )
--   --    {!!} -- (λ x y z b → TypeOfHLevel≡ 2 (ua (swap0and2M b)))
--   --    {!!} -- (λ x y z {xs} b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
--   --    --                    (∙≡∙→square _ _ _ _
--   --    --                     (isInjectiveTransport
--   --    --                      (funExt (Mb.elim _  refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))))))


--   --    {!!} -- (λ x y z {xs} b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
--   --    --                    (∙≡∙→square _ _ _ _
--   --    --                     (isInjectiveTransport
--   --    --                      (funExt (Mb.elim _  refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))))))
--   --    (λ _ → isGroupoidΠ λ _ → isGroupoidHSet)


-- -- ×Vev≃⊎Fin→ : {!!}
-- -- ×Vev≃⊎Fin→ = {!!}


-- -- -- to≃ : ∀ n → GroupHom (Perm n) (SymData n)
-- -- -- to≃ zero = Eliminators.recPG (Eli zero) _ (λ ()) (⊥.rec ∘ ¬PermR'zero)
-- -- -- to≃ (suc n) = Eliminators.recPG (Eli n) _ adjTransposition w 
-- -- --   where
-- -- --     w : _
-- -- --     w (zero invo) = adjTransposition²=idEquiv (+k zero)
-- -- --     w (zero braid) = adjTranspositionBraid
-- -- --     w (zero (comm x)) = commTranspositions' x


-- -- -- _↔×_ : {A : Type ℓ} → ∀ {n} →  ×Vec A n → ×Vec A n → Type ℓ
-- -- -- _↔×_ {n = zero} x x₁ = ⊥*  
-- -- -- _↔×_ {n = one} x x₁ = ⊥* 
-- -- -- _↔×_ {n = suc (suc n)} (x , y , xs) (x' , y' , xs') =
-- -- --  ((x ≡ y') × (y ≡ x')) ⊎ ((y , xs) ↔× (y' , xs) )




-- -- mkPaΣ : ∀ {a₀₀ a₀₁ : Σ (hSet ℓ-zero) λ (T , _) → T → A} (a₀₋ : a₀₀ ≡ a₀₁)
-- --   {a₁₀ a₁₁ : Σ (hSet ℓ-zero) λ (T , _) → T → A} (a₁₋ : a₁₀ ≡ a₁₁)
-- --   (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
-- --    → (s : Square
-- --        (cong (fst ∘ fst) a₀₋)
-- --        (cong (fst ∘ fst) a₁₋)
-- --        (cong (fst ∘ fst) a₋₀)
-- --        (cong (fst ∘ fst) a₋₁))
-- --    → SquareP (λ i j → s i j → A)
-- --         (cong (snd) a₀₋)
-- --        (cong (snd) a₁₋)
-- --        (cong (snd) a₋₀)
-- --        (cong (snd) a₋₁) 
-- --    → Square a₀₋ a₁₋ a₋₀ a₋₁
-- -- mkPaΣ = {!!}

-- -- FMI* : (Agrp : isGroupoid A) → FMSet2 A → Σ (hSet ℓ-zero) λ (T , _) → T → A
-- -- FMI* Agrp = 
-- --   Elim.f
-- --    ((⊥.⊥ , isProp→isSet isProp⊥) , ⊥.elim)
-- --    (λ x {xs} (b , f) →
-- --       ((Maybe (fst b) , isOfHLevelMaybe zero (snd b)) , Mb.elim _ x f) )
-- --    (λ x y (b , f) →
-- --       ΣPathP (TypeOfHLevel≡ 2 (ua (swap0and1M b)) ,
-- --         toPathP (funExt (Mb.elim _  (transportRefl _) (Mb.elim _ (transportRefl _)
-- --            λ _ → transportRefl _ ∙ cong f (transportRefl _))))))
-- --    (λ x y (b , f) → mkPaΣ _ _ _ _
-- --       ((cong ua (equivEq (funExt ((Mb.elim _ refl (Mb.elim _ refl λ _ → refl) ))))
-- --           ∙ uaInvEquiv (swap0and1M b)) )
-- --           {!!})
-- --    {!!}
-- --    {!!}
-- --    {!!}
-- --    λ _ → isGroupoidΣ isGroupoidHSet λ _ → isGroupoidΠ λ _ → Agrp

-- -- lookupFM2 : (Agrp : isGroupoid A) → (xs : FMSet2 A) → fst (fst (FMI* Agrp xs)) → A
-- -- lookupFM2 Agrp xs = snd (FMI* Agrp xs)




-- -- -- -- -- lookupFM2 : (Agrp : isGroupoid A) → (xs : FMSet2 A) → fst (FMI xs) → A
-- -- -- -- -- lookupFM2 Agrp = 
-- -- -- -- --   Elim.f
-- -- -- -- --    ⊥.elim
-- -- -- -- --    (λ x x₁ → Mb.rec x x₁)
-- -- -- -- --    {!!}
-- -- -- -- --    {!!}
-- -- -- -- --    {!!}
-- -- -- -- --    {!!}
-- -- -- -- --    {!!}
-- -- -- -- --    λ _ → isGroupoidΠ λ _ → Agrp

-- -- -- --   -- Elim.f 
-- -- -- --   --  (Fin zero , isSetFin)
-- -- -- --   --  (λ _ {xs} _ → Fin (suc (len2 xs)) , isSetFin)
-- -- -- --   --  (λ x y {xs} _ → TypeOfHLevel≡ 2 (ua swap0and1≃))
-- -- -- --   --  (λ x y {xs} _ → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- --   --                   (cong ua swap0and1≃=invEquivSwap0and1 ∙ uaInvEquiv swap0and1≃))
-- -- -- --   --  (λ x y z {xs} _ → TypeOfHLevel≡ 2 (ua swap0and2≃))
-- -- -- --   --  (λ x y z {xs} _ → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- --   --                     (∙≡∙→square _ _ _ _
-- -- -- --   --                      (({!!} ∙ {!!}) ∙  uaCompEquiv _ _)))
-- -- -- --   --  {!!}
-- -- -- --   --  (λ _ → isGroupoidHSet)


-- -- -- -- -- isPropGrpSq : {A : I → I → Type ℓ} →
-- -- -- -- --               (∀ i j → isGroupoid (A i j))
-- -- -- -- --                 → {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
-- -- -- -- --                 {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
-- -- -- -- --                 (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
-- -- -- -- --               → isProp (SquareP A a₀₋ a₁₋ a₋₀ a₋₁)
-- -- -- -- -- isPropGrpSq x a₀₋ a₁₋ a₋₀ a₋₁ = {!!}

-- -- -- -- -- emPerm : (xs : FMSet2 A) → EM₁ (SymData (len2 xs))
-- -- -- -- -- emPerm =
-- -- -- -- --   (Elim.f {B = λ xs → EM₁ (SymData (len2 xs))}
-- -- -- -- --      embase
-- -- -- -- --      (λ _ → gh→em₂→ _ (sucPermFDMorphism _))
-- -- -- -- --      (λ x y {xs}
-- -- -- -- --        → elimSet (SymData (len2 xs))
-- -- -- -- --          (λ _ → emsquash _ _) (emloop swap0and1≃)
-- -- -- -- --            (lem1 (len2 xs)))

-- -- -- -- --      (λ x y {xs} →
-- -- -- -- --        elimProp _ (λ _ → isPropGrpSq (λ i j → emsquash) _ _ _ _)
-- -- -- -- --        (cong emloop swap0and1≃=invEquivSwap0and1 ∙ emloop-sym _ swap0and1≃))
-- -- -- -- --      (λ x y z {xs} →
-- -- -- -- --        elimSet (SymData (len2 xs))
-- -- -- -- --          (λ _ → emsquash _ _) (emloop swap0and2≃)
-- -- -- -- --          ((lem2 (len2 xs))))
-- -- -- -- --      (λ x y z {xs} →
-- -- -- -- --         elimProp _ (λ _ → isPropGrpSq (λ i j → emsquash) _ _ _ _)
-- -- -- -- --          (∙≡∙→square _ _ _ _
-- -- -- -- --            ((sym (emloop-comp _ _ _) ∙∙
-- -- -- -- --                 cong emloop (equivEq (refl =→ refl =→ refl =→ refl))
-- -- -- -- --                 ∙∙ emloop-comp _ _ _))))
-- -- -- -- --      (λ x y z {xs} →
-- -- -- -- --         elimProp _ (λ _ → isPropGrpSq (λ i j → emsquash) _ _ _ _)
-- -- -- -- --          (∙≡∙→square _ _ _ _
-- -- -- -- --            ((sym (emloop-comp _ _ _) ∙∙
-- -- -- -- --                 cong emloop (equivEq (refl =→ refl =→ refl =→ refl))
-- -- -- -- --                 ∙∙ emloop-comp _ _ _))))
-- -- -- -- --      (λ _ → emsquash)
-- -- -- -- --      )

-- -- -- -- --   where
-- -- -- -- --     lem1 : ∀ n → ∀ g → PathP
-- -- -- -- --       (λ i →
-- -- -- -- --          (emloop {Group = SymData (suc (suc n))} (sucPerm (sucPerm g)) i)
-- -- -- -- --          ≡
-- -- -- -- --          (emloop (sucPerm (sucPerm g)) i))
-- -- -- -- --       (emloop swap0and1≃) (emloop swap0and1≃)
-- -- -- -- --     lem1 n g =
-- -- -- -- --       ∙≡∙→square _ _ _ _
-- -- -- -- --               (sym (emloop-comp _ _ _) ∙∙
-- -- -- -- --                 cong emloop (commSwap0and1SucSuc g)
-- -- -- -- --                 ∙∙ emloop-comp _ _ _)
-- -- -- -- --     lem2 : ∀ n (g : fst (SymData n)) →
-- -- -- -- --              Square
-- -- -- -- --                (emloop {Group = (SymData (3 + n))} swap0and2≃)
-- -- -- -- --                (emloop swap0and2≃)
-- -- -- -- --                (emloop (sucPerm (sucPerm (sucPerm g))))
-- -- -- -- --                (emloop ((sucPerm (sucPerm (sucPerm g)))))

-- -- -- -- --     lem2 n g = ∙≡∙→square _ _ _ _
-- -- -- -- --        ((sym (emloop-comp _ _ _) ∙∙
-- -- -- -- --                 cong emloop (equivEq (refl =→ refl =→ refl =→ refl))
-- -- -- -- --                 ∙∙ emloop-comp _ _ _))

-- -- -- -- -- -- codes≃ : ∀ n → EM₁ (SymData n) → Σ Type₀ λ A → A ≃ fst (SymData n)
-- -- -- -- -- -- codes≃ n =
-- -- -- -- -- --   elimSet _ {!!}
-- -- -- -- -- --     (_ , idEquiv _)
-- -- -- -- -- --      {!!}

-- -- -- -- -- -- toPerm : (xs : FMSet2 A) → fst (SymData (len2 xs))
-- -- -- -- -- -- toPerm xs = {! !}

-- -- -- -- -- paPerm : {xs ys : FMSet2 A} → xs ≡ ys
-- -- -- -- --    →   Codes (SymData (len2 xs)) (emPerm xs) ≡
-- -- -- -- --        Codes (SymData (len2 ys)) (emPerm ys)
-- -- -- -- --    --Codes (SymData (len2 ys)) (emPerm ys)
-- -- -- -- -- paPerm {xs = xs} {ys} p =
-- -- -- -- --    cong (λ zs → Codes (SymData (len2 zs)) (emPerm zs)) p 

-- -- -- -- -- -- paPerm' : {xs ys : FMSet2 A} → xs ≡ ys
-- -- -- -- -- --    →   {!!}
-- -- -- -- -- --    --Codes (SymData (len2 ys)) (emPerm ys)
-- -- -- -- -- -- paPerm' {xs = xs} {ys} p =
-- -- -- -- -- --    {!cong (λ zs → Codes (SymData (len2 zs)) (emPerm zs)) p !}
-- -- -- -- -- --    -- cong (λ zs → Codes (SymData (len2 zs)) (emPerm zs)) p 
-- -- -- -- -- --   where
-- -- -- -- -- --     zz : {!!}
-- -- -- -- -- --     zz = decode _ (emPerm ys) {!!}

-- -- -- -- -- -- emK≃ : ∀ n → 
-- -- -- -- -- --      EM₁ (SymData n) → hSet ℓ-zero
-- -- -- -- -- -- emK≃ n = {!!}


-- -- -- -- -- emF : ∀ {n} → 
-- -- -- -- --      (x : EM₁ (SymData n)) → Type
-- -- -- -- -- emF {n} = fst ∘ EMFam.EM₁HFam isSetFin


-- -- -- -- -- -- zzz : (Agrp : isGroupoid A) → (xs : FMSet2 A) → (x : A) 
-- -- -- -- -- --       → (emF (emPerm xs) → A) → emF (emPerm (x ∷2 xs)) → A
-- -- -- -- -- -- zzz Agrp = Elim.f
-- -- -- -- -- --      (λ x _ _ → x)
-- -- -- -- -- --      (λ x {xs} f a g → {!!})
-- -- -- -- -- --      {!!}
-- -- -- -- -- --      {!!}
-- -- -- -- -- --      {!!}
-- -- -- -- -- --      {!!}
-- -- -- -- -- --      {!!}
-- -- -- -- -- --      -- {!!}
-- -- -- -- -- --      λ _ → isGroupoidΠ3 λ _ _ _ → Agrp 

-- -- -- -- --   -- where

-- -- -- -- --   --   pp : emPerm (x ∷2 xs) ≡
-- -- -- -- --   --         gh→em₂→ _ (sucPermFDMorphism _) (emPerm xs)
-- -- -- -- --   --   pp = {!!}

-- -- -- -- --   --   ppp : emF (emPerm (x ∷2 xs)) ≡
-- -- -- -- --   --          emF (gh→em₂→ _ (sucPermFDMorphism _) (emPerm xs))
-- -- -- -- --   --   ppp = {!!}

-- -- -- -- -- -- lookupEm : (Agrp : isGroupoid A) → (x : FMSet2 A) 
-- -- -- -- -- --       → emF (emPerm x) → A
-- -- -- -- -- -- lookupEm Agrp =
-- -- -- -- -- --   Elim.f
-- -- -- -- -- --    (λ ())
-- -- -- -- -- --    {!!}
-- -- -- -- -- --    {!!}
-- -- -- -- -- --    {!!}
-- -- -- -- -- --    {!!}
-- -- -- -- -- --    {!!}
-- -- -- -- -- --    {!!}
-- -- -- -- -- --    λ _ → isGroupoidΠ λ _ → Agrp 


-- -- -- -- -- --   -- elimSet _
-- -- -- -- -- --   --  (λ x → snd (EMFam.EM₁HFam isSetFin x))
-- -- -- -- -- --   --  zero {!!}

-- -- -- -- -- -- -- -- emK' : ∀ n → 
-- -- -- -- -- -- -- --      (x : EM₁ (SymData (suc n))) → 
-- -- -- -- -- -- -- -- emK' n =
-- -- -- -- -- -- -- --   elimSet _
-- -- -- -- -- -- -- --    (λ x → snd (EMFam.EM₁HFam isSetFin x))
-- -- -- -- -- -- -- --    zero {!!}


-- -- -- -- -- -- -- -- paK : {xs ys : FMSet2 A} → xs ≡ ys
-- -- -- -- -- -- -- --    → fst (SymData (len2 ys)) 
-- -- -- -- -- -- -- -- paK {xs = xs} {ys} p = {!!}

-- -- -- -- -- -- --     -- zz : {!!}
-- -- -- -- -- -- --     -- zz = {!encode (SymData (len2 ys)) ?!}

-- -- -- -- -- -- -- -- paUnwind : (x y : A) (xs ys : FMSet2 A) →
-- -- -- -- -- -- -- --              (p : x ∷2 xs ≡ y ∷2 ys)
-- -- -- -- -- -- -- --              → Σ (singl xs) λ (xs' , p') → cong (x ∷2_) p' ∙ {!!} ≡ p 
-- -- -- -- -- -- -- -- paUnwind = {!!}

-- -- -- -- -- -- -- headInsert : (x : A) → (xs : FMSet2 A) → (Fin (len2 xs))
-- -- -- -- -- -- --                 → singl (x ∷2 xs)
-- -- -- -- -- -- -- headInsert = {!!}

-- -- -- -- -- -- -- paMid : (x y : A) (xs ys : FMSet2 A) → 
-- -- -- -- -- -- --              (p : x ∷2 xs ≡ y ∷2 ys)
-- -- -- -- -- -- --              → Σ (Σ (FMSet2 A)
-- -- -- -- -- -- --                  λ zs → (xs ≡ y ∷2 zs) × (x ∷2 zs ≡ ys))
-- -- -- -- -- -- --                  λ (zs , (q , r)) → (cong (x ∷2_) q ∙∙ comm x y zs ∙∙ cong (y ∷2_) r) ≡ p
-- -- -- -- -- -- -- paMid = {!!}



-- -- -- -- -- -- -- -- -- --   inj∷2 : (xs ys : FMSet2 A) → (x : A)
-- -- -- -- -- -- -- -- -- --            → x ∷2 xs ≡ x ∷2 ys → xs ≡ ys
-- -- -- -- -- -- -- -- -- --   inj∷2 = ElimSet.f
-- -- -- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- -- -- --     -- (ElimSet.f
-- -- -- -- -- -- -- -- -- --     --    (λ _ _ → refl)
-- -- -- -- -- -- -- -- -- --     --    (λ x x₁ x₂ → {!!} ∘ cong len2  )
-- -- -- -- -- -- -- -- -- --     --    {!!}
-- -- -- -- -- -- -- -- -- --     --    {!!}
-- -- -- -- -- -- -- -- -- --     --    λ _ → isSetΠ2 λ _ _ → trunc _ _ )
-- -- -- -- -- -- -- -- -- --     (λ x {xs} b →
-- -- -- -- -- -- -- -- -- --       ElimSet.f
-- -- -- -- -- -- -- -- -- --        {!!}
-- -- -- -- -- -- -- -- -- --        (λ x' {ys} b' y' p →
-- -- -- -- -- -- -- -- -- --          {!!})
-- -- -- -- -- -- -- -- -- --          {!!} {!!}
-- -- -- -- -- -- -- -- -- --         λ _ → isSetΠ2 λ _ _ → trunc _ _)
-- -- -- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- -- -- --     λ _ → isSetΠ3 λ _ _ _ → trunc _ _ 

-- -- -- -- -- -- -- -- -- -- -- -- -- Rec.f
-- -- -- -- -- -- -- -- -- -- -- -- --      (isSet→isGroupoid isSetℕ) zero (λ _ → suc)
-- -- -- -- -- -- -- -- -- -- -- -- --        (λ _ _ _ → refl) (λ _ _ _ _ → refl)
-- -- -- -- -- -- -- -- -- -- -- -- --        (λ _ _ _ _ → refl) (λ _ _ _ _ → refl) (λ _ _ _ _ → refl)


-- -- -- -- -- -- -- -- -- -- -- -- -- RecSet.f isSetℕ zero (λ _ → suc) (λ _ _ _ → refl) (λ _ _ _ _ → refl)

-- -- -- -- -- -- -- -- -- -- -- --   -- open import Cubical.HITs.EilenbergMacLane1 as EM

-- -- -- -- -- -- -- -- -- -- -- module _ (A : Type ℓ) where
-- -- -- -- -- -- -- -- -- -- --   -- open import Cubical.Data.List.FinData


-- -- -- -- -- -- -- -- -- -- --   FMSet2OfLen : ℕ → Type ℓ
-- -- -- -- -- -- -- -- -- -- --   FMSet2OfLen n = Σ (FMSet2 A) λ x → len2 x ≡ n

-- -- -- -- -- -- -- -- -- -- -- module _ {A : Type ℓ} where
-- -- -- -- -- -- -- -- -- -- --   -- isSetLofLA : ∀ n → isSet (ListOfLen A n)
-- -- -- -- -- -- -- -- -- -- --   -- isSetLofLA n = isOfHLevelListOfLen 0 isSetA n 

-- -- -- -- -- -- -- -- -- -- --   FMSet2OfLen≡ : ∀ {n} → {x y : FMSet2OfLen A n} → fst x ≡ fst y → x ≡ y 
-- -- -- -- -- -- -- -- -- -- --   FMSet2OfLen≡ = Σ≡Prop λ _ → isSetℕ _ _

-- -- -- -- -- -- -- -- -- -- --   isGroupoidFMSet2OfLen : ∀ n → isGroupoid (FMSet2OfLen A n)
-- -- -- -- -- -- -- -- -- -- --   isGroupoidFMSet2OfLen n = 
-- -- -- -- -- -- -- -- -- -- --     (isOfHLevelΣ 3 trunc λ _ → isSet→isGroupoid (isProp→isSet (isSetℕ _ _)))

