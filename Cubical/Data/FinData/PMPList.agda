{-# OPTIONS --safe #-}
module Cubical.Data.FinData.PMPList where

open import Cubical.Foundations.Everything
open import Cubical.Data.FinData
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.Data.Sigma


open import Cubical.Data.FinData.Properties

open import Cubical.Algebra.Group

open import Cubical.Algebra.Group.Morphisms

open import Cubical.Algebra.Group.Generators

open import Cubical.Data.FinData.PermutationPrim as P

open import Cubical.HITs.ListedFiniteSet.Base2 as FM2

open import Cubical.HITs.EilenbergMacLane1 as EM


open import Cubical.Relation.Binary

open import Cubical.HITs.GroupoidQuotients as GQ renaming ([_] to [_]//)

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.List.FinData

infixr 9 _∘'_

_∘'_ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
        → (g : B → C) → (f : A → B) → A → C 
g ∘' f = λ x → g (f x)
{-# INLINE _∘'_ #-}


module _ {ℓ} {A : Type ℓ} where

  Vec : ℕ → Type ℓ
  Vec zero = Unit*
  Vec (suc x) = A × Vec x

  ↔snd : ∀ n → Vec n → Vec n → {!!} 
  ↔snd = {!!}

-- _ℕ=_ : ℕ → ℕ → Type
-- _ℕ=_ zero zero = Unit
-- _ℕ=_ zero (suc x₁) = ⊥
-- _ℕ=_ (suc x) zero = ⊥
-- _ℕ=_ (suc x) (suc x₁) = _ℕ=_ x x₁



-- module FC2M {ℓ} {A : Type ℓ} (isGrpA : isGroupoid A) where

--   adj↔ : (xs ys : List A) → (length xs) ℕ= (length ys) →
--           Fin (predℕ (length xs)) → {!!}
--   adj↔ = {!!}

--   ↔snd : ∀ (xs ys : List A) → (length xs) ℕ= (length ys) →
--           (EM₁ (Permutation (length xs))) → hSet ℓ
--   ↔snd xs ys x = EM.rec _
--    isGroupoidHSet
--      ((xs ≡ ys) , isOfHLevelList 1 isGrpA _ _)
--       (P.Rrec.f w) {!!}
--      where
--        w : P.Rrec
--              (((xs ≡ ys) , isOfHLevelList 1 isGrpA xs ys) ≡
--               ((xs ≡ ys) , isOfHLevelList 1 isGrpA xs ys))
--        Rrec.isSetA w = isGroupoidHSet _ _
--        Rrec.εA w = refl
--        Rrec.∷A w = {!!}
--        Rrec.invoA w = {!!}
--        Rrec.braidA w = {!!}
--        Rrec.commA w = {!!}
--   -- ↔snd [] [] _ _ = Unit* , isSetUnit*
--   -- ↔snd (x ∷ xs) (y ∷ ys) x =
--   --   EM.rec _ isGroupoidHSet
--   --    {!(xs ≡ ys , ?!}  {!!} {!!}
--   --  --   P.Rrec.f w
--   --  where
--   --    w : P.Rrec (hSet ℓ)
--   --    w = {!!}

 
-- --   record _↔ₙ_  {n} (x y : Fin n → A) : Type ℓ where
-- --     constructor prm
-- --     field
-- --       F≃ : Perm n
-- --       l≡ : x ∘ (fst (to≃ F≃)) ≡ y 
       



-- --   open _↔ₙ_

-- --   -- transCompP : ∀ {n} → (e f : Perm n) {a b : Fin n → A}
-- --   --                (p : a ∘ fst (to≃ n e) ≡ b)
-- --   --              → a ∘ fst (to≃ n (f · e)) ≡ b ∘ fst (to≃ n f)
-- --   -- transCompP = Relim.f w
-- --   --   where
-- --   --     w : Relim _
-- --   --     Relim.isSetA w _ = isSetΠ λ _ →
-- --   --        isSetImplicitΠ λ _ →
-- --   --         -- isSetImplicitΠ λ _ →
-- --   --         isSetImplicitΠ λ _ → isSetΠ λ _ → isGroupoidΠ (λ _ → grpA) _ _ 
-- --   --     Relim.εA w f p = {!!} --{!!} ∙ cong (_∘' fst (to≃ _ f)) p
-- --   --     Relim.∷A w k x x₁ x₂ = {!!}
-- --   --     Relim.invoA w = {!!}
-- --   --     Relim.braidA w = {!!}
-- --   --     Relim.commA w = {!!}

-- --   isTrans↔ₙ : ∀ n → BinaryRelation.isTrans (_↔ₙ_ {n = n}) 
-- --   isTrans↔ₙ n a b c (prm e p) (prm f q) =
-- --     prm (f · e) (cong (a ∘_) (to≃· f e) ∙∙ cong (_∘ fst (to≃ f)) p ∙∙ q)

-- --   Fin→//↔ : ℕ → Type ℓ
-- --   Fin→//↔ n = (Fin n → A) // isTrans↔ₙ n

-- --   tabulateFM2 : ∀ {n} → (Fin n → A) → FMSet2 A
-- --   tabulateFM2 {zero} _ = []
-- --   tabulateFM2 {suc n} f = (f zero) ∷2 tabulateFM2 (f ∘ suc)


-- --   hlpSwap : ∀ {n} → {f g : Fin n → A} → ∀ {k}
-- --             →  f ∘ (fst (adjTransposition* k)) ≡ g
-- --             →  f ≡ g ∘ (fst (adjTransposition* k))

-- --   hlpSwap {suc (suc n)} {k = zero} p =
-- --     (λ i → p i one) =→ (λ i → p i zero) =→ cong (_∘' (suc ∘' suc)) p
-- --   hlpSwap {suc (suc n)} {f} {g} {k = suc k} p =
-- --     (λ i → p i zero) =→ hlpSwap {k = k} (cong (_∘' suc) p)
  
-- --   record Elim≡ (B : ℕ → Type ℓ) : Type ℓ where
-- --     field
-- --       grpB : ∀ {n} → isGroupoid (B n)
-- --       b : ∀ n → (Fin n → A) → B n
-- --       b= : ∀ n k → (x : (Fin n → A))
-- --           → b n x ≡ b n (x ∘ fst (adjTransposition* k)) 
        
-- --       invoB : ∀ n → (k : Fin (predℕ n)) → (x : Fin n → A)
-- --         → Square
-- --               (b= n k (x ∘ fst (adjTransposition* k)))
-- --               (sym (b= n k x))
-- --               refl
-- --               (cong (b n ∘ (x ∘_) ∘ fst) (adjTransposition*²=idEquiv k) )

-- --       braidB : ∀ n k → (x : (Fin n → A)) 
-- --         → Square
-- --             (b= n (sucF n k) _)
-- --             (b= n (weakF n k) _)
-- --             (sym (b= n (weakF n k) x) ∙∙ refl ∙∙ (b= n (sucF n k) _) )
-- --             (b= n (weakF n k) _ ∙∙
-- --               cong (b n ∘ (x ∘_) ∘ fst) (adjTransposition*Braid _ k)
-- --               ∙∙ sym (b= n (sucF n k) _))
-- --       commB : ∀ n k l v → (x : (Fin n → A))
-- --         → Square
-- --              (b= n k x)
-- --              (b= n k _ ∙ cong (b n ∘ (x ∘_) ∘ fst)
-- --                (adjTransposition*Comm _ k l v))
-- --              (b= n l x)
-- --              (b= n l _)

-- --     commB' : ∀ n k l v → (x : (Fin n → A))
-- --       → Square
-- --            (sym (b= n l x) ∙∙ refl ∙∙ (b= n k x))
-- --            (cong (b n ∘ (x ∘_) ∘ fst) ((adjTransposition*Comm _ k l v)))
-- --            (b= n k _)
-- --            (b= n l _)
-- --     commB' n k l v x i j = hcomp
-- --         (λ k' → λ { 
-- --           (i = i1) → compPath-filler (b= n k _)
-- --               (cong (b n ∘ (x ∘_) ∘ fst)
-- --                (adjTransposition*Comm _ k l v)) j k'
-- --          ;(j = i0) → invSides-filler (sym (b= n l x)) (b= n k _) k' (~ i)
-- --          ;(j = i1) → commB n k l v x i k'
-- --           }) ((b= n l x) i)

-- --     f= : {n : ℕ} → _ 
-- --     f= {n} = Relim.f fR=
-- --      where
       
-- --        fR= : Relim (λ (e : Perm n) → (x y : Fin n → A)
-- --                → (p : x ∘ fst (to≃ e) ≡ y) → b n x ≡ b n y)
-- --        Relim.isSetA fR= _ = isSetΠ3 λ _ _ _ → grpB _ _
-- --        Relim.εA fR= _ _ = cong (b n)
-- --        Relim.∷A fR= k {xs} X x y p = 
-- --           X x (λ x₁ → x (fst (to≃ xs) x₁)) refl
-- --            ∙∙ b= n k (x ∘ fst (to≃ xs)) ∙∙ cong (b n) p

-- --        Relim.invoA fR= k {xs} X i x y p j =
-- --         let r = b= n k (x ∘ fst (to≃ xs))
-- --         in hcomp (λ k → λ {
-- --              (j = i0) → leftright (X x _ refl) r (~ i) (~ k) 
-- --             ;(j = i1) → b n (p k)
-- --             ;(i = i1) → hcomp
-- --                   (λ k' → λ {
-- --                       (k = i0) → r (k' ∧ ~ j)
-- --                      ;(k = i1) → X x (p k') (λ i' → p (k' ∧ i')) j
-- --                      ;(j = i1) → b n (p (k ∧ k'))
-- --                      })
-- --                   (X x _ refl (~ k ∨ j))
-- --              }) (invoB _ k (x ∘ fst (to≃ (xs))) i j)

            
-- --        Relim.braidA fR= k {xs} X i x y p =
-- --           (((X x x' refl  ∙'
-- --             λ j → doubleCompPath-filler
-- --               (sym (b= n (weakF n k) x')) refl (b= n (sucF n k) _) j i) ∙'
-- --              braidB n k x' i) ∙∙
-- --             (λ j → doubleCompPath-filler
-- --                 (b= n (weakF n k) _)
-- --                 (cong (b n ∘ (x' ∘_) ∘ fst) (adjTransposition*Braid _ k))
-- --                 (sym (b= n (sucF n k) (x' ∘
-- --                   fst (adjTransposition* _) ∘ fst (adjTransposition* _))))
-- --                (~ j) i)
-- --             ∙∙ cong (b n) p)
            
-- --          where

-- --           x' = _
-- --        Relim.commA fR= k l v X i x y p =
-- --          let x' = _
-- --          in (X x x' refl ∙'
-- --            λ j → doubleCompPath-filler
-- --               (sym (b= n l x')) refl (b= n k x') j i)
-- --             ∙∙ flipSquare (commB' n k l v x') i ∙∙ cong (b n) p 

-- --     f=Nat : ∀ {n : ℕ} (e : Perm n) (x y : Fin n → A) →
-- --       (p : x ∘ fst (to≃ e) ≡ y) →
-- --        Square (f= e x y p)
-- --               (cong (b _) p)
-- --               (f= e x _ refl)
-- --               refl
-- --     f=Nat e x y p i j =
-- --       hcomp (λ k → λ {
-- --              (i = i0) → f= e x (p k) (λ i' → p (k ∧ i')) j
-- --            ; (i = i1) → b _ (p (j ∧ k))
-- --            ; (j = i0) → f= e x _ refl i
-- --            ; (j = i1) → b _ (p k)
-- --              }) (f= e x _ refl (i ∨ j))
    
-- --        -- f= e x {!p (~ j ∨ (i))!} {!!}
-- --        --   (j ∨ i)

-- --     comp//lem : ∀ {n} → (P.RelimProp λ f → (e : Perm n)
-- --               {x : Fin n → A} {y : Fin n → A} {z : Fin n → A}
-- --                (p : x ∘ fst (to≃ e) ≡ y)
-- --                (q : y ∘ fst (to≃ f) ≡ z) →
-- --             (f= e x y p) ∙ (f= f y z q) ≡
-- --             f= (f · e) _ _
-- --              (cong (x ∘_) (to≃· f e) ∙∙ cong (_∘ fst (to≃ f)) p ∙∙ q))
-- --             --Rrec.feq (fR n) (isTrans↔ₙ n a b₁ c (prm e p) (prm f q))
-- --     RelimProp.isPropA comp//lem _ = isPropΠ λ _ →
-- --       isPropImplicitΠ2 λ _ _ → isPropImplicitΠ λ _ →
-- --        isPropΠ2 λ _ _ → grpB _ _ _ _ 
-- --     RelimProp.εA (comp//lem {n}) e {x} {y} {z} p =
-- --      J (λ z q → f= e x y p ∙ (λ i → b n (q i)) ≡
-- --       f= e x z
-- --       (cong (_∘_ x) (to≃· ε e) ∙∙
-- --        cong (λ section₁ → section₁ ∘ fst (to≃ ε)) p ∙∙ q))
-- --        (sym (rUnit _) ∙ cong (f= e x y) (compPath-filler _ _))
-- --     RelimProp.∷A (comp//lem {n}) k {xs} X e {x} {y} {z} p q =
-- --       (cong (f= e x y p ∙_)
-- --            lX  ∙ (assoc _ _ _))
-- --          ∙∙ cong ( _∙ zP ) X' ∙∙
-- --          rX 
-- --       where

-- --        zP : b _ (λ x₁ → z (fst (adjTransposition* k) x₁)) ≡ b _ z
-- --        zP = b= _ k _ ∙ cong  (b _) (sym (hlpSwap {f = z}  refl))

-- --        p' = (cong (_∘_ x) (to≃· xs e) ∙∙
-- --               cong (λ section₁ → section₁ ∘ fst (to≃ xs)) p
-- --                 ∙∙ hlpSwap {g = z} q)

-- --        lX : (f= xs y (y ∘ fst (to≃ xs)) refl
-- --                ∙∙ b= _ k (y ∘ fst (to≃ xs))
-- --                ∙∙ cong (b _) q)
-- --               ≡
-- --                f= xs y (z ∘ fst (adjTransposition* k)) (hlpSwap q)
-- --                ∙ zP
-- --        lX = {!!}

-- --        rX : f= (xs · e) x (z ∘ fst (adjTransposition* k))
-- --             (cong (_∘_ x) (to≃· xs e) ∙∙
-- --               cong (λ section₁ → section₁ ∘ fst (to≃ xs)) p
-- --                 ∙∙ hlpSwap q)
-- --          ∙ zP ≡
-- --           (f= (xs · e) x _ refl
-- --           ∙∙
-- --            b= _ k (x ∘ fst (to≃ (xs · e)))
-- --            ∙∙
-- --            cong (b _)
-- --             (cong (x ∘_) (to≃· (k ∷ xs) e)
-- --              ∙∙
-- --              cong (_∘ fst (to≃ (k ∷ xs))) p
-- --              ∙∙
-- --              q))
-- --        rX i j =
-- --          hcomp
-- --             (λ k' → λ {
-- --               (i = i0) → hcomp
-- --                  (λ k'' → λ {
-- --                       (k' = i0) → b= n k (p' (j ∧ ~ k'') ) (k'' ∧  j)
-- --                     ; (j = i0) → f= (xs · e) x _ refl (~ k')
-- --                     ; (j = i1) → compPath-filler
-- --                        (λ i' →
-- --                         b= n k (p' ( ~ k'' ∨ k')) i')
-- --                        (cong (b _) (sym (hlpSwap {f = z}
-- --                          {g = (p' ( ~ k'' ∨ k'))}
-- --                        λ i' → p' ((~ k'' ∨ k') ∨ ~ i' )))) k' k''
-- --                    })
-- --                  (f=Nat (xs · e) x (z ∘ fst (adjTransposition* k))
-- --                     p' (~ k') j)
-- --              ;(j = i0) → f= (xs · e) x _ refl (~ k')
-- --              ;(j = i1) → {!!}
-- --                })
-- --             (b= n k (x ∘ fst (to≃ (xs · e))) j)


-- --        X' = X e {x = x} {y = y} {z = z ∘ fst (adjTransposition* k)} p
-- --              (hlpSwap q)

-- --     fR : ∀ n → GQ.Rrec {Rt = isTrans↔ₙ n} (B n)
-- --     Rrec.Bgpd (fR n) = grpB
-- --     Rrec.fb (fR n) = b n
-- --     Rrec.feq (fR n) (prm e p) =
-- --       f= e _ _ p
-- --     Rrec.fsq (fR n) (prm e p) (prm f q) =
-- --       compPath-filler _ _ ▷ P.RelimProp.f (comp//lem) f e p q


-- --     f : ∀ n → Fin→//↔ n → (B n)
-- --     f n = GQ.Rrec.f (fR n)


-- --   ajdTFM2 : (n : ℕ) (k : Fin (predℕ n)) (x : Fin n → A) →
-- --       tabulateFM2 x ≡ tabulateFM2 (x ∘ fst (adjTransposition* k))
-- --   ajdTFM2 (suc .(suc _)) zero x = comm _ _ _
-- --   ajdTFM2 (suc .(suc _)) (suc k) x =
-- --     cong (x zero ∷2_) (ajdTFM2 _ k (x ∘ suc))
     
-- --   invoTFM2 : ∀ n (k : Fin (predℕ n))
-- --              (x : Fin n → A) →
-- --            Square (ajdTFM2 n k (x ∘ fst (adjTransposition* k)))
-- --            (sym (ajdTFM2 n k x)) refl
-- --            (cong (tabulateFM2 ∘ (x ∘_) ∘ fst) (adjTransposition*²=idEquiv k))
-- --   invoTFM2 (suc (suc n)) zero x = comm-inv _ _ _
-- --   invoTFM2 (suc (suc (suc n))) (suc k) x =
-- --     flipSquare ( congP (λ _ → cong (x zero ∷2_))
-- --       (flipSquare (invoTFM2 _ k (x ∘ suc))) ▷       
-- --        cong
-- --            {x = equivEq (refl =→ cong ((suc ∘'_) ∘ fst)
-- --                (adjTransposition*²=idEquiv k))}
-- --            {y = (adjTransposition*²=idEquiv (suc k))}
-- --              (cong (tabulateFM2 ∘ _∘_ x ∘ fst))
-- --              (isOfHLevel≃ 2 isSetFin isSetFin _ _ _ _))

-- --   braidTFM2 : ∀ n (k : Fin (predℕ (predℕ n)))
-- --               (x : Fin n → A) →
-- --             Square
-- --             (ajdTFM2 n (sucF n k) _)
-- --             (ajdTFM2 n (weakF n k) _)
-- --             (sym (ajdTFM2 n (weakF n k) x) ∙∙ refl ∙∙
-- --              ajdTFM2 n (sucF n k) x)
-- --             (ajdTFM2 n (weakF n k) _
-- --              ∙∙ cong ((tabulateFM2 ∘ (x ∘_) ∘ fst))
-- --                (adjTransposition*Braid n k)
-- --              ∙∙ sym (ajdTFM2 n (sucF n k) _))
-- --   braidTFM2 (suc (suc (suc n))) zero x =
-- --     flipSquare λ j → (sym (comm-inv _ _ _) ◁ flipSquare (hexU _ _ _ _)) j
-- --        ∙∙ refl ∙∙
-- --       (flipSquare (hexL _ _ _ _) ▷ cong (cong (x two ∷2_)) (comm-inv _ _ _)) j
    
-- --   braidTFM2 (suc n'@(suc (suc (suc n)))) (suc k) x = 
-- --     flipSquare 
-- --        (sym (cong-∙∙ (x zero ∷2_)
-- --          (sym (ajdTFM2 n' (weakenFin k) _)) _ _)
-- --         ◁ (λ i i₁ → x zero ∷2 braidTFM2 n' k (x ∘ suc) i₁ i)
-- --          ▷ (cong-∙∙ (x zero ∷2_) (ajdTFM2 n' (weakenFin k) _) _ _))

-- --   commTFM2 : (n : ℕ) (k l : Fin (predℕ n)) (v : commT n k l)
-- --       (x : Fin n → A) →
-- --       Square
-- --        (ajdTFM2 n k x)
-- --        (ajdTFM2 n k (x ∘ fst (adjTransposition* l)) ∙
-- --          (cong (tabulateFM2 ∘ _∘_ x ∘ fst) (adjTransposition*Comm n k l v)))

-- --        (ajdTFM2 n l x)
-- --         (ajdTFM2 n l (x ∘ fst (adjTransposition* k)))

-- --   commTFM2 (suc (suc (suc n))) zero (suc (suc l)) v x =
-- --      (λ i j → 
-- --        comm (x zero) (x one) (ajdTFM2 (suc n) l (x ∘' suc ∘' suc ) (i)) (j))
-- --      ▷ rUnit _
       
-- --   commTFM2 (suc (suc (suc n))) (suc k) (suc (suc l)) v x = 
-- --      (λ i j → x zero ∷2
-- --          (commTFM2 (suc (suc n)) k (suc l) v (x ∘ suc) i j)) 
-- --       ▷ (cong-∙ (x zero ∷2_) (ajdTFM2 _ (k)
-- --        (x ∘' suc ∘' fst (adjTransposition* (suc (l))))) _)
       
      
-- --   toFM2 : ∀ {n} → Fin→//↔ n → FMSet2 A
-- --   toFM2 {n} = Elim≡.f w n
-- --     where
-- --       w : Elim≡ _
-- --       Elim≡.grpB w = trunc
-- --       Elim≡.b w _ = tabulateFM2
-- --       Elim≡.b= w = ajdTFM2
-- --       Elim≡.invoB w = invoTFM2  
-- --       Elim≡.braidB w = braidTFM2
-- --       Elim≡.commB w = commTFM2
  
-- --   append→ : ∀ {n} → A → Fin→//↔ n → Fin→//↔ (suc n) 
-- --   append→ {n} a = Elim≡.f w n
-- --     where
-- --       w : Elim≡ (Fin→//↔ ∘ suc)
-- --       Elim≡.grpB w = squash//
-- --       Elim≡.b w _ = [_]// ∘ λ f → λ { zero → a ; (suc k) → f k }
-- --       Elim≡.b= w = {!!}
-- --       -- Elim≡.b= w (suc _) k _ = eq// (prm (η (suc k)) (refl =→ refl))      
-- --       Elim≡.invoB w = {!!}
-- --       Elim≡.braidB w = {!!}
-- --       Elim≡.commB w = {!!}

-- --   fromFM2 : (l : FMSet2 A) → Fin→//↔ (len2 l)
-- --   fromFM2 = FM2.RElim.f rFrom

-- --     where
-- --       rFrom : FM2.RElim (λ (l : FMSet2 A) → Fin→//↔ (len2 l))
-- --       RElim.[]* rFrom = [ (λ ()) ]//
-- --       RElim._∷*_ rFrom = λ a {xs} → append→ {n = len2 xs} a
-- --       -- λ a → append→ a
-- --       RElim.comm* rFrom = {!!}
-- --        -- λ x y {xs} b → appendComm x y b
-- --       RElim.comm-inv* rFrom = {!!}
-- --        -- λ x y b → appendSym _  x y b
-- --       RElim.hexDiag* rFrom = {!!}
-- --        -- λ x y z b → appendDiag x y z b
-- --       RElim.hexU* rFrom = {!!}
-- --        -- λ x y z {xs} b → appendHexU (len2 xs) x y z b
-- --       RElim.hexL* rFrom = {!!}
-- --       -- λ x y z {xs} b → appendHexL (len2 xs) x y z b
-- --       RElim.trunc* rFrom = λ _ → squash// 




-- --   --   -- fR= : ∀ n → (e : fst (Perm n)) → (x y : Fin n → A)
-- --   --   --         → (p : x ∘ fst (to≃' n e) ≡ y) → b n x ≡ b n y
-- --   --   -- fR= zero e x y p = cong (b zero) =■
-- --   --   -- fR= (suc n) (η k) x y p = b= n k x y p
-- --   --   -- fR= (suc n) (e · e₁) x y p =
-- --   --   --     fR= (suc n) e₁ x _ refl
-- --   --   --   ∙ fR= (suc n) e _ y p
-- --   --   -- fR= (suc n) ε x y = cong (b (suc n))
-- --   --   -- fR= (suc n) (inv e) x y p =
-- --   --   --   sym (fR= (suc n) e y x
-- --   --   --     (cong (_∘' fst (to≃' (suc n) e)) (sym p)
-- --   --   --       ∙ cong (x ∘'_ ) (funExt (retEq (to≃' (suc n) e)))))
-- --   --   -- fR= (suc n) (PresentedGroup.assoc e e₁ e₂ i) x y p =
-- --   --   --    GL.assoc
-- --   --   --   (fR= (suc n) e₂ x _ refl)
-- --   --   --   (fR= (suc n) e₁ _ _  refl)
-- --   --   --   (fR= (suc n) e _ y p) (~ i)
-- --   --   -- fR= (suc n) (idr e i) x y p = lUnit (fR= (suc n) e x y p) i
-- --   --   -- fR= (suc n) (idl e i) x y p =
-- --   --   --    (rUnit (fR= (suc n) e x y p) ∙
-- --   --   --      λ i → fR= (suc n) e x (p (~ i)) (λ j → p (~ i ∧ j))
-- --   --   --        ∙ cong (b (suc n)) λ j → p (~ i ∨ j)) i
-- --   --   -- fR= (suc n) (invr e i) x y p = {!!}
-- --   --   -- fR= (suc n) (invl e i) x y p = {!!}
-- --   --   -- fR= (suc .(k + suc n)) (rel (zero {k = k} (invo {n})) i) x y p j =  
-- --   --   --   invoB= (k + suc n) x y (+k zero) i p j
-- --   --   -- fR= (suc .(k + suc (suc n))) (rel (zero {k = k} (braid {n})) i) x y p =
-- --   --   --   braidB= n k x y i p
-- --   --   -- fR= (suc .(k + suc (suc n))) (rel (zero {k = k} (comm {n} x₁)) i) x y p =
-- --   --   --   commB= k n x₁ x y i p
-- --   --   -- fR= (suc n) (trunc e e₁ x₁ y₁ i i₁) x y p j =
-- --   --   --   {!!}
