{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Sigma.Record.Properties where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

open import Cubical.Data.List
open import Cubical.Data.Vec
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to ⊥-rec )

open import Cubical.Foundations.Everything

open import Cubical.Foundations.CartesianKanOps

open import Cubical.Data.Sigma.Record.Base


pathPSigma-≡-sigmaPathP :
                      ∀ {ℓ ℓ'} → {A : I → Type ℓ} → {B : ∀ i → A i → Type ℓ' }
                      → {a : Σ (A i0) (B i0)} → {b : Σ (A i1) (B i1)}
                      → (PathP (λ i → Σ (A i) (B i)) a b)
                         ≡
                        (Σ[ p ∈ (PathP A (fst a) (fst b)) ]
                         (PathP (λ i → B i (p i)) (snd a) (snd b)))
pathPSigma-≡-sigmaPathP =
  isoToPath (iso
    (λ x → (λ i → fst (x i)) , (λ i → snd (x i)))
    (λ x i → (fst x i) , (snd x i)) (λ _ → refl) λ _ → refl)


push-popVal-Iso : ∀ {ℓ} → ∀ {n}
                     → (A : Sigₗ ℓ n)
                     → Iso (Σ (Recₗ (trim-sig A)) (pop-Type-overRecₗ A)) (Recₗ A)
Iso.fun (push-popVal-Iso A) x = pushVal A (fst x) (snd x)
Iso.inv (push-popVal-Iso A) x = trim-rec A x , popVal A x 
Iso.rightInv (push-popVal-Iso {n = zero} A) b = refl
Iso.rightInv (push-popVal-Iso {n = suc zero} A) b = refl
Iso.rightInv (push-popVal-Iso {n = suc (suc zero)} A) b = refl
Iso.rightInv (push-popVal-Iso {n = suc (suc (suc n))} A) b i =
  (fst b) , Iso.rightInv (push-popVal-Iso (snd A (fst b))) (snd b) i
Iso.leftInv (push-popVal-Iso {n = zero} A) a = refl
Iso.leftInv (push-popVal-Iso {n = suc zero} A) a = refl
Iso.leftInv (push-popVal-Iso {n = suc (suc zero)} A) a = refl
Iso.leftInv (push-popVal-Iso {n = suc (suc (suc n))} A) a i =
  let prev = Iso.leftInv (push-popVal-Iso (snd A (fst (fst a))))
             (snd (fst a) , (snd a)) i

  in  (fst (fst a) , (fst prev)) , snd prev


push-trim-Recₗ : ∀ {ℓ} → ∀ {n} → {s : Sigₗ ℓ n} → ∀ x →
                   Σ (Recₗ (trim-sig (push-Type s x)))
                      (pop-Type-overRecₗ (push-Type s x))
                   ≡ Σ (Recₗ s) x
push-trim-Recₗ {ℓ} {0} {s = s} x = refl
push-trim-Recₗ {ℓ} {1} {s = s} x = refl
push-trim-Recₗ {ℓ} {suc (suc n)} {s = s} x
  = 
 isoToPath (push-popVal-Iso (push-Type s x))
   ∙∙ cong (Σ (fst s))
        ((funExt (λ x₁ →
          sym (isoToPath (push-popVal-Iso  (snd (push-Type s x) x₁)))
          ∙ push-trim-Recₗ {s = (snd s x₁)}  (λ b → x (x₁ , b)))))
   ∙∙ sym (ua  assocΣ)

push-trim-Recₗ' : ∀ {ℓ} → ∀ {n} → {s : Sigₗ ℓ n} → ∀ x →
                   Recₗ (trim-sig (push-Type s x))
                   ≡
                   Recₗ s
push-trim-Recₗ' {ℓ} {0} {s = s} x = refl
push-trim-Recₗ' {ℓ} {1} {s = s} x = refl
push-trim-Recₗ' {ℓ} {suc (suc n)} {s = s} x = 
 cong (Σ _) (funExt λ x₁ → push-trim-Recₗ' {s = snd s x₁} (λ x₂ → x (x₁ , x₂)))



concatSigₗ-rec-Iso : ∀ {ℓ} → ∀ {n m} → (sₙ : Sigₗ ℓ n) → (sₘ : Sigₗ ℓ m) →
                      Iso (Recₗ sₙ × Recₗ sₘ) (Recₗ (concatSigₗ sₙ sₘ)) 
concatSigₗ-rec-Iso {n = zero} {zero} sₙ sₘ =
  iso (λ x → lift tt) (λ _ → lift tt , lift tt) (λ _ → refl) λ _ → refl
concatSigₗ-rec-Iso {n = zero} {suc m} sₙ sₘ =
  iso snd (_ ,_) (λ b → refl) λ a → refl

concatSigₗ-rec-Iso {ℓ} {n = suc n} {zero} sₙ _ = 
  compIso (iso fst (_, _) (λ _ → refl) (λ _ → refl))
   (pathToIso λ i → Recₗ (transp (λ i₁ → Sigₗ ℓ (suc (+-zero n (~ i₁ ∨ (~ i))))) (~ i) sₙ))
  
concatSigₗ-rec-Iso {n = suc zero} {suc m} sₙ sₘ =
  iso (λ x → x) (λ x → x) (λ b → refl) (λ b → refl)

concatSigₗ-rec-Iso {n = suc (suc n)} {suc m} sₙ sₘ =
  let prev : (x : fst sₙ) → Iso (Recₗ (snd sₙ x) × Recₗ sₘ) (Recₗ (concatSigₗ (snd sₙ x) sₘ))
      prev x = concatSigₗ-rec-Iso {n = suc n} {suc m} ((snd sₙ) x) sₘ
  in
   iso
    (λ x → fst (fst x) , Iso.fun (prev (fst (fst x))) (snd (fst x) , snd x))
    (λ x → let y = Iso.inv (prev (fst x)) (snd x)
           in (fst x ,  fst y) , snd y)
    (λ b i → fst b , Iso.rightInv (prev (fst b)) (snd b) i )
    λ a i → let y = Iso.leftInv (prev (fst (fst a))) ( snd (fst a) , snd a) i
             in ((fst (fst a)) , fst y) , snd y 


concatSigₗ-dep-rec-Iso : ∀ {ℓ} → ∀ {n m}
                          → (sₙ : Sigₗ ℓ n)
                          → (sₘ : Recₗ sₙ → Sigₗ ℓ m)
                          → Iso (Σ (Recₗ sₙ) (Recₗ ∘ sₘ)) (Recₗ (concatSigₗ-dep sₙ sₘ)) 
concatSigₗ-dep-rec-Iso {n = zero} sₙ sₘ =
  iso (snd) (_ ,_) (λ b → refl) λ a → refl
concatSigₗ-dep-rec-Iso {ℓ} {n = suc n} {zero} sₙ sₘ =
    compIso (iso fst (_, _) (λ _ → refl) (λ _ → refl))
   (pathToIso λ i → Recₗ (transp (λ i₁ → Sigₗ ℓ (suc (+-zero n (~ i₁ ∨ (~ i))))) (~ i) sₙ))
concatSigₗ-dep-rec-Iso {n = suc zero} {suc m} sₙ sₘ =
    iso (λ x → x) (λ x → x) (λ b → refl) (λ b → refl)
concatSigₗ-dep-rec-Iso {n = suc (suc n)} {suc m} sₙ sₘ =
  let prev : (x : fst sₙ) →  Iso (Σ (Recₗ (snd sₙ x)) (Recₗ ∘ sₘ ∘ (x ,_)))
                              (Recₗ (concatSigₗ-dep (snd sₙ x) (sₘ ∘ (x ,_)))) 
      prev x = concatSigₗ-dep-rec-Iso {n = suc n} {suc m} ((snd sₙ) x) (sₘ ∘ (x ,_))
  in
   iso
    (λ x → fst (fst x) , Iso.fun (prev (fst (fst x))) (snd (fst x) , snd x))
    (λ x → let y = Iso.inv (prev (fst x)) (snd x)
           in (fst x ,  fst y) , snd y)
    (λ b i → fst b , Iso.rightInv (prev (fst b)) (snd b) i )
    λ a i → let y = Iso.leftInv (prev (fst (fst a))) ( snd (fst a) , snd a) i
             in ((fst (fst a)) , fst y) , snd y 


concat-split-Sigₗ : ∀ {ℓ} → ∀ n m → Iso (Sigₗ ℓ (n + m))
                             (Σ[ sₙ ∈ Sigₗ ℓ n ] (Recₗ sₙ → Sigₗ ℓ m))
concat-split-Sigₗ {ℓ} n m =
  iso splitSigₗ (uncurry concatSigₗ-dep) (rightInv n m) (leftInv n m)

  where
    rightInv : ∀ n m → section splitSigₗ (uncurry (concatSigₗ-dep {n = n} {m}))
    rightInv zero m b = refl
    rightInv (suc n) zero b i =
        (transportTransport⁻ (λ i₁ → Sigₗ ℓ (suc (+-zero n i₁))) (fst b)) i , (const _) 
    rightInv (suc zero) (suc m) b = refl
    rightInv (suc (suc n)) (suc m) ((A ,  x) ,  y) i =
      let  z : (a : A) → Σ (Sigₗ ℓ (suc n)) (λ sₙ → Recₗ sₙ → Sigₗ ℓ (suc m))
           z a = rightInv (suc n) (suc m) ( x a , y ∘ (a ,_) ) i
      in (A , fst ∘ z ) , λ x₁ → snd (z (fst x₁)) (snd x₁) 
     

    leftInv : ∀ n m → retract splitSigₗ (uncurry (concatSigₗ-dep {n = n} {m}))
    leftInv zero m a = refl
    leftInv (suc n) zero = transportTransport⁻ (λ i → Sigₗ ℓ ((+-zero (suc n)) (~ i)))
    leftInv (suc zero) (suc m) a = refl
    leftInv (suc (suc n)) (suc m) (A , x) i = A , λ a → leftInv (suc n) (suc m) ( x a ) i


concat-split : ∀ {ℓ} → ∀ n m →
                   PathP (λ i → isoToPath (concat-split-Sigₗ {ℓ} n m) i → Type ℓ)
                     Recₗ  λ x → Σ (Recₗ (fst x)) λ y → Recₗ ((snd x) y) 
concat-split {ℓ} n m = toPathP (funExt λ x → isoToPath (uncurry h x) )
  where

   h : (sₙ : Sigₗ ℓ n ) (sₘ : Recₗ sₙ → Sigₗ ℓ m) → _
   h sₙ sₘ = compIso (pathToIso
                 (λ i →  Recₗ (concatSigₗ-dep (transportRefl sₙ i )
                        (coe1→i (λ i → Recₗ (transp (λ _ → Sigₗ ℓ n) i sₙ) → Sigₗ ℓ m) i sₘ))))
              (invIso (concatSigₗ-dep-rec-Iso sₙ sₘ))


concat-split' : ∀ {ℓ} → ∀ n m → 
                     Path (Σ (Type (ℓ-suc ℓ)) (λ x → x → Type ℓ))
                          (Sigₗ ℓ (n + m) , Recₗ)
                          
                          ((Σ[ sₙ ∈ Sigₗ ℓ n     ] (Recₗ sₙ → Sigₗ ℓ m))
                           , λ x → Σ[ rₙ ∈ Recₗ (fst x) ] Recₗ ((snd x) rₙ))
concat-split' n m i = isoToPath (concat-split-Sigₗ n m) i , concat-split n m i



LR-Path : ∀ {ℓ} → ∀ n → Path (Σ (Type (ℓ-suc ℓ)) (λ x → x → Type ℓ))
                           ((Sigₗ ℓ (suc (suc n))) , Recₗ)
                           ((Σ[ sₙ ∈ (Sigₗ ℓ (suc n)) ] (Recₗ sₙ → Sigₗ ℓ 1))
                            , λ x → Σ[ rₙ ∈ (Recₗ (fst x)) ] (Recₗ (snd x rₙ)))
LR-Path {ℓ} (n) = (λ i → (Sigₗ ℓ (+-comm 1 ((suc n)) i) , Recₗ)) ∙ concat-split' (suc n) 1



-- LR-Path : ∀ {ℓ} → ∀ n → Path (Σ (Type (ℓ-suc ℓ)) (λ x → x → Type ℓ))
--                            ((Sigₗ ℓ n) , Recₗ) ((Sigᵣ ℓ n) , Recᵣ)
-- LR-Path zero = refl
-- LR-Path (suc zero) = refl
-- LR-Path {ℓ} (suc (suc n)) =
--      (λ i → (Sigₗ ℓ (+-comm 1 ((suc n)) i) , Recₗ))
--   ∙∙ concat-split' (suc n) 1
--   ∙∙
--   cong (λ a → (Σ (fst a) (λ x → snd a x → Type ℓ)) , λ x → Σ ((snd a) (fst x)) (snd x))
--    (LR-Path (suc n))








-- --- EXPERIMENTS



-- ×-n-assoc : ∀ {ℓ} → ∀ {n} → Vec (Type ℓ) n → Σ (Type (ℓ-suc ℓ)) λ x → x
-- ×-n-assoc {n = n} v =
--    (_ ≡ _) , (λ i → snd (LR-Path n i) (coe0→i (λ j → fst (LR-Path n j)) i (fromVecOfTypes v)))

-- ×-n-assoc-test :  ℕ × Bool × Unit × ℕ × Bool ≡ (((ℕ × Bool) × Unit) × ℕ) × Bool 
-- ×-n-assoc-test = snd (×-n-assoc (ℕ ∷ Bool ∷ Unit ∷ ℕ ∷ Bool ∷ []))


-- repeat-Type-sigₗ : ∀ {ℓ} → ∀ n → Sigₗ (ℓ-suc ℓ) n
-- repeat-Type-sigₗ zero = _
-- repeat-Type-sigₗ (suc zero) = Type _
-- repeat-Type-sigₗ (suc (suc n)) = Type _ , const (repeat-Type-sigₗ (suc n))


-- Σ-n-assoc : ∀ {ℓ} → ∀ n → (s : Sigₗ ℓ n) → Σ (Type (ℓ-suc ℓ)) (λ x → x)
-- Σ-n-assoc n s =
--   (_ ≡ _) , (λ i → snd (LR-Path n i) (coe0→i (λ j → fst (LR-Path n j)) i s))


-- -- SigSigᵣ : ∀ ℓ → ∀ n → Σ[ s ∈ Sigᵣ (ℓ-suc ℓ) n ] (Recᵣ s → Sigᵣ ℓ n)  
-- -- SigSigᵣ ℓ zero = _ , (idfun _)
-- -- SigSigᵣ ℓ (suc zero) = Type ℓ , idfun _ 
-- -- SigSigᵣ ℓ (suc (suc zero)) = (Type ℓ , λ x → x → Type ℓ) , idfun _
-- -- SigSigᵣ ℓ (suc (suc (suc n))) =
-- --    let (s , to) = SigSigᵣ ℓ (suc (suc n))
-- --    in (s , λ x → Recᵣ (to x) → Type ℓ) ,
-- --         (λ x → (to (fst x)) , (λ x₁ → (snd x) x₁)) 

-- -- SigSigᵣ : ∀ ℓ → ∀ n → Σ[ s ∈ Sigᵣ (ℓ-suc ℓ) n ] (Iso (Recᵣ s) (Sigᵣ ℓ n))  
-- -- SigSigᵣ ℓ zero = _ , idIso
-- -- SigSigᵣ ℓ (suc zero) = Type ℓ , idIso 
-- -- SigSigᵣ ℓ (suc (suc zero)) = (Type ℓ , λ x → x → Type ℓ) , idIso
-- -- SigSigᵣ ℓ (suc (suc (suc n))) =
-- --    let (s , iso to from ri li) = SigSigᵣ ℓ (suc (suc n))
-- --    in (s , λ x → Recᵣ (to x) → Type ℓ) ,
-- --        iso ((λ x → (to (fst x)) , snd x) )
-- --                (λ x → (from (fst x)) , λ x₁ → snd x (subst Recᵣ (ri (fst x)) x₁))
-- --             (λ b i → ri (fst b) i ,
-- --                λ x → snd b (coei→1 (λ i → Σ (Recᵣ (fst (ri (fst b) i))) (snd (ri (fst b) i))) i x) )
-- --             λ a i → {!!}

-- --   where

-- --    to = Iso.fun (snd (SigSigᵣ ℓ (suc (suc n))))
   
-- --    from = Iso.fun (snd (SigSigᵣ ℓ (suc (suc n))))
-- --    li = Iso.leftInv (snd (SigSigᵣ ℓ (suc (suc n))))
-- --    ri = Iso.rightInv (snd (SigSigᵣ ℓ (suc (suc n))))

-- --    zzzz : (a : Σ (Recᵣ (fst (SigSigᵣ ℓ (suc (suc n)))))
-- --                  (λ x → Recᵣ (Iso.fun (snd (SigSigᵣ ℓ (suc (suc n)))) x) → Type ℓ))
-- --                  → Recᵣ
-- --                      (Iso.fun (snd (SigSigᵣ ℓ (suc (suc n))))
-- --                       (Iso.inv (snd (SigSigᵣ ℓ (suc (suc n))))
-- --                        (Iso.fun (snd (SigSigᵣ ℓ (suc (suc n)))) (fst a)))) →
-- --                      Type ℓ
-- --    zzzz a y = snd a ( {!qq!}) 

-- --      where
  
-- --        zzTy= : Σ
-- --                  (Recᵣ
-- --                   (fst
-- --                    (Iso.fun (snd (SigSigᵣ ℓ (suc (suc n))))
-- --                     (Iso.inv (snd (SigSigᵣ ℓ (suc (suc n))))
-- --                      (Iso.fun (snd (SigSigᵣ ℓ (suc (suc n)))) (fst a))))))
-- --                  (snd
-- --                   (Iso.fun (snd (SigSigᵣ ℓ (suc (suc n))))
-- --                    (Iso.inv (snd (SigSigᵣ ℓ (suc (suc n))))
-- --                     (Iso.fun (snd (SigSigᵣ ℓ (suc (suc n)))) (fst a)))))
-- --                  ≡ Σ {!!} {!!}
-- --        zzTy= = (λ i → Σ (Recᵣ (fst (to (li (fst a) i)))) ((snd (to (li (fst a) i)))))

-- --        qq : {!!}
-- --        qq = transport (zzTy=) y

-- --    zzz : (a : Σ (Recᵣ (fst (SigSigᵣ ℓ (suc (suc n)))))
-- --                 (λ x → Recᵣ (Iso.fun (snd (SigSigᵣ ℓ (suc (suc n)))) x) → Type ℓ))
-- --                       → (Iso.inv (snd (SigSigᵣ ℓ (suc (suc n))))
-- --                          (Iso.fun (snd (SigSigᵣ ℓ (suc (suc n)))) (fst a))
-- --                          , zzzz a)
-- --                         ≡ a
-- --    zzz = {!!}

-- -- -- ?3 (i = i1) = snd a x : Set ℓ
-- -- -- ?3 (i = i0)
-- -- --   = snd a
-- -- --     (transp
-- -- --      (λ i₁ →
-- -- --         Σ
-- -- --         (Recᵣ
-- -- --          (fst
-- -- --           (Iso.rightInv (snd (SigSigᵣ ℓ (suc (suc n))))
-- -- --            (Iso.fun (snd (SigSigᵣ ℓ (suc (suc n)))) (fst a)) i₁)))
-- -- --         (snd
-- -- --          (Iso.rightInv (snd (SigSigᵣ ℓ (suc (suc n))))
-- -- --           (Iso.fun (snd (SigSigᵣ ℓ (suc (suc n)))) (fst a)) i₁)))
-- -- --      i0 x)
-- -- --   : Set ℓ


-- --  -- Recᵣ (Iso.fun (snd (SigSigᵣ ℓ (suc (suc n)))) (fst a))


-- -- -- (λ x → (to (fst x)) , (λ x₁ → (snd x) x₁)) 


-- -- -- SigSigₗ : ∀ ℓ → ∀ n → Σ[ s ∈ Sigₗ (ℓ-suc ℓ) n ] (Recₗ s → Sigₗ ℓ n)  
-- -- -- SigSigₗ ℓ zero = _ , (idfun _)
-- -- -- SigSigₗ ℓ (suc zero) = Type ℓ , idfun _ 
-- -- -- SigSigₗ ℓ (suc (suc zero)) = (Type ℓ , λ x → x → Type ℓ) , idfun _
-- -- -- SigSigₗ ℓ (suc (suc (suc n))) =
-- -- --    let (s , to) = SigSigₗ ℓ (suc (suc n))
-- -- --        nextS = push-Type s (λ x → Recₗ ((to x)) → Type ℓ )
-- -- --    in nextS ,
-- -- --       λ x → let ww = Iso.inv (push-popVal-Iso nextS) x  
-- -- --                 z = (transport (push-trim-Recₗ {s = s} (λ x → Recₗ (to x) → Type ℓ )) ww)
-- -- --             in push-Type (to (fst z)) λ x₁ → (snd z x₁)

-- -- -- mk-Σ-n-assocTy : ∀ ℓ → ℕ → Σ (Type (ℓ-suc (ℓ-suc ℓ))) λ x → x
-- -- -- mk-Σ-n-assocTy ℓ n =  _ , pop-Type false []
-- -- --                       (push-Type {!fst (SigSigₗ ℓ n)!} {!!}) 


-- -- -- mk-Σ-n-assoc : fst (mk-Σ-n-assocTy ℓ-zero 3)
-- -- -- mk-Σ-n-assoc = snd (mk-Σ-n-assocTy ℓ-zero 3)

-- -- -- mk-Σ-n-assocXX : {!!}
-- -- -- mk-Σ-n-assocXX = {!snd (mk-Σ-n-assocTy ℓ-zero 2)!}

-- -- -- -- Sig-ff :  ∀ {ℓ} → ∀ {n} → Type ℓ → Sigₗ ℓ n → Sigₗ ℓ (suc n)
-- -- -- -- Sig-ff {n = zero} x x₁ = x
-- -- -- -- Sig-ff {n = suc zero} x x₁ = {!!}
-- -- -- -- Sig-ff {n = suc (suc n)} x x₁ = x , λ x₂ →  (x → fst x₁) , λ x₃ → (snd x₁) (x₃ x₂)

-- -- -- -- SigSigₗ : ∀ ℓ → ∀ n → Type ℓ → Sigₗ (ℓ-suc ℓ) n 
-- -- -- -- SigSigₗ ℓ zero _ = _
-- -- -- -- SigSigₗ ℓ (suc zero) x = Type ℓ
-- -- -- -- SigSigₗ ℓ (suc (suc zero)) x = (Type ℓ) , (λ x → x → Type ℓ)
-- -- -- -- SigSigₗ ℓ (suc (suc (suc n))) = {!!}

-- -- -- -- -- SigSigₗ : ∀ ℓ → ∀ n → Type ℓ  → Sigₗ (ℓ-suc ℓ) n 
-- -- -- -- -- SigSigₗ ℓ zero _ = _ 
-- -- -- -- -- SigSigₗ ℓ (suc zero) x = x → Type ℓ  
-- -- -- -- -- SigSigₗ ℓ (suc (suc zero)) x = (x → Type ℓ) , (λ x → {!!})
-- -- -- -- -- SigSigₗ ℓ (suc (suc (suc n))) = {!!}
-- -- -- -- --   -- Type ℓ ,
-- -- -- -- --   --           λ x → let  z : {!!}
-- -- -- -- --   --                      z = concatSigₗ-dep {n = 1} x {!!}
-- -- -- -- --   --                   in {!!}


-- -- -- -- -- -- -- SigSigₗ : ∀ ℓ → ∀ n → Sigₗ (ℓ-suc ℓ) n
-- -- -- -- -- -- -- SigSigₗ ℓ n = transport⁻ (cong fst (LR-Path {ℓ-suc ℓ} n)) (fst (SigSig ℓ n)) 

-- -- -- -- -- -- SigSig-test : Recᵣ (fst (SigSig ℓ-zero 6))
-- -- -- -- -- -- SigSig-test = {!!}

-- -- -- -- -- -- -- SigSig : ∀ ℓ → ∀ n → Σ[ s ∈ Sigᵣ (ℓ-suc ℓ) n ] ((Recᵣ s → Sigᵣ ℓ n) × (Sigᵣ ℓ n → Recᵣ s) )  
-- -- -- -- -- -- -- SigSig ℓ zero = _ , (idfun _ , idfun _)
-- -- -- -- -- -- -- SigSig ℓ (suc zero) = Type ℓ , idfun _ , idfun _
-- -- -- -- -- -- -- SigSig ℓ (suc (suc zero)) = {!!}
-- -- -- -- -- -- -- SigSig ℓ (suc (suc (suc n))) =
-- -- -- -- -- -- --    let (s , (to , from)) = SigSig ℓ (suc (suc n))
-- -- -- -- -- -- --    in (s , (Lift ∘ Recᵣ) ∘ to) ,
-- -- -- -- -- -- --                               (λ x → to (fst x) , λ x₁ → {!!}) , {!!}






-- -- -- -- -- -- -- ×-n-assoc' : ∀ {ℓ} → ℕ → Σ (Type (ℓ-suc (ℓ-suc ℓ))) λ x → x
-- -- -- -- -- -- -- ×-n-assoc' n =
-- -- -- -- -- -- --   _ , pop-Type true [] ((push-Type (repeat-Type-sigₗ n)
-- -- -- -- -- -- --     {!!}))



