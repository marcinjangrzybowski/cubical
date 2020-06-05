{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Sigma.Record.Path where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

open import Cubical.Data.List
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Vec

open import Cubical.Foundations.Everything

open import Cubical.Foundations.CartesianKanOps

open import Cubical.HITs.Interval.Base renaming (elim to I-elim ; rec to I-rec)

open import Cubical.Data.Sigma.Record.Base

open import Cubical.Data.Sigma.Record.Properties


 

sigₗ-PathP : ∀ {ℓ} → ∀ {n}
                 → (p : I → Sigₗ ℓ n)
                 → (x₀ : Recₗ (p i0)) → (x₁ : Recₗ (p i1))
                 → Σ[ sₚ ∈ Sigₗ ℓ n ]
                    (Recₗ sₚ) ≡ (PathP (λ i → Recₗ (p i)) x₀ x₁) 
sigₗ-PathP {ℓ} {0} p x₀ x₁ = _ , isoToPath (iso (λ x i → _) (λ _ → _) (λ b i i₁ → _) (λ a i → _))  
sigₗ-PathP {ℓ} {1} p x₀ x₁ = PathP p x₀ x₁ , refl
sigₗ-PathP {ℓ} {suc (suc n)} p x₀ x₁ =
  let                                              
       (sPrev , lawPrev) = (sigₗ-PathP (λ i → trim-sig (p i))
                               (trim-rec (p i0) x₀) (trim-rec (p i1) x₁))   

       typeToPush : Recₗ sPrev → Type ℓ
       typeToPush x = PathP (λ i → pop-Type-overRecₗ (p i) (transport (lawPrev) x i))
                            (popVal (p i0) x₀)
                            (popVal (p i1) x₁)

       sNext : Sigₗ ℓ _
       sNext = push-Type sPrev typeToPush

       pu-po-sq : (i j : I) → Type ℓ 
       pu-po-sq i j = isoToPath (push-popVal-Iso (p i)) j


       -- this lemma just removes transp in various places
       coe-fix : _
       coe-fix = (λ i → Σ ((PathP (λ i → Recₗ (trim-sig (p i)))
                    (trim-rec (p i0) x₀)
                    (trim-rec (p i1) x₁)))
                     (λ p₁ → PathP (λ j →
                                  pop-Type-overRecₗ (p j)
                                       (transportTransport⁻
                                        (snd
                                         (sigₗ-PathP (λ i → trim-sig (p i))
                                          (trim-rec (p i0) x₀)
                                          (trim-rec (p i1) x₁))) p₁ i
                                        j)
                           )
                             (popVal (p i0) x₀)
                             (popVal (p i1) x₁)))
                ∙  λ i → Σ (PathP (λ i → Recₗ (trim-sig (p i)))
                                  (trim-rec (p i0) (transportRefl x₀ (~ i)))
                                  (trim-rec (p i1) (transportRefl x₁ (~ i))))
                           λ p₁ → PathP (λ j → pop-Type-overRecₗ (p j) (p₁ j))
                                      (popVal (p i0) (transportRefl x₀ (~ i)))
                                      (popVal (p i1) (transportRefl x₁ (~ i)))

       lawNext : Recₗ (push-Type sPrev typeToPush)
                          ≡
                 PathP (λ i → Recₗ (p i)) x₀ x₁
       lawNext =     sym (isoToPath (push-popVal-Iso sNext) )
                  ∙∙ (push-trim-Recₗ {s = sPrev} typeToPush
                     ∙ (λ i → Σ (lawPrev i) (coe0→i (λ i → lawPrev i → Type ℓ) i typeToPush))
                  ∙∙ coe-fix
                  ∙∙ sym (pathPSigma-≡-sigmaPathP))
                  ∙∙
                   λ j → PathP (λ i → pu-po-sq i j)
                          (coe1→i (pu-po-sq i0) j x₀)
                          (coe1→i (pu-po-sq i1) j x₁)

  in sNext , lawNext



-- if we dont yet have records of the ends,
-- we can prepend sigₗ-PathP with its ends, to get the signature
-- containg all the paths and ends

sigₗ-Ends-with-PathP : ∀ {ℓ} → ∀ {n} → (I → Sigₗ ℓ n) → Sigₗ ℓ ((n + n) + n)
sigₗ-Ends-with-PathP x =
  concatSigₗ-dep (concatSigₗ (x i0) (x i1))
    λ x₀₁ →
      let (x₀ , x₁) = Iso.inv (concatSigₗ-rec-Iso (x i0) (x i1)) x₀₁
      in fst (sigₗ-PathP x x₀ x₁)


-- this alternative construction of path with ends signature arranges paths in diferent order
-- putting paths right after coresponnding ends

sigₗ-Ends-with-PathP' : ∀ {ℓ} → ∀ {n} → (I → Sigₗ ℓ n) → Sigₗ ℓ (n * 3)
sigₗ-Ends-with-PathP' {n = 0} x = lift _
sigₗ-Ends-with-PathP' {n = 1} x = (x i0) , (λ x0 → (x i1) , λ x1 → PathP x x0 x1)
sigₗ-Ends-with-PathP' {n = suc (suc n)} x =
              fst (x i0) ,
      λ x0 →  fst (x i1) ,
      λ x1 → PathP (λ i → fst (x i)) x0 x1 ,
      λ p → sigₗ-Ends-with-PathP' λ i → snd (x i) (p i) 


recₗ-Ends-with-PathP'-toPath :
                   ∀ {ℓ} → ∀ {n}
                   → (p : I → Sigₗ ℓ n)
                   → Recₗ (sigₗ-Ends-with-PathP' p)
                   → ∀ i → Recₗ (p i)
recₗ-Ends-with-PathP'-toPath {n = 0} p x i = _
recₗ-Ends-with-PathP'-toPath {n = 1} p x i = snd (snd x) i
recₗ-Ends-with-PathP'-toPath {n = suc (suc n)} p x i =
  (fst (snd (snd x)) i) ,
    (recₗ-Ends-with-PathP'-toPath ((λ i₁ → snd (p i₁) (fst (snd (snd x)) i₁)))
      (snd (snd (snd x)) ) i)

recₗ-Ends-with-PathP'-fromPath : ∀ {ℓ} → ∀ {n} → (p : I → Sigₗ ℓ n)
                 → (∀ i → Recₗ (p i))
                 → Recₗ (sigₗ-Ends-with-PathP' p)
recₗ-Ends-with-PathP'-fromPath {ℓ} {0} p x = _
recₗ-Ends-with-PathP'-fromPath {ℓ} {1} p x = (x i0) , ((x i1) , λ i → x i)
recₗ-Ends-with-PathP'-fromPath {ℓ} {suc (suc n)} p x =
   fst (x i0) , fst (x i1) , (λ i → fst (x i))
   , recₗ-Ends-with-PathP'-fromPath (λ z → snd (p z) (fst (x z))) λ i → snd (x i)


sigₗ-Ends-with-PathP'-Recₗ-Iso' : ∀ {ℓ} → ∀ {n} → (p : I → Sigₗ ℓ n)
                     → Iso
                       (Π (Recₗ ∘ I-rec λ i → p i ))
                       (Recₗ (sigₗ-Ends-with-PathP' λ i → p i))
                       
Iso.fun (sigₗ-Ends-with-PathP'-Recₗ-Iso' p) x =
  recₗ-Ends-with-PathP'-fromPath (λ i → p i) λ i → x (seg i)
Iso.inv (sigₗ-Ends-with-PathP'-Recₗ-Iso' p) x =
  I-elim (Recₗ ∘ I-rec λ i → p i) (λ i → recₗ-Ends-with-PathP'-toPath (λ i → p i) x i)

Iso.rightInv (sigₗ-Ends-with-PathP'-Recₗ-Iso' {n = 0} p) b = refl
Iso.rightInv (sigₗ-Ends-with-PathP'-Recₗ-Iso' {n = 1} p) b = refl
Iso.rightInv (sigₗ-Ends-with-PathP'-Recₗ-Iso' {n = suc (suc n)} p) b i =
  (fst b) , (fst (snd b) , (fst (snd (snd b))) ,
    Iso.rightInv (sigₗ-Ends-with-PathP'-Recₗ-Iso' (λ z → snd (p z) (fst (snd (snd b)) z)))
           ((snd (snd (snd b)))) i)


Iso.leftInv (sigₗ-Ends-with-PathP'-Recₗ-Iso' {n = 0} p) a = refl
Iso.leftInv (sigₗ-Ends-with-PathP'-Recₗ-Iso' {n = 1} p) a = intervalEta a

Iso.leftInv (sigₗ-Ends-with-PathP'-Recₗ-Iso' {n = suc (suc n)} p) a i zero =
  fst (a zero) ,
    Iso.leftInv (sigₗ-Ends-with-PathP'-Recₗ-Iso' (λ z → snd (p z) (fst (a (seg z)))))
     (I-elim (Recₗ ∘ I-rec (λ z → snd (p z) (fst (a (seg z))))) (λ i₁ → snd (a (seg i₁))))
     i zero
     
Iso.leftInv (sigₗ-Ends-with-PathP'-Recₗ-Iso' {n = suc (suc n)} p) a i one =
    fst (a one) ,
    Iso.leftInv (sigₗ-Ends-with-PathP'-Recₗ-Iso' (λ z → snd (p z) (fst (a (seg z)))))
     (I-elim (Recₗ ∘ I-rec (λ z → snd (p z) (fst (a (seg z))))) (λ i₁ → snd (a (seg i₁))))
     i one

Iso.leftInv (sigₗ-Ends-with-PathP'-Recₗ-Iso' {n = suc (suc n)} p) a i (seg i₁) =
   (fst (a (seg i₁))) ,
       Iso.leftInv (sigₗ-Ends-with-PathP'-Recₗ-Iso' (λ z → snd (p z) (fst (a (seg z)))))
     (I-elim (Recₗ ∘ I-rec (λ z → snd (p z) (fst (a (seg z))))) (λ i₁ → snd (a (seg i₁))))
     i (seg i₁)



sigₗ-Ends-with-PathP'-Iso-Interval : ∀ {ℓ} → ∀ {n} → (p : Interval → Sigₗ ℓ n)
                     → Iso
                       (Π (Recₗ ∘ p ))
                       (Recₗ (sigₗ-Ends-with-PathP' λ i → p (seg i)))
sigₗ-Ends-with-PathP'-Iso-Interval p = 
  compIso (pathToIso ( λ i → Π (Recₗ ∘ (intervalEta-rec  p) (~ i))) )
             (sigₗ-Ends-with-PathP'-Recₗ-Iso' λ i → p (seg i))


-- sigₗ-Ends-with-PathP-Iso : ∀ {ℓ} → ∀ {n} → (p : I → Sigₗ ℓ n) →
--                             Recₗ (sigₗ-Ends-with-PathP p)
--                              ≡
--                             Recₗ (sigₗ-Ends-with-PathP' p) 
-- sigₗ-Ends-with-PathP-Iso = {!!}




--------

-- SigSigᵣ : ∀ ℓ → ∀ n → Σ[ s ∈ Sigᵣ (ℓ-suc ℓ) n ] (Iso (Recᵣ s) (Sigᵣ ℓ n))  
-- SigSigᵣ ℓ zero = _ , idIso
-- SigSigᵣ ℓ (suc zero) = Type ℓ , idIso 
-- SigSigᵣ ℓ (suc (suc zero)) = (Type ℓ , λ x → x → Type ℓ) , idIso
-- SigSigᵣ ℓ (suc (suc (suc n))) =
--    let (s , iso to from ri li) = SigSigᵣ ℓ (suc (suc n))
--    in (s , λ x → Recᵣ (to x) → Type ℓ) ,
--        iso ((λ x → (to (fst x)) , snd x) )
--                (λ x → (from (fst x)) , λ x₁ → snd x (subst Recᵣ (ri (fst x)) x₁))
--             (λ b i → ri (fst b) i ,
--                λ x → snd b (coei→1 (λ i → Σ (Recᵣ (fst (ri (fst b) i))) (snd (ri (fst b) i))) i x) )
--                λ a i → {!!}

-- -- SigSigₗ : ∀ ℓ → ∀ n → Σ[ s ∈ Sigₗ (ℓ-suc ℓ) n ] (Recₗ s → Sigₗ ℓ n)  
-- -- SigSigₗ ℓ zero = _ , (idfun _)
-- -- SigSigₗ ℓ (suc zero) = Type ℓ , idfun _ 
-- -- SigSigₗ ℓ (suc (suc zero)) = (Type ℓ , λ x → x → Type ℓ) , idfun _
-- -- SigSigₗ ℓ (suc (suc (suc n))) =
-- --    let (s , to) = SigSigₗ ℓ (suc (suc n))
-- --        nextS = push-Type s (λ x → Recₗ ((to x)) → Type ℓ )
-- --    in nextS ,
-- --       λ x → let ww = Iso.inv (push-popVal-Iso nextS) x  
-- --                 z = (transport (push-trim-Recₗ {s = s} (λ x → Recₗ (to x) → Type ℓ )) ww)
-- --             in push-Type (to (fst z)) λ x₁ → (snd z x₁)

-- SigSigₗ : ∀ ℓ → ∀ n → Σ[ s ∈ Sigₗ (ℓ-suc ℓ) n ] (Iso (Recₗ s) (Sigₗ ℓ n))  
-- SigSigₗ ℓ zero = _ , idIso
-- SigSigₗ ℓ (suc zero) = Type ℓ , idIso 
-- SigSigₗ ℓ (suc (suc zero)) = (Type ℓ , λ x → x → Type ℓ) , idIso
-- SigSigₗ ℓ (suc (suc (suc n))) =
--    let (s , iso to from li ri ) = SigSigₗ ℓ (suc (suc n))
--        nextS = push-Type s (λ x → Recₗ ((to x)) → Type ℓ )
--    in nextS ,
--       iso (λ x → let ww = Iso.inv (push-popVal-Iso nextS) x  
--                      z = (transport (push-trim-Recₗ {s = s} (λ x → Recₗ (to x) → Type ℓ )) ww)
--                  in push-Type (to (fst z)) λ x₁ → (snd z x₁))
--            (λ x → let zz : {!!}
--                       zz = {!!}
--                       in pushVal nextS {!!} {!!})
--            {!!}
--            {!!}


-------------


-- Sigₗ : ∀ ℓ → ℕ → Type (ℓ-suc ℓ)
-- Sigₗ ℓ 0 = Lift Unit
-- Sigₗ ℓ 1 = Type ℓ
-- Sigₗ ℓ (suc (suc n)) = Σ[ Ty ∈ Type ℓ ]  (Ty → Sigₗ ℓ (suc n))

-- Recₗ : ∀ {ℓ} → ∀ {n} → Sigₗ ℓ n → Type ℓ
-- Recₗ {n = 0} _ = Lift Unit
-- Recₗ {n = 1} x = x
-- Recₗ {n = suc (suc n)} x = Σ (fst x) (Recₗ ∘ snd x)


-- Sigᵣ : ∀ ℓ → ℕ → Type (ℓ-suc ℓ)

-- Recᵣ : ∀ {ℓ} → ∀ {n} → Sigᵣ ℓ n → Type ℓ


-- Sigᵣ ℓ 0 = Lift Unit
-- Sigᵣ ℓ 1 = Type ℓ
-- Sigᵣ ℓ (suc (suc n)) = Σ (Sigᵣ ℓ (suc n)) (λ x → Recᵣ x → Type ℓ)

-- Recᵣ {ℓ} {0} x = Lift Unit
-- Recᵣ {ℓ} {1} x = x
-- Recᵣ {ℓ} {suc (suc n)} x = Σ (Recᵣ (fst x)) (snd x)


-- SR : ∀ ℓ → ∀ n → Vec Interval n → Σ (Type (ℓ-suc ℓ)) λ x → x → Type ℓ

-- SR-law : ∀ ℓ → ∀ n → (v : Vec Interval (suc n)) →
--           Σ (Iso (Σ-syntax (Type ℓ) (λ Ty → Ty → fst (SR ℓ (suc n) v)))
--                (Σ (fst (SR ℓ (suc n) v)) (λ x → snd (SR ℓ (suc n) v) x → Type ℓ)))
--             λ qq → (a : Σ (fst (SR ℓ (suc n) v)) (λ x → (snd (SR ℓ (suc n) v)) x → Type ℓ))
--                         → Iso
--                         (transport (λ i₁ → isoToPath qq i₁ → Type ℓ)
--                          (λ x → Σ (fst x) (λ x₁ → snd (SR ℓ (suc n) v) (snd x x₁))) a)
--                         (Σ (snd (SR ℓ (suc n) v) (fst a)) (snd a))

-- SR ℓ zero _ = Lift Unit , λ _ → Lift Unit
-- SR ℓ (suc zero) _ = Type ℓ , λ x₂ → x₂
-- SR ℓ (suc (suc n)) (zero ∷ v) =
--   (Σ[ Ty ∈ Type ℓ ]  (Ty → fst (SR ℓ (suc n) v)))
--   , λ x → Σ (fst x) (snd (SR ℓ (suc n) v) ∘ snd x) 
-- SR ℓ (suc (suc n)) (one ∷ v) =
--   Σ (fst (SR ℓ (suc n) v)) (λ x → (snd (SR ℓ (suc n) v)) x → Type ℓ)
--   , λ x → Σ ((snd  (SR ℓ (suc n) v) (fst x))) (snd x) 
-- SR ℓ (suc (suc n)) (seg i ∷ v) =
--   sigmaPath→pathSigma
--     ( ((Σ[ Ty ∈ Type ℓ ]  (Ty → fst (SR ℓ (suc n) v)))
--       , λ x → Σ (fst x) (snd (SR ℓ (suc n) v) ∘ snd x)) )
--       ( Σ (fst (SR ℓ (suc n) v)) (λ x → (snd (SR ℓ (suc n) v)) x → Type ℓ)
--   , λ x → Σ ((snd  (SR ℓ (suc n) v) (fst x))) (snd x) )
--       (isoToPath qq , funExt λ x → isoToPath (zz x)) i

--   where

--     qq : Iso (Σ-syntax (Type ℓ) (λ Ty → Ty → fst (SR ℓ (suc n) v)))
--            (Σ (fst (SR ℓ (suc n) v)) (λ x → snd (SR ℓ (suc n) v) x → Type ℓ))
--     qq = fst (SR-law ℓ n v)

--     zz : (a : Σ (fst (SR ℓ (suc n) v)) (λ x → (snd (SR ℓ (suc n) v)) x → Type ℓ))
--           → Iso
--               (transport (λ i₁ → isoToPath qq i₁ → Type ℓ)
--                (λ x → Σ (fst x) (λ x₁ → snd (SR ℓ (suc n) v) (snd x x₁))) a)
--               (Σ (snd (SR ℓ (suc n) v) (fst a)) (snd a))
--     zz = snd (SR-law ℓ n v)

-- fst (SR-law ℓ zero v) = idIso
-- Iso.fun (snd (SR-law ℓ zero v) a) x = fst x , subst (snd a) {!!} (snd x) 
-- Iso.inv (snd (SR-law ℓ zero v) a) = {!!}
-- Iso.rightInv (snd (SR-law ℓ zero v) a) = {!!}
-- Iso.leftInv (snd (SR-law ℓ zero v) a) = {!!}

-- SR-law ℓ (suc n) v = {!!}


-- SR : ∀ ℓ → ∀ n → Vec Interval n → Σ (Type (ℓ-suc ℓ)) λ x → x → Type ℓ

-- SR-law : ∀ ℓ → ∀ n → (v : Vec Interval (suc n))
--              → Σ (Σ-syntax (Type ℓ) (λ Ty → Ty → fst (SR ℓ (suc n) v)) ≡
--                    Σ (fst (SR ℓ (suc n) v)) (λ x → snd (SR ℓ (suc n) v) x → Type ℓ))
--                   λ p → _

-- SR ℓ zero _ = Lift Unit , λ _ → Lift Unit
-- SR ℓ (suc zero) _ = Type ℓ , λ x₂ → x₂
-- SR ℓ (suc (suc n)) (zero ∷ v) =
--   (Σ[ Ty ∈ Type ℓ ]  (Ty → fst (SR ℓ (suc n) v)))
--   , λ x → Σ (fst x) (snd (SR ℓ (suc n) v) ∘ snd x) 
-- SR ℓ (suc (suc n)) (one ∷ v) =
--   Σ (fst (SR ℓ (suc n) v)) (λ x → (snd (SR ℓ (suc n) v)) x → Type ℓ)
--   , λ x → Σ ((snd  (SR ℓ (suc n) v) (fst x))) (snd x) 
-- SR ℓ (suc (suc n)) (seg i ∷ v) =
--   sigmaPath→pathSigma
--     ( ((Σ[ Ty ∈ Type ℓ ]  (Ty → fst (SR ℓ (suc n) v)))
--       , λ x → Σ (fst x) (snd (SR ℓ (suc n) v) ∘ snd x)) )
--       ( Σ (fst (SR ℓ (suc n) v)) (λ x → (snd (SR ℓ (suc n) v)) x → Type ℓ)
--   , λ x → Σ ((snd  (SR ℓ (suc n) v) (fst x))) (snd x) )
--       (SR-law ℓ n v) i


-- SR-law ℓ zero v = {!!}
-- SR-law ℓ (suc n) v = {!!}

SR : ∀ ℓ → ∀ n → Vec Interval n → Σ (Type (ℓ-suc ℓ)) λ x → x → Type ℓ

SR-law : ∀ ℓ → ∀ n → (v : Vec Interval (suc n))
             → (Σ-syntax (Type ℓ) (λ Ty → Ty → fst (SR ℓ (suc n) v)) ,
                 (λ x → Σ (fst x) (λ x₁ → snd (SR ℓ (suc n) v) (snd x x₁)))) ≡
               (Σ (fst (SR ℓ (suc n) v))
                  (λ x → snd (SR ℓ (suc n) v) x → Type ℓ) ,
                      λ x → Σ (snd (SR ℓ (suc n) v) (fst x)) (snd x))

SR ℓ zero _ = Lift Unit , λ _ → Lift Unit
SR ℓ (suc zero) _ = Type ℓ , λ x₂ → x₂
SR ℓ (suc (suc n)) (zero ∷ v) =
  (Σ[ Ty ∈ Type ℓ ]  (Ty → fst (SR ℓ (suc n) v)))
  , λ x → Σ (fst x) (snd (SR ℓ (suc n) v) ∘ snd x) 
SR ℓ (suc (suc n)) (one ∷ v) =
  Σ (fst (SR ℓ (suc n) v)) (λ x → (snd (SR ℓ (suc n) v)) x → Type ℓ)
  , λ x → Σ ((snd  (SR ℓ (suc n) v) (fst x))) (snd x) 
SR ℓ (suc (suc n)) (seg i ∷ v) = SR-law ℓ n v i


SR-law ℓ zero v = refl
SR-law ℓ (suc n) v =
   {!!}
