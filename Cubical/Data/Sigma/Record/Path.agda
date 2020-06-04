{-# OPTIONS --cubical --safe #-}
module Cubical.Data.Sigma.Record.Path where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

open import Cubical.Data.List
open import Cubical.Data.Bool
open import Cubical.Data.Sigma

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
-- putting coresponding paths right after coresponnding ends

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












