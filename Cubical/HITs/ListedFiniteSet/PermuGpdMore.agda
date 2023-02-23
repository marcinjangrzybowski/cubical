{-# OPTIONS --safe  #-}  --experimental-lossy-unification
module Cubical.HITs.ListedFiniteSet.PermuGpdMore where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)
open import Cubical.Data.Nat as ℕ

open import Cubical.Data.Nat.Order.Recursive as OR

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Bool

open import Cubical.Data.List

open import Cubical.Functions.Logic as Lo
open import Cubical.Foundations.Function

open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Functions.Involution

open import Cubical.Foundations.Equiv.PathSplit

open import Cubical.Foundations.Path

open import Cubical.Foundations.Structure

open import Cubical.Data.Maybe as Mb

open import Cubical.HITs.EilenbergMacLane1

open import Cubical.HITs.ListedFiniteSet.Base2

open import Cubical.Data.Nat.FinGenAut as A

import Cubical.Data.Nat.Order.Permutation as P

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Algebra.SymmetricGroup

open import Cubical.HITs.EilenbergMacLane1 as  EM

open import Cubical.HITs.ListedFiniteSet.Sum

open import Cubical.HITs.ListedFiniteSet.PermuGpd



toP𝔾 : ?
toP𝔾 = ?

Perm' : {!!}
Perm' = {!!}

-- PGiso : Iso Perm₂ (Σ ℕ (EM₁ ∘ P.PermG ))
-- Iso.fun PGiso x = _ , toPG' x
-- Iso.inv PGiso = uncurry fromPG'
-- Iso.rightInv PGiso = ? --PGsec
-- Iso.leftInv PGiso = ? --PGret




-- -- -- PGiso : Iso Perm₂ (Σ ℕ (EM₁ ∘ P.PermG ))
-- -- -- Iso.fun PGiso x = _ , toPG' x
-- -- -- Iso.inv PGiso = uncurry fromPG'
-- -- -- Iso.rightInv PGiso = PGsec
-- -- -- Iso.leftInv PGiso = PGret


-- -- adjTranspositionMb : ∀ n → (k : Σ ℕ (λ k → suc k < n)) → Fin₂' n ≃ Fin₂' n
-- -- adjTranspositionMb (suc (suc n)) (zero , k<) = swap0and1M (hFin₂ (nPerm₂ n))
-- -- adjTranspositionMb (suc (suc n)) (suc k , k<) =
-- --   congMaybeEquiv (adjTranspositionMb (suc n) (k , k<))
-- -- -- adjTransposition zero = swap0and1≃
-- -- -- adjTransposition (suc k) = sucPerm (adjTransposition k)


-- -- -- invoTo≃ : ∀ n → (k : Σ ℕ (λ k → suc k < n)) → (x : Fin₂ (nPerm₂ n) ≃ Fin₂ (nPerm₂ n)) →
-- -- --       adjTranspositionMb n k ∙ₑ adjTranspositionMb n k ∙ₑ x ≡ x
-- -- -- invoTo≃ (suc (suc n)) (zero , snd₁) x = equivEq ( (funExt (Mb.elim _ refl
-- -- --    (Mb.elim _ refl λ _ → refl))))
-- -- -- invoTo≃ (suc (suc (suc n))) (suc k , snd₁) x = {!!}
-- -- -- -- equivEq (funExt (Mb.elim _ refl
-- -- -- --   {!(invoTo≃ (suc n) (k , snd₁)) (congMaybeEquiv x)!}))
-- -- -- -- -- 

-- -- -- PGto≃ : ∀ n → P.Perm n →
-- -- --        (Fin₂ (nPerm₂ n)) ≃ (Fin₂ (nPerm₂ n)) 
-- -- -- PGto≃ n = P.Rrec.f w

-- -- --   where
-- -- --     w : P.Rrec (Fin₂ (nPerm₂ n) ≃ Fin₂ (nPerm₂ n))
-- -- --     P.Rrec.isSetA w = isOfHLevel≃ 2 (isSetFin₂ (nPerm₂ n)) (isSetFin₂ (nPerm₂ n))
-- -- --     P.Rrec.εA w = idEquiv _
-- -- --     P.Rrec.∷A w k = adjTranspositionMb n k ∙ₑ_
-- -- --     P.Rrec.invoA w k = {!!}
-- -- --     P.Rrec.braidA w = {!!}
-- -- --     P.Rrec.commA w = {!!}

-- -- -- PGfrom≃ : {!!}
-- -- -- PGfrom≃ = {!!}

-- -- toFin'' : ∀ n → Fin n → Fin'' n
-- -- toFin'' (suc n) (zero , _) = nothing
-- -- toFin'' (suc n) (suc k , k<) = just (toFin'' n (k , k<))

-- -- fromFin'' : ∀ n → Fin'' n → Fin n
-- -- fromFin'' (suc n) nothing = zero , _
-- -- fromFin'' (suc n) (just x) = P.sucF (fromFin'' n x)

-- -- IsoFin'' : ∀ n → Iso (Fin'' n) (Fin n)
-- -- Iso.fun (IsoFin'' n) = fromFin'' n
-- -- Iso.inv (IsoFin'' n) = toFin'' n
-- -- Iso.rightInv (IsoFin'' (suc n)) (zero , snd₁) = refl
-- -- Iso.rightInv (IsoFin'' (suc n)) (suc fst₁ , snd₁) =
-- --   cong P.sucF ((Iso.rightInv (IsoFin'' n) _))
-- -- Iso.leftInv (IsoFin'' (suc n)) nothing = refl
-- -- Iso.leftInv (IsoFin'' (suc n)) (just x) = cong just (Iso.leftInv (IsoFin'' n) _)

-- -- PermGIso : ∀ n → GroupIso (P.PermG n) (Symmetric-Group _ (isSetFin₂ (nPerm₂ n)))
-- -- PermGIso = {!!}
-- -- -- Iso.fun (fst (PermGIso n)) = {!!} 
-- -- -- Iso.inv (fst (PermGIso n)) = {!!}
-- -- -- Iso.rightInv (fst (PermGIso n)) = {!!}
-- -- -- Iso.leftInv (fst (PermGIso n)) = {!!}
-- -- -- snd (PermGIso n) = {!!}


-- -- -- -- PermGIsoCommK : ∀ n k → Iso.inv (fst (PermGIso n))
-- -- -- --    (pathToEquiv (cong Fin₂ (commK n k))) ≡ P.η k 
-- -- -- -- PermGIsoCommK = {!!}


-- -- sym-emloopK : ∀ n k → (emloop {Group = (P.PermG n)} (P.η k))
-- --                  ≡ sym (emloop {Group = (P.PermG n)} (P.η k))
                      
-- -- sym-emloopK n k = emloop-sym (P.PermG n) (P.η k)


-- -- secCong' : ∀ n → (x y : EM₁ (P.PermG n)) →
-- --     hasSection (cong {x = x} {y = y} (fromPG' n))
-- -- secCong' n = {!!}

-- --   where
-- --     module iso = Iso (fst (PermGIso n))
-- --     open IsGroupHom (snd (PermGIso n))


-- --     secCong'BB : hasSection (cong {x = embase} {y = embase} (fromPG' n))  
-- --     fst secCong'BB p = emloop (iso.inv (pathToEquiv (cong Fin₂ p)))
-- --     snd secCong'BB p = {!!}

-- --     sBL : (g : P.Perm n) → PathP
-- --       (λ z →
-- --          fromPG' n (emloop g z) ≡ fromPG' n embase → emloop {Group =  P.PermG n} g z ≡ embase)
-- --       (fst secCong'BB) (fst secCong'BB)
-- --     sBL = {!!}

-- --     secCong'BL : (g : P.Perm n) →
-- --       PathP (λ i → hasSection (cong {x = emloop g i} {y = embase} (fromPG' n)))
-- --          secCong'BB
-- --          secCong'BB   
-- --     secCong'BL g = ΣPathPProp
-- --       (λ a → isPropΠ λ x → trunc _ _ _ _)
-- --         {!!}


-- -- -- secCongF : ∀ n → (x y : EM₁ (P.PermG n)) →
-- -- --     (EMrec.f (fromPG'R n) x ≡ EMrec.f (fromPG'R n) y → x ≡ y)
-- -- -- secCongF n = EMelimSet.f w
-- -- --   where

-- -- --     module iso = Iso (fst (PermGIso n))
-- -- --     open IsGroupHom (snd (PermGIso n))


-- -- --     w : EMelimSet (P.PermG n)
-- -- --           (λ z →
-- -- --              (y : EM₁ (P.PermG n)) →
-- -- --              EMrec.f (fromPG'R n) z ≡ EMrec.f (fromPG'R n) y → z ≡ y)
-- -- --     EMelimSet.isSetB w _ = isSetΠ2 λ _ _ → emsquash _ _
-- -- --     EMelimSet.b w = EMelimSet.f ww
-- -- --       where
-- -- --         ww : EMelimSet (P.PermG n)
-- -- --                (λ z →
-- -- --                   EMrec.f (fromPG'R n) embase
-- -- --                     ≡ EMrec.f (fromPG'R n) z → embase ≡ z)
-- -- --         EMelimSet.isSetB ww _ = isSetΠ λ _ → emsquash _ _
-- -- --         EMelimSet.b ww x =
-- -- --            emloop (iso.inv (pathToEquiv (cong Fin₂ x)))
-- -- --         EMelimSet.bPathP ww = P.RelimProp.f www
-- -- --           where


-- -- --             qqq : ∀ xs k →
-- -- --              PathP
-- -- --               (λ i → nPerm₂ n ≡ P.Rrec.f (fromPG≡ n) xs i → embase ≡ emloop xs i)
-- -- --               (λ x → emloop (iso.inv (pathToEquiv (λ i → Fin₂ (x i)))))
-- -- --               (λ x → emloop (iso.inv (pathToEquiv (λ i → Fin₂ (x i))))) →
-- -- --               PathP
-- -- --               (λ i →
-- -- --                  iter n (_∷2_ tt) [] ≡
-- -- --                  hcomp
-- -- --                  (doubleComp-faces (λ _ → iter n (_∷2_ tt) [])
-- -- --                   (P.Rrec.f (fromPG≡ n) xs) i)
-- -- --                  (commK n k i) →
-- -- --                  Path (EM₁ (P.PermG n)) embase (emloop (k P.∷ xs) i))
-- -- --               (λ x →
-- -- --                  emloop
-- -- --                  (Iso.inv (fst (PermGIso n))
-- -- --                   (pathToEquiv (λ i → fst (RRec.f Fin₂R (x i))))))
-- -- --               (λ x →
-- -- --                  emloop
-- -- --                  (Iso.inv (fst (PermGIso n))
-- -- --                   (pathToEquiv (λ i → fst (RRec.f Fin₂R (x i))))))
-- -- --             qqq xs k s = funExtDep qw
-- -- --               -- λ {x₀} {x₁} p → {!s' {x₀} {x₁}!} 

-- -- --               where
-- -- --                 s' : _
-- -- --                 s' = funExtDep⁻ s

-- -- --                 qw : {x₀ : iter n (_∷2_ tt) [] ≡ iter n (_∷2_ tt) []}
-- -- --                       {x₁ : iter n (_∷2_ tt) [] ≡ nPerm₂ n}
-- -- --                       (p
-- -- --                        : PathP
-- -- --                          (λ z →
-- -- --                             iter n (_∷2_ tt) [] ≡
-- -- --                             hcomp
-- -- --                             (doubleComp-faces (λ _ → iter n (_∷2_ tt) [])
-- -- --                              (P.Rrec.f (fromPG≡ n) xs) z)
-- -- --                             (commK n k z))
-- -- --                          x₀ x₁) →
-- -- --                           Square
-- -- --                             ((emloop {Group = P.PermG n}
-- -- --                               (iso.inv (pathToEquiv
-- -- --                                 (λ i → fst (RRec.f Fin₂R (x₀ i)))))))
-- -- --                             ((emloop
-- -- --                               (iso.inv (pathToEquiv
-- -- --                                 (λ i → fst (RRec.f Fin₂R (x₁ i)))))))
-- -- --                             refl
-- -- --                             (emloop (k P.∷ xs))

-- -- --                 qw {x₀} {x₁} p =
-- -- --                     flipSquare ((flipSquare s*)
-- -- --                       ▷ sym (emloop-comp (P.PermG n) (P.η k) xs))

-- -- --                   where

-- -- --                     p′ : Square
-- -- --                            x₀
-- -- --                            x₁
-- -- --                            (λ i → iter n (_∷2_ tt) [])
-- -- --                            ((λ i → commK n k i) ∙ (P.Rrec.f (fromPG≡ n) xs))
-- -- --                     p′ = p
 
-- -- --                     p* : Square
-- -- --                            (x₀ ∙ commK n k)
-- -- --                            x₁
-- -- --                            (λ i → iter n (_∷2_ tt) [])
-- -- --                            (P.Rrec.f (fromPG≡ n) xs)
-- -- --                     p* i j =
-- -- --                       hcomp
-- -- --                         (λ k' → λ {
-- -- --                            (i = i1) → p i j
-- -- --                           ;(j = i0) → p i j
-- -- --                           ;(j = i1) → compPath-filler' (commK n k)
-- -- --                               (P.Rrec.f (fromPG≡ n) xs) (~ k') i
-- -- --                           })
-- -- --                         (p i j)

-- -- --                     s'app :
-- -- --                       Square x₀ x₁ refl (P.Rrec.f (fromPG≡ n) xs) → 
-- -- --                              Square
-- -- --                                (emloop (iso.inv (pathToEquiv (λ i → Fin₂ (x₀ i)))))
-- -- --                                (emloop (iso.inv (pathToEquiv (λ i → Fin₂ (x₁ i)))))
-- -- --                                refl
-- -- --                                λ i → emloop xs i
-- -- --                     s'app = s' {x₀} {x₁}



-- -- --                     s'app* : 
-- -- --                              Square
-- -- --                                (emloop (iso.inv (pathToEquiv
-- -- --                                   (λ i → Fin₂ ((x₀ ∙ commK n k) i)))))
-- -- --                                (emloop (iso.inv (pathToEquiv (λ i → Fin₂ (x₁ i)))))
-- -- --                                refl
-- -- --                                (emloop xs)
-- -- --                     s'app* = s' {x₀ ∙ commK n k} {x₁} p*

-- -- --                     s*i0i0 :  (iso.inv
-- -- --                                  (pathToEquiv (cong Fin₂ x₀))
-- -- --                                    P.· iso.inv (pathToEquiv (cong Fin₂ (commK n k)))) 
-- -- --                                ≡ (((iso.inv (pathToEquiv
-- -- --                                   (λ i → Fin₂ ((x₀ ∙ commK n k) i))))))
-- -- --                     s*i0i0 k' = {!!}

-- -- --                     s*i0 : Square
-- -- --                               ((emloop (iso.inv (pathToEquiv
-- -- --                                   (λ i → Fin₂ ((x₀ ∙ commK n k) i))))))
-- -- --                               (emloop (iso.inv (pathToEquiv (λ i → Fin₂ (x₀ i)))))
-- -- --                               refl
-- -- --                               (sym (emloop (P.η k)))
-- -- --                     s*i0 i j = hcomp (λ k' → λ {
-- -- --                          (i = i0) → emloop (s*i0i0 k') j
-- -- --                        ; (i = i1) → 
-- -- --                            (emloop (iso.inv (pathToEquiv (λ i → Fin₂ (x₀ i))))) j
-- -- --                        ; (j = i0) → embase
-- -- --                        ; (j = i1) → emloop-sym (P.PermG n) (P.η k) k' i
-- -- --                         })

-- -- --                       (emcomp (iso.inv (pathToEquiv (λ i → Fin₂ (x₀ i))))
-- -- --                        (P.η k) i j   )


-- -- --                     s* : Square
-- -- --                            (emloop (iso.inv (pathToEquiv (λ i → Fin₂ (x₀ i)))))
-- -- --                            (emloop (iso.inv (pathToEquiv (λ i → Fin₂ (x₁ i)))))
-- -- --                            refl
-- -- --                            (emloop (P.η k) ∙ emloop xs)
                           
-- -- --                     s* i j = hcomp (λ k' → λ {
-- -- --                          (i = i0) → s*i0 k' j
-- -- --                        ; (i = i1) → (s'app* i j)
-- -- --                        ; (j = i0) → (s'app* i j)
-- -- --                        ; (j = i1) → compPath-filler'
-- -- --                           (emloop (P.η k)) (emloop xs) k' i
-- -- --                         }) (s'app* i j)

-- -- --             www : P.RelimProp
-- -- --                     (λ z →
-- -- --                        PathP
-- -- --                        (λ i →
-- -- --                           EMrec.f (fromPG'R n) embase
-- -- --                         ≡ EMrec.f (fromPG'R n) (emloop z i) →
-- -- --                           embase ≡ emloop z i)
-- -- --                        (EMelimSet.b ww) (EMelimSet.b ww))
-- -- --             P.RelimProp.isPropA www _ = {!!}
-- -- --             P.RelimProp.εA www i x i₁ =
-- -- --               hcomp (λ k → λ {
-- -- --                  (i = i0) →
-- -- --                     emloop (iso.inv (pathToEquiv (λ i₂ → Fin₂ (x i₂)))) i₁
-- -- --                  ;(i = i1) →
-- -- --                     emloop (iso.inv (pathToEquiv (λ i₂ → Fin₂ (x i₂)))) i₁
-- -- --                  ;(i₁ = i0) → embase
-- -- --                  ;(i₁ = i1) → emloop-1g (P.Perm n , snd (P.PermG n)) (~ k) i
-- -- --                  }) (emloop (iso.inv (pathToEquiv (λ i₂ → Fin₂ (x i₂)))) i₁)
-- -- --             P.RelimProp.∷A www k {xs} = qqq xs k

-- -- --     EMelimSet.bPathP w = {!!}
-- -- --      -- P.RelimProp.f ww

-- -- --      --  where
-- -- --      --    ww : P.RelimProp
-- -- --      --           (λ z →
-- -- --      --              PathP
-- -- --      --              (λ i →
-- -- --      --                 (y : EM₁ (P.PermG n)) →
-- -- --      --                 EMrec.f (fromPG'R n) (emloop z i) ≡ EMrec.f (fromPG'R n) y →
-- -- --      --                 emloop z i ≡ y)
-- -- --      --              (EMelimSet.b w) (EMelimSet.b w))
-- -- --      --    P.RelimProp.isPropA ww = {!!}
-- -- --      --    P.RelimProp.εA ww = funExt λ x → funExt λ x₁ →
-- -- --      --       flipSquare (emloop-1g (P.Perm n , snd (P.PermG n)) ◁
-- -- --      --          flipSquare (refl {x = EMelimSet.b w x x₁}))
-- -- --      --    P.RelimProp.∷A ww k {xs} X = funExt (EMelimProp.f wwz)
-- -- --      --      where
-- -- --      --       wwz : EMelimProp (P.PermG n)
-- -- --      --               (λ z →
-- -- --      --                  PathP
-- -- --      --                  (λ z₁ →
-- -- --      --                     EMrec.f (fromPG'R n) (emloop (k P.∷ xs) z₁) ≡
-- -- --      --                     EMrec.f (fromPG'R n) z →
-- -- --      --                     emloop (k P.∷ xs) z₁ ≡ z)
-- -- --      --                  (EMelimSet.b w z) (EMelimSet.b w z))
-- -- --      --       EMelimProp.isPropB wwz = {!!}
-- -- --      --       EMelimProp.b wwz = {!!}
-- -- --      --         --  funExtDep qq

-- -- --              -- where

-- -- --              --  qq : {x₀ x₁ : nPerm₂ n ≡ nPerm₂ n}
-- -- --              --       (p
-- -- --              --        : PathP (λ z → (commK n k ∙ P.Rrec.f (fromPG≡ n) xs) z ≡ nPerm₂ n)
-- -- --              --          x₀ x₁) →
-- -- --              --       Square
-- -- --              --         ((emloop (iso.inv (pathToEquiv (λ i → Fin₂ (x₀ i))))))
-- -- --              --         ((emloop (iso.inv (pathToEquiv (λ i → Fin₂ (x₁ i))))))
-- -- --              --         (emloop (k P.∷ xs))
-- -- --              --         refl
                   
-- -- --              --       -- PathP (λ i → emloop (k P.∷ xs) i ≡ embase)
-- -- --              --       -- (emloop (iso.inv (pathToEquiv (λ i → Fin₂ (x₀ i)))))
-- -- --              --       -- (emloop (iso.inv (pathToEquiv (λ i → Fin₂ (x₁ i)))))
-- -- --              --  qq {x₀} {x₁} p =
-- -- --              --     flipSquare (
-- -- --              --       (emloop-comp (P.PermG n) (P.η k) xs)
-- -- --              --         ◁ flipSquare qqOk)

-- -- --              --    where
-- -- --              --      p′ : Square
-- -- --              --            x₀
-- -- --              --            x₁
-- -- --              --            (commK n k ∙ P.Rrec.f (fromPG≡ n) xs)
-- -- --              --            refl
-- -- --              --      p′ = p


-- -- --              --      zz : Square
-- -- --              --             x₀
-- -- --              --             x₁
-- -- --              --             (λ i → P.Rrec.f (fromPG≡ n) xs i)
-- -- --              --             refl
-- -- --              --              →
-- -- --              --             Square
-- -- --              --             (EMelimSet.b w embase x₀)
-- -- --              --             (EMelimSet.b w embase x₁)
-- -- --              --             (emloop xs)
-- -- --              --             refl

-- -- --              --      zz = funExtDep⁻ (funExt⁻ X embase) {x₀} {x₁}

-- -- --              --      zzApp : Square
-- -- --              --           (EMelimSet.b w embase (x₀ ∙ commK n k))
-- -- --              --           (EMelimSet.b w embase x₁)
-- -- --              --           (emloop xs)
-- -- --              --           refl
-- -- --              --      zzApp = funExtDep⁻ (funExt⁻ X embase) {x₀ ∙ commK n k} {x₁}
-- -- --              --       {!!}

-- -- --              --      qqOk : Square
-- -- --              --               (EMelimSet.b w embase x₀)
-- -- --              --               (EMelimSet.b w embase x₁)
-- -- --              --               (emloop (P.η k) ∙ emloop xs)
-- -- --              --               refl
                           
-- -- --              --      qqOk = {!!}

-- -- -- sec* : ∀ n → section (cong (fromPG' n)) (secCongF n embase embase)
-- -- -- sec* n b = ww

-- -- --   where
-- -- --     ww : Square (cong (fromPG' n) (secCongF n embase embase b))
-- -- --            b refl refl
-- -- --     ww = {!!}


-- -- -- secCong' : ∀ n → (x y : EM₁ (P.PermG n)) →
-- -- --     hasSection (cong {x = x} {y = y} (fromPG' n))
-- -- -- fst (secCong' n x y) = secCongF n x y
-- -- -- snd (secCong' n x y) = {!!}

-- -- -- PG≃PS : isPathSplitEquiv (uncurry fromPG')
-- -- -- isPathSplitEquiv.sec PG≃PS = (λ x → _ , toPG' x) , PGret
-- -- -- isPathSplitEquiv.secCong PG≃PS = {!!}
   


-- -- -- -- -- module _ {ℓ} {A : Type ℓ} where 

-- -- -- -- --   toPerm₂ : FMSet2 A → Perm₂
-- -- -- -- --   toPerm₂ [] = []
-- -- -- -- --   toPerm₂ (x ∷2 x₁) = (_ ∷2 toPerm₂ x₁)
-- -- -- -- --   toPerm₂ (comm x y x₁ i) = (comm _ _ (toPerm₂ x₁) i)
-- -- -- -- --   toPerm₂ (comm-inv x y x₁ i i₁) = (comm-inv _ _ (toPerm₂ x₁) i i₁)
-- -- -- -- --   toPerm₂ (hexDiag x y z x₁ i) = (hexDiag _ _ _ (toPerm₂ x₁) i)
-- -- -- -- --   toPerm₂ (hexU x y z x₁ i i₁) = (hexU _ _ _ (toPerm₂ x₁) i i₁)
-- -- -- -- --   toPerm₂ (hexL x y z x₁ i i₁) = (hexL _ _ _ (toPerm₂ x₁) i i₁)
-- -- -- -- --   toPerm₂ (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) =
-- -- -- -- --     (trunc _ _ _ _
-- -- -- -- --      (λ i j → toPerm₂ (x₃ i j)) ((λ i j → toPerm₂ (y₁ i j))) i i₁ x₄)


-- -- -- -- -- -- module _ {ℓ} (A : Type ℓ) (isGrpA : isGroupoid A) where 

-- -- -- -- -- --   toPerm₂ : FMSet2 A → Perm₂
-- -- -- -- -- --   toPerm₂ [] = []
-- -- -- -- -- --   toPerm₂ (x ∷2 x₁) = (_ ∷2 toPerm₂ x₁)
-- -- -- -- -- --   toPerm₂ (comm x y x₁ i) = (comm _ _ (toPerm₂ x₁) i)
-- -- -- -- -- --   toPerm₂ (comm-inv x y x₁ i i₁) = (comm-inv _ _ (toPerm₂ x₁) i i₁)
-- -- -- -- -- --   toPerm₂ (hexDiag x y z x₁ i) = (hexDiag _ _ _ (toPerm₂ x₁) i)
-- -- -- -- -- --   toPerm₂ (hexU x y z x₁ i i₁) = (hexU _ _ _ (toPerm₂ x₁) i i₁)
-- -- -- -- -- --   toPerm₂ (hexL x y z x₁ i i₁) = (hexL _ _ _ (toPerm₂ x₁) i i₁)
-- -- -- -- -- --   toPerm₂ (trunc x x₁ x₂ y x₃ y₁ i i₁ x₄) =
-- -- -- -- -- --     (trunc _ _ _ _
-- -- -- -- -- --      (λ i j → toPerm₂ (x₃ i j)) ((λ i j → toPerm₂ (y₁ i j))) i i₁ x₄)


-- -- -- -- -- --   commLem :  (x y : A) {C : Type}
-- -- -- -- -- --                (b : C → A) →
-- -- -- -- -- --             ⊎.rec {A = Unit} (λ _ → x) (⊎.rec {A = Unit} (λ _ → y) b) ≡
-- -- -- -- -- --       ⊎.rec (λ _ → y) (⊎.rec (λ _ → x) b) ∘ swap0and1⊎f
-- -- -- -- -- --   commLem x y b i (_⊎_.inl x₁) = x
-- -- -- -- -- --   commLem x y b i (_⊎_.inr (_⊎_.inl x₁)) = y
-- -- -- -- -- --   commLem x y b i (_⊎_.inr (_⊎_.inr x₁)) = b x₁

-- -- -- -- -- --   toF→R : RElim {A = A} (λ z → Fin⊎' z → A)
-- -- -- -- -- --   RElim.[]* toF→R = ⊥.rec*
-- -- -- -- -- --   (toF→R RElim.∷* x) = ⊎.rec λ _ → x
-- -- -- -- -- --   RElim.comm* toF→R x y {xs} b =
-- -- -- -- -- --     commLem x y b ◁ ua→' _ _
    
-- -- -- -- -- --   RElim.comm-inv* toF→R = {!!}
-- -- -- -- -- --   RElim.hexDiag* toF→R = {!!}
-- -- -- -- -- --   RElim.hexU* toF→R = {!!}
-- -- -- -- -- --   RElim.hexL* toF→R = {!!}
-- -- -- -- -- --   RElim.trunc* toF→R = {!!}

-- -- -- -- -- --   toF→ : (x : FMSet2 A) → Fin⊎' x → A
-- -- -- -- -- --   toF→ = RElim.f {!!}

-- -- -- -- -- curry' : ∀ {ℓ ℓ' ℓ''}
-- -- -- -- --   {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
-- -- -- -- --    → ((A × B) → C) → A → B → C
-- -- -- -- -- curry' f x y = f (x , y)


-- -- -- -- -- module _ {ℓ} (A : Type ℓ) where 
-- -- -- -- --   open mkRecTest ℓ



-- -- -- -- --   maybeSucIso : {B : Type₀}
-- -- -- -- --      → Iso (A × (B → A)) (Maybe B → A)
-- -- -- -- --   maybeSucIso = w
-- -- -- -- --     where

-- -- -- -- --        w : Iso (A × (_ → A)) (Maybe _ → A)
-- -- -- -- --        Iso.fun w = uncurry Mb.rec
-- -- -- -- --        Iso.inv w f = (f nothing) , (f ∘ just)
-- -- -- -- --        Iso.rightInv w b = funExt (Mb.elim _ refl λ _ → refl)
-- -- -- -- --        Iso.leftInv w _ = refl

-- -- -- -- --   ∷VecR : {B : Type₀} →
-- -- -- -- --           Σ (Type ℓ) (λ T → T ≃ (B → A))
-- -- -- -- --         → Σ (Type ℓ) (λ T → T ≃ (Maybe B → A))
-- -- -- -- --   ∷VecR (T , e) =
-- -- -- -- --     (A × T) , ≃-× (idEquiv _) e ∙ₑ isoToEquiv (maybeSucIso) 

-- -- -- -- --   ∷VecR' : {B : Type₀} →
-- -- -- -- --           Σ (Type ℓ) (λ T → (B → A) ≃ T )
-- -- -- -- --         → Σ (Type ℓ) (λ T → (Maybe B → A) ≃ T)
-- -- -- -- --   ∷VecR' (T , e) =
-- -- -- -- --     (A × T) ,  isoToEquiv (invIso (maybeSucIso)) ∙ₑ ≃-× (idEquiv _) e

-- -- -- -- --   swap× : (B : Type ℓ) → (A × (A × B)) → (A × (A × B)) 
-- -- -- -- --   swap× _ x = (fst (snd x)) , ((fst x) , (snd (snd x)))

-- -- -- -- --   swapInvol : (B : Type ℓ) → isInvolution {A = (A × (A × B))}
-- -- -- -- --        (swap× B)
-- -- -- -- --   swapInvol _ _ = refl

-- -- -- -- --   swapIso' : (B : Type ℓ) → Iso (A × (A × B)) (A × (A × B))
-- -- -- -- --   swapIso' B = involIso {f = (swap× B)}
-- -- -- -- --    (swapInvol B)

-- -- -- -- --   commInvVecRsq : (B : Type ℓ) →  
-- -- -- -- --      Square (ua (isoToEquiv (swapIso' B)))
-- -- -- -- --       (sym ((ua (isoToEquiv (swapIso' B)))))
-- -- -- -- --        refl refl
-- -- -- -- --   commInvVecRsq B = involPathSym λ z _ → z
    

-- -- -- -- --   -- toF→R : RElim {A = A} (λ z → Fin₂ (toPerm₂ z) → A)
-- -- -- -- --   -- RElim.[]* toF→R = ⊥.rec
-- -- -- -- --   -- RElim._∷*_ toF→R a {xs} = Mb.rec a 
-- -- -- -- --   -- RElim.comm* toF→R = {!!}
-- -- -- -- --   -- RElim.comm-inv* toF→R = {!!}
-- -- -- -- --   -- RElim.hexDiag* toF→R = {!!}
-- -- -- -- --   -- RElim.hexU* toF→R = {!!}
-- -- -- -- --   -- RElim.hexL* toF→R = {!!}
-- -- -- -- --   -- RElim.trunc* toF→R = {!!}

-- -- -- -- --   -- toF→ : (x : FMSet2 A) → Fin₂ (toPerm₂ x) → A
-- -- -- -- --   -- toF→ = RElim.f {!!}


-- -- -- -- --   -- commInvVecRsqFun : (h : hSet ℓ-zero)
-- -- -- -- --   --   (b  : Σ (Type ℓ) (λ T → T ≃ (fst h → A))) →
-- -- -- -- --   --    SquareP (λ i j →  commInvVecRsq (fst b) i j  → (invoFinR h i j → A))
-- -- -- -- --   --        ((ua→ λ a →
-- -- -- -- --   --       toPathP (funExt (Mb.elim _
-- -- -- -- --   --        (transportRefl (fst (snd a)))
-- -- -- -- --   --         (Mb.elim _
-- -- -- -- --   --           (transportRefl (fst a))
-- -- -- -- --   --           λ x → transportRefl _ ∙ cong (fst (snd b) (snd (snd a)))
-- -- -- -- --   --             (transportRefl _))))))
-- -- -- -- --   --        (symP ((ua→ λ a →
-- -- -- -- --   --       toPathP (funExt (Mb.elim _
-- -- -- -- --   --        (transportRefl (fst (snd a)))
-- -- -- -- --   --         (Mb.elim _
-- -- -- -- --   --           (transportRefl (fst a))
-- -- -- -- --   --           λ x → transportRefl _ ∙ cong (fst (snd b) (snd (snd a)))
-- -- -- -- --   --             (transportRefl _)))))))
-- -- -- -- --   --        (refl {x = fst ((snd ∘ ∷VecR ∘ ∷VecR) b)})
-- -- -- -- --   --        (refl {x = fst ((snd ∘ ∷VecR ∘ ∷VecR) b)})
-- -- -- -- --   -- commInvVecRsqFun h b =
-- -- -- -- --   --    {!!}


-- -- -- -- -- -- sqF'-no : ∀ xs → SquareP (λ i j → Fin₂ (comm-inv _ _ xs i j))
-- -- -- -- -- --          (ua-gluePath _ (λ i → just nothing))
-- -- -- -- -- --          (symP (ua-gluePath _ (λ i → nothing)))
-- -- -- -- -- --          (λ _ → nothing)
-- -- -- -- -- --          (λ _ → just nothing)
-- -- -- -- -- -- sqF'-no xs = isSet→SquareP
-- -- -- -- -- --   (λ i j → isSetFin₂ (comm-inv _ _ xs i j)) _ _ _ _



-- -- -- -- --   sqTySingl≃ : (B : I → I → Type₀)
-- -- -- -- --       (A' : I → I → Type ℓ)
-- -- -- -- --       (e' : ∀ i j → (B i j → A) → A' i j)
-- -- -- -- --       {p00 : isEquiv (e' i0 i0)}
-- -- -- -- --       {p01 : isEquiv (e' i0 i1)}
-- -- -- -- --       {p10 : isEquiv (e' i1 i0)}
-- -- -- -- --       {p11 : isEquiv (e' i1 i1)}
-- -- -- -- --       (p0j : PathP (λ j → isEquiv (e' i0 j)) p00 p01 )
-- -- -- -- --       (p1j : PathP (λ j → isEquiv (e' i1 j)) p10 p11 )
-- -- -- -- --       (pi0 : PathP (λ i → isEquiv (e' i i0)) p00 p10 )
-- -- -- -- --       (pi1 : PathP (λ i → isEquiv (e' i i1)) p01 p11 )
-- -- -- -- --       → SquareP
-- -- -- -- --       (λ i j → Σ (Type ℓ) (λ T → (B i j → A) ≃ T))
-- -- -- -- --       (λ j → (A' i0 j) , e' i0 j , p0j j)
-- -- -- -- --       (λ j → (A' i1 j) , e' i1 j , p1j j)
-- -- -- -- --       (λ i → (A' i i0) , e' i i0 , pi0 i)
-- -- -- -- --       (λ i → (A' i i1) , e' i i1 , pi1 i)
-- -- -- -- --   sqTySingl≃ B A' e' p0j p1j pi0 pi1 i j =
-- -- -- -- --     A' i j , (e' i j) , (isSet→SquareP (λ i j → isProp→isSet (isPropIsEquiv (e' i j)))
-- -- -- -- --       p0j p1j pi0 pi1 i j)

-- -- -- -- --   -- ua∘ : ∀ {ℓ} {A A' B B' C : Type ℓ} → (e : {!!}) → (f : {!!})
-- -- -- -- --   --            → {!!}
-- -- -- -- --   -- ua∘ = {!!}

-- -- -- -- --   -- commInvSq : (B : Type ℓ) → Square
-- -- -- -- --   --   (ua (isoToEquiv (swapIso {A = A} {B = A} {C = B})))
-- -- -- -- --   --    (sym ((ua (isoToEquiv (swapIso {A = A} {B = A} {C = B})))))
-- -- -- -- --   --    refl refl
-- -- -- -- --   -- commInvSq B =
-- -- -- -- --   --   {!involPathSym {f = ?} ?!}

-- -- -- -- --   PermVecR : RElim {A = Unit}
-- -- -- -- --                  λ e → Σ (Type ℓ) (λ T → (Fin₂ e → A) ≃ T)
-- -- -- -- --   RElim.[]* PermVecR = Unit* , invEquiv (Unit*≃⊥→A A)
-- -- -- -- --   RElim._∷*_ PermVecR = λ _ → ∷VecR'
-- -- -- -- --   RElim.comm* PermVecR x y {xs} b =
-- -- -- -- --     ΣPathP (ua (isoToEquiv (swapIso' (fst b))) ,
-- -- -- -- --       ΣPathPProp (isPropIsEquiv) zz )
-- -- -- -- --    where
-- -- -- -- --      zz : PathP
-- -- -- -- --             (λ z → (Fin₂ (comm x y xs z) → A)
-- -- -- -- --               → ua (isoToEquiv (swapIso' (fst b))) z)
            
-- -- -- -- --             (fst
-- -- -- -- --              (isoToEquiv (invIso maybeSucIso) ∙ₑ
-- -- -- -- --               ≃-× (idEquiv A) (snd (∷VecR' b))))
-- -- -- -- --             (fst
-- -- -- -- --              (isoToEquiv (invIso maybeSucIso) ∙ₑ
-- -- -- -- --               ≃-× (idEquiv A) (snd (∷VecR' b))))
-- -- -- -- --      zz i g =
-- -- -- -- --       let g' : Maybe (Maybe (fst (RRec.f Fin₂R xs))) → Fin₂ (comm x y xs i)
-- -- -- -- --           g' qq = glue (λ { (i = i0) → qq
-- -- -- -- --                  ; (i = i1) → fst (swap0and1M ((RRec.f Fin₂R xs))) qq })
-- -- -- -- --                 (fst (swap0and1M ((RRec.f Fin₂R xs))) qq)
-- -- -- -- --       in glue (λ { (i = i0) → g nothing , g (just nothing)
-- -- -- -- --                                 , fst (snd b) (λ x₁ → g (just (just x₁)))
-- -- -- -- --                  ; (i = i1) → g nothing , (g (just nothing)
-- -- -- -- --                                 , fst (snd b) (λ x₁ → g _)) })
-- -- -- -- --                 (g (g' (just nothing)) , (g (g' nothing) ,
-- -- -- -- --                   fst (snd b) (g ∘ g' ∘ just ∘ just)))  
-- -- -- -- --   RElim.comm-inv* PermVecR x y {xs} b = 
-- -- -- -- --     sqTySingl≃ _ (λ i j → commInvVecRsq (fst b) i j)
-- -- -- -- --       (λ i j g →
-- -- -- -- --            sqA i j 
-- -- -- -- --             (ua-gluePath ((isoToEquiv (swapIso' (fst b))))
-- -- -- -- --             (λ i₁ → (g (sqF'-ju-no i j)) , (g (sqF'-no i j) ,
-- -- -- -- --                 fst (snd b) (g ∘ sqF'-ju-ju i j)))
-- -- -- -- --             i)
-- -- -- -- --             )
-- -- -- -- --           _ _ _ _

-- -- -- -- --     where 

-- -- -- -- --       sqAside : PathP (λ i → involPath {f = swap× (fst b)} (swapInvol (fst b)) i → A × A × fst b)
-- -- -- -- --                   (λ x₁ → x₁) (swap× (fst b))
-- -- -- -- --       sqAside i x = swap× (fst b) ((ua-unglue
-- -- -- -- --          (isoToEquiv (swapIso' (fst b))) i x))

-- -- -- -- --       sqA : InvolSym.Ty {f = swap× (fst b)} (swapInvol (fst b)) sqAside 
-- -- -- -- --       sqA i j x =
-- -- -- -- --         glue
-- -- -- -- --           (λ { (j = i0) → 
-- -- -- -- --               (swap× (fst b))
-- -- -- -- --                (ua-unglue ((isoToEquiv (swapIso' (fst b)))) i x)
-- -- -- -- --              ; (j = i1) → ua-unglue ((isoToEquiv (swapIso' (fst b)))) i x
               
-- -- -- -- --            })
-- -- -- -- --            ( ua-gluePath (isoToEquiv (swapIso' (fst b))) (λ _ → 
-- -- -- -- --               swap× (fst b)
-- -- -- -- --                (ua-unglue ((isoToEquiv (swapIso' (fst b)))) i x)) i)


-- -- -- -- --       sqF'-no : SquareP (λ i j → Fin₂ (comm-inv x y xs i j))
-- -- -- -- --                (ua-gluePath _ (λ i → just nothing))
-- -- -- -- --                (symP (ua-gluePath _ (λ i → nothing)))
-- -- -- -- --                (λ _ → nothing)
-- -- -- -- --                (λ _ → just nothing)
-- -- -- -- --       sqF'-no = isSet→SquareP
-- -- -- -- --           (λ i j → isSetFin₂ (comm-inv _ _ xs i j)) _ _ _ _

-- -- -- -- --       e = (swap0and1Mf (RRec.f Fin₂R xs) ,
-- -- -- -- --                               involIsEquiv (isInvolutionSwap0and1M (RRec.f Fin₂R xs)))

-- -- -- -- --       sqF'-ju-no : SquareP (λ i j → Fin₂ (comm-inv x y xs i j))
-- -- -- -- --                (ua-gluePath e (λ i → nothing))
-- -- -- -- --                (symP (ua-gluePath _ (λ i → just (nothing))))
-- -- -- -- --                (λ _ → just nothing)
-- -- -- -- --                (λ _ → nothing)
-- -- -- -- --       sqF'-ju-no = isSet→SquareP
-- -- -- -- --           (λ i j → isSetFin₂ (comm-inv _ _ xs i j)) _ _ _ _

-- -- -- -- --       sqF'-ju-ju : SquareP (λ i j → Fin₂ xs → Fin₂ (comm-inv x y xs i j))
-- -- -- -- --                (λ j x → ua-gluePath e {x = just (just x)} {just (just x)} (λ i → just (just x)) j)
-- -- -- -- --                (λ j x → ua-gluePath e {x = just (just x)} {just (just x)} (λ i → just (just x)) (~ j))
-- -- -- -- --                (λ _ x → just (just x))
-- -- -- -- --                (λ _ x → just (just x))
-- -- -- -- --       sqF'-ju-ju = isSet→SquareP
-- -- -- -- --           (λ i j → isSet→ (isSetFin₂ (comm-inv _ _ xs i j)))
-- -- -- -- --             (λ j x → ua-gluePath e {x = just (just x)} {just (just x)} (λ i → just (just x)) j)
-- -- -- -- --             (λ j x → ua-gluePath e {x = just (just x)} {just (just x)} (λ i → just (just x)) (~ j))
-- -- -- -- --                (λ _ x → just (just x))
-- -- -- -- --                (λ _ x → just (just x))



-- -- -- -- --   RElim.hexDiag* PermVecR = {!!}
-- -- -- -- --   RElim.hexU* PermVecR = {!!}
-- -- -- -- --   RElim.hexL* PermVecR = {!!}
-- -- -- -- --   RElim.trunc* PermVecR = {!!}


-- -- -- -- --   PermVec₂ : Perm₂  → Type ℓ
-- -- -- -- --   PermVec₂ = fst ∘ RElim.f PermVecR  


-- -- -- -- --   PermVec : ℕ → Type ℓ
-- -- -- -- --   PermVec = fst ∘ RElim.f PermVecR ∘ nPerm₂ 

-- -- -- -- --   -- fromList : {!!}
-- -- -- -- --   -- fromList = {!!}

-- -- -- -- --   -- ↔Ty : (x y : List A) → nPerm₂ (length x) ≡ nPerm₂ (length y) → Type ℓ
-- -- -- -- --   -- ↔Ty [] [] x₁ = Unit*
-- -- -- -- --   -- ↔Ty [] (x ∷ y) x₁ = ⊥.rec (znots (cong len2 x₁))
-- -- -- -- --   -- ↔Ty (x ∷ x₂) [] x₁ = ⊥.rec (snotz (cong len2 x₁))
-- -- -- -- --   -- ↔Ty (x ∷ x₂) (x₃ ∷ y) x₁ = {!!}


-- -- -- -- --   -- infix 4  _↔_

-- -- -- -- --   -- record _↔_ {ℓ} {A : Type ℓ} (x y : List A) : Type ℓ where
-- -- -- -- --   --   constructor prm
-- -- -- -- --   --   field
-- -- -- -- --   --     F≃ : (Fin (length x) ≃ Fin (length y))
-- -- -- -- --   --     l≡ : ∀ k → lookup x k ≡ lookup y (equivFun F≃ k)

-- -- -- -- --   -- open _↔_


-- -- -- -- --   -- toVecΣ : RElim {A = A} (λ z → PermVec₂ (toPerm₂ z))
-- -- -- -- --   -- RElim.[]* toVecΣ = tt*
-- -- -- -- --   -- (toVecΣ RElim.∷* x) = x ,_
-- -- -- -- --   -- RElim.comm* toVecΣ x y {xs} b =
-- -- -- -- --   --   ua-gluePath _ refl
-- -- -- -- --   -- RElim.comm-inv* toVecΣ x y b _ = {!!}
-- -- -- -- --   -- RElim.hexDiag* toVecΣ = {!!}
-- -- -- -- --   -- RElim.hexU* toVecΣ = {!!}
-- -- -- -- --   -- RElim.hexL* toVecΣ = {!!}
-- -- -- -- --   -- RElim.trunc* toVecΣ = {!!}

-- -- -- -- -- -- -- --   VecMb : ℕ → Type ℓ
-- -- -- -- -- -- -- --   VecMb n = iter n (A ×_) Unit*


-- -- -- -- -- -- -- --   Vec≡ : ∀ n → (VecMb n) ≡ (PermVec n)
-- -- -- -- -- -- -- --   Vec≡ zero = refl
-- -- -- -- -- -- -- --   Vec≡ (suc n) = cong′ (A ×_) (Vec≡ n) 

-- -- -- -- -- -- -- --   VecIso : ∀ n → Iso (VecMb n) (PermVec n)
-- -- -- -- -- -- -- --   VecIso zero = idIso 
-- -- -- -- -- -- -- --   VecIso (suc n) = prodIso idIso (VecIso n)

-- -- -- -- -- -- -- --   _≡ℕ_ : ℕ → ℕ → Type
-- -- -- -- -- -- -- --   zero ≡ℕ zero = Unit
-- -- -- -- -- -- -- --   zero ≡ℕ suc x₁ = ⊥.⊥
-- -- -- -- -- -- -- --   suc x ≡ℕ zero = ⊥.⊥
-- -- -- -- -- -- -- --   suc x ≡ℕ suc x₁ = x ≡ℕ x₁

-- -- -- -- -- -- -- --   ListOfLen : ∀ n → Iso (Σ (List A) λ l → length l ≡ℕ n) (PermVec n)
-- -- -- -- -- -- -- --   ListOfLen zero = w
-- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- --       w : Iso (Σ (List A) (λ l → length l ≡ℕ zero)) (PermVec zero)
-- -- -- -- -- -- -- --       Iso.fun w _ = _
-- -- -- -- -- -- -- --       Iso.inv w _ = [] , _
-- -- -- -- -- -- -- --       Iso.rightInv w _ = refl
-- -- -- -- -- -- -- --       Iso.leftInv w ([] , snd₁) = refl
      
  
-- -- -- -- -- -- -- --   ListOfLen (suc n) = w
-- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- --       w : Iso (Σ (List A) (λ l → length l ≡ℕ suc n)) (PermVec (suc n))
-- -- -- -- -- -- -- --       Iso.fun w (x ∷ xs , p) =
-- -- -- -- -- -- -- --         x , Iso.fun (ListOfLen n) (xs , p) 
-- -- -- -- -- -- -- --       Iso.inv w (x , f) =
-- -- -- -- -- -- -- --         let (xs , p)  = Iso.inv (ListOfLen n) f
-- -- -- -- -- -- -- --         in (x ∷ xs , p)
-- -- -- -- -- -- -- --       Iso.rightInv w (x , f) =
-- -- -- -- -- -- -- --         cong (x ,_) (Iso.rightInv (ListOfLen n) f)
-- -- -- -- -- -- -- --       Iso.leftInv w (x ∷ xs , p) =
-- -- -- -- -- -- -- --         cong (λ (xs , p) → x ∷ xs , p)
-- -- -- -- -- -- -- --              (Iso.leftInv (ListOfLen n) (xs , p))




-- -- -- -- -- -- -- -- -- FMI : FMSet2 A → hSet ℓ-zero
-- -- -- -- -- -- -- -- -- FMI =
-- -- -- -- -- -- -- -- --   Elim.f 
-- -- -- -- -- -- -- -- --    (⊥.⊥ , isProp→isSet isProp⊥)
-- -- -- -- -- -- -- -- --    (λ x {xs} b → Maybe (fst b) , isOfHLevelMaybe zero (snd b) )
-- -- -- -- -- -- -- -- --    (λ x y b → TypeOfHLevel≡ 2 (ua (swap0and1M b)))
-- -- -- -- -- -- -- -- --    (λ x y {xs} b →
-- -- -- -- -- -- -- -- --       ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- --         (cong ua (equivEq (funExt ((Mb.elim _ refl (Mb.elim _ refl λ _ → refl) ))))
-- -- -- -- -- -- -- -- --           ∙ uaInvEquiv (swap0and1M b)) )
-- -- -- -- -- -- -- -- --    (λ x y z b → TypeOfHLevel≡ 2 (ua (swap0and2M b)))
-- -- -- -- -- -- -- -- --    (λ x y z {xs} b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- --                       (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- --                        (isInjectiveTransport
-- -- -- -- -- -- -- -- --                         (funExt (Mb.elim _  refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))))))


-- -- -- -- -- -- -- -- --    (λ x y z {xs} b → ΣSquareSet (λ _ → isProp→isSet (isPropIsSet))
-- -- -- -- -- -- -- -- --                       (∙≡∙→square _ _ _ _
-- -- -- -- -- -- -- -- --                        (isInjectiveTransport
-- -- -- -- -- -- -- -- --                         (funExt (Mb.elim _  refl (Mb.elim _ refl (Mb.elim _ refl λ _ → refl)))))))
-- -- -- -- -- -- -- -- --    (λ _ → isGroupoidHSet)



