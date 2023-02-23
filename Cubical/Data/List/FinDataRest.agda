{-# OPTIONS --safe  --experimental-lossy-unification  #-} 
module Cubical.Data.List.FinDataRest where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path

open import Cubical.Functions.Involution

open import Cubical.Functions.FunExtEquiv

open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary

open import Cubical.Data.List renaming (map to mapList)
open import Cubical.Data.FinData

open import Cubical.Data.Nat renaming (snotz to ℕsnotz ; znots to ℕznots)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ renaming ([_] to [_]/)
open import Cubical.HITs.GroupoidQuotients as GQ renaming ([_] to [_]//)

open import Cubical.HITs.ListedFiniteSet.Base2 as FM2

open import Cubical.HITs.FiniteMultiset as FM
  renaming (_∷_ to _∷fm_ ; [] to []fm ; _++_ to _++fm_) hiding ([_])
open import Cubical.HITs.FreeComMonoids using (FreeComMonoid;AssocList≃FreeComMonoid)
open import Cubical.HITs.AssocList using (FMSet≃AssocList)


open import Cubical.Algebra.Group
open import Cubical.Algebra.SymmetricGroup
open import Cubical.Algebra.Group.Generators
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Data.List.FinData

private
  variable
    ℓ : Level
    A B : Type ℓ

-- isSet-cong : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
--                 → (isSet-A : isSet A)
--                 → ∀ {a b : A}
--                 → (p : a ≡ b) → (f : A → B) →
--                  {!!} 
-- isSet-cong {B = B} isSet-A p f = {!!}
-- -- cong (cong f) (isSet-A _ _ p refl)


transportLem : ∀ {ℓ} {A B : Type ℓ} {p : A ≡ B} {a : A} {b : B} →
                 a ≡ transport (sym p) b → transport p a ≡ b 
transportLem = {!!} 


transportLem' : ∀ {ℓ} {A B : Type ℓ} {p : A ≡ B} {a : A} {b : B} →
                  transport p a ≡ b → a ≡ transport (sym p) b 
transportLem' = {!!} 


module FC2MMore {ℓ} {A : Type ℓ} where
  open FC2M {A = A}

  fromFM2len : ∀ n → FMSet2OfLen A n → Fin→//↔ n 
  fromFM2len n (x , p) = subst Fin→//↔ p (fromFM2 x)



  append→lem : ∀ x n (xs : Fin→//↔ n) →
    fst (toFM2 (suc n) ( append→ x xs))
    ≡
    x ∷2 fst (toFM2 n xs)

  append→lem x zero = GQ.RelimSet.f r
    where
     r : RelimSet _
     RelimSet.truncB r _ = trunc _ _
     RelimSet.fb r = λ _ → refl
     RelimSet.fbEq r r' =
      flipSquare (cong′ (refl ∙_) (cong′ (refl ∙_) (sym compPathRefl) ∙ sym compPathRefl)
      ∙ sym compPathRefl)
     
  append→lem x (suc n) = GQ.RelimSet.f r
    where
     r : RelimSet _
     RelimSet.truncB r _ = trunc _ _
     RelimSet.fb r = λ _ → refl
     RelimSet.fbEq r r' =
      flipSquare
       (sym {!!})

  toFM2fromFst : ∀ (x : FMSet2 A) → 
      fst (toFM2 (len2 x) (fromFM2 x)) ≡ x
  toFM2fromFst = RElimSet'.f r
    where
      r : RElimSet' _
      RElimSet'.[]* r = refl
      (r RElimSet'.∷* x) {xs} p =
       (append→lem x (len2 xs) (fromFM2 xs)) ∙ cong (x ∷2_) p
      RElimSet'.comm* r x y {xs} b =
        ss
        where
          ss'' : ∀ n → (xs* : Fin→//↔ n) →
                  
                 Square
                  (append→lem x (suc n) (append→ y xs*) ∙ cong (x ∷2_) (append→lem y n xs*))
                  (append→lem y (suc n) (append→ x xs*) ∙ cong (y ∷2_) (append→lem x n xs*))
                  (cong (fst ∘ toFM2 (suc (suc n))) (appendComm x y xs*))
                  (comm x y (fst (toFM2 n xs*)))
          ss'' zero = {!!}
          ss'' (suc n) = GQ.RelimProp.f ss'R
            where
              ss'R : RelimProp _
              RelimProp.truncB ss'R = {!!}
              RelimProp.fb ss'R f =
                 sym compPathRefl
                  ◁ flipSquare
                   (sym (lUnit _) ∙
                    toFM2≡U-swap0and1 (suc n) x y f )
                   ▷ compPathRefl


          ssI0 : ∀ x y → Square
                   (append→lem x (suc (len2 xs)) (append→ y (fromFM2 xs))
                     ∙ cong (x ∷2_) (append→lem y (len2 xs) (fromFM2 xs)))
                   (append→lem x (suc (len2 xs)) (append→ y (fromFM2 xs))
                  ∙ cong (x ∷2_) (append→lem y (len2 xs) (fromFM2 xs)
                          ∙ cong (y ∷2_) b))
                   refl
                   ((cong (λ xs → x ∷2 y ∷2 xs) (b)))
          ssI0 x y =
            (cong (append→lem x (suc (len2 xs)) (append→ y (fromFM2 xs)) ∙_)
              (((rUnit _ ∙ cong′ ((cong (x ∷2_) (append→lem y (len2 xs) (fromFM2 xs))) ∙_)
                             (sym (rCancel (cong (x ∷2_) (cong (y ∷2_) b)))))
                       
                 ∙ assoc _ _ _) ∙ cong (_∙ sym ((cong (λ xs → x ∷2 y ∷2 xs) (b))))
                 (sym (cong-∙ _ _ _)))
              ∙ assoc _ _ _)
            ◁
            symP (compPath-filler _ _)

          ss : Square
                  (append→lem x (suc (len2 xs)) (append→ y (fromFM2 xs))
                  ∙ cong (x ∷2_) (append→lem y (len2 xs) (fromFM2 xs)
                          ∙ cong (y ∷2_) b))
                  (append→lem y (suc (len2 xs)) (append→ x (fromFM2 xs))
                  ∙ cong (y ∷2_) (append→lem x (len2 xs) (fromFM2 xs)
                          ∙ cong (x ∷2_) b))
                  (cong (fst ∘ toFM2 (suc (suc (len2 xs))))
                   (appendComm x y (fromFM2 xs)))
                  (comm x y xs)
          ss i j =
            hcomp
              (λ k → λ {
                    (i = i0) → ssI0 x y k j
                  ; (i = i1) → ssI0 y x k j
                  ; (j = i0) → (cong (fst ∘ toFM2 (suc (suc (len2 xs))))
                   (appendComm x y (fromFM2 xs))) i
                  ; (j = i1) → comm x y (b k) i
                  })
              (ss'' (len2 xs) (fromFM2 xs) i j)
              
      RElimSet'.trunc* r _ = trunc _ _

  toFM2from : ∀ n → retract (fromFM2len n) (toFM2 n)
  toFM2from n = uncurry λ x y →
    Σ≡Prop (λ _ → isSetℕ _ _)
       (funExt⁻ {f = fst ∘ toFM2 n ∘ transport (λ i → (Fin (y i) → A) // isTrans↔ₙ (y i))}
                {g = fst ∘ toFM2 (len2 x)}
                  (λ i → fst ∘ toFM2 (y (~ i)) ∘
                    transport⁻-fillerExt⁻ ((λ i → (Fin (y (~ i)) → A) // isTrans↔ₙ (y (~ i)))) i)
         (fromFM2 x) ∙ toFM2fromFst x ) 

  -- fromFM2toL : ∀ n → (f : Fin→//↔ n)
  --                 → PathP {!!} (len2 (fst (toFM2 n f))) n
  -- fromFM2toL n = {!!}


  -- fromFM2toP : ∀ n → (f : Fin→//↔ n)
  --                 → (fromFM2 (fst (toFM2 n f)))
  --                  ≡ (transport (λ i → Fin→//↔ (snd (toFM2 n f) (~ i))) f)
  -- fromFM2toP n = GQ.RelimSet.f {!!}
  --   where
  --    r : ∀ n → RelimSet λ f →
  --                     (fromFM2 (fst (toFM2 n f)))
  --                  ≡ (transport (λ i → Fin→//↔ (snd (toFM2 n f) (~ i))) f)
                      
  --    RelimSet.truncB (r n) = {!!}
  --    RelimSet.fb (r zero) _ = cong [_]// =■
  --    RelimSet.fb (r (suc n)) f =
  --      let p'  = (RelimSet.fb (r n) (f ∘ suc))
  --      in cong (append→ (f zero)) p' ∙
  --           cong [_]// ((cong f (transportFin-zero _)
  --               ∙ sym (transportRefl _)) =→
  --                funExt λ x → cong (transport refl ∘ f)
  --                   (sym (transportFin-suc _ _ _)))
  --    RelimSet.fbEq (r zero) r' = {!!}
  --    RelimSet.fbEq (r (suc n)) = {!!}


  -- splitFMPa : ∀ n → (f g : Fin (suc n) → A) → (r' : f ↔ₙ g) →
  --       (f ↔ₙ {!!}) × ({!!} ↔ₙ {!toFM2≡Punch e0 b!})
  -- splitFMPa = {!!}


  -- preCompId : ∀ n → (Fin n ≃ Fin n) → Fin→//↔ n → Fin→//↔ n
  -- preCompId n e = GQ.Rrec.f r
  --  where
  --    r : Rrec (Fin→//↔ n)
  --    Rrec.Bgpd r = squash//
  --    Rrec.fb r = [_]// ∘ _∘ (fst e) 
  --    Rrec.feq r {b = b} (prm F≃ l≡) =
  --     eq// (prm (e ∙ₑ F≃ ∙ₑ invEquiv e)
  --       (cong (_∘ (fst e)) l≡ ∙ funExt λ x → cong b (sym (secEq e (fst F≃ (fst e x))))))
  --    Rrec.fsq r = {!!}
     
  -- mkPaPunch : ∀ {n} → (e : Fin (suc n) ≃ Fin (suc n))
  --           → (b : Fin (suc n) → A)
  --           → (b ∘ fst e) ↔ₙ b
  -- FC2M._↔ₙ_.F≃ (mkPaPunch e b) = e
  -- FC2M._↔ₙ_.l≡ (mkPaPunch e b) = refl


  fromFM2to[f]// : ∀ {n} → (f : Fin n → A)
                    → fromFM2len n (toFM2 n [ f ]//) ≡ [ f ]//
  fromFM2to[f]// {zero} _ = cong [_]// =■
  fromFM2to[f]// {suc n} f =
       let p'  = transportLem' (fromFM2to[f]// (f ∘ suc))
       in toPathP (transportRefl _ ∙
            transportLem
             (cong (append→ (f zero)) p' ∙
              cong [_]// ((cong f (transportFin-zero _)
                ∙ sym (transportRefl _)) =→
                  funExt λ x → cong (transport refl ∘ f)
                    (sym (transportFin-suc _ _ _)))))

  fromToPunch :  ∀ {n} → (k : Fin (suc n)) → (b : Fin (suc n) → A) →
      Square
        ((cong (fromFM2len (suc n)) (FMSet2OfLen≡ (toFM2≡Punch k b))))
        (eq// (prm (rot≃ k) refl))
        (fromFM2to[f]// (b ∘ fst (rot≃ k)))
        (fromFM2to[f]// b)

  fromToPunch = {!!}

  split↔ᵣ : ?
  split↔ᵣ = ?

  fromFM2to : ∀ n → section (fromFM2len n) (toFM2 n)
  fromFM2to n = GQ.RelimSet.f (r n)
    where
      r : ∀ n → RelimSet (λ z → fromFM2len n (toFM2 n z) ≡ z)
      RelimSet.truncB (r n) = λ _ → squash// _ _
      RelimSet.fb (r n) = fromFM2to[f]// 
      RelimSet.fbEq (r zero) _ = {!!}
      RelimSet.fbEq (r (suc n)) {f} {g} r'@(prm e p) =
       flipSquare (
          (cong (cong (fromFM2len (suc n))) {!!}
            ∙ cong-∙ ((fromFM2len (suc n)))
              (FMSet2OfLen≡ (cong₂ _∷2_ pLLh pLLt))
              (FMSet2OfLen≡ (toFM2≡Punch e0 g)))
            ◁  {!!} ▷
            {!!})
       where
        e' = fst (unwindPermHead e)
        p' = snd (unwindPermHead e)
        e0 = fst e zero

        pLLh = (funExt⁻ p zero ∙ cong g (funExt⁻ (cong fst p') zero))
        pLLt = (cong (fst ∘ (toFM2 (n)))
                 (eq// (prm e' (cong (_∘ suc) p
                   ∙ cong (g ∘_) (cong ((_∘ suc) ∘ fst) p') ))))

        pL : cong (fst ∘ (toFM2 (suc n)))
             (eq// r')
              ≡
              cong₂ _∷2_ pLLh pLLt
               ∙ toFM2≡Punch e0 g
        pL = {!!}




-- Rrec.f (toFM2r n)
--       (transp (λ i → (Fin (y i) → A) // isTrans↔ₙ (y i)) i0
--        (RElim.f Cubical.Data.List.FinData.FC2M.rFrom x))
--       .fst
--       ≡
--       fst
--       (Rrec.f (toFM2r (len2 x))
--        (RElim.f Cubical.Data.List.FinData.FC2M.rFrom x))


--   -- zzLem' : (a₁ : FMSet2 A) (a : A) (xs : FMSet2 A)  (x : len2 a₁ ≡ suc (len2 xs))
--   --     (y
--   --      : PathP (λ i → Fin→//↔ (x i)) (fromFM2 a₁) (fromFM2 (a ∷2 xs))) →
--   --     Path (Σ (FMSet2 A) (λ xs' → Σ ((len2 xs' ≡  suc (len2 xs)))
--   --       λ pl → PathP (λ i → Fin→//↔ (pl i))
--   --               (fromFM2 xs') (fromFM2 (a ∷2 xs))))
--   --      ((a ∷2 xs , (refl , refl )) ) (a₁ , x , y)
--   -- zzLem' = RElimSet'.f rr
--   --   where
--   --    rr : RElimSet' _
--   --    RElimSet'.[]* rr _ _ = ⊥.rec ∘ ℕznots
--   --    (rr RElimSet'.∷* x) x₁ a xs x₂ y =
--   --      ΣPathP ({!!} , {!!})
--   --      where
--   --        zzQ : {!!}
--   --        zzQ = x₁ a {!!} {!!} {!!} 
--   --    RElimSet'.comm* rr = {!!}
--   --    RElimSet'.trunc* rr = {!!}

--   -- zzLem : (a : A) (xs : FMSet2 A)
--   --          → isContr (Σ (FMSet2 A)
--   --            λ xs' → Σ (len2 xs' ≡  suc (len2 xs))
--   --              λ pl → PathP (λ i → Fin→//↔ (pl i))
--   --               (fromFM2 xs') (fromFM2 (a ∷2 xs)))
--   -- zzLem a xs = ((a ∷2 xs) , (refl , refl)) ,
--   --    uncurry (uncurry ∘ {!!} )
--   -- -- fst (zzLem a xs) = (a ∷2 xs) , (refl , refl)
--   -- -- snd (zzLem a xs) = uncurry (uncurry ∘ RElimSet'.f rr)
--   -- --   where
--   -- --     rr : RElimSet' _
--   -- --     RElimSet'.[]* rr = ⊥.rec ∘ ℕznots --uncurry (⊥.rec ∘ ℕznots)
--   -- --     (rr RElimSet'.∷* x) {xs'} x₁ x₂ y =
--   -- --       {!!}
--   -- --     RElimSet'.comm* rr = {!!}
--   -- --     RElimSet'.trunc* rr = {!!}

--   fromCong : ∀ xs ys → (pl : (len2 xs) ≡ (len2 ys))
--         → PathP (λ i → Fin→//↔ (pl i)) (fromFM2 xs) (fromFM2 ys)
--         → xs ≡ ys
--   fromCong = RElimSet.f
--     (record
--        { []* = RElimSet.f
--          (record
--            { []* = λ _ → {!!}
--            ; _∷*_ = λ x x₁ → ⊥.rec ∘ ℕznots
--            ; comm* = {!!}
--            ; hexDiag* = {!!}
--            ; trunc* = λ _ → isSetΠ2 λ _ _ → trunc _ _
--            })
--        ; _∷*_ = {!RElimSet.f ?!}
--        ; comm* = {!!}
--        ; hexDiag* = {!!}
--        ; trunc* = {!!}
--        }) 

--   zz : ∀ n → (f : Fin→//↔ n)
--           → isContr (fiber (fromFM2len n) f)
--   zz zero f = {!!}
--   zz (suc n) = GQ.RelimProp.f r 
--     where
--       r : RelimProp (λ z → isContr (fiber (fromFM2len (suc n)) z))
--       RelimProp.truncB r = λ _ → isPropIsContr
--       RelimProp.fb r f = gg


--        where

--         ss' = snd (zz n [ f ∘ suc ]//)

--         xs' = fst (fst (fst  (zz n [ f ∘ suc ]//)))

--         p' = snd (fst (fst  (zz n [ f ∘ suc ]//)))

--         q' = snd ((fst  (zz n [ f ∘ suc ]//)))


--         ggP : fromFM2len (suc n) (f zero ∷2 xs' , (λ i → suc (p' i))) ≡ [ f ]//
--         ggP =  fromPathP
--            (congP (λ _ → append→ (f zero))
--              (toPathP refl))
--          ∙ cong (append→ (f zero)) q' ∙ cong [_]//
--           (funExt  λ { zero → refl ; (suc k) → refl }) 


--         gg' : isContr (Σ (FMSet2OfLen A (suc n)) λ x → fromFM2len (suc n) x ≡
--                                fromFM2len (suc n) ( f zero ∷2 xs' , cong suc p'))
--         -- gg' = 
--         gg' = (_ , refl) , uncurry (uncurry (RElimSet'.f rr))
        
--           where
--             rr : RElimSet' _
--             RElimSet'.[]* rr = ⊥.rec ∘ ℕznots
--             (rr RElimSet'.∷* x) {xs} x₁ y y₁ =
--                 {!!}
--               where
--                 remXs : FMSet2 A
--                 remXs = {!!}

--                 remXsLen : len2 remXs ≡ n
--                 remXsLen = {!!}

--                 remXs≡xs' : remXs ≡ xs'
--                 remXs≡xs' = {!!}

--                 sss : _
--                 sss = ss' ((remXs , remXsLen) ,
--                   (λ i → fromFM2len n (remXs≡xs' i , {!!})) ∙ q')

--                 zzz : {!!}
--                 zzz = {!fromCong _ _ y!}

--             RElimSet'.comm* rr = {!!}
--             RElimSet'.trunc* rr = {!!}

--         gg : isContr (Σ (FMSet2OfLen A (suc n)) λ x → fromFM2len (suc n) x ≡ [ f ]//)
--         gg = subst (λ ff → isContr (Σ (FMSet2OfLen A (suc n)) λ x → fromFM2len (suc n) x ≡ ff))
--                ggP gg'
               
--         -- fst gg = ( f zero ∷2 xs' , cong suc p') , ggP
--         -- snd gg ((xs , p) , q) =
--         --   {!!}
--         --  where
--         --    xsRemoved : {!!}
--         --    xsRemoved = {!!}

--         --    xsRemovedLen : {!!}
--         --    xsRemovedLen = {!!}


--         --    sss' : fst (zz n [ (λ x → f (suc x)) ]//) ≡
--         --             ((xsRemoved , xsRemovedLen) , _)
--         --    sss' = ss' ((xsRemoved , xsRemovedLen) , {!q'!})


-- -- ΣPathP
-- --            (Σ≡Prop (λ _ → isSetℕ _ _) (fst= (fst y .fst)
-- --              (snd (fst y) ∙ sym (cong suc p'))
-- --              ( transportLem (snd y) ◁ {!!} ▷
-- --                sym (transportLem {p = cong (Fin→//↔ ∘ suc) p'} ggP))) , {!!})


--         -- gg' : isContr (Σ (FMSet2OfLen A (suc n)) λ x → fromFM2len (suc n) x ≡ [ f ]//)
--         -- gg' = {!!}


--        --  let (((xs' , p') , q') , s) = zz n [ f ∘ suc ]//
            
--        --      qqq : (x : FMSet2 A) (y : len2 x ≡ suc n)
--        --            (y₁ : fromFM2len (suc n) (x , y) ≡ [ f ]//) →
--        --             f zero ∷2 fst (fst (fst (zz n [ (λ x₁ → f (suc x₁)) ]//))) ≡ x
--        --      qqq = RElimSet.f rr
            
            
--        --  in (( f zero ∷2 xs' , cong suc p') ,
--        --    fromPathP {A = (λ i →
--        --   (Fin (suc (snd (fst (fst (zz n [ (λ x → f (suc x)) ]//))) i)) → A)
--        --   //
--        --   isTrans↔ₙ (suc (snd (fst (fst (zz n [ (λ x → f (suc x)) ]//))) i)))}
--        --    {!!} ∙ cong (append→ (f zero)) q' ∙ cong [_]//
--        --    (funExt  λ { zero → refl ; (suc k) → refl }) ) ,
--        --     uncurry (uncurry
--        --       {!!})
--        -- where

--        --  ss' = snd (zz n [ f ∘ suc ]//)

--        --  rr : RElimSet λ z →
--        --                        (y : len2 z ≡ suc n) →
--        --                        fromFM2len (suc n) (z , y) ≡ [ f ]// →
--        --                        f zero ∷2 fst (fst (fst (zz n [ (λ x₁ → f (suc x₁)) ]//))) ≡ z
--        --  RElimSet.[]* rr = ⊥.rec ∘ ℕznots
--        --  (rr RElimSet.∷* x) {xs} x₁ y x₂ =
--        --    let y' = injSuc y
--        --        sss = ss' ((xs , y') , {!!})
--        --    in {!!} ∙ cong (x ∷2_) (cong fst (cong fst sss))
--        --  RElimSet.comm* rr = {!!}
--        --  RElimSet.hexDiag* rr = {!!}
--        --  RElimSet.trunc* rr = {!!}


--   -- zz : isEquiv' (fst ∘ uncurry toFM2)
--   -- zz = RElimProp'.f r
--   --   where
--   --    r : RElimProp' (λ z → isContr (fiber (fst ∘ uncurry toFM2) z))
--   --    RElimProp'.[]* r = ((0 , [ (λ ()) ]//) , refl) , {!!}
--   --    fst (fst ((r RElimProp'.∷* a) {xs} b)) =
--   --      suc (fst (fst (fst b)))
--   --      , append→ a (snd (fst (fst b)))
--   --    snd (fst ((r RElimProp'.∷* a) {xs} b)) =
--   --     append→lem a  _ _ ∙ cong (a ∷2_) (snd (fst b))
--   --    snd ((r RElimProp'.∷* a) {xs} b) = {!!}
--   --    -- uncurry (uncurry zzz)
--   --    --   where
--   --    --     zzz : (x : ℕ) (y : Fin→//↔ x)
--   --    --             (y₁ : (fst ∘ uncurry toFM2) (x , y) ≡ a ∷2 xs) →
--   --    --             fst ((r RElimProp'.∷* a) b) ≡ ((x , y) , y₁)
--   --    --     zzz zero y y₁ = {!!}
--   --    --     fst (fst (zzz (suc x) [ a ]// p i)) =
--   --    --       suc (cong fst (cong fst (snd b ((x , [ a ∘ suc ]//) , {!p!}))) i)
--   --    --     snd (fst (zzz (suc x) [ a ]// p i)) = {!!}
--   --    --     snd (zzz (suc x) [ a ]// p i) = {!!}
--   --    --       -- let pp = snd b ((x , [ a ∘ suc ]//) , {!p!})
--   --    --       -- in {!!}
--   --    --     zzz (suc x) (eq// r₁ i) = {!!}
--   --    --     zzz (suc x) (comp// r₁ s j i) = {!!}
--   --    --     zzz (suc x) (squash// y y₁ p q r₁ s i i₁ i₂) = {!!}
--   --    RElimProp'.trunc* r _ = isPropIsContr
     
--   -- fst (zz n y) = {!fromFM2 (fst y)!} , {!!}
--   -- snd (zz n y) = {!!}
  
--   -- zz : ∀ n → isEquiv' (toFM2 n)
--   -- zz zero y = {!!}
--   -- zz (suc n) = uncurry (RElimProp'.f r)
--   --   where
--   --    r : RElimProp' _
--   --    RElimProp'.[]* r = ⊥.rec ∘ ℕznots
--   --    fst ((r RElimProp'.∷* x) x₁ y) = {!!}
--   --    snd ((r RElimProp'.∷* x) x₁ y) = {!!}
--   --    RElimProp'.trunc* r = {!!}


  
-- --   -- append→lem x n = GQ.RelimSet.f r
-- --   --   where
-- --   --    r : RelimSet {!!}
-- --   --    RelimSet.truncB r x = trunc _ _
-- --   --    RelimSet.fb r a = refl
-- --   --    RelimSet.fbEq r r₁ = ss
-- --   --      where
-- --   --        ss : Square (RelimSet.fb r _) (RelimSet.fb r _)
-- --   --                (λ i → fst (toFM2 (suc n) (append→ x (eq// r₁ i))))
-- --   --                 λ i → x ∷2 fst (toFM2 n (eq// r₁ i))
-- --   --        ss =
-- --   --         flipSquare {!!}

-- --   toFM2fromFst : ∀ (x : FMSet2 A) → 
-- --       fst (toFM2 (len2 x) (fromFM2 x)) ≡ x
-- --   toFM2fromFst = RElimSet'.f r
-- --     where
-- --       r : RElimSet' _
-- --       RElimSet'.[]* r = refl
-- --       (r RElimSet'.∷* x) {xs} p =
-- --        (append→lem x (len2 xs) (fromFM2 xs)) ∙ cong (x ∷2_) p
-- --       RElimSet'.comm* r = {!!}
-- --       RElimSet'.trunc* r _ = trunc _ _


-- -- -- fst
-- -- --       (Rrec.f (toFM2r (suc (len2 xs)))
-- -- --        (Rrec.f (rAppend x (len2 xs))
-- -- --         (RElim.f Cubical.Data.List.FinData.FC2M.r xs)))
-- -- --       ≡
-- -- --       fst
-- -- --       (Rrec.f (toFM2r (suc (len2 xs)))
-- -- --        (Rrec.f (rAppend x (len2 xs))
-- -- --         (RElim.f Cubical.Data.List.FinData.FC2M.r xs)))

-- -- -- fst
-- -- --       (Rrec.f (toFM2r (suc (len2 xs)))
-- -- --        (Rrec.f (Cubical.Data.List.FinData.FC2M.rAppend x)
-- -- --         (RElim.f Cubical.Data.List.FinData.FC2M.r xs)))
-- -- --       ≡
-- -- --       fst
-- -- --       (Rrec.f (toFM2r (suc (len2 xs)))
-- -- --        (Rrec.f (Cubical.Data.List.FinData.FC2M.rAppend x)
-- -- --         (RElim.f Cubical.Data.List.FinData.FC2M.r xs)))

-- -- --   toFM2fromFst' : ∀ n → ∀ (x : FMSet2 A) → (p : len2 x ≡ n) →
-- -- --       fst (toFM2 n (fromFM2len n (x , p))) ≡ x
-- -- --   toFM2fromFst' n x p =
-- -- --       {!!} ∙ toFM2fromFst x    
-- -- --   -- toFM2fromFst zero = RElimSet'.f r
-- -- --   --   where
-- -- --   --     r : RElimSet' _
-- -- --   --     RElimSet'.[]* r _ = refl
-- -- --   --     (r RElimSet'.∷* x) _ = ⊥.rec ∘ ℕsnotz
-- -- --   --     RElimSet'.comm* r x y b = funExtDep λ {x₀} → ⊥.rec (ℕsnotz x₀) 
-- -- --   --     (RElimSet'.trunc* r) _ = isSetΠ λ _ → trunc _ _
      
-- -- --   -- toFM2fromFst (suc n) = RElimSet'.f r
-- -- --   --   where
-- -- --   --     r : RElimSet' _
-- -- --   --     RElimSet'.[]* r = ⊥.rec ∘ ℕznots
-- -- --   --     (r RElimSet'.∷* x) {xs} x₁ p =
-- -- --   --       let p' = toFM2fromFst n xs (injSuc p)  
-- -- --   --       in {!p'!}
-- -- --   --     RElimSet'.comm* r = {!!}
-- -- --   --     RElimSet'.trunc* r = {!!}



-- -- -- --   toFM2from : ∀ n → retract (fromFM2len n) (toFM2 n)
-- -- -- --   toFM2from n = uncurry λ x y →
-- -- -- --     Σ≡Prop (λ _ → isSetℕ _ _) (toFM2fromFst n x y) 

-- -- -- --   -- toFM2from : ∀ n → retract (fromFM2len n) (toFM2 n)
-- -- -- --   -- toFM2from zero = uncurry {!!}
-- -- -- --   --   where
-- -- -- --   --     r : RElimSet' λ z →
-- -- -- --   --                      (y : len2 z ≡ zero) →
-- -- -- --   --                      fst (toFM2 zero (fromFM2len zero (z , y))) ≡ z 
-- -- -- --   --     RElimSet'.[]* r = λ _ → refl
-- -- -- --   --     (r RElimSet'.∷* x) x₁ = ⊥.rec ∘ ℕsnotz
-- -- -- --   --     RElimSet'.comm* r x y b = funExtDep λ {x₀} → ⊥.rec (ℕsnotz x₀)      
-- -- -- --   --     RElimSet'.trunc* r = {!!}

  
-- -- -- --   -- toFM2from (suc n) = {!!}

-- -- -- --   -- uncurry (RElimSet.f {!!})
-- -- -- --   --   where
-- -- -- --   --     r : RElimSet λ z → (y : len2 z ≡ n) → fst (toFM2 n (fromFM2len n (z , y))) ≡ z
-- -- -- --   --     RElimSet.[]* r = {!!}
-- -- -- --   --     RElimSet._∷*_ r = {!!}
-- -- -- --   --     RElimSet.comm* r = {!!}
-- -- -- --   --     RElimSet.hexDiag* r = {!!}
-- -- -- --   --     RElimSet.trunc* r = {!!}



-- -- -- --   -- inj∷2 : (xs ys : FMSet2 A) → (x : A)
-- -- -- --   --          → x ∷2 xs ≡ x ∷2 ys → xs ≡ ys
-- -- -- --   -- inj∷2 = {!!}

-- -- -- --   -- inj∷2' : ∀ xs (x : A)  → x ∷2 fst (toFM2 (len2 xs) (fromFM2 xs)) ≡ x ∷2 xs
-- -- -- --   --          → fst (toFM2 (len2 xs) (fromFM2 xs)) ≡ xs 
-- -- -- --   -- inj∷2' = {!!}
  
-- -- -- -- --   lem-toFM2from' : ∀ n → (x : A) → (xs : Fin→//↔ n) →
-- -- -- -- --       fst (toFM2 (suc n) (append→ x xs)) ≡
-- -- -- -- --         x ∷2 fst (toFM2 n xs)
-- -- -- -- --   lem-toFM2from' n x = 
-- -- -- -- --     GQ.elimSet _ (λ _ → trunc _ _)
-- -- -- -- --      (λ a → refl)
-- -- -- -- --        (w n)
-- -- -- -- --        where

-- -- -- -- --          w : ∀ n → {a b : Fin n → A} (r : a ↔ₙ b) →
-- -- -- -- --             PathP
-- -- -- -- --                (λ i →
-- -- -- -- --                   fst (toFM2 (suc n) (append→ x (eq// r i))) ≡
-- -- -- -- --                   x ∷2 fst (toFM2 n (eq// r i)))
-- -- -- -- --                (λ _ → fst (toFM2 (suc n) (append→ x [ a ]//)))
-- -- -- -- --                (λ _ → fst (toFM2 (suc n) (append→ x [ b ]//)))
-- -- -- -- --          w n {a} {b} r i j = w' n {a} {b} r j i 

-- -- -- -- --             where



-- -- -- -- --               w''' : ∀ n → (b : Fin (suc n) → A) (e : Fin (suc n) ≃ Fin (suc n))
-- -- -- -- --                             → toFM2≡U (cons→ x b) (sucPerm e) ≡ cong (x ∷2_) (toFM2≡U b e)
-- -- -- -- --               w''' n b e =
-- -- -- -- --                let (e' , p') = unwindPermHead e
-- -- -- -- --                    e0 = fst e zero
-- -- -- -- --                    (e'* , p'*) = unwindPermHead (sucPerm e)

-- -- -- -- --                    ss : Square

-- -- -- -- --                         (λ i → x ∷2 fst (tabulateFM2OfLen
-- -- -- -- --                           λ x₁ → (cons→ x b ∘ fst (p'* i) ) (suc x₁)))

-- -- -- -- --                            refl refl  refl
-- -- -- -- --                    ss i j =
-- -- -- -- --                       x ∷2 fst (tabulateFM2OfLen {n = suc n}
-- -- -- -- --                          λ x₁ → (cons→ x b ∘ compPathRefl {x = fst (sucPerm e)} (~ i) j ) (suc x₁))
                         
-- -- -- -- --                in   ((cong (λ e → fst (tabulateFM2OfLen (λ x' → ((cons→ x b) ∘ fst e) (x')))) p'*)
-- -- -- -- --                          ∙ cong (x ∷2_)
-- -- -- -- --                            (toFM2≡U b (e'*))
-- -- -- -- --                          ∙ toFM2≡Punch zero (cons→ x b))
-- -- -- -- --                   ≡⟨ assoc _ _ _ ∙ sym (rUnit _) ⟩ _
-- -- -- -- --                   ≡⟨ cong 
-- -- -- -- --                       {x =
-- -- -- -- --                         cong
-- -- -- -- --                          {y = fst
-- -- -- -- --                                 (sucPerm (fst (unwindPermHead (sucPerm e))) ∙ₑ
-- -- -- -- --                                  rot≃ (equivFun (sucPerm e) zero))}
-- -- -- -- --                           (fst ∘ tabulateFM2OfLen ∘ ((cons→ x b) ∘_)) (cong fst p'*)}
                      
-- -- -- -- --                          (_∙ (cong (x ∷2_) (toFM2≡U b e'*)))
-- -- -- -- --                          ss

-- -- -- -- --                           ∙ sym (lUnit _) ⟩
-- -- -- -- --                           cong (x ∷2_) (toFM2≡U b e'*)
-- -- -- -- --                   ≡⟨ cong (cong (x ∷2_) ∘ toFM2≡U b) (equivEq refl) ⟩
-- -- -- -- --                    cong (x ∷2_) (toFM2≡U b e) ∎

-- -- -- -- --               w'' : ∀ n → {a b : Fin (suc n) → A} (e : Fin (suc n) ≃ Fin (suc n))
-- -- -- -- --                            (p :  a ≡ b ∘ (fst e)) →
-- -- -- -- --                     Square
-- -- -- -- --                      (cong (fst ∘ (tabulateFM2OfLen)) ((cong (cons→ x)) p)
-- -- -- -- --                         ∙ toFM2≡U (cons→ x b) (sucPerm e))
-- -- -- -- --                      (cong (x ∷2_) --(toFM2≡ (suc n) r)
-- -- -- -- --                        (cong (fst ∘ (tabulateFM2OfLen)) p ∙
-- -- -- -- --                          toFM2≡U b e ) )
-- -- -- -- --                      refl refl
-- -- -- -- --               w'' n {a} {b} e p =
-- -- -- -- --                  cong (cong (fst ∘ (tabulateFM2OfLen)) ((cong (cons→ x)) p) ∙_)
-- -- -- -- --                  (w''' n b e)
-- -- -- -- --                 ∙ sym (cong-∙ (x ∷2_)
-- -- -- -- --                        (cong (fst ∘ (tabulateFM2OfLen)) p)
-- -- -- -- --                        (toFM2≡U b e)) 

-- -- -- -- --               w' : ∀ n → {a b : Fin n → A} (r : a ↔ₙ b) →
-- -- -- -- --                     Square
-- -- -- -- --                      (λ i → fst (toFM2 (suc n) (eq// {a = cons→ x a} {cons→ x b}
-- -- -- -- --                           (prm (sucPerm (_↔ₙ_.F≃ r)) (refl =→ _↔ₙ_.l≡ r)) i)))
-- -- -- -- --                      (cong (x ∷2_) (toFM2≡ n r)) --(λ i → x ∷2 fst (toFM2 n (eq// r i)))
-- -- -- -- --                      refl refl
-- -- -- -- --               w' zero r = cong (refl ∙_) (cong (refl ∙_) (sym compPathRefl)
-- -- -- -- --                              ∙ sym compPathRefl) ∙ sym compPathRefl
-- -- -- -- --               w' (suc n) {a} {b} r@(prm e p) = w'' n e p 

-- -- -- -- --   toFM2-appendComm : ∀ x* y* x → ∀ n → (a : Fin n → A) →
-- -- -- -- --           (λ i → x* ∷2 fst (toFM2 (suc (suc n)) (appendComm y* x [ a ]// i)))
-- -- -- -- --           ≡ cong (x* ∷2_) (comm y* x (fst (tabulateFM2OfLen a) ))
-- -- -- -- --             -- (cong (fst ∘ (tabulateFM2OfLen)) refl ∙ toFM2≡U (cons→ x (cons→ y* a)) swap0and1≃ )
-- -- -- -- --   toFM2-appendComm x* y* x n a =
-- -- -- -- --     cong (cong (x* ∷2_)) (sym (lUnit _) ∙ {!!})

-- -- -- -- --   ss'' : ∀ x* y* x → ∀ n → (xs' : Fin→//↔ n) → Square
-- -- -- -- --         ((cong ((x* ∷2_) ∘ fst ∘ toFM2 (suc (suc n)))
-- -- -- -- --              (appendComm y* x xs')))
-- -- -- -- --         (cong (fst ∘ toFM2 (suc (suc (suc n))))
-- -- -- -- --          (appendComm x* y*
-- -- -- -- --             (append→ x xs')
-- -- -- -- --             -- (fromFM2 (x ∷2 xs)
-- -- -- -- --              -- )
-- -- -- -- --          ))
-- -- -- -- --         (sym (lem-toFM2from' (suc (suc n)) x* (append→ y* (append→ x xs'))))
-- -- -- -- --         (sym (lem-toFM2from' (suc (suc n)) x* (append→ x (append→ y* xs'))) ∙
-- -- -- -- --           cong (fst ∘ toFM2 (suc (suc (suc n))))
-- -- -- -- --           (  appendComm x* x (append→ y* xs')
-- -- -- -- --            ∙ cong (append→ x) (appendComm x* y* xs')
-- -- -- -- --            ∙ appendComm x y* ((append→ x* xs'))
-- -- -- -- --            ∙ cong (append→ y*) (appendComm x x* xs')))
-- -- -- -- --   ss'' x* y* x n = 
-- -- -- -- --     GQ.elimProp _ {!!}
-- -- -- -- --      (∙≡∙→square _ _ _ _ ∘
-- -- -- -- --        λ a →
-- -- -- -- --          (cong ((cong (_∷2_ x* ∘ fst ∘ toFM2 (suc (suc n)))
-- -- -- -- --       (appendComm y* x [ a ]//)) ∙_) (sym (lUnit _))
-- -- -- -- --           ∙ {!!} ∙ {!!}) ∙ lUnit _)
    
  
-- -- -- -- --   toFM2from'comm' : (x : A) (xs : FMSet2 A) →
-- -- -- -- --       ((x₁ y : A) (b : fst (toFM2 (len2 xs) (fromFM2 xs)) ≡ xs) →
-- -- -- -- --        Square
-- -- -- -- --        (lem-toFM2from' (suc (len2 xs)) x₁ (fromFM2 (y ∷2 xs)) ∙
-- -- -- -- --         (λ i →
-- -- -- -- --            x₁ ∷2
-- -- -- -- --            (lem-toFM2from' (len2 xs) y (fromFM2 xs) ∙ (λ i₁ → y ∷2 b i₁)) i))
-- -- -- -- --        (lem-toFM2from' (suc (len2 xs)) y (fromFM2 (x₁ ∷2 xs)) ∙
-- -- -- -- --         (λ i →
-- -- -- -- --            y ∷2
-- -- -- -- --            (lem-toFM2from' (len2 xs) x₁ (fromFM2 xs) ∙ (λ i₁ → x₁ ∷2 b i₁))
-- -- -- -- --            i))
-- -- -- -- --        (λ i →
-- -- -- -- --           fst (toFM2 (suc (suc (len2 xs))) (appendComm x₁ y (fromFM2 xs) i)))
-- -- -- -- --        (comm x₁ y xs)) →
-- -- -- -- --       (x₁ y : A)
-- -- -- -- --       (b : fst (toFM2 (suc (len2 xs)) (fromFM2 (x ∷2 xs))) ≡ x ∷2 xs) →
-- -- -- -- --       Square
-- -- -- -- --       (lem-toFM2from' (suc (suc (len2 xs))) x₁ (fromFM2 (y ∷2 x ∷2 xs)) ∙
-- -- -- -- --        (λ i →
-- -- -- -- --           x₁ ∷2
-- -- -- -- --           (lem-toFM2from' (suc (len2 xs)) y (fromFM2 (x ∷2 xs)) ∙
-- -- -- -- --            (λ i₁ → y ∷2 b i₁))
-- -- -- -- --           i))
-- -- -- -- --       (lem-toFM2from' (suc (suc (len2 xs))) y (fromFM2 (x₁ ∷2 x ∷2 xs)) ∙
-- -- -- -- --        (λ i →
-- -- -- -- --           y ∷2
-- -- -- -- --           (lem-toFM2from' (suc (len2 xs)) x₁ (fromFM2 (x ∷2 xs)) ∙
-- -- -- -- --            (λ i₁ → x₁ ∷2 b i₁))
-- -- -- -- --           i))
-- -- -- -- --       (λ i →
-- -- -- -- --          fst
-- -- -- -- --          (toFM2 (suc (suc (suc (len2 xs))))
-- -- -- -- --           (appendComm x₁ y (fromFM2 (x ∷2 xs)) i)))
-- -- -- -- --       (comm x₁ y (x ∷2 xs))
-- -- -- -- --   toFM2from'comm' x xs P x* y* b i j =
-- -- -- -- --      hcomp
-- -- -- -- --        (λ k → λ {
-- -- -- -- --          (i = i0) → {!!}
-- -- -- -- --         ;(i = i1) → {!!}
-- -- -- -- --         ;(j = i0) → ss k i
-- -- -- -- --         ;(j = i1) → hh' k i
-- -- -- -- --         })
-- -- -- -- --        (x* ∷2 zz i j)

-- -- -- -- --     where
-- -- -- -- --       b' : x ∷2 fst (toFM2 (len2 xs) (fromFM2 xs)) ≡ x ∷2 xs
-- -- -- -- --       b' = sym (lem-toFM2from' (len2 xs) x (fromFM2 xs))  ∙ b

-- -- -- -- --       -- hh : Square
-- -- -- -- --       --         (cong (x ∷2_) (comm x* y* xs))
-- -- -- -- --       --         (comm x* y* (x ∷2 xs))
-- -- -- -- --       --         (comm _ _ _ ∙ cong (x* ∷2_) (comm x y* xs))
-- -- -- -- --       --         (comm _ _ _ ∙ cong (y* ∷2_) (comm x x* xs))
-- -- -- -- --       -- hh = {!!}

-- -- -- -- --       hh' : Square
-- -- -- -- --               (cong (x* ∷2_) (comm y* x xs))
-- -- -- -- --               (comm x* y* (x ∷2 xs))
-- -- -- -- --               refl
-- -- -- -- --               (comm _ _ _ ∙ cong (x ∷2_) (comm _ _ _)
-- -- -- -- --                 ∙ comm _ _ _ ∙ cong (y* ∷2_) (comm _ _ _))
-- -- -- -- --       hh' = {!!}

-- -- -- -- --       ss : Square
-- -- -- -- --             ((cong ((x* ∷2_) ∘ fst ∘ toFM2 (suc (suc (len2 xs))))
-- -- -- -- --                  (appendComm y* x (fromFM2 xs))))
-- -- -- -- --             (cong (fst ∘ toFM2 (suc (suc (suc (len2 xs)))))
-- -- -- -- --              (appendComm x* y*
-- -- -- -- --                 (append→ x (fromFM2 xs))
-- -- -- -- --                 -- (fromFM2 (x ∷2 xs)
-- -- -- -- --                  -- )
-- -- -- -- --              ))
-- -- -- -- --             {!!}
-- -- -- -- --             {!!}
-- -- -- -- --       ss i j = ss'' x* y* x  (len2 xs) (fromFM2 xs) i j

-- -- -- -- --       zz : Square
-- -- -- -- --              _ _
-- -- -- -- --                (cong (fst ∘ toFM2 (suc (suc (len2 xs))))
-- -- -- -- --                  (appendComm y* x (fromFM2 xs)))
-- -- -- -- --                -- (λ i₁ →
-- -- -- -- --                --       fst (toFM2 (suc (suc (len2 xs))) (appendComm y* x (fromFM2 xs) i₁)))
-- -- -- -- --              (comm y* x xs)
-- -- -- -- --       zz = P y* x (inj∷2' xs x b') --(inj∷2 _ _ x b')


-- -- -- -- --      -- where
-- -- -- -- --   --      ss : Square {A = FMSet2 A} (comm x₁ y (x ∷2 xs))
-- -- -- -- --   --                  {!!}
-- -- -- -- --   --                  {!!}
-- -- -- -- --   --                  {!!}
-- -- -- -- --   --      ss = {!!}


-- -- -- -- -- --   toFM2from'comm : (xs : FMSet2 A) (x y : A) 
-- -- -- -- -- --          (b : fst (toFM2 (len2 xs) (fromFM2 xs)) ≡ xs) →
-- -- -- -- -- --          Square
-- -- -- -- -- --          -- (λ i →
-- -- -- -- -- --          --    fst (toFM2 (suc (suc (len2 xs))) (fromFM2 (comm x y xs i))) ≡
-- -- -- -- -- --          --    comm x y xs i)
-- -- -- -- -- --          (lem-toFM2from' (suc (len2 xs)) x (fromFM2 (y ∷2 xs)) ∙
-- -- -- -- -- --           (λ i →
-- -- -- -- -- --              x ∷2
-- -- -- -- -- --              (lem-toFM2from' (len2 xs) y (fromFM2 xs) ∙ (λ i₁ → y ∷2 b i₁)) i))
-- -- -- -- -- --          (lem-toFM2from' (suc (len2 xs)) y (fromFM2 (x ∷2 xs)) ∙
-- -- -- -- -- --           (λ i →
-- -- -- -- -- --              y ∷2
-- -- -- -- -- --              (lem-toFM2from' (len2 xs) x (fromFM2 xs) ∙ (λ i₁ → x ∷2 b i₁)) i))
             
-- -- -- -- -- --          (λ i → fst (toFM2 (suc (suc (len2 xs))) (appendComm x y (fromFM2 xs) i)))

-- -- -- -- -- --          (comm x y xs)
-- -- -- -- -- --   toFM2from'comm = 
-- -- -- -- -- --     FM2.ElimProp.f
-- -- -- -- -- --       {!!}
-- -- -- -- -- --       {!!}
-- -- -- -- -- --       {!!}
-- -- -- -- -- --       -- λ _ → isPropΠ λ _ → {!trunc _ _ _ _!}


-- -- -- -- -- -- --   -- toFM2from' : ∀ (x : FMSet2 A) → (fst (toFM2 (len2 x) (fromFM2 x))) ≡ x
-- -- -- -- -- -- --   -- toFM2from' = FM2.ElimSet.f
-- -- -- -- -- -- --   --   refl
-- -- -- -- -- -- --   --   (λ _ x₁ → (lem-toFM2from' _ _ _) ∙ cong (_ ∷2_) x₁)
-- -- -- -- -- -- --   --   (λ x y {xs} b → toFM2from'comm  x y xs b)
-- -- -- -- -- -- --   --   {!!}
-- -- -- -- -- -- --   --   λ _ → trunc _ _ 


-- -- -- -- -- -- -- --   -- -- subst-Fin→//↔ : ∀ {n m} → (n ≡ m) → Fin→//↔ n → Fin→//↔ m
-- -- -- -- -- -- -- --   -- -- subst-Fin→//↔ x x₁ = {!!}

-- -- -- -- -- -- -- --   -- fromFM2len : ∀ n → FMSet2OfLen A n → Fin→//↔ n 
-- -- -- -- -- -- -- --   -- fromFM2len n (x , p) = subst Fin→//↔ p (fromFM2 x)

-- -- -- -- -- -- -- --   -- fromFM2to : ∀ n → section (fromFM2len n) (toFM2 n)
-- -- -- -- -- -- -- --   -- fromFM2to n =
-- -- -- -- -- -- -- --   --   GQ.elimSet _ (λ _ → squash// _ _)
-- -- -- -- -- -- -- --   --    {!!}
-- -- -- -- -- -- -- --   --    {!!}

-- -- -- -- -- -- -- --   --   where
-- -- -- -- -- -- -- --   --     h : ∀ n → (a : Fin n → A) → fromFM2len n (toFM2 n [ a ]//) ≡ [ a ]//
-- -- -- -- -- -- -- --   --     h zero a = eq// (prm (idEquiv _) =■)
-- -- -- -- -- -- -- --   --     h one a = eq// (FC2M.prm (idEquiv _) (transportRefl _ ∙ {!!} =→ {!!}))
-- -- -- -- -- -- -- --   --     h (suc (suc n)) a = {!!}





-- -- -- -- -- -- -- --   -- lem-toFM2from''0 : ∀ {n m} →  (p : n ≡ m) →  
-- -- -- -- -- -- -- --   --         PathP (λ i → Fin→//↔ (p i) → FMSet2 A)
-- -- -- -- -- -- -- --   --         (fst ∘ (toFM2 n)) (fst ∘ (toFM2 m))
-- -- -- -- -- -- -- --   -- lem-toFM2from''0 {n} = J (λ m (p : n ≡ m) →  
-- -- -- -- -- -- -- --   --         PathP (λ i → Fin→//↔ (p i) → FMSet2 A)
-- -- -- -- -- -- -- --   --         (fst ∘ (toFM2 n)) (fst ∘ (toFM2 m)))
-- -- -- -- -- -- -- --   --         refl

-- -- -- -- -- -- -- --   -- lem-toFM2from'' : (xs : FMSet2 A) → (x : A) →  
-- -- -- -- -- -- -- --   --         PathP (λ i → Fin→//↔ (len2suc x xs i) → FMSet2 A)
-- -- -- -- -- -- -- --   --         (fst ∘ (toFM2 (len2 (x ∷2 xs))))
          
-- -- -- -- -- -- -- --   --         (fst ∘ (toFM2 (suc (len2 xs))))
-- -- -- -- -- -- -- --   -- lem-toFM2from'' xs x = lem-toFM2from''0 (len2suc x xs)

-- -- -- -- -- -- -- -- -- fst (toFM2 (suc (len2 xs)) (fromFM2 (x ∷2 xs))) ≡
-- -- -- -- -- -- -- -- -- fst (toFM2 (suc (len2 xs)) (append→ x (fromFM2 xs)))


-- -- -- -- -- -- -- --   -- toFM2from : ∀ n → retract (fromFM2len n) (toFM2 n)
-- -- -- -- -- -- -- --   -- toFM2from n = {!!}
