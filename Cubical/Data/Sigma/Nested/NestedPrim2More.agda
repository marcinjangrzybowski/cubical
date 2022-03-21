{-# OPTIONS --cubical --no-import-sorts #-}

module Cubical.Data.Sigma.Nested.NestedPrim2More where

open import Cubical.Core.Everything

open import Cubical.Data.Nat
open import Cubical.Data.Sigma


open import Cubical.Foundations.Everything
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma.Nested.Base

open import Cubical.HITs.GroupoidTruncation renaming (elim to Gelim ; rec to Grec)

open import Cubical.Reflection.StrictEquiv

open import Cubical.Data.Sigma.Nested.NestedPrim2


ua-comp  : ∀ {ℓ} → ∀ {A B C : Type ℓ} → (iAB : A ≃ B) → (iBC : B ≃ C) → ua iAB ∙ ua iBC ≡ ua (compEquiv iAB iBC)  
ua-comp {A = A} {B = B} {C = C} iAB iBC =
  sym (invEq≡→equivFun≡ (invEquiv univalence) (equivEq (funExt
      λ x i → transp (λ i → C) i (fst iBC (transp (λ i → B) i (fst iAB (transp (λ i → A) i x)))))))

module _ {ℓ ℓ' : Level} where

  postulate fiberwiseJ : (Ty : ∀ (A B : Type (ℓ-suc ℓ)) (A≃B : A ≃ B) (Ar : A → Type ℓ) (Br : B → Type ℓ) → (∀ b → Ar (equivFun (invEquiv A≃B) b) ≃ Br b) → Type ℓ')
             → (∀ B → (Br : B → Type ℓ) → Ty B B (idEquiv B) Br Br λ b → idEquiv (Br b))
             → ∀ A B A≃B Ar Br Ar≃Br → Ty A B A≃B Ar Br Ar≃Br
  -- fiberwiseJ = {!!}


module _ {ℓ} {C : Type (ℓ-suc ℓ)}  where

  -- lem-penta : (IsoAB : Iso A B)
  --           → (AB-Rec≃ : ∀ a → Ar (equivFun (isoToEquiv (invIso IsoAB)) a) ≃ Br a)
  --           → (AB-RecP-≃ : (∀ a → Ar (equivFun (isoToEquiv (invIso IsoAB)) a) ≃ Br a) ≃ PathP (λ i → isoToPath IsoAB i → Type ℓ) Ar Br)

  --           → Path (Σ A (λ a → Ar a → C) ≡ Σ B (λ a → Br a → C))
  --             (ua (compEquiv (invEquiv (Σ-cong-equiv-fst {B = λ v → Ar v → C} (isoToEquiv (invIso IsoAB))))
  --                            (Σ-cong-equiv-snd λ a → cong≃ (λ X → X → C) (AB-Rec≃ a))
  --                            ))
  --             (
  --             cong {A = Σ (Type (ℓ-suc ℓ)) λ x → x → Type ℓ } (λ a → Σ (fst a) λ x → (snd a) x → C)
  --                   (λ i → (isoToPath IsoAB i) , equivFun (AB-RecP-≃) AB-Rec≃ i))
  -- lem-penta IsoAB AB-Rec≃ AB-RecP-≃ = invEq≡→equivFun≡ (invEquiv univalence) (equivEq (funExt w))
  --    where
  --      w : ∀ x → {!!} ≡ {!!}
  --      w (xx , yy) = ΣPathP ((transportRefl _) ,
  --           toPathP (funExt λ x → cong (transp (λ i → C) i0 ∘ transp (λ i → C) i0)
  --             λ i → yy (ww x i)))
  --         where


  --           -- ww'' : cong Br
  --           --          (λ i → transportRefl (equivFun (isoToEquiv IsoAB) xx) (~ i))
  --           --          ∙
  --           --          ua
  --           --          (invEquiv
  --           --           (AB-Rec≃ (transport (λ _ → B) (equivFun (isoToEquiv IsoAB) xx))))
  --           --          ≡
  --           --          ua (invEquiv (AB-Rec≃ (equivFun (isoToEquiv IsoAB) xx))) ∙
  --           --          cong (λ z → Ar (equivFun (isoToEquiv (invIso IsoAB)) z))
  --           --          (λ i → transportRefl (equivFun (isoToEquiv IsoAB) xx) (~ i))
  --           -- ww'' = sym (homotopyNatural {f = Br}
  --           --                  (λ a → ua (invEquiv (AB-Rec≃ a)))
  --           --                  {equivFun (isoToEquiv IsoAB) xx} {transport refl (equivFun (isoToEquiv IsoAB) xx)}
  --           --                  (sym (transportRefl (equivFun (isoToEquiv IsoAB) xx)))
  --           --                  )

  --           -- ww''2 : cong Br
  --           --           (λ i → transportRefl (equivFun (isoToEquiv IsoAB) xx) (~ i))
  --           --           ∙ funExt⁻ (λ i → fromPathP (equivFun AB-RecP-≃ AB-Rec≃) (~ i)) (transport (λ _ → B) (equivFun (isoToEquiv IsoAB) xx))
  --           --            -- (λ j → equivFun AB-RecP-≃ AB-Rec≃ (~ j) (transp (λ i → isoToPath IsoAB (i ∧ ~ j)) j xx) )
  --           --           ≡
  --           --           funExt⁻ (λ i → fromPathP (equivFun AB-RecP-≃ AB-Rec≃) (~ i))
  --           --           (equivFun (isoToEquiv IsoAB) xx)
  --           --           ∙
  --           --           cong (λ z → transport (λ i → isoToPath IsoAB i → Type ℓ) Ar z)
  --           --           (λ i → transportRefl (equivFun (isoToEquiv IsoAB) xx) (~ i))
  --           -- ww''2 = sym (homotopyNatural {f = Br}
  --           --                  (funExt⁻ (sym (fromPathP (equivFun AB-RecP-≃ AB-Rec≃))))
  --           --                  {equivFun (isoToEquiv IsoAB) xx} {transport refl (equivFun (isoToEquiv IsoAB) xx)}
  --           --                  (sym (transportRefl (equivFun (isoToEquiv IsoAB) xx)))
  --           --                  )

  --           -- zzz : {!!}
  --           -- zzz = {!!}

  --           ww' :  (cong Br (sym (transportRefl (equivFun (isoToEquiv IsoAB) xx)))
  --                         ∙
  --                         (λ j → equivFun AB-RecP-≃ AB-Rec≃ (~ j) (transp (λ i → isoToPath IsoAB (i ∧ ~ j)) j xx) )
  --                      )
  --                        ≡
  --                        {!!}
  --           ww' = (λ ii → (cong Br (sym (transportRefl (equivFun (isoToEquiv IsoAB) xx)))
  --                         ∙
  --                         ((λ j → equivFun AB-RecP-≃ AB-Rec≃ (~ j) (transp (λ i → isoToPath IsoAB (i ∧ ~ j)) j xx) ))
  --                      ))

  --                     ∙ {!!} ∙ {!!}

  --           eee : {!!}
  --           eee = ((AB-Rec≃ (fst (invEquiv (Σ-cong-equiv-fst {B = λ v → Ar v → C} (isoToEquiv (invIso IsoAB))) .fst (xx , yy)))))

  --           ww : (x : Br (equivFun (isoToEquiv IsoAB) xx)) → 
  --                 (transp (λ j → equivFun AB-RecP-≃ AB-Rec≃ (~ j) (transp (λ i → isoToPath IsoAB (i ∧ ~ j)) j xx)) i0
  --                  (transp (λ j → Br (transportRefl (equivFun (isoToEquiv IsoAB) xx) (~ j))) i0 x))
  --                        ≡                         
  --                  (transp (λ j → Ar (snd (equivCtr (isoToEquiv (invIso IsoAB)) xx) j)) i0
  --                   (transp (λ j → ua (AB-Rec≃ (fst (invEquiv (Σ-cong-equiv-fst {B = λ v → Ar v → C} (isoToEquiv (invIso IsoAB))) .fst (xx , yy)))) (~ j)) i0 x))
  --           ww x =
  --              sym (transportComposite (λ j → Br (transportRefl (equivFun (isoToEquiv IsoAB) xx) (~ j)))
  --                                       ((λ j → equivFun AB-RecP-≃ AB-Rec≃ (~ j) (transp (λ i → isoToPath IsoAB (i ∧ ~ j)) j xx)))
  --                                       x)

  --               ∙∙
  --                 {!!}
                  
  --                 -- (λ i → transp (λ j → {! (snd (equivCtr (isoToEquiv (invIso IsoAB)) xx) j)!} j) i0 (equivFun (invEquiv eee) x))
                  
  --               ∙∙
  --                (
  --                   cong (transp (λ j → Ar (snd (equivCtr (isoToEquiv (invIso IsoAB)) xx) j)) i0)
  --                     (sym (uaβ (invEquiv eee) x)
  --                       ∙ (funExt⁻ (transportUaInv eee) x)))
  --               -- transportComposite ((λ j → ua (AB-Rec≃ (fst (invEquiv (Σ-cong-equiv-fst {B = λ v → Ar v → C} (isoToEquiv (invIso IsoAB))) .fst (xx , yy)))) (~ j)))
  --               --             ((λ j → Ar (snd (equivCtr (isoToEquiv (invIso IsoAB)) xx) j))) x



  lem-pentaApp : (A B : Type (ℓ-suc ℓ)) (IsoAB : A ≃ B ) → (Ar : A → Type ℓ) → (Br : B → Type ℓ)
            → (AB-Rec≃ : ∀ a → Ar (equivFun ( (invEquiv IsoAB)) a) ≃ Br a)
            → 

              (ua (compEquiv (invEquiv (Σ-cong-equiv-fst (invEquiv IsoAB)))
                             (Σ-cong-equiv-snd λ a → cong≃ (λ X → X → C) (AB-Rec≃ a))
                             ))
              ≡ 
              cong {A = Σ (Type (ℓ-suc ℓ)) λ x → x → Type ℓ } (λ a → Σ (fst a) λ x → (snd a) x → C)
                    (λ i → (ua (IsoAB) i) , (over-≃-fun (IsoAB) Ar _) AB-Rec≃  i)
  lem-pentaApp =
    fiberwiseJ
    (λ (A B : Type (ℓ-suc ℓ)) (IsoAB : A ≃ B ) (Ar : A → Type ℓ) (Br : B → Type ℓ) (AB-Rec≃ : ∀ a → Ar (equivFun ( (invEquiv IsoAB)) a) ≃ Br a)
            → 

              (ua (compEquiv (invEquiv (Σ-cong-equiv-fst (invEquiv IsoAB)))
                             (Σ-cong-equiv-snd λ a → cong≃ (λ X → X → C) (AB-Rec≃ a))
                             ))
              ≡ 
              cong {A = Σ (Type (ℓ-suc ℓ)) λ x → x → Type ℓ } (λ a → Σ (fst a) λ x → (snd a) x → C)
                    (λ i → (ua (IsoAB) i) , (over-≃-fun (IsoAB) Ar _) AB-Rec≃  i))
    w
     where
        w : (B : Type (ℓ-suc ℓ)) (Br : B → Type ℓ) →
              ua
              (compEquiv (invEquiv (Σ-cong-equiv-fst (invEquiv (idEquiv B))))
               (Σ-cong-equiv-snd (λ a → cong≃ (λ X → X → C) (idEquiv (Br a)))))
              ≡
              (λ i →
                 Σ (ua (idEquiv B) i)
                 (λ x →
                    over-≃-fun (idEquiv B) Br (λ z → Br z) (λ b → idEquiv (Br b)) i x →
                    C))
        w B Br = sym (ua-comp _ _) ∙
                 cong (_∙ (ua (Σ-cong-equiv-snd (λ a → cong≃ (λ X → X → C) (idEquiv (Br (equivFun (invEquiv (idEquiv B)) a)))))))
                    (((cong ua (equivEq (funExt λ x → ΣPathP (refl , (funExt (λ x₁ → transportRefl _ ∙ cong (snd x) (transportRefl _))))))) ∙ uaIdEquiv))
                  ∙ ( (sym (lUnit (ua ((Σ-cong-equiv-snd (λ a → cong≃ (λ X → X → C) (_)))))))
                    ∙∙ ww''
                    ∙∙ (((λ _ → cong (Σ B) λ i a → ua (AB-Rec≃ a) i → C)) ∙ ww*))
            where

               AB-Rec≃ : ∀ a → Br (equivFun ( (invEquiv (idEquiv (B)))) a) ≃ Br a
               AB-Rec≃ a = idEquiv (Br (equivFun (invEquiv (idEquiv B)) a))

              
               ww'' : ua
                        (Σ-cong-equiv-snd
                         (λ a →
                            cong≃ (λ X → X → C)
                            (fst (idEquiv (Br (equivFun (invEquiv (idEquiv B)) a))) ,
                             snd (idEquiv (Br (equivFun (invEquiv (idEquiv B)) a))))))
                        ≡ λ i → Σ B (λ a → ua (AB-Rec≃ a) i → C)
               ww'' = isInjectiveTransport (funExt λ x → ΣPathP (refl ,
                       (funExt (λ x₁ → transportRefl _ ∙ cong (λ a → transp (λ i → C) i0 (snd x (fst (fst (AB-Rec≃ (fst x) .snd .equiv-proof a))))) (transportRefl _)))))


               -- ww*0 : {!!}
               -- ww*0 = isInjectiveTransport (funExt λ x → ΣPathP (refl , funExt λ x₁ → {!!} ∙ sym (transportRefl _)))

               ww* : (λ i → Σ B (λ a → ua (AB-Rec≃ a) i → C)) ≡
                       (λ i →
                          Σ (ua (idEquiv B) i)
                          (λ x →  over-≃-fun (idEquiv B) Br Br (λ b → idEquiv (Br b)) i x → C))
               ww* = cong {A = Σ (B ≡ B) λ x → PathP (λ i → (x) i → Type ℓ) Br Br} {B = λ _ → Σ B (λ v → ua (AB-Rec≃ v) i0 → C) ≡   Σ B (λ v → ua (AB-Rec≃ v) i1 → C)}
                        {y = (λ i → ua (idEquiv B) i) ,
                               (λ i z → over-≃-fun (idEquiv B) Br Br AB-Rec≃ i z)}
                       (λ a i → Σ ((fst a) i) λ x →  snd a i x → C) (ΣPathP (refl {x = λ i → refl {x = B} i}, sym (www ∙ www*))
                       
                            ∙ ΣPathP (sym (uaIdEquiv {A = B}) , (symP (transport-filler (λ i → PathP (λ i₁ → uaIdEquiv {A = B} (i) i₁ → Type ℓ) Br Br)
                                      (λ i z → over-≃-fun (idEquiv B) Br Br AB-Rec≃ i z)))))
                    where
                    
                      www* : refl
                              ≡
                             (λ i z → ua (idEquiv (Br (equivFun (invEquiv (idEquiv B)) z))) i)
                      www* i i₁ z = uaIdEquiv {A = Br z} (~ i ) i₁


                      www' : transport (λ i → PathP (λ i₁ → uaIdEquiv {A = B} i i₁ → Type ℓ) Br Br)
                               (transport (λ i → PathP (λ i₁ → (uaIdEquiv {A = B} (~ i)) i₁ → Type ℓ) Br Br) refl)
                              ≡
                             refl
                      www' = transportTransport⁻ (λ i → PathP (λ i₁ → uaIdEquiv {A = B} i i₁ → Type ℓ) Br Br) _ 


                      www : transport (λ i → PathP (λ i₁ → uaIdEquiv {A = B} i i₁ → Type ℓ) Br Br) ((over-≃-fun (idEquiv B) Br Br AB-Rec≃))
                              ≡
                             refl
                      www i i₁ zz = {!!}


           
      

-- i = i0 ⊢ transport
--          (λ i₂ → PathP (λ i₃ → uaIdEquiv i₂ i₃ → Type ℓ) Br Br)
--          (over-≃-fun (idEquiv B) Br Br AB-Rec≃) i₁ x
-- i = i1 ⊢ ua (AB-Rec≃ x) i₁
-- i₁ = i0 ⊢ Br x
-- i₁ = i1 ⊢ Br x
                     

-- i = i0 ⊢ Σ B (λ a → ua (AB-Rec≃ a) i₁ → C)
-- i = i1 ⊢ Σ (ua (idEquiv B) i₁)
--          (λ x →
--             over-≃-fun (idEquiv B) Br Br (λ b → idEquiv (Br b)) i₁ x → C)
-- i₁ = i0 ⊢ Σ B (λ a → Br (equivFun (invEquiv (idEquiv B)) a) → C)
-- i₁ = i1 ⊢ Σ B (λ a → Br a → C)

  -- lem-pentaApp : (IsoAB : A ≃ B ) → (Ar : A → Type ℓ)
  --           → (AB-Rec≃ : ∀ a → Ar (equivFun ( (invEquiv IsoAB)) a) ≃ Br a)

  --           → 

  --             (ua (compEquiv (invEquiv (Σ-cong-equiv-fst (invEquiv IsoAB)))
  --                            (Σ-cong-equiv-snd λ a → cong≃ (λ X → X → C) (AB-Rec≃ a))
  --                            ))
  --             ≡ 
  --             cong {A = Σ (Type (ℓ-suc ℓ)) λ x → x → Type ℓ } (λ a → Σ (fst a) λ x → (snd a) x → C)
  --                   (λ i → (ua (IsoAB) i) , (over-≃-fun (IsoAB) Ar _) AB-Rec≃  i)
  -- lem-pentaApp =
  --     EquivJ (λ A IsoAB → (Ar : A → Type ℓ) → (AB-Rec≃ : ∀ a → Ar (equivFun ( (invEquiv IsoAB)) a) ≃ Br a)

  --           → 

  --             (ua (compEquiv (invEquiv (Σ-cong-equiv-fst (invEquiv IsoAB)))
  --                            (Σ-cong-equiv-snd λ a → cong≃ (λ X → X → C) (AB-Rec≃ a))
  --                            ))
  --             ≡ 
  --             cong {A = Σ (Type (ℓ-suc ℓ)) λ x → x → Type ℓ } (λ a → Σ (fst a) λ x → (snd a) x → C)
  --                   (λ i → (ua (IsoAB) i) , (over-≃-fun (IsoAB) Ar _) AB-Rec≃  i))
  --         w
  --     where
  --       w : (Ar : B → Type ℓ)
  --             (AB-Rec≃
  --              : (a : B) → Ar (equivFun (invEquiv (idEquiv B)) a) ≃ Br a) →
  --             ua
  --             (compEquiv (invEquiv (Σ-cong-equiv-fst (invEquiv (idEquiv B)))) (Σ-cong-equiv-snd (λ a → cong≃ (λ X → X → C) (AB-Rec≃ a))))
  --             ≡
  --             (λ i → Σ (ua (idEquiv B) i) (λ x → over-≃-fun (idEquiv B) Ar Br AB-Rec≃ i x → C))
  --       w Ar AB-Rec≃ = 
  --               sym (ua-comp _ _) ∙
  --                cong (_∙ (ua (Σ-cong-equiv-snd (λ a → cong≃ (λ X → X → C) (AB-Rec≃ a)))))
  --                  ((cong ua ww) ∙ uaIdEquiv) ∙∙ (sym (lUnit (ua ((Σ-cong-equiv-snd (λ a → cong≃ (λ X → X → C) (AB-Rec≃ a)))))))
  --                  ∙∙  (ww'' ∙∙ (λ _ → cong (Σ B) λ i a → ua (AB-Rec≃ a) i → C) ∙∙ ww*)
  --        -- ua (Σ-cong-equiv-snd (λ a → cong≃ (λ X → X → C) (AB-Rec≃ a)))
  --          where
  --            AR≡BR : Ar ≡ Br
  --            AR≡BR = funExt λ x → ua (AB-Rec≃ x)


  --            ww : _
  --            ww = equivEq (funExt λ x → ΣPathP (refl , (funExt (λ x₁ → transportRefl _ ∙ cong (snd x) (transportRefl _)))))

  --            ww'' : _
  --            ww'' = isInjectiveTransport (funExt λ x → ΣPathP (refl ,
  --               (funExt (λ x₁ → transportRefl _ ∙ cong (λ a → transp (λ i → C) i0 (snd x (fst (fst (AB-Rec≃ (fst x) .snd .equiv-proof a))))) (transportRefl _)))))


  --            ww* : _≡_ {A = Σ B (λ v → ua (AB-Rec≃ v) i0 → C) ≡
  --                             Σ B (λ v → ua (AB-Rec≃ v) i1 → C)} (λ i → Σ B (λ a → ua (AB-Rec≃ a) i → C))
  --                    (λ i → Σ (ua (idEquiv B) i) (λ x → over-≃-fun (idEquiv B) Ar Br AB-Rec≃ i x → C))
  --            ww* =  cong {A = Σ (B ≡ B) λ x → PathP (λ i → (x) i → Type ℓ) Ar Br} {B = λ _ → Σ B (λ v → ua (AB-Rec≃ v) i0 → C) ≡   Σ B (λ v → ua (AB-Rec≃ v) i1 → C)}
  --                       {y = (λ i → ua (idEquiv B) i) ,
  --                              (λ i z → over-≃-fun (idEquiv B) Ar Br AB-Rec≃ i z)}
  --                      (λ a i → Σ ((fst a) i) λ x →  snd a i x → C) (ΣPathP (refl {x = λ i → refl {x = B} i}, sym www)
  --                           ∙ ΣPathP (sym (uaIdEquiv {A = B}) , (symP (transport-filler (λ i → PathP (λ i₁ → uaIdEquiv {A = B} (i) i₁ → Type ℓ) Ar Br) (λ i z → over-≃-fun (idEquiv B) Ar Br AB-Rec≃ i z)))))
  --               where
  --                 www : transport (λ i → PathP (λ i₁ → uaIdEquiv {A = B} i i₁ → Type ℓ) Ar Br) (over-≃-fun (idEquiv B) Ar Br AB-Rec≃)
  --                         ≡
  --                        (λ i z → ua (AB-Rec≃ z) i)
  --                 www  = {!!}






                       -- i = i0 ⊢ transport (λ i₂ → PathP (λ i₃ → refl i₃ → Type ℓ) Ar Br)
                       --          (λ i₂ z → ua (AB-Rec≃ z) i₂) i₁ x
                       -- i = i1 ⊢ transport
                       --          (λ i₂ → PathP (λ i₃ → uaIdEquiv i₂ i₃ → Type ℓ) Ar Br)
                       --          (λ i₂ z → over-≃-fun (idEquiv B) Ar Br AB-Rec≃ i₂ z) i₁ x
                       -- i₁ = i0 ⊢ Ar x
                       -- i₁ = i1 ⊢ Br x
           --  sym (ua-comp _ _) ∙ {!!}

           -- where
           --    ww : ua
           --               (Iso.fun
           --                (Σ-cong-iso-snd
           --                 (λ x → equivToIso (cong≃ (λ X → X → C) (AB-Rec≃ x))))
           --                ,
           --                isoToIsEquiv
           --                (Σ-cong-iso-snd
           --                 (λ x → equivToIso (cong≃ (λ X → X → C) (AB-Rec≃ x)))))
           --               ≡
           --               (λ i →
           --                  Σ (ua (idEquiv B) i)
           --                  (λ x → over-≃-fun (idEquiv B) Ar Br AB-Rec≃ i x → C))
           --    ww = isInjectiveTransport (funExt λ x → ΣPathP (refl , (funExt (λ x₁ → {!!}))))

--   -- invEq≡→equivFun≡ (invEquiv univalence) (equivEq (funExt w))
--      -- where
--      --   w : ∀ x → {!!} ≡ {!!}
--      --   w (xx , yy) = ΣPathP ((transportRefl _) ,
--      --        toPathP (funExt λ x → cong (transp (λ i → C) i0 ∘ transp (λ i → C) i0)
--      --          λ i → yy (ww x i)))
--      --      where


--      --        -- ww'' : cong Br
--      --        --          (λ i → transportRefl (equivFun (isoToEquiv IsoAB) xx) (~ i))
--      --        --          ∙
--      --        --          ua
--      --        --          (invEquiv
--      --        --           (AB-Rec≃ (transport (λ _ → B) (equivFun (isoToEquiv IsoAB) xx))))
--      --        --          ≡
--      --        --          ua (invEquiv (AB-Rec≃ (equivFun (isoToEquiv IsoAB) xx))) ∙
--      --        --          cong (λ z → Ar (equivFun (isoToEquiv (invIso IsoAB)) z))
--      --        --          (λ i → transportRefl (equivFun (isoToEquiv IsoAB) xx) (~ i))
--      --        -- ww'' = sym (homotopyNatural {f = Br}
--      --        --                  (λ a → ua (invEquiv (AB-Rec≃ a)))
--      --        --                  {equivFun (isoToEquiv IsoAB) xx} {transport refl (equivFun (isoToEquiv IsoAB) xx)}
--      --        --                  (sym (transportRefl (equivFun (isoToEquiv IsoAB) xx)))
--      --        --                  )

--      --        -- ww''2 : cong Br
--      --        --           (λ i → transportRefl (equivFun (isoToEquiv IsoAB) xx) (~ i))
--      --        --           ∙ funExt⁻ (λ i → fromPathP (equivFun AB-RecP-≃ AB-Rec≃) (~ i)) (transport (λ _ → B) (equivFun (isoToEquiv IsoAB) xx))
--      --        --            -- (λ j → equivFun AB-RecP-≃ AB-Rec≃ (~ j) (transp (λ i → isoToPath IsoAB (i ∧ ~ j)) j xx) )
--      --        --           ≡
--      --        --           funExt⁻ (λ i → fromPathP (equivFun AB-RecP-≃ AB-Rec≃) (~ i))
--      --        --           (equivFun (isoToEquiv IsoAB) xx)
--      --        --           ∙
--      --        --           cong (λ z → transport (λ i → isoToPath IsoAB i → Type ℓ) Ar z)
--      --        --           (λ i → transportRefl (equivFun (isoToEquiv IsoAB) xx) (~ i))
--      --        -- ww''2 = sym (homotopyNatural {f = Br}
--      --        --                  (funExt⁻ (sym (fromPathP (equivFun AB-RecP-≃ AB-Rec≃))))
--      --        --                  {equivFun (isoToEquiv IsoAB) xx} {transport refl (equivFun (isoToEquiv IsoAB) xx)}
--      --        --                  (sym (transportRefl (equivFun (isoToEquiv IsoAB) xx)))
--      --        --                  )

--      --        -- zzz : {!!}
--      --        -- zzz = {!!}
--      --        off = over-≃-fun (isoToEquiv IsoAB) Ar Br

--      --        ww' :  (cong Br (sym (transportRefl (equivFun (isoToEquiv IsoAB) xx)))
--      --                      ∙
--      --                      (λ j → off AB-Rec≃ (~ j) (transp (λ i → isoToPath IsoAB (i ∧ ~ j)) j xx) )
--      --                   )
--      --                     ≡
--      --                     {!!}
--      --        ww' = (λ ii → (cong Br (sym (transportRefl (equivFun (isoToEquiv IsoAB) xx)))
--      --                      ∙
--      --                      ((λ j → off AB-Rec≃ (~ j) (transp (λ i → isoToPath IsoAB (i ∧ ~ j)) j xx) ))
--      --                   ))

--      --                  ∙ {!!} ∙ {!!}

--      --        eee : {!!}
--      --        eee = ((AB-Rec≃ (fst (invEquiv (Σ-cong-equiv-fst {B = λ v → Ar v → C} (isoToEquiv (invIso IsoAB))) .fst (xx , yy)))))

--      --        ww : (x : Br (equivFun (isoToEquiv IsoAB) xx)) → 
--      --              (transp (λ j → off AB-Rec≃ (~ j) (transp (λ i → isoToPath IsoAB (i ∧ ~ j)) j xx)) i0
--      --               (transp (λ j → Br (transportRefl (equivFun (isoToEquiv IsoAB) xx) (~ j))) i0 x))
--      --                     ≡                         
--      --               (transp (λ j → Ar (snd (equivCtr (isoToEquiv (invIso IsoAB)) xx) j)) i0
--      --                (transp (λ j → ua (AB-Rec≃ (fst (invEquiv (Σ-cong-equiv-fst {B = λ v → Ar v → C} (isoToEquiv (invIso IsoAB))) .fst (xx , yy)))) (~ j)) i0 x))
--      --        ww x =
--      --           sym (transportComposite (λ j → Br (transportRefl (equivFun (isoToEquiv IsoAB) xx) (~ j)))
--      --                                    ((λ j → off AB-Rec≃ (~ j) (transp (λ i → isoToPath IsoAB (i ∧ ~ j)) j xx)))
--      --                                    x)

--      --            ∙∙
--      --              {!!}
                  
--      --              -- (λ i → transp (λ j → {! (snd (equivCtr (isoToEquiv (invIso IsoAB)) xx) j)!} j) i0 (equivFun (invEquiv eee) x))
                  
--      --            ∙∙
--      --             (
--      --                cong (transp (λ j → Ar (snd (equivCtr (isoToEquiv (invIso IsoAB)) xx) j)) i0)
--      --                  (sym (uaβ (invEquiv eee) x)
--      --                    ∙ (funExt⁻ (transportUaInv eee) x)))
--      --            -- transportComposite ((λ j → ua (AB-Rec≃ (fst (invEquiv (Σ-cong-equiv-fst {B = λ v → Ar v → C} (isoToEquiv (invIso IsoAB))) .fst (xx , yy)))) (~ j)))
--      --            --             ((λ j → Ar (snd (equivCtr (isoToEquiv (invIso IsoAB)) xx) j))) x







-- isoToPath≡ua∘isoToEquiv : ∀ {ℓ} → ∀ {A B : Type ℓ} → Path (Iso A B → A ≡ B) isoToPath (ua ∘ isoToEquiv)
-- isoToPath≡ua∘isoToEquiv = refl



-- module _ {ℓ} {A B C D : Type (ℓ-suc ℓ)} (Ar : A → Type ℓ) (Br : B → Type ℓ) (Cr : C → Type ℓ) (Dr : D → Type ℓ) where



--   hlp1 : Σ
--            (Σ (Σ A (λ a → Ar a → B))
--             (λ x → Σ (Ar (fst x)) (λ x₁ → Br (snd x x₁)) → C))
--            ((λ x₄ → Σ (Σ (Ar (fst (fst x₄))) (λ x₅ → Br (snd (fst x₄) x₅))) (λ x₅ → Cr (snd x₄ x₅)) → D))
--            ≃
--            Σ (Σ A (λ a → Ar a → Σ B (λ x → Br x → C)))
--            (λ a → Σ (Ar (fst a)) (λ a₁ → Σ  (Br (fst (snd a a₁))) (Cr ∘ snd (snd a a₁))) → D)
--   hlp1 = compEquiv (invEquiv (Σ-cong-equiv-fst (invEquiv (((assoc-Σ-curry Ar Br Cr ))))))
--                           (Σ-cong-equiv-snd {B = λ (a : Σ A (λ v → Ar v → Σ B (λ x → Br x → C))) →
--                                                      Σ (Σ (Ar (fst a)) (λ z → Br (fst (snd a z))))
--                                                      (λ xx →
--                                                         Cr (snd (snd a (fst xx)) (snd xx))) →
--                                                      D} λ a → cong≃ (λ X → X → D) Σ-assoc-≃)

--   -- penta-Σ-curry-≃ :
--   --                Path ( (Σ
--   --                                 (Σ (Σ A (λ x₄ → Ar x₄ → B))
--   --                                  (λ x₄ →
--   --                                     Σ (Ar (fst x₄)) (λ x₅ → Br (snd x₄ x₅)) → C))
--   --                                 (λ x₄ →
--   --                                    Σ
--   --                                    (Σ (Ar (fst (fst x₄))) (λ x₅ → Br (snd (fst x₄) x₅)))
--   --                                    (λ x₅ → Cr (snd x₄ x₅)) →
--   --                                    D))
--   --                        ≃  (Σ A
--   --                                 (λ x₄ →
--   --                                    Ar x₄ →
--   --                                    Σ B
--   --                                    (λ x₅ →
--   --                                       Br x₅ → Σ C (λ x₆ → Cr x₆ → D)))))
--   --                  (compEquiv ((assoc-Σ-curry _ _ Dr )) ((assoc-Σ-curry _ (λ v → Br v) λ x → Σ (Cr (fst x)) λ x₁ → Dr (snd x x₁))) )
--   --                   (compEquiv hlp1
--   --                        (compEquiv ((assoc-Σ-curry Ar (λ z → Σ (Br (fst z)) (λ x₁ → Cr (snd z x₁))) Dr))
--   --                                 (Σ-cong-equiv-snd λ a → equivΠCod λ a₁ → (assoc-Σ-curry _ _ Dr))))
--   -- penta-Σ-curry-≃ = equivEq (funExt w)

--   --    where
--   --      w : _
--   --      fst (w (((fst₁ , snd₃) , snd₂) , snd₁) i) = fst₁
--   --      fst (snd (w (((fst₁ , snd₃) , snd₂) , snd₁) i) x) = snd₃ x
--   --      fst (snd (snd (w (((fst₁ , snd₃) , snd₂) , snd₁) i) x) x₁) = snd₂ (x , x₁)
--   --      snd (snd (snd (w (((fst₁ , snd₃) , snd₂) , snd₁) i) x) x₁) x₂ =
            
--   --        transp (λ i₁ → D) (~ i)
--   --          (transp (λ i₁ → D) (~ i) (snd₁ ((transp
--   --                         (λ j → Σ (Σ (Ar fst₁) (λ x₅ → Br (snd₃ x₅))) (λ x₅ → Cr (snd₂ (fst x₅ , snd x₅))))
--   --                          (~ i) (((transp (λ i₁ → Ar fst₁) (~ i) x) , (transp (λ i₁ → Br (snd₃ (transp (λ i₂ → Ar fst₁) (~ i₁ ∨ (~ i)) x))) (~ i) x₁))
--   --                             , transp
--   --                               (λ i₁ →
--   --                                  Cr
--   --                                  (snd₂
--   --                                   (transp (λ i₂ → Ar fst₁) (~ i₁ ∨ (~ i)) x ,
--   --                                    transp (λ i₂ → Br (snd₃ (transp (λ i₃ → Ar fst₁) (~ i₂ ∨ ~ i₁ ∨ (~ i)) x)))
--   --                                    (~ i₁ ∨ (~ i)) x₁)))
--   --                               (~ i) x₂)))) )


--   lemL : ua (compEquiv (invEquiv (Σ-cong-equiv-fst (invEquiv (((assoc-Σ-curry Ar Br Cr ))))))
--                           (Σ-cong-equiv-snd {B = λ (a : Σ A (λ v → Ar v → Σ B (λ x → Br x → C))) →
--                                                      Σ (Σ (Ar (fst a)) (λ z → Br (fst (snd a z))))
--                                                      (λ xx →
--                                                         Cr (snd (snd a (fst xx)) (snd xx))) →
--                                                      D} λ a → cong≃ (λ X → X → D) (assoc-Σ-curryΣ- Ar Br Cr a)))
--                 ≡ cong {A = Σ (Type (ℓ-suc ℓ)) λ x → x → Type ℓ } (λ a → Σ (fst a) λ x → (snd a) x → D)
--                     (λ i → (ua ((assoc-Σ-curry Ar Br Cr)) i) , (over-≃-fun (assoc-Σ-curry Ar Br Cr) (Ty0 Ar Br Cr) (Ty1 Ar Br Cr) (assoc-Σ-curryΣ- Ar Br Cr)) i)
--   lemL = {!lem-pentaApp {C = D} (Ty0 Ar Br Cr) (Ty1 Ar Br Cr) ((assoc-Σ-curry Ar Br Cr)) (assoc-Σ-curryΣ- Ar Br Cr)!}
--               -- ∙ cong (cong (λ a → Σ (fst a) (λ x → snd a x → D))) {!!} --lem-pentaApp (Ty0 Ar Br Cr) (Ty1 Ar Br Cr) ((assoc-Σ-curry Ar Br Cr)) (assoc-Σ-curryΣ- Ar Br Cr)
-- --     -- where
-- --     --   w' : (x : Σ
-- --     --              (Σ (Σ A (λ a → Ar a → B))
-- --     --               (λ x → Σ (Ar (fst x)) (λ x₁ → Br (snd x x₁)) → C))
-- --     --              (λ x₄ →
-- --     --                 Σ (Σ (Ar (fst (fst x₄))) (λ x₅ → Br (snd (fst x₄) x₅)))
-- --     --                 (λ x₅ → Cr (snd x₄ x₅)) →
-- --     --                 D))
-- --     --         → invEq (invEquiv univalence)
-- --     --             ({!!})
-- --     --             .fst x
-- --     --             ≡
-- --     --             Σ-cong-equiv-snd (λ a → cong≃ (λ X → X → D) Σ-assoc-≃) .fst
-- --     --             (invEquiv
-- --     --              (Σ-cong-equiv-fst (isoToEquiv (invIso (assoc-Σ-curry Ar Br Cr))))
-- --     --              .fst x)
-- --     --   w' x = {!!}

-- --     --   w : (x : Σ
-- --     --              (Σ (Σ A (λ a → Ar a → B))
-- --     --               (λ x → Σ (Ar (fst x)) (λ x₁ → Br (snd x x₁)) → C))
-- --     --              (λ x₄ →
-- --     --                 Σ (Σ (Ar (fst (fst x₄))) (λ x₅ → Br (snd (fst x₄) x₅)))
-- --     --                 (λ x₅ → Cr (snd x₄ x₅)) →
-- --     --                 D))
-- --     --         → invEq (invEquiv univalence)
-- --     --             (cong (λ (a : Σ (Type (ℓ-suc ℓ)) (λ X → X → Type ℓ)) → Σ (fst a) (λ x₁ → snd a x₁ → D))
-- --     --              (λ i →
-- --     --                 isoToPath (assoc-Σ-curry Ar Br Cr) i , assoc-Σ-curryP Ar Br Cr i))
-- --     --             .fst x
-- --     --             ≡
-- --     --             Σ-cong-equiv-snd (λ a → cong≃ (λ X → X → D) Σ-assoc-≃) .fst
-- --     --             (invEquiv
-- --     --              (Σ-cong-equiv-fst (isoToEquiv (invIso (assoc-Σ-curry Ar Br Cr))))
-- --     --              .fst x)
-- --     --   w (x , snd₁) = {!!}


--   -- lemR : ∀ {B C : Type (ℓ-suc ℓ)} → (Iso-BC : B ≃ C) → ua (Σ-cong-equiv-snd λ a → equivΠCod λ a₁ →  Iso-BC)
--   --          ≡
--   --        (cong (Σ A) (funExt λ y → cong (λ x → Ar y → x) (ua Iso-BC)))
--   -- lemR B≃C = isInjectiveTransport (funExt λ x → ΣPathP (refl , funExt λ x₁ → refl)) 


--   -- penta-Σ-curry :
--   --                Path ( (Σ
--   --                                 (Σ (Σ A (λ x₄ → Ar x₄ → B))
--   --                                  (λ x₄ →
--   --                                     Σ (Ar (fst x₄)) (λ x₅ → Br (snd x₄ x₅)) → C))
--   --                                 (λ x₄ →
--   --                                    Σ
--   --                                    (Σ (Ar (fst (fst x₄))) (λ x₅ → Br (snd (fst x₄) x₅)))
--   --                                    (λ x₅ → Cr (snd x₄ x₅)) →
--   --                                    D))
--   --                        ≡  (Σ A
--   --                                 (λ x₄ →
--   --                                    Ar x₄ →
--   --                                    Σ B
--   --                                    (λ x₅ →
--   --                                       Br x₅ → Σ C (λ x₆ → Cr x₆ → D)))))
--   --                  (ua (assoc-Σ-curry _ _ Dr ) ∙  ua (assoc-Σ-curry _ (λ v → Br v) λ x → Σ (Cr (fst x)) λ x₁ → Dr (snd x x₁)) )
                    
--   --                   (cong {A = Σ (Type (ℓ-suc ℓ)) λ x → x → Type ℓ } (λ (a : Σ (Type (ℓ-suc ℓ)) (λ x → x → Type ℓ)) → Σ (fst a) λ x → (snd a) x → D)
--   --                       (λ i → (ua (assoc-Σ-curry Ar Br Cr) i) , assoc-Σ-curryP Ar Br Cr i)

--   --                      ∙∙ ua (assoc-Σ-curry Ar (λ z → Σ (Br (fst z)) (λ x₁ → Cr (snd z x₁))) Dr)
--   --                         ∙∙ cong (Σ A) (funExt λ y → cong (λ x → Ar y → x) (ua (assoc-Σ-curry _ _ Dr))))
--   -- penta-Σ-curry = 
  
--   --     (ua-comp _ _)
--   --     ∙∙ cong ua penta-Σ-curry-≃ ∙∙ 
--   --     ((sym (ua-comp _ _) ∙ cong (ua (hlp1) ∙_) (sym (ua-comp _ _)))     
--   --     ∙∙
--   --     sym (doubleCompPath-elim' _ _ _)
--   --     -- (λ i j → ( {!!} ∙ ((isoToPath (assoc-Σ-curry Ar (λ z → Σ (Br (fst z)) (λ x₁ → Cr (snd z x₁))) Dr)) ∙ {!refl i!})) j )
--   --     ∙∙
--   --     (cong₂ {C = λ _ _ → _ ≡ (Σ A
--   --                                 (λ x₄ →
--   --                                    Ar x₄ →
--   --                                    Σ B
--   --                                    (λ x₅ →
--   --                                       Br x₅ → Σ C (λ x₆ → Cr x₆ → D))))}
--   --               (_∙∙ (ua (assoc-Σ-curry Ar (λ z → Σ (Br (fst z)) (λ x₁ → Cr (snd z x₁))) Dr)) ∙∙_) lemL (lemR (assoc-Σ-curry Br Cr Dr)))
--   --     )

-- -- module _ {ℓ} where


-- --   ParSig : Par → Type (ℓ-suc ℓ) 
-- --   ParRec : (p : Par) → ParSig p → Type ℓ

-- --   ParSig □ = Type ℓ
-- --   ParSig [- x - y -] = Σ (ParSig x) λ x₁ → ParRec x x₁ → ParSig y
-- --   ParSig (assocPar x x₁ x₂ i) = ua (assoc-Σ-curry (ParRec x ) (ParRec x₁) (ParRec x₂)) i
-- --   ParSig (pentaPar x x₁ x₂ x₃ i j) = penta-Σ-curry (ParRec x ) (ParRec x₁) (ParRec x₂) (ParRec x₃) i j 
  
-- --   ParRec □ x = x
-- --   ParRec [- p - p₁ -] x = Σ (ParRec p (fst x)) (ParRec p₁ ∘ snd x)
-- --   ParRec (assocPar x x₁ x₂ i) = assoc-Σ-curryP (ParRec x ) (ParRec x₁) (ParRec x₂) i
-- --   ParRec (pentaPar x x₁ x₂ x₃ i j) = {!!}

-- --   gtr : (x : ∥ Par ∥₃) → Σ (hSet ℓ) λ x₁ → (fst x₁) → hSet ℓ
-- --   gtr = Grec (isOfHLevelΣ 3 isGroupoidHSet λ _ → isOfHLevelΠ 3 λ _ → isGroupoidHSet)
-- --        {!!}

  
-- -- -- ParRec : ∀ {ℓ} → {p : Par} → ParSig ℓ p → Type ℓ


-- -- -- ParSig ℓ □ = Type ℓ
-- -- -- ParSig ℓ [- x - x₁ -] = Σ (ParSig ℓ x) λ x₂ → ParRec {ℓ} {x} x₂ → ParSig ℓ x₁
-- -- -- ParSig ℓ (assocPar x x₁ x₂ i) = {!isoToPath (Σ-assoc-Iso {A = ParSig ℓ x} {B = λ a → ParRec a → ParSig ℓ x₁} {C = λ a b → ?}) i !}

-- -- -- ParRec {p = □} x = x
-- -- -- ParRec {p = [- p - p₁ -]} x = Σ (ParRec {p = p} (fst x)) (ParRec {p = p₁} ∘ snd x)
-- -- -- ParRec {p = assocPar p p₁ p₂ i} x = {!!}

-- -- -- ------------------


-- -- -- NestedΣ : ∀ {ℓ} → ∀ sh → Sig ℓ (len sh) → Type ℓ

-- -- -- NestedΣ-NestedΣᵣ-Iso : ∀ {ℓ} → (sh : Par) → (s : Sig ℓ (len sh))
-- -- --                       → Iso (NestedΣ sh s) (NestedΣᵣ s)


-- -- -- NestedΣ □ x = x
-- -- -- NestedΣ [- shL - shR -] s =

-- -- --    let (sL , sR) = sig-cs.split {n = len shL} {m = len shR} s
-- -- --    in Σ (NestedΣ shL sL) (NestedΣ shR ∘ sR ∘ Iso.fun (NestedΣ-NestedΣᵣ-Iso shL _)) 

-- -- -- NestedΣ (assocPar sh sh₁ sh₂ i) s = {!!}

-- -- -- NestedΣ-NestedΣᵣ-Iso □ s = idIso
-- -- -- NestedΣ-NestedΣᵣ-Iso [- shL - shR -] s =
-- -- --   let (sL , sR) = sig-cs.split {n = len shL} {m = len shR} s
-- -- --   in
-- -- --      _ Iso⟨ Σ-cong-iso-snd (λ _ → NestedΣ-NestedΣᵣ-Iso shR _) ⟩
-- -- --      _ Iso⟨ Σ-cong-iso-fst (NestedΣ-NestedΣᵣ-Iso shL sL) ⟩
-- -- --      _ Iso⟨ nestedΣᵣ-cs.isom-split {n = len shL} {m = len shR} _ ⟩ _ ∎Iso
-- -- -- NestedΣ-NestedΣᵣ-Iso (assocPar sh sh₁ sh₂ i) s = {!!}

-- -- -- -- NestedΣ (⬠ sh sh₁ sh₂ sh₃ x₁ i) x = {!!}
-- -- -- -- NestedΣ (isGroupoidPar sh sh₁ x₁ y x₂ y₁ i i₁ x₃) x = {!!}

-- -- -- -- isSet-Par' : ∀ p q → len p ≡ len q → p ≡ q
-- -- -- -- isSet-Par' p q x = {!p q!}

-- -- -- -- isSet-Par' : ∀ n → ∀ p → len p ≡ suc n → p ≡ rigthMost n
-- -- -- -- isSet-Par' zero □ x = refl
-- -- -- -- isSet-Par' zero [- p - p₁ -] x = {!!}
-- -- -- -- isSet-Par' zero (assocPar p p₁ p₂ i) x = {!!}
-- -- -- -- isSet-Par' zero (⬠ p p₁ p₂ p₃ x₁ i) x = {!len (⬠ p p₁ p₂ p₃ i0 i0)!}
-- -- -- -- isSet-Par' zero (isGroupoidPar p p₁ x₁ y x₂ y₁ i i₁ x₃) x = {!!}
-- -- -- -- isSet-Par' (suc n) □ x = {!!}
-- -- -- -- isSet-Par' (suc zero) [- p - p₁ -] x = {!!}
-- -- -- -- isSet-Par' (suc (suc n)) [- p - p₁ -] x =
-- -- -- --   let z = isSet-Par' (suc n) {!!} {!!}
-- -- -- --   in {!!}
-- -- -- -- isSet-Par' (suc n) (assocPar p p₁ p₂ i) x = {!!}
-- -- -- -- isSet-Par' (suc n) (⬠ p p₁ p₂ p₃ x₁ i) x = {!!}
-- -- -- -- isSet-Par' (suc n) (isGroupoidPar p p₁ x₁ y x₂ y₁ i i₁ x₃) x = {!!}


-- -- -- -- isSet-Par : ∀ n → ∀ p q → {!len p ≡ len q → p ≡ q!}
-- -- -- -- isSet-Par = {!!}

-- -- -- -- NestedΣ : ∀ {ℓ} → ∀ sh → Sig ℓ (len sh) → hSet ℓ

-- -- -- -- -- for any signature, there is isomorphism betwen NestedΣᵣ (nested Sigma in rigtmost shape)
-- -- -- -- -- and NestedΣ sh (nested Sigma in shape described by the argument of type Par)

-- -- -- -- NestedΣ-NestedΣᵣ-Iso : ∀ {ℓ} → (sh : Par) → (s : Sig ℓ (len sh))
-- -- -- --                       → Iso (fst (NestedΣ sh s)) (NestedΣᵣ s)

-- -- -- -- NestedΣ □ x = x , {!!}
-- -- -- -- NestedΣ [- shL - shR -] s = 
-- -- -- --    let (sL , sR) = sig-cs.split {n = len shL} {m = len shR} s
-- -- -- --    in Σ (fst (NestedΣ shL sL)) (fst ∘ NestedΣ shR ∘ sR ∘ Iso.fun (NestedΣ-NestedΣᵣ-Iso shL _)) , {!!}


-- -- -- -- NestedΣ (Par≡ i) s = {!!} --TypeOfHLevel≡ 2 {X = {! [- x - [- y - z -] -]!}} {Y = {!!}} {!!} i
-- -- -- -- NestedΣ (isSetPar sh sh₁ x₁ y i i₁) x = {!!}

-- -- -- -- NestedΣ-NestedΣᵣ-Iso = {!!}



-- -- -- -- -- -- NestedΣ : ∀ {ℓ} → ∀ sh → Sig ℓ (len sh) → Type ℓ

-- -- -- -- -- -- -- for any signature, there is isomorphism betwen NestedΣᵣ (nested Sigma in rigtmost shape)
-- -- -- -- -- -- -- and NestedΣ sh (nested Sigma in shape described by the argument of type Par)

-- -- -- -- -- -- NestedΣ-NestedΣᵣ-Iso : ∀ {ℓ} → (sh : Par) → (s : Sig ℓ (len sh))
-- -- -- -- -- --                       → Iso (NestedΣ sh s) (NestedΣᵣ s)

-- -- -- -- -- -- NestedΣ □ x = x
-- -- -- -- -- -- NestedΣ [- shL - shR -] s =
-- -- -- -- -- --    let (sL , sR) = sig-cs.split {n = len shL} {m = len shR} s
-- -- -- -- -- --    in Σ (NestedΣ shL sL) (NestedΣ shR ∘ sR ∘ Iso.fun (NestedΣ-NestedΣᵣ-Iso shL _))

-- -- -- -- -- -- NestedΣ-NestedΣᵣ-Iso □ s = idIso
-- -- -- -- -- -- NestedΣ-NestedΣᵣ-Iso [- shL - shR -] s =
-- -- -- -- -- --   let (sL , sR) = sig-cs.split {n = len shL} {m = len shR} s
-- -- -- -- -- --   in
-- -- -- -- -- --      _ Iso⟨ Σ-cong-iso-snd (λ _ → NestedΣ-NestedΣᵣ-Iso shR _) ⟩
-- -- -- -- -- --      _ Iso⟨ Σ-cong-iso-fst (NestedΣ-NestedΣᵣ-Iso shL sL) ⟩
-- -- -- -- -- --      _ Iso⟨ nestedΣᵣ-cs.isom-split {n = len shL} {m = len shR} _ ⟩ _ ∎Iso


-- -- -- -- -- -- -- NestedΣ≡ : ∀ {ℓ} → ∀ n → Sig ℓ n → ∥ Σ Par ((n ≡_) ∘ len) ∥  → Type {!!}

-- -- -- -- -- -- -- -- NestedΣ≡' : ∀ {ℓ} → ∀ n → (s : Sig ℓ n) → (p : ∥ Σ Par ((n ≡_) ∘ len) ∥ ) → NestedΣ≡ n s p ≡ NestedΣᵣ s 
-- -- -- -- -- -- -- -- NestedΣ≡'

-- -- -- -- -- -- -- -- --{ℓ} n s ∣ p , p≡ ∣ = isoToPath (NestedΣ-NestedΣᵣ-Iso p (subst (Sig _) p≡ s)) ∙ λ j → NestedΣᵣ ((transp (λ i → Sig ℓ (p≡ (i ∧ ~ j))) j s))
-- -- -- -- -- -- -- -- -- NestedΣ≡' n s (squash p q i) i₁ = {!NestedΣ≡' n s p!}


-- -- -- -- -- -- -- NestedΣ≡ n s = invEq (SetElim.trunc→Set≃₂ {!!}) {!!}

-- -- -- -- -- -- -- -- NestedΣₗ : ∀ {ℓ} → ∀ n → (s : Sig ℓ n) → Type ℓ 
-- -- -- -- -- -- -- -- NestedΣₗ zero s = {!!}
-- -- -- -- -- -- -- -- NestedΣₗ (suc n) s = {!!}

-- -- -- -- -- -- -- -- -- fromNestedΣₗ : ∀ {ℓ} → ∀ n → (s : Sig ℓ n) → Σ (Type ℓ) (λ x → (x → NestedΣᵣ s))
-- -- -- -- -- -- -- -- -- fromNestedΣₗ zero s = (Lift Unit) , idfun _
-- -- -- -- -- -- -- -- -- fromNestedΣₗ (suc zero) s = s , idfun _
-- -- -- -- -- -- -- -- -- fromNestedΣₗ (suc (suc n)) s = {!!} , {!!}
