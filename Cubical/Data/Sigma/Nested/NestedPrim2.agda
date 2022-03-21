{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Data.Sigma.Nested.NestedPrim2 where

open import Cubical.Core.Everything

open import Cubical.Data.Nat
open import Cubical.Data.Sigma


open import Cubical.Foundations.Everything
open import Cubical.Foundations.CartesianKanOps

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma.Nested.Base

open import Cubical.HITs.GroupoidTruncation renaming (elim to Gelim ; rec to Grec)

open import Cubical.Reflection.StrictEquiv

-- crude (temporary) name "Par" for this datatype
-- comes from Parenthesis
--
-- it is clearly binary tree, but without any data atached to nodes, or leafs
--
-- maybe this should be datatype on its own ?
-- what would be the good name for it?
--
-- I have version of this where Par is indexed by its "length",
-- but this verision was shorter
--
-- this datatype is used to describe different ways to apply multiple Σ
-- to create NestedΣ type
--

data Par : Type₀ where
  □ : Par
  [-_-_-] : Par → Par → Par
  assocPar : ∀ x y z → [- [- x - y -] - z -] ≡ [- x - [- y - z -] -]
  -- isSetPar : isSet Par
  pentaPar : ∀ x y z w → Path ( [- [- [- x - y -] - z -] - w -] ≡ [- x - [- y - [- z - w -] -] -])
               (assocPar _ _ _  ∙ assocPar _ _ _)
               (cong ([-_- w -]) (assocPar _ _ _) ∙∙ (assocPar _ _ _) ∙∙ cong ([- x -_-]) (assocPar _ _ _))              
  -- isGroupoidPar : isGroupoid Par
  
leftMost : ℕ → Par
leftMost zero = □
leftMost (suc n) = [- leftMost n - □ -]

rigthMost : ℕ → Par
rigthMost zero = □
rigthMost (suc n) = [- □ - rigthMost n -]




len : Par → ℕ
len □ = 1
len [- x - x₁ -] = len x + len x₁
len (assocPar x x₁ x₂ i) = +-assoc (len x) (len x₁) (len x₂) (~ i)
len (pentaPar x x₁ x₂ x₃ i j) = 
 
  isSetℕ (len x + len x₁ + len x₂ + len x₃) (len x + (len x₁ + (len x₂ + len x₃)))
      (λ j → hcomp
               (λ i₁ → primPOr j (~ j) (λ _ → +-assoc (len x) (len x₁) (len x₂ + len x₃) (~ i₁))
                                         λ _ → +-assoc (len x + len x₁) (len x₂) (len x₃) (i1))
               (+-assoc (len x + len x₁) (len x₂) (len x₃) (~ j)) )
  
   (λ j → hcomp
            (λ i₁ → primPOr j (~ j)
                         (λ _ → (len x) + +-assoc (len x₁) (len x₂) (len x₃) (~ i₁))
                         λ _ → (+-assoc (len x) (len x₁) (len x₂) i₁) + (len x₃)
                         )
            (+-assoc (len x) (len x₁ + len x₂) (len x₃) (~ j)))
   i j

sss : section (Grec (isSet→isGroupoid isSetℕ) (predℕ ∘ len)) (∣_∣₃ ∘ rigthMost)
sss zero = refl 
sss (suc zero) = refl
sss (suc (suc b)) = cong suc (sss (suc b))



-- Iso-∥Par∥₃-ℕ : Iso ∥ Par ∥₃ ℕ 
-- Iso.fun Iso-∥Par∥₃-ℕ = Grec (isSet→isGroupoid isSetℕ) (predℕ ∘ len)
-- Iso.inv Iso-∥Par∥₃-ℕ = ∣_∣₃ ∘ rigthMost
-- Iso.rightInv Iso-∥Par∥₃-ℕ = sss
-- Iso.leftInv Iso-∥Par∥₃-ℕ = Gelim (λ _ → isSet→isGroupoid (squash₃ _ _)) w
--   where

--     w : (x : Par) → ∣ rigthMost (predℕ (len x)) ∣₃ ≡ ∣ x ∣₃
--     w □ = refl
--     w [- □ - x₁ -] = {!w x₁!}
--     w [- [- x - x₂ -] - x₁ -] = {!!}
--     w [- assocPar x x₂ x₃ i - x₁ -] = {!!}
--     w [- pentaPar x x₂ x₃ x₄ x₅ i - x₁ -] = {!!}
--     w (assocPar x x₁ x₂ i) = {!!}
--     w (pentaPar x x₁ x₂ x₃ x₄ i) = {!!}

-- len (isGroupoidPar x x₁ x₂ y x₃ y₁ i i₁ i₂) =
--   isOfHLevelSuc 2 isSetℕ (len x) (len x₁) (λ i₂ → len (x₂ i₂)) (λ i₂ → len (y i₂)) (λ i₁ i₂ → len (x₃ i₁ i₂)) (λ i₁ i₂ → len (y₁ i₁ i₂)) i i₁ i₂ 

isoToPath' : ∀ {ℓ} → ∀ {A B : Type ℓ} → Iso A B → A ≡ B
isoToPath' = ua ∘ isoToEquiv


transportEquivP : ∀ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1}
                     → (PathP A x y) ≡ (transport (λ i → A i) x ≡ y)
transportEquivP {A = A} {x} {y} i = PathP (λ j → A (j ∨ i)) (transp (λ j → A (j ∧ i)) (~ i) x) y


  

module _ {ℓ} {A B : Type (ℓ-suc ℓ)} (A≃B : A ≃ B) (Ar : A → Type ℓ) (Br : B → Type ℓ) where

  over-≃-fun' : (∀ b → Ar (equivFun (invEquiv A≃B) b) ≃ Br b) → PathP (λ i → ua A≃B i → Type ℓ) Ar Br
  over-≃-fun' x = toPathP ((ww ∙ cong (Ar ∘_) (sym (transportUaInv A≃B) ∙ funExt λ x₁ → transportRefl _)) ∙ funExt λ b → ua (x b))

    where
      ww : transport (λ i → (ua A≃B) i → Type ℓ) Ar ≡
             Ar ∘ transport (sym (ua A≃B))
      ww = fromPathP (funTypeTranspCod (idfun (Type (ℓ-suc ℓ))) (Type ℓ) (ua A≃B) Ar)


  -- over-≃-fun : (∀ b → Ar (equivFun (invEquiv A≃B) b) ≃ Br b) → PathP (λ i → ua A≃B i → Type ℓ) Ar Br
  -- over-≃-fun x i ab = hcomp (λ j → λ
  --                           { (i = i0) → Ar (((λ i₁ → invEq A≃B (transp (λ i₂ → B) i₁ (equivFun A≃B ab))) ∙ (retEq A≃B ab)) j)
  --                           ; (i = i1) → Br ab
  --                        })
  --                        (ua {A = Ar (equivFun (invEquiv A≃B) (coei→1 (λ k → ua A≃B k) i ab))}
  --                            {B = Br (coei→1 (λ k → ua A≃B k) i ab)}
  --                             (x (coei→1 (λ k → ua {A = A} {B = B}  A≃B k) i ab)) i)




  over-≃-fun : (∀ b → Ar (equivFun (invEquiv A≃B) b) ≃ Br b) → PathP (λ i → ua A≃B i → Type ℓ) Ar Br
  over-≃-fun x i ab = hcomp (λ j → λ
                            { (i = i0) → Ar ab
                            ; (i = i1) → ((λ i₁ → Ar ((( (invEq A≃B (transp (λ i₁ → B) i₁ ab)))))) ∙ ua (x ab)) j
                         })
                          ((Ar (transp (λ j → ua A≃B (i ∧ ~ j)) (~ i) ab)))




  zzzz : ((x : B) → Ar (invEq A≃B x) ≡ Br x) ≃ ((x : B) → Ar (invEq A≃B x) ≃ Br x)
  zzzz = equivΠCod λ b → univalence {A = Ar (invEq A≃B b )} {B = Br b}

  -- over-≃-Iso : (∀ b → Ar (equivFun (invEquiv A≃B) b) ≡ Br b) ≃ (PathP (λ i → ua A≃B i → Type ℓ) Ar Br)
  -- over-≃-Iso = compEquiv zzzz (pathToEquiv ({!!}))
 
  over-≃ : (∀ b → Ar (equivFun (invEquiv A≃B) b) ≃ Br b) ≃ PathP (λ i → ua A≃B i → Type ℓ) Ar Br
  over-≃ = compEquiv (invEquiv zzzz) (compEquiv funExtEquiv ((pathToEquiv (cong (_≡ Br) (funExt (λ x i → Ar (fst (fst (A≃B .snd .equiv-proof (transp (λ i → B) (~ i) x))))))  ∙ sym transportEquivP))))

  over-ua : ((a : B) → transp (λ i → ua A≃B i → Type ℓ) i0 Ar a ≃ Br a) → PathP (λ i → ua A≃B i → Type ℓ) Ar Br
  over-ua x = toPathP (funExt (ua ∘ x))

  zzzqqq : Ar ∘ equivFun (invEquiv A≃B) ≡ transport (λ i → ua A≃B i → Type ℓ) Ar
  zzzqqq = (cong (Ar ∘_) ( sym (funExt (uaβ (invEquiv A≃B))) ∙ transportUaInv A≃B)) ∙ sym (fromPathP (funTypeTranspCod (idfun _) _ (ua A≃B) Ar))

  -- over-ua' : (∀ b → Ar (equivFun (invEquiv A≃B) b) ≃ Br b) → PathP (λ i → ua A≃B i → Type ℓ) Ar Br
  -- over-ua' = {!funTypeTranspCod!}



over-≃-funJ : ∀ {ℓ} →  (B : Type (ℓ-suc ℓ)) (Br : B → Type ℓ) →
                             (over-≃-fun (idEquiv B) Br Br (λ b → idEquiv (Br (equivFun (invEquiv (idEquiv B)) b))))
                     ≡ transp (λ j → PathP (λ i → (uaIdEquiv {A = B} (~ j)) i → Type ℓ) Br Br) i0 refl
over-≃-funJ {ℓ} B Br i i₁ = {!!}

--    where
--      w :  (λ i ab →
--                 hcomp (λ j → λ
--                             { (i = i0) → Br (((λ i₁ → (transp (λ i₂ → B) i₁ (ab))) ∙ (refl)) j)
--                             ; (i = i1) → Br ab
--                          })
--                          (ua {A = Br (equivFun (invEquiv (idEquiv B)) (coei→1 (λ k → ua (idEquiv B) k) i ab))}
--                              {B = Br (coei→1 (λ k → ua (idEquiv B) k) i ab)}
--                               ((idEquiv (Br (coei→1 (λ k → ua {A = B} {B = B}  (idEquiv B) k) i ab)))) i))
--           ≡ (λ i ab →
--          hcomp
--          (λ j →
--             λ { (i = i0) → Br ((transportRefl ab j))
--               ; (i = i1) → Br ab
--               })
--          ((Br (coei→1 (λ k → ua (idEquiv B) k) i ab)))) 
--            -- transp (λ j → PathP (λ i → (uaIdEquiv {A = B} (~ j)) i → Type ℓ) Br Br) i0 refl
--      w =
--         (λ jj → (λ i ab →
--                 hcomp (λ j → λ
--                             { (i = i0) → Br (( rUnit (λ i₁ → (transp (λ i₂ → B) i₁ (ab))) (~ jj)) j)
--                             ; (i = i1) → Br ab
--                          }) (uaIdEquiv {A = (Br (coei→1 (λ k → ua {A = B} {B = B}  (idEquiv B) k) i ab))} jj i)))
--         ∙ (λ ii → (λ i ab →
--          hcomp
--          (λ j →
--             λ { (i = i0) → Br ((transportRefl ab j))
--               ; (i = i1) → Br ab
--               })
--          ((Br (coei→1 (λ k → ua (idEquiv B) k) i ab)))))
         
 



module _ {ℓ} {A B C : Type (ℓ-suc ℓ)} (Ar : A → Type ℓ) (Br : B → Type ℓ) (Cr : C → Type ℓ) where
  assoc-Σ-curry-Iso :  Iso (Σ (Σ A λ a → Ar a → B) λ x → Σ (Ar (fst x)) (λ x₁ → Br (snd x x₁)) → C)
                        (Σ A λ a → Ar a → Σ B λ x → Br x → C) 
  Iso.fun assoc-Σ-curry-Iso s = (fst (fst s)) , λ x → (snd (fst s)) x , λ x₁ → snd s (_ , x₁)
  Iso.inv assoc-Σ-curry-Iso s = (fst s , λ x → fst (snd s x)) , λ y → snd (snd s (fst y)) (snd y)
  Iso.rightInv assoc-Σ-curry-Iso _ = refl
  Iso.leftInv assoc-Σ-curry-Iso _ = refl


  unquoteDecl assoc-Σ-curry  = declStrictIsoToEquiv assoc-Σ-curry assoc-Σ-curry-Iso

  Ty0 : (Σ (Σ A λ a → Ar a → B) λ x → Σ (Ar (fst x)) (λ x₁ → Br (snd x x₁)) → C) → Type ℓ
  Ty0 x = Σ (Σ (Ar (fst (fst x))) λ x₁ → Br (snd (fst x) x₁)) λ x₁ → Cr (snd x x₁)

  Ty1 : (Σ A λ a → Ar a → Σ B λ x → Br x → C) → Type ℓ
  Ty1 x = Σ (Ar (fst x)) λ x₁ → Σ (Br (fst (snd x x₁))) (Cr ∘ snd (snd x x₁))


  assoc-Σ-curryP'≃ :   ((a : _) → Ty0 a)
                      ≃
                        (((a : _) → Ty1 a)) 
  assoc-Σ-curryP'≃ = (equivΠ (isoToEquiv (assoc-Σ-curry-Iso)) (λ _ → Σ-assoc-≃))



  assoc-Σ-curryΣ : ∀ a → Ty0 a ≃ Ty1 (equivFun assoc-Σ-curry a)  
  assoc-Σ-curryΣ a = Σ-assoc-≃

  assoc-Σ-curryΣ- : ∀ a → Ty0 (invEq assoc-Σ-curry a) ≃ Ty1 a   
  assoc-Σ-curryΣ- a = Σ-assoc-≃
  

  assoc-Σ-curryP : PathP (λ i → ua (assoc-Σ-curry) i → Type ℓ)
                       Ty0
                       Ty1
  assoc-Σ-curryP = (over-≃-fun (assoc-Σ-curry) Ty0 Ty1) assoc-Σ-curryΣ- 


     --   w'' : _
     --   w'' a = ua  Σ-assoc-≃ ∙ λ ii → Σ (Ar (transp (λ i → A) ii (fst a)))
     --                                     (λ a₁ →
     --                                        Σ
     --                                        (Br
     --                                         (transp (λ i → B) ii
     --                                          (fst
     --                                           (snd a (transp (λ j → Ar (transp (λ i → A) (j ∨ ii) (fst a))) ii a₁)))))
     --                                        (λ z →
     --                                           Cr
     --                                           (transp (λ i → C) ii
     --                                            (snd (snd a (transp (λ j → Ar (transp (λ i → A) (j ∨ ii) (fst a))) ii a₁))
     --                                             (transp
     --                                              (λ j →
     --                                                 Br
     --                                                 (transp (λ i → B) (j ∨ ii)
     --                                                  (fst
     --                                                   (snd a (transp (λ j₁ → Ar (transp (λ i → A) (j₁ ∨ ii) (fst a))) ii a₁))))) ii z)))))


-- module _ {ℓ} {A B C : Type (ℓ-suc ℓ)} (Ar : A → Type ℓ) (Br : B → Type ℓ) where

--   -- lem-penta : (IsoAB : Iso A B)
--   --           → (AB-Rec≃ : ∀ a → Ar (equivFun (isoToEquiv (invIso IsoAB)) a) ≃ Br a)
--   --           → (AB-RecP-≃ : (∀ a → Ar (equivFun (isoToEquiv (invIso IsoAB)) a) ≃ Br a) ≃ PathP (λ i → isoToPath IsoAB i → Type ℓ) Ar Br)

--   --           → Path (Σ A (λ a → Ar a → C) ≡ Σ B (λ a → Br a → C))
--   --             (ua (compEquiv (invEquiv (Σ-cong-equiv-fst {B = λ v → Ar v → C} (isoToEquiv (invIso IsoAB))))
--   --                            (Σ-cong-equiv-snd λ a → cong≃ (λ X → X → C) (AB-Rec≃ a))
--   --                            ))
--   --             (
--   --             cong {A = Σ (Type (ℓ-suc ℓ)) λ x → x → Type ℓ } (λ a → Σ (fst a) λ x → (snd a) x → C)
--   --                   (λ i → (isoToPath IsoAB i) , equivFun (AB-RecP-≃) AB-Rec≃ i))
--   -- lem-penta IsoAB AB-Rec≃ AB-RecP-≃ = invEq≡→equivFun≡ (invEquiv univalence) (equivEq (funExt w))
--   --    where
--   --      w : ∀ x → {!!} ≡ {!!}
--   --      w (xx , yy) = ΣPathP ((transportRefl _) ,
--   --           toPathP (funExt λ x → cong (transp (λ i → C) i0 ∘ transp (λ i → C) i0)
--   --             λ i → yy (ww x i)))
--   --         where


--   --           -- ww'' : cong Br
--   --           --          (λ i → transportRefl (equivFun (isoToEquiv IsoAB) xx) (~ i))
--   --           --          ∙
--   --           --          ua
--   --           --          (invEquiv
--   --           --           (AB-Rec≃ (transport (λ _ → B) (equivFun (isoToEquiv IsoAB) xx))))
--   --           --          ≡
--   --           --          ua (invEquiv (AB-Rec≃ (equivFun (isoToEquiv IsoAB) xx))) ∙
--   --           --          cong (λ z → Ar (equivFun (isoToEquiv (invIso IsoAB)) z))
--   --           --          (λ i → transportRefl (equivFun (isoToEquiv IsoAB) xx) (~ i))
--   --           -- ww'' = sym (homotopyNatural {f = Br}
--   --           --                  (λ a → ua (invEquiv (AB-Rec≃ a)))
--   --           --                  {equivFun (isoToEquiv IsoAB) xx} {transport refl (equivFun (isoToEquiv IsoAB) xx)}
--   --           --                  (sym (transportRefl (equivFun (isoToEquiv IsoAB) xx)))
--   --           --                  )

--   --           -- ww''2 : cong Br
--   --           --           (λ i → transportRefl (equivFun (isoToEquiv IsoAB) xx) (~ i))
--   --           --           ∙ funExt⁻ (λ i → fromPathP (equivFun AB-RecP-≃ AB-Rec≃) (~ i)) (transport (λ _ → B) (equivFun (isoToEquiv IsoAB) xx))
--   --           --            -- (λ j → equivFun AB-RecP-≃ AB-Rec≃ (~ j) (transp (λ i → isoToPath IsoAB (i ∧ ~ j)) j xx) )
--   --           --           ≡
--   --           --           funExt⁻ (λ i → fromPathP (equivFun AB-RecP-≃ AB-Rec≃) (~ i))
--   --           --           (equivFun (isoToEquiv IsoAB) xx)
--   --           --           ∙
--   --           --           cong (λ z → transport (λ i → isoToPath IsoAB i → Type ℓ) Ar z)
--   --           --           (λ i → transportRefl (equivFun (isoToEquiv IsoAB) xx) (~ i))
--   --           -- ww''2 = sym (homotopyNatural {f = Br}
--   --           --                  (funExt⁻ (sym (fromPathP (equivFun AB-RecP-≃ AB-Rec≃))))
--   --           --                  {equivFun (isoToEquiv IsoAB) xx} {transport refl (equivFun (isoToEquiv IsoAB) xx)}
--   --           --                  (sym (transportRefl (equivFun (isoToEquiv IsoAB) xx)))
--   --           --                  )

--   --           -- zzz : {!!}
--   --           -- zzz = {!!}

--   --           ww' :  (cong Br (sym (transportRefl (equivFun (isoToEquiv IsoAB) xx)))
--   --                         ∙
--   --                         (λ j → equivFun AB-RecP-≃ AB-Rec≃ (~ j) (transp (λ i → isoToPath IsoAB (i ∧ ~ j)) j xx) )
--   --                      )
--   --                        ≡
--   --                        {!!}
--   --           ww' = (λ ii → (cong Br (sym (transportRefl (equivFun (isoToEquiv IsoAB) xx)))
--   --                         ∙
--   --                         ((λ j → equivFun AB-RecP-≃ AB-Rec≃ (~ j) (transp (λ i → isoToPath IsoAB (i ∧ ~ j)) j xx) ))
--   --                      ))

--   --                     ∙ {!!} ∙ {!!}

--   --           eee : {!!}
--   --           eee = ((AB-Rec≃ (fst (invEquiv (Σ-cong-equiv-fst {B = λ v → Ar v → C} (isoToEquiv (invIso IsoAB))) .fst (xx , yy)))))

--   --           ww : (x : Br (equivFun (isoToEquiv IsoAB) xx)) → 
--   --                 (transp (λ j → equivFun AB-RecP-≃ AB-Rec≃ (~ j) (transp (λ i → isoToPath IsoAB (i ∧ ~ j)) j xx)) i0
--   --                  (transp (λ j → Br (transportRefl (equivFun (isoToEquiv IsoAB) xx) (~ j))) i0 x))
--   --                        ≡                         
--   --                  (transp (λ j → Ar (snd (equivCtr (isoToEquiv (invIso IsoAB)) xx) j)) i0
--   --                   (transp (λ j → ua (AB-Rec≃ (fst (invEquiv (Σ-cong-equiv-fst {B = λ v → Ar v → C} (isoToEquiv (invIso IsoAB))) .fst (xx , yy)))) (~ j)) i0 x))
--   --           ww x =
--   --              sym (transportComposite (λ j → Br (transportRefl (equivFun (isoToEquiv IsoAB) xx) (~ j)))
--   --                                       ((λ j → equivFun AB-RecP-≃ AB-Rec≃ (~ j) (transp (λ i → isoToPath IsoAB (i ∧ ~ j)) j xx)))
--   --                                       x)

--   --               ∙∙
--   --                 {!!}
                  
--   --                 -- (λ i → transp (λ j → {! (snd (equivCtr (isoToEquiv (invIso IsoAB)) xx) j)!} j) i0 (equivFun (invEquiv eee) x))
                  
--   --               ∙∙
--   --                (
--   --                   cong (transp (λ j → Ar (snd (equivCtr (isoToEquiv (invIso IsoAB)) xx) j)) i0)
--   --                     (sym (uaβ (invEquiv eee) x)
--   --                       ∙ (funExt⁻ (transportUaInv eee) x)))
--   --               -- transportComposite ((λ j → ua (AB-Rec≃ (fst (invEquiv (Σ-cong-equiv-fst {B = λ v → Ar v → C} (isoToEquiv (invIso IsoAB))) .fst (xx , yy)))) (~ j)))
--   --               --             ((λ j → Ar (snd (equivCtr (isoToEquiv (invIso IsoAB)) xx) j))) x





--   lem-pentaApp : (IsoAB : A ≃ B)
--             → (AB-Rec≃ : ∀ a → Ar (equivFun ( (invEquiv IsoAB)) a) ≃ Br a)

--             → Path (Σ A (λ a → Ar a → C) ≡ Σ B (λ a → Br a → C))
              
--               (ua (compEquiv (invEquiv (Σ-cong-equiv-fst {!(λ z → snd IsoAB .equiv-proof z .fst .fst) , ?!}))
--                              (Σ-cong-equiv-snd λ a → cong≃ (λ X → X → C) (AB-Rec≃ a))
--                              ))
              
--               (
--               cong {A = Σ (Type (ℓ-suc ℓ)) λ x → x → Type ℓ } (λ a → Σ (fst a) λ x → (snd a) x → C)
--                     (λ i → (ua IsoAB i) , (over-≃-fun (IsoAB) Ar Br) AB-Rec≃ i))
--   lem-pentaApp = {!!}

      

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



-- ua-comp  : ∀ {ℓ} → ∀ {A B C : Type ℓ} → (iAB : A ≃ B) → (iBC : B ≃ C) → ua iAB ∙ ua iBC ≡ ua (compEquiv iAB iBC)  
-- ua-comp {A = A} {B = B} {C = C} iAB iBC =
--   sym (invEq≡→equivFun≡ (invEquiv univalence) (equivEq (funExt
--       λ x i → transp (λ i → C) i (fst iBC (transp (λ i → B) i (fst iAB (transp (λ i → A) i x)))))))


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

--   penta-Σ-curry-≃ :
--                  Path ( (Σ
--                                   (Σ (Σ A (λ x₄ → Ar x₄ → B))
--                                    (λ x₄ →
--                                       Σ (Ar (fst x₄)) (λ x₅ → Br (snd x₄ x₅)) → C))
--                                   (λ x₄ →
--                                      Σ
--                                      (Σ (Ar (fst (fst x₄))) (λ x₅ → Br (snd (fst x₄) x₅)))
--                                      (λ x₅ → Cr (snd x₄ x₅)) →
--                                      D))
--                          ≃  (Σ A
--                                   (λ x₄ →
--                                      Ar x₄ →
--                                      Σ B
--                                      (λ x₅ →
--                                         Br x₅ → Σ C (λ x₆ → Cr x₆ → D)))))
--                    (compEquiv ((assoc-Σ-curry _ _ Dr )) ((assoc-Σ-curry _ (λ v → Br v) λ x → Σ (Cr (fst x)) λ x₁ → Dr (snd x x₁))) )
--                     (compEquiv hlp1
--                          (compEquiv ((assoc-Σ-curry Ar (λ z → Σ (Br (fst z)) (λ x₁ → Cr (snd z x₁))) Dr))
--                                   (Σ-cong-equiv-snd λ a → equivΠCod λ a₁ → (assoc-Σ-curry _ _ Dr))))
--   penta-Σ-curry-≃ = equivEq (funExt λ x → ΣPathP (refl , (funExt (λ x₁ → ΣPathP (refl , (funExt λ x₂ → ΣPathP (refl , (funExt λ x₃ → {!!}))))))))

--   lemL : ua hlp1 ≡ cong {A = Σ (Type (ℓ-suc ℓ)) λ x → x → Type ℓ } (λ a → Σ (fst a) λ x → (snd a) x → D)
--                     (λ i → (ua ((assoc-Σ-curry Ar Br Cr)) i) , assoc-Σ-curryP Ar Br Cr i)
--   lemL = lem-pentaApp (Ty0 Ar Br Cr) (Ty1 Ar Br Cr) ((assoc-Σ-curry Ar Br Cr)) (assoc-Σ-curryΣ- Ar Br Cr)
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


-- --   lemR : ∀ {B C : Type (ℓ-suc ℓ)} → (Iso-BC : B ≃ C) → ua (Σ-cong-equiv-snd λ a → equivΠCod λ a₁ →  Iso-BC)
-- --            ≡
-- --          (cong (Σ A) (funExt λ y → cong (λ x → Ar y → x) (ua Iso-BC)))
-- --   lemR B≃C = isInjectiveTransport (funExt λ x → ΣPathP (refl , funExt λ x₁ → refl)) 


-- --   penta-Σ-curry :
-- --                  Path ( (Σ
-- --                                   (Σ (Σ A (λ x₄ → Ar x₄ → B))
-- --                                    (λ x₄ →
-- --                                       Σ (Ar (fst x₄)) (λ x₅ → Br (snd x₄ x₅)) → C))
-- --                                   (λ x₄ →
-- --                                      Σ
-- --                                      (Σ (Ar (fst (fst x₄))) (λ x₅ → Br (snd (fst x₄) x₅)))
-- --                                      (λ x₅ → Cr (snd x₄ x₅)) →
-- --                                      D))
-- --                          ≡  (Σ A
-- --                                   (λ x₄ →
-- --                                      Ar x₄ →
-- --                                      Σ B
-- --                                      (λ x₅ →
-- --                                         Br x₅ → Σ C (λ x₆ → Cr x₆ → D)))))
-- --                    (ua (assoc-Σ-curry _ _ Dr ) ∙  ua (assoc-Σ-curry _ (λ v → Br v) λ x → Σ (Cr (fst x)) λ x₁ → Dr (snd x x₁)) )
                    
-- --                     (cong {A = Σ (Type (ℓ-suc ℓ)) λ x → x → Type ℓ } (λ (a : Σ (Type (ℓ-suc ℓ)) (λ x → x → Type ℓ)) → Σ (fst a) λ x → (snd a) x → D)
-- --                         (λ i → (ua (assoc-Σ-curry Ar Br Cr) i) , assoc-Σ-curryP Ar Br Cr i)

-- --                        ∙∙ ua (assoc-Σ-curry Ar (λ z → Σ (Br (fst z)) (λ x₁ → Cr (snd z x₁))) Dr)
-- --                           ∙∙ cong (Σ A) (funExt λ y → cong (λ x → Ar y → x) (ua (assoc-Σ-curry _ _ Dr))))
-- --   penta-Σ-curry = 
  
-- --       (ua-comp _ _)
-- --       ∙∙ cong ua penta-Σ-curry-≃ ∙∙ 
-- --       ((sym (ua-comp _ _) ∙ cong (ua (hlp1) ∙_) (sym (ua-comp _ _)))     
-- --       ∙∙
-- --       sym (doubleCompPath-elim' _ _ _)
-- --       -- (λ i j → ( {!!} ∙ ((isoToPath (assoc-Σ-curry Ar (λ z → Σ (Br (fst z)) (λ x₁ → Cr (snd z x₁))) Dr)) ∙ {!refl i!})) j )
-- --       ∙∙
-- --       (cong₂ {C = λ _ _ → _ ≡ (Σ A
-- --                                   (λ x₄ →
-- --                                      Ar x₄ →
-- --                                      Σ B
-- --                                      (λ x₅ →
-- --                                         Br x₅ → Σ C (λ x₆ → Cr x₆ → D))))}
-- --                 (_∙∙ (ua (assoc-Σ-curry Ar (λ z → Σ (Br (fst z)) (λ x₁ → Cr (snd z x₁))) Dr)) ∙∙_) lemL (lemR (assoc-Σ-curry Br Cr Dr)))
-- --       )

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
