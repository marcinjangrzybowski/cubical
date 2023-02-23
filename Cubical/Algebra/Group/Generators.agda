{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.Generators where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything


open import Cubical.Data.List
open import Cubical.Data.Sigma


open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Bool

open import Cubical.Functions.Logic

open import Cubical.HITs.PropositionalTruncation
  renaming (rec to rec₁ ; map to map₁ ; map2 to map2₁ ; elim to elim₁)

open import Cubical.HITs.SetQuotients
  renaming (rec to rec/ ; [_] to [_]/ ; rec2 to rec2/ ; elimProp to elimProp/)

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup

open import Cubical.Algebra.SymmetricGroup

-- open import Cubical.HITs.FreeGroup

open GroupStr

open GroupTheory




concatG : ∀ {ℓ} → (G : Group ℓ) → List ⟨ G ⟩  → ⟨ G ⟩
concatG G = foldr (G .snd ._·_) (G .snd .1g )



concatG· : ∀ {ℓ} → {G : Group ℓ} → (xs ys : List ⟨ G ⟩)
    → (G .snd ._·_) (concatG G xs) (concatG G ys) ≡
         concatG G (xs ++ ys) 
concatG· {G = G} [] ys = G .snd .·IdL _
concatG· {G = G} (x ∷ xs) ys = sym (G .snd .·Assoc _ _ _) ∙ cong (G .snd · x) (concatG· {G = G} (xs) ys)

-- concatG·map : ∀ {ℓ ℓ'} → {A : Type ℓ'} (G : Group ℓ) → (f : A → ⟨ G ⟩) (xs ys : List A)
--     → (G .snd ._·_) (concatG G (map f xs)) (concatG G (map f ys)) ≡
--          concatG G (map f (xs ++ ys)) 
-- concatG·map G f xs ys =
--   concatG· {G = G} (map f xs) (map f ys) ∙ cong (concatG G) (sym (map-++ f xs ys))

concatG·map : ∀ {ℓ ℓ'} → {A : Type ℓ'} (G : Group ℓ) → (f : A → ⟨ G ⟩) (xs ys : List A)
    → (G .snd ._·_) (concatG G (map f xs)) (concatG G (map f ys)) ≡
         concatG G (map f (xs ++ ys)) 
concatG·map G f [] ys = G .snd .·IdL _
concatG·map G f (x ∷ xs) ys = sym (G .snd .·Assoc _ _ _)
  ∙ cong (G .snd · f x) (concatG·map G f (xs) ys)


concatGRev : ∀ {ℓ ℓ'} (G : Group ℓ) → {A : Type ℓ'} → (f : A → ⟨ G ⟩) 
              → (∀ a → Σ _ λ b → (f b) ≡ (G .snd .GroupStr.inv (f a)))
              → ∀ l → Σ _ λ l' → G .snd .GroupStr.inv (concatG G (map f l))
                 ≡ (concatG G (map f l'))  
concatGRev G f invA =
  ind ([] , inv1g G)
      (λ {a} {l} (l' , p)  →
         let (a' , p') = invA a
           in l' ++ [ a' ] , (invDistr G _ _ ∙ cong₂ (G .snd ._·_) p (sym p' ∙ sym (·IdR (snd G) (f a'))) )
                 ∙ ((concatG· {G = G} (map f l') _) ∙
                   sym (cong (concatG G) (map-++ f l' _))))

GeneratedBy : ∀ {ℓ ℓ'} (G : Group ℓ) → {A : Type ℓ'} → (f : A → ⟨ G ⟩) → hProp (ℓ-max ℓ ℓ')
GeneratedBy G f = ∀[ x ] ∃[ l ] ((concatG G (map f l) ≡ x ), G .snd .is-set _ _)


GeneratedElim : ∀ {ℓ ℓ' ℓ''} (G : Group ℓ) → {A : Type ℓ'} → {f : A → ⟨ G ⟩} →
                 ⟨ GeneratedBy G f ⟩ → {B :  fst G → Type ℓ''} → (∀ a → isProp (B a)) 
                  → (∀ l → B (concatG G (map f l))) → ∀ a → B a
GeneratedElim G {f = f} gen trun h x =
 elim₁ (λ _ → trun _) (λ (x' , p) → subst _ p (h x')) (gen x)


GeneratedElim' : ∀ {ℓ ℓ' ℓ''} (G : Group ℓ) → {A : Type ℓ'} → {f : A → ⟨ G ⟩} →
                 ⟨ GeneratedBy G f ⟩ → {B :  fst G → Type ℓ''} → (∀ a → isProp (B a))  
                  → (B ((GroupStr.1g (snd G))))
                  → (∀ a → ∀ x → B x → B ((G .snd · (f a)) x)) → ∀ a → B a
GeneratedElim' G {f = f} gen tB hε h =
  GeneratedElim G gen tB (ind hε λ {a} {l} x → h a _ x)


GeneratedByConstr : ∀ {ℓ ℓ'} (G : Group ℓ) → {A : Type ℓ'} → (f : A → ⟨ G ⟩) → Type (ℓ-max ℓ ℓ')
GeneratedByConstr G f = ∀ x →  Σ[ l ∈ _ ] (concatG G (map f l) ≡ x )


GeneratedElimConstr : ∀ {ℓ ℓ' ℓ''} (G : Group ℓ) → {A : Type ℓ'} → {f : A → ⟨ G ⟩} →
                 GeneratedByConstr G f → (B :  fst G → Type ℓ'') 
                  → (∀ l → B (concatG G (map f l))) → ∀ a → B a
GeneratedElimConstr G {f = f} gen tB h x = subst tB ((snd (gen x))) (h (fst (gen x)))

GeneratedElimConstrβ : ∀ {ℓ ℓ' ℓ''} (G : Group ℓ) → {A : Type ℓ'} → {f : A → fst G } →
                   (gen : GeneratedByConstr G f)
                   → (B :  fst G → Type ℓ'') 
                  → (h : ∀ l → B (concatG G (map f l)))
                  → ∀ x → subst B ((snd (gen x))) (h (fst (gen x))) ≡ (GeneratedElimConstr G  gen B h x)
                      -- PathP (λ i → B (snd (gen x) i))
                      --    (h (fst (gen x)))
                      --    (GeneratedElimConstr G  gen B h x)
                         
GeneratedElimConstrβ G gen B h x = refl

GeneratedElimConstr2 : ∀ {ℓ ℓ' ℓ''} (G : Group ℓ) → {A : Type ℓ'} → {f : A → ⟨ G ⟩} →
                 GeneratedByConstr G f → (B :  fst G → fst G → Type ℓ'') 
                  → (∀ l l' → B (concatG G (map f l)) (concatG G (map f l'))) → ∀ a b → B a b
GeneratedElimConstr2 G {f = f} gen tB h x x' =
    transport (cong₂ tB ((snd (gen x))) ((snd (gen x'))) )
     (h (fst (gen x))
     (fst (gen x')))


GeneratedElimConstrDep : ∀ {ℓ ℓ' ℓ'' ℓ*} (G : Group ℓ) → {A : Type ℓ'} → {f : A → fst G } →
                   (gen : GeneratedByConstr G f)
                   → (B :  fst G → Type ℓ'') 
                  → (h : ∀ l → B (concatG G (map f l)))
                  → (B' : ∀ g → B g → Type ℓ*)
                  → (h' : ∀ l → B' (concatG G (map f l)) (h l))
                  → ∀ a → B' a (GeneratedElimConstr G {f = f} gen B h a)
GeneratedElimConstrDep G {f = f} gen B h B' h' x =
   transport (cong₂ B' (snd (gen x)) (toPathP refl)) (h' (fst (gen x)))

GeneratedElimConstrDep2 : ∀ {ℓ ℓ' ℓ'' ℓ*} (G : Group ℓ) → {A : Type ℓ'} → {f : A → fst G } →
                   (gen : GeneratedByConstr G f)
                   → (B :  fst G → Type ℓ'') 
                  → (h : ∀ l → B (concatG G (map f l)))
                  → (B' : ∀ g g' → B g → B g'  → Type ℓ*)
                  → (h' : ∀ l l' 
                           → B' (concatG G (map f l)) (concatG G (map f l'))
                                
                                (h l) (h l'))
                  → ∀ a b
                  → B' a b
                    (GeneratedElimConstr G {f = f} gen B h a)
                    (GeneratedElimConstr G {f = f} gen B h b)
GeneratedElimConstrDep2 G {f = f} gen B h B' h' x x' =
   transport (λ i → B' ((snd (gen x)) i) ((snd (gen x')) i)
              (toPathP {A = λ i → B (snd (gen x) i)} {x = h (fst (gen x))} refl i)
              ((toPathP {A = λ i → B (snd (gen x') i)} {x = h (fst (gen x'))} refl i)))
       (h' (fst (gen x)) (fst (gen x'))) 


GeneratedElimConstrDep3 : ∀ {ℓ ℓ' ℓ'' ℓ*} (G : Group ℓ) → {A : Type ℓ'} → {f : A → fst G } →
                   (gen : GeneratedByConstr G f)
                   → (B :  fst G → Type ℓ'') 
                  → (h : ∀ l → B (concatG G (map f l)))
                  → (B' : ∀ g g' g'' → B g → B g' → B g'' → Type ℓ*)
                  → (h' : ∀ l l' l''
                           → B' (concatG G (map f l)) (concatG G (map f l'))
                                (concatG G (map f l''))
                                (h l) (h l') (h l''))
                  → ∀ a b c
                  → B' a b c
                    (GeneratedElimConstr G {f = f} gen B h a)
                    (GeneratedElimConstr G {f = f} gen B h b)
                    (GeneratedElimConstr G {f = f} gen B h c)
GeneratedElimConstrDep3 G {f = f} gen B h B' h' x x' x'' =
   transport (λ i → B' ((snd (gen x)) i) ((snd (gen x')) i) ((snd (gen x'')) i)
              (toPathP {A = λ i → B (snd (gen x) i)} {x = h (fst (gen x))} refl i)
              ((toPathP {A = λ i → B (snd (gen x') i)} {x = h (fst (gen x'))} refl i))
              ((toPathP {A = λ i → B (snd (gen x'') i)} {x = h (fst (gen x''))} refl i)))
       (h' (fst (gen x)) (fst (gen x')) (fst (gen x''))) 

-- GeneratedElimConstrDep++ : ∀ {ℓ ℓ' ℓ'' ℓ*} (G : Group ℓ) → {A : Type ℓ'} → {f : A → fst G } →
--                    (gen : GeneratedByConstr G f)
--                    → (B :  fst G → Type ℓ'') 
--                   → (h : ∀ l → B (concatG G (map f l)))
--                   → (B2 :  fst G → fst G → Type ℓ'') 
--                   → (h2 : ∀ l l' → B2 (concatG G (map f l)) (concatG G (map f l')))
--                   → (B' : ∀ g g' → B g → B g' → B ((G .snd ._·_) g g') → B2 g g' → Type ℓ*)
                  
--                   → (h' : ∀ l l' 
--                            → B' (concatG G (map f l)) (concatG G (map f l'))
--                                 (h l) (h l')
--                                  (subst B (sym (concatG·map G f l l')) (h (l ++ l'))) (h2 l l'))
--                   → ∀ a b 
--                   → B' a b
--                     (GeneratedElimConstr G {f = f} gen B h a)
--                     (GeneratedElimConstr G {f = f} gen B h b)
--                     (GeneratedElimConstr G {f = f} gen B h (G .snd ._·_ a b))
--                     (GeneratedElimConstr2 G {f = f} gen B2 h2 a b)
-- GeneratedElimConstrDep++ G {f = f} gen B h B2 h2 B' h' x x'  = 
--    transport (λ i → B' ((snd (gen x)) i) ((snd (gen x')) i)
--               (toPathP {A = λ i → B (snd (gen x) i)} {x = h (fst (gen x))} refl i)
--               (toPathP {A = λ i → B (snd (gen x') i)} {x = h (fst (gen x'))} refl i)
--               ((toPathP {A = λ i → B (G .snd ._·_ (snd (gen x) i) (snd (gen x') i))}
--                     {x = (subst B (sym (concatG·map G f (fst (gen x)) (fst (gen x'))))
--                      (h ((fst (gen x)) ++ (fst (gen x')))))}
--                     {y = (GeneratedElimConstr G {f = f} gen B h (G .snd ._·_ x x'))}
--                     (let ppp : subst {x = G .snd ._·_ (concatG G (map f (fst (gen x))))
--                                             (concatG G (map f (fst (gen x'))))}
--                                      {G .snd ._·_ x x'} B (cong₂ (G .snd ._·_) (snd (gen x)) (snd (gen x')))
--                               (subst {x = concatG G (map f (fst (gen x) ++ fst (gen x')))}
--                                       {G .snd ._·_ (concatG G (map f (fst (gen x))))
--                                          (concatG G (map f (fst (gen x'))))} B (sym (concatG·map G f (fst (gen x)) (fst (gen x'))))
--                                   ((h (fst (gen x) ++ fst (gen x'))))) ≡
--                                  subst {x = concatG G (map f (fst (gen (G .snd ._·_ x x'))))}
--                                        {G .snd ._·_ x x'}
--                                        B (snd (gen (G .snd ._·_ x x')))
--                                   (h (fst (gen (G .snd ._·_ x x'))))
--                          ppp = {!toPathP !}

--                          p* : concatG G (map f (fst (gen x) ++ fst (gen x')))
--                             ≡ concatG G (map f (fst (gen (G .snd ._·_ x x'))))
--                          p* = {!concatG·map!}

--                          ppp' = (sym (transportComposite
--                            (cong B (λ i₁ → concatG·map G f (fst (gen x)) (fst (gen x')) (~ i₁)))
--                            (λ i₁ → B (G .snd ._·_ (snd (gen x) i₁) (snd (gen x') i₁)))
--                              (h (fst (gen x) ++ fst (gen x'))))
--                              ∙ {!!})

--                          zzz0 : {!!}
--                          zzz0 = cong (GeneratedElimConstr G gen B h)
--                             ({! !})


--                          zzz : {!!}
--                          zzz = cong (GeneratedElimConstr G gen B h)
--                             ({!!} ∙  (sym (concatG·map G f (fst (gen x)) (fst (gen x')))
--                              ∙ sym (snd
--                                  (gen
--                                   (G .snd ._·_ (concatG G (map f (fst (gen x))))
--                                    (concatG G (map f (fst (gen x'))))))))
--                             ∙ ( λ i → snd (gen (G .snd ._·_ ((snd (gen x)) i) ((snd (gen x')) i))) i))

--                          zzzz : {!!}
--                          zzzz = {!  !}
--                      in  {!!} ∙ fromPathP zzz)

--                       i))
--               (toPathP {A = λ i → B2 (snd (gen x) i) (snd (gen x') i)}
--                     {x = h2 (fst (gen x)) (fst (gen x'))} refl i)
--                     )
--        (h' (fst (gen x)) (fst (gen x'))) 

-- transp
--       (λ i₁ → B (G .snd ._·_ (snd (gen x) i₁) (snd (gen x') i₁))) i0
--       (transp
--        (λ i₁ → B (concatG·map G f (fst (gen x)) (fst (gen x')) (~ i₁))) i0
--        (h (fst (gen x) ++ fst (gen x'))))
--       ≡
--       transp (λ i₁ → B (snd (gen (G .snd ._·_ x x')) i₁)) i0
--       (h (fst (gen (G .snd ._·_ x x'))))



GeneratedElimConstr' : ∀ {ℓ ℓ' ℓ''} (G : Group ℓ) → {A : Type ℓ'} → {f : A → ⟨ G ⟩} →
                 GeneratedByConstr G f → (B :  fst G → Type ℓ'') 
                  → (B ((GroupStr.1g (snd G))))
                  → (∀ a → ∀ x → B x → B ((G .snd · (f a)) x)) → ∀ a → B a
GeneratedElimConstr' G {f = f} gen tB hε h =
  GeneratedElimConstr G gen tB (ind hε λ {a} {l} x → h a _ x)
  

module GeneratedByConstrHom {ℓ ℓ' ℓ''} {G : Group ℓ} (H : Group ℓ'')
                    {A : Type ℓ'}
                    {f : A → ⟨ G ⟩}
                    (gen : GeneratedByConstr G f)
                    (genId : fst (gen (GroupStr.1g (snd G))) ≡ [])
                    (gInv : ∀ a → Σ _ λ b → (f b) ≡ (G .snd .GroupStr.inv (f a)))
                    (h : A → ⟨ H ⟩)
                  where

  module GS = GroupStr (snd G)
  module HS = GroupStr (snd H)

  ff : ⟨ G ⟩ → ⟨ H ⟩
  ff = concatG H ∘ (map h) ∘ fst ∘ gen

  module FF (fResp : ∀ a g → ff (f a GS.· g) ≡ (h a HS.· ff g)) where

    -- ww : ∀ (x y : ⟨ G ⟩ ) →  concatG H (map h (fst (gen ((G .snd · x) y))))
    --                              ≡ concatG H (map h (fst (gen x) ++ fst (gen y)))
    -- ww = GeneratedElimConstr G gen _
    --    {!λ !}

    pres1FF : ff GS.1g ≡ HS.1g
    pres1FF = cong (concatG H ∘ map h) genId

    -- ffHom : IsGroupHom (snd G) ff (snd H) 
    -- IsGroupHom.pres· ffHom =
    --   GeneratedElimConstr' G gen _
    --     (λ y → cong ff (GS.·IdL y) ∙ sym (HS.·IdL (ff y)) ∙
    --       cong (HS._· (ff y)) (sym (pres1FF)))
    --    λ a x x₁ y →
    --     let p = x₁ y
    --     in cong ff (sym (GS.·Assoc _ _ _)) ∙
    --       fResp a _ ∙ (cong (h a HS.·_) p ∙ HS.·Assoc _ _ _)
    --       ∙ cong (HS._· (ff y)) (sym (fResp a x)) 
    -- IsGroupHom.pres1 ffHom = pres1FF
    -- IsGroupHom.presinv ffHom = 
    --      GeneratedElimConstr G gen _
    --     λ l → cong (concatG H ∘ map h ∘ fst ∘ gen) (snd (concatGRev G f gInv l)) ∙
    --            {!!} 

 

module GeneratedByConstrHom' {ℓ ℓ' ℓ''} {G : Group ℓ} (H : Group ℓ'')
                    {A : Type ℓ'}
                    {f : A → ⟨ G ⟩}
                    (gen : GeneratedByConstr G f)
                    (genId : fst (gen (GroupStr.1g (snd G))) ≡ [])
                    (gInv : ∀ a → Σ _ λ b → (f b) ≡ (G .snd .GroupStr.inv (f a)))
                    (ff : ⟨ G ⟩ → ⟨ H ⟩)
                    (h : A → ⟨ H ⟩)
                  where

  module GS = GroupStr (snd G)
  module HS = GroupStr (snd H)

  module FF (fResp : ∀ a g → ff (f a GS.· g) ≡ (h a HS.· ff g)) where

    -- ww : ∀ (x y : ⟨ G ⟩ ) →  concatG H (map h (fst (gen ((G .snd · x) y))))
    --                              ≡ concatG H (map h (fst (gen x) ++ fst (gen y)))
    -- ww = GeneratedElimConstr G gen _
    --    {!λ !}

    -- pres1FF : ff GS.1g ≡ HS.1g
    -- pres1FF = {!!}
    -- -- cong (concatG H ∘ map h) genId

    -- ffHom : IsGroupHom (snd G) ff (snd H) 
    -- IsGroupHom.pres· ffHom =
    --   GeneratedElimConstr' G gen _
    --     (λ y → cong ff (GS.·IdL y) ∙ sym (HS.·IdL (ff y)) ∙
    --       cong (HS._· (ff y)) (sym (pres1FF)))
    --    λ a x x₁ y →
    --     let p = x₁ y
    --     in cong ff (sym (GS.·Assoc _ _ _)) ∙
    --       fResp a _ ∙ (cong (h a HS.·_) p ∙ HS.·Assoc _ _ _)
    --       ∙ cong (HS._· (ff y)) (sym (fResp a x)) 
    -- IsGroupHom.pres1 ffHom = pres1FF
    -- IsGroupHom.presinv ffHom = {!!} 


idEquivsG : ∀ {ℓ'} (B : Type ℓ') → Group ℓ'
idEquivsG B = makeGroup {G = singl (idEquiv B)}
     (idEquiv _ , refl)
     (λ (e , p) (f , q) → (e ∙ₑ f) , equivEq (cong fst (cong₂ _∙ₑ_ p q)))
     (λ (e , p) → invEquiv e , sym (invEquivIdEquiv B) ∙ cong invEquiv p)
     (isProp→isSet (isPropSingl {a = idEquiv B}))
     (λ _ _ _ → w _ _)
     (λ _ → w _ _)
     (λ _ → w _ _)
     (λ _ → w _ _)
     (λ _ → w _ _)
   where
     w : _
     w = isPropSingl {a = idEquiv B}

-- idEquivsG' : ∀ {ℓ'} (B : Type ℓ') → Group ℓ'
-- idEquivsG' B = makeGroup {G = singl (idEquiv B)}
--      (idEquiv _ , refl)
--      (λ (e , p) (f , q) → (e ∙ₑ f) , (p ∙ {!equivEq (cong (e ∙ₑ_) q)!}))
--      (λ (e , p) → invEquiv e , sym (invEquivIdEquiv B) ∙ cong invEquiv p)
--      (isProp→isSet (isPropSingl {a = idEquiv B}))
--      (λ _ _ _ → w _ _)
--      (λ _ → w _ _)
--      (λ _ → w _ _)
--      (λ _ → w _ _)
--      (λ _ → w _ _)
--    where
--      w : _
--      w = isPropSingl {a = idEquiv B}


toConst≃fromGens : ∀ {ℓ ℓ'} {G : Group ℓ} → {A : Type ℓ'} → {f : A → ⟨ G ⟩} →
                   ⟨ GeneratedBy G f ⟩ → 
                   ∀ {ℓ''} {B : Type ℓ''} 
                   → (g : A → singl (idEquiv B))
                   → GroupHom G (idEquivsG B)
fst (toConst≃fromGens f g) =
  rec₁ isPropSingl (uncurry
   (λ l _ → concatG (idEquivsG _) (map g l))) ∘ f 
snd (toConst≃fromGens {G = G} f {B = B} g) = zz

   where
     zz : IsGroupHom (G .snd) _ (idEquivsG B .snd)
     IsGroupHom.pres· zz = λ _ _ → isPropSingl _ _
     IsGroupHom.pres1 zz = isPropSingl _ _
     IsGroupHom.presinv zz = λ _ → isPropSingl _ _

-- module IsoOnGens' {ℓ ℓ' ℓ''} (A : Type ℓ'')
--                     (G : Group ℓ )(g : A → ⟨ G ⟩) (gGen : ⟨ GeneratedBy G g ⟩)
--                     (H : Group ℓ') (m : GroupHom G H)
--                     (h : A → ⟨ H ⟩) (hGen : GeneratedByConstr H h)
--                     (gh : fst m ∘ g ≡ h)
--                     (hGenId : [] ≡ fst (hGen (H .snd .GroupStr.1g)) )
--                     (hGenP : ∀ a → [ a ] ≡ fst (hGen (fst m (g a))) )
--                     (hGenP : ∀ a x →
--                           (G .snd .GroupStr._·_) (g a) (concatG G (map g (fst (hGen x)))) 
--                          ≡ concatG G
--                            (map g (fst (hGen ((H .snd .GroupStr._·_ (fst m (g a)) x))))))
--                     -- (gSIF : ∀ a → g a ≡ GroupStr.inv (snd G) (g a))
--                     -- (hSIF : ∀ a → (fst m ∘ g) a ≡ GroupStr.inv (snd H) ((fst m ∘ g) a))
--                     -- (gh : retract (fst m) (λ x → concatG G (map g (fst (hGen x)))))
                    
--                       where

--   module M = IsGroupHom (snd m)

--   riFold : ∀ l → fst m (concatG G (map g l)) ≡ concatG H (map (fst m ∘ g) l)
--   riFold [] = M.pres1
--   riFold (x ∷ l) = M.pres· _ _ ∙ cong (H .snd ._·_ _) (riFold l)

--   -- se : section (fst m) (λ x → concatG G (map g (fst (hGen x))))
--   -- se b = let (l , p) = hGen b in riFold l ∙ p      

--   -- hGenResp· : ∀ x y → concatG H
--   --     (map (fst m ∘ g) (fst (hGen (H .snd .GroupStr._·_ x y)))) ≡
--   --                     {!!}
--   -- hGenResp· x y = (snd (hGen (H .snd .GroupStr._·_ x y))) ∙ {!!}

--   -- isoGH : Iso ⟨ G ⟩ ⟨ H ⟩ 
--   -- Iso.fun isoGH = fst m
--   -- Iso.inv isoGH = concatG G ∘ map g ∘ fst ∘ hGen 
--   -- Iso.rightInv isoGH = se
--   -- Iso.leftInv isoGH =
--   --   GeneratedElim G gGen (λ _ → G .snd .GroupStr.is-set _ _)
--   --     (ind (cong (concatG G ∘ map g ∘ fst ∘ hGen) M.pres1
--   --         ∙ (cong (concatG G ∘ map g) (sym hGenId)))
--   --      λ {a} {l} p →
--   --        let p' = snd (hGen (fst m (concatG G (g a ∷ map g l))))
--   --        in
--   --            {!!}
--   --            ∙ cong (G .snd .GroupStr._·_ (g _)) p )


--   -- (sym hGenId)
--   -- Iso.inv isoGH = concatG G ∘ map g ∘ {!!} 
--   -- Iso.rightInv isoGH = se




--   -- m' : IsGroupHom (snd H) (concatG G ∘ map g ∘ fst ∘ hGen) (snd G)
--   -- m' = {!!}
--  -- (concatG G ∘ map g ∘ fst ∘ hGen) ((snd H · x) y) ≡
--  --      concatG G (map g (fst (hGen x)) ++ map g (fst (hGen y)))

--   -- IsGroupHom.pres· m' x y = cong (concatG G)
--   --    (cong {x = fst (hGen (snd H ._·_ x y))} (map g)
--   --      {!!}
--   --  ∙  (map-++ g (fst (hGen x)) (fst (hGen y))))
--   --  ∙ sym (concatG· {G = G} ((map g ∘ fst ∘ hGen) x) ((map g ∘ fst ∘ hGen) y))
--   -- IsGroupHom.pres1 m' = {!!}
--   -- IsGroupHom.presinv m' = {!!}

--   -- h : (a : A) →
--   --     foldr (G .snd ._·_) (G .snd .1g) (map g (fst (hGen (fst m (g a ))))) ≡ g a
--   -- h = {!!}
--   -- H/ : Group (ℓ-max ℓ' ℓ'') 
--   -- H/ = _ , RGenL/ H (λ x → fst m (g x)) hSIF

--   -- homH/ : GroupHom H/ G
--   -- fst homH/ = rec/ ((snd G) .GroupStr.is-set)
--   --              (concatG G ∘ map g)
--   --                w
--   --    where
--   --      w : (a b : List A) →
--   --            RGenL H (λ x → fst m (g x)) a b →
--   --            concatG G (map g a) ≡ concatG G (map g b)
--   --      w a b p = {!p'!}
--   --        where
--   --          p' : _
--   --          p' = (sym (foldr-map (H .snd ._·_) (H .snd .1g) (fst m ∘ g) a))
--   --            ∙ p ∙
--   --              foldr-map (H .snd ._·_) (H .snd .1g) (fst m ∘ g) b  


--   -- IsGroupHom.pres· (snd homH/) =
--   --   elimProp2 {!!} {!!}
--   -- IsGroupHom.pres1 (snd homH/) = refl
--   -- IsGroupHom.presinv (snd homH/) =
--   --   elimProp/ {!!} {!!}

--   -- m' : GroupHom H G
--   -- m' = compGroupHom (GeneratedByConstr→L/ H _ hSIF hGen) homH/

--   m' : GroupHom H G
--   fst m' = concatG G ∘ map g ∘ fst ∘ hGen
--   IsGroupHom.pres· (snd m') = {!!}
--   IsGroupHom.pres1 (snd m') = {!!}
--   IsGroupHom.presinv (snd m') = {!!}


--   isoGH : Iso ⟨ G ⟩ ⟨ H ⟩ 
--   Iso.fun isoGH = fst m
--   Iso.inv isoGH = concatG G ∘ map g ∘ fst ∘ hGen 
--   Iso.rightInv isoGH = se
--   -- Iso.inv isoGH = concatG G ∘ map g ∘ {!!} 
--   -- Iso.rightInv isoGH = se




-- -- concatGRev' : ∀ {ℓ ℓ'} (G : Group ℓ) → {A : Type ℓ'} → (f : A → ⟨ G ⟩) 
-- --               → (∀ a → (f a) ≡ (G .snd .GroupStr.inv (f a)))
-- --               → ∀ l → (concatG G (map f (rev l))) ≡ G .snd .GroupStr.inv (concatG G (map f l))  
-- -- concatGRev' G f invA =
-- --   {!!}


-- -- RGenL : ∀ {ℓ ℓ'} (G : Group ℓ) → {A : Type ℓ'} → (f : A → ⟨ G ⟩) → List A → List A → Type ℓ
-- -- RGenL G f x y = concatG G (map f x) ≡ concatG G (map f y)


-- -- RGenL/· : ∀ {ℓ ℓ'} (G : Group ℓ) → {A : Type ℓ'} → (f : A → ⟨ G ⟩) →
            
-- --            (List A / RGenL G f) → (List A / RGenL G f) → (List A / RGenL G f)
-- -- RGenL/· G f = setQuotBinOp (λ a → refl) (λ _ → refl) _++_
-- --     λ a a' b b' p q →
-- --        cong (concatG G)  (map-++ f a b)
-- --        ∙ sym (concatG· {G = G} (map f a) (map f b))
-- --        ∙ cong₂ (G .snd ._·_) p q
-- --        ∙ concatG· {G = G} (map f a') (map f b')
-- --        ∙ cong (concatG G) (sym (map-++ f a' b'))

-- -- RGenL/ : ∀ {ℓ ℓ'} (G : Group ℓ) → {A : Type ℓ'} → (f : A → ⟨ G ⟩) →
-- --            (∀ a → f a ≡ GroupStr.inv (snd G) (f a)) → 
-- --            GroupStr (List A / RGenL G f)
-- -- 1g (RGenL/ G f gsf) = [ [] ]/
-- -- _·_ (RGenL/ G f gsf ) = RGenL/· G f 
-- --   -- setQuotBinOp (λ a → refl) (λ _ → refl) _++_
-- --   --   λ a a' b b' p q →
-- --   --      cong (concatG G)  (map-++ f a b)
-- --   --      ∙ sym (concatG· {G = G} (map f a) (map f b))
-- --   --      ∙ cong₂ (G .snd ._·_) p q
-- --   --      ∙ concatG· {G = G} (map f a') (map f b')
-- --   --      ∙ cong (concatG G) (sym (map-++ f a' b'))
-- -- inv (RGenL/ G f gsf ) =
-- --   setQuotUnaryOp rev λ a a' p →
-- --       concatGRev' G f gsf a
-- --          ∙ (cong (G .snd .inv) p ) ∙
-- --        (sym (concatGRev' G f gsf a')) 
-- -- IsGroup.isMonoid (isGroup (RGenL/ G f gsf )) =
-- --   ismonoid (issemigroup squash/
-- --     (elimProp3 (λ _ _ _ → squash/ _ _) λ a b c → cong [_]/ (sym (++-assoc a b c)) ))
-- --     (elimProp/ (λ _ → squash/ _ _) (cong [_]/ ∘ ++-unit-r ))
-- --     ((elimProp/ (λ _ → squash/ _ _) λ _ → refl))
-- -- IsGroup.·InvR (isGroup (RGenL/ G f gsf )) =
-- --   elimProp/ (λ _ → squash/ _ _) --concatG· {G = G} a (rev a)
-- --     λ a → eq/ _ _
-- --        ((cong (concatG G) (map-++ f a (rev a))
-- --         ∙ sym (concatG· {G = G} (map f a) (map f (rev a))) ∙
-- --          cong (G .snd ._·_ (foldr (G .snd ._·_) (G .snd .1g) (map f a)))
-- --           (concatGRev' G f gsf a))
-- --         ∙ GroupStr.·InvR (snd G) (concatG G (map f a)))

-- -- IsGroup.·InvL (isGroup (RGenL/ G f gsf )) =
-- --    elimProp/ (λ _ → squash/ _ _) (ind refl {! !})

-- -- GeneratedByConstr→L/ : ∀ {ℓ ℓ'} (G : Group ℓ) → {A : Type ℓ'} → (f : A → ⟨ G ⟩) →
-- --          (gsf : ∀ a → f a ≡ GroupStr.inv (snd G) (f a)) → 
-- --          GeneratedByConstr G f →
-- --           GroupHom G ( _ , RGenL/ G f gsf)
-- -- fst (GeneratedByConstr→L/ G f gsf gen) = [_]/ ∘ fst ∘ gen
-- -- snd (GeneratedByConstr→L/ G f gsf gen) = w
-- --   where
-- --     module GG = GroupStr (snd G)

-- --     w : IsGroupHom (G .snd) (fst (GeneratedByConstr→L/ G f gsf gen))
-- --           (RGenL/ G f gsf)
-- --     IsGroupHom.pres· w x y =
-- --       eq/ _ _
-- --         ( snd (gen _) ∙
-- --            cong₂ GG._·_ (sym (snd (gen x))) (sym (snd (gen y)))
-- --           ∙ concatG·map G f (fst (gen x)) (fst (gen y))
-- --           )
-- --     IsGroupHom.pres1 w = eq/ _ _ (snd (gen GG.1g))
-- --     IsGroupHom.presinv w x = eq/ _ _
-- --        {!!}
-- --       -- ({!!} ∙ sym (concatGRev' G f gsf (fst (gen x))))

  




module IsoOnGens {ℓ ℓ' ℓ''} (A : Type ℓ'')
                    (G : Group ℓ )(g : A → ⟨ G ⟩) (gGen : ⟨ GeneratedBy G g ⟩)
                    (H : Group ℓ')(h : A → ⟨ H ⟩) (hGen : ⟨ GeneratedBy H h ⟩)
                    (m : GroupHom G H)
                    (m' : GroupHom H G)
                    
                    (sec' : ∀ a → fst m (fst m' (h a)) ≡ h a)
                    (ret' : ∀ a → fst m' (fst m (g a)) ≡ g a)
                      where

  module M = IsGroupHom (snd (compGroupHom m m'))
  module M' = IsGroupHom (snd (compGroupHom m' m))


  sec-fold : ∀ l → fst m (fst m' (concatG H (map h l))) ≡ concatG H (map h l)
  sec-fold = ind M'.pres1 λ p → M'.pres· _ _ ∙ cong₂ (snd H ._·_) (sec' _) p

  ret-fold : ∀ l → fst m' (fst m (concatG G (map g l))) ≡ concatG G (map g l)
  ret-fold = ind M.pres1 λ p → M.pres· _ _ ∙ cong₂ (snd G ._·_) (ret' _) p



  sec : section (fst m) (fst m')
  sec x =
     rec₁ (H .snd .is-set _ _)
      (λ (l , p) → cong (fst m ∘ fst m') (sym p) ∙∙ sec-fold l ∙∙ p)
      (hGen x)

  ret : retract (fst m) (fst m')
  ret x =
     rec₁ (G .snd .is-set _ _)
      (λ (l , p) → cong (fst m' ∘ fst m) (sym p) ∙∙ ret-fold l ∙∙ p)
      (gGen x)

  GIso : GroupIso G H
  Iso.fun (fst GIso) = fst m
  Iso.inv (fst GIso) = fst m'
  Iso.rightInv (fst GIso) = sec
  Iso.leftInv (fst GIso) = ret
  snd GIso = snd m



-- -- foldr-map : ∀ {ℓA ℓB ℓC} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
-- --              → (f : B → C → C) → (c : C) → (g : A → B) → (l : List A)
-- --              → foldr f c (map g l) ≡ foldr (f ∘ g) c l
-- -- foldr-map f c g = ind refl (cong (f (g _)))



-- module IsoOnGens' {ℓ ℓ' ℓ''} (A : Type ℓ'')
--                     (G : Group ℓ )(g : A → ⟨ G ⟩) (gGen : ⟨ GeneratedBy G g ⟩)
--                     (H : Group ℓ') (m : GroupHom G H)
--                     (hGen : GeneratedByConstr H (fst m ∘ g) )
--                     (gSIF : ∀ a → g a ≡ GroupStr.inv (snd G) (g a))
--                     (hSIF : ∀ a → (fst m ∘ g) a ≡ GroupStr.inv (snd H) ((fst m ∘ g) a))
--                     -- (gh : retract (fst m) (λ x → concatG G (map g (fst (hGen x)))))
                    
--                       where

--   module M = IsGroupHom (snd m)

--   riFold : ∀ l → fst m (concatG G (map g l)) ≡ concatG H (map (fst m ∘ g) l)
--   riFold [] = M.pres1
--   riFold (x ∷ l) = M.pres· _ _ ∙ cong (H .snd ._·_ _) (riFold l)

--   se : section (fst m) (λ x → concatG G (map g (fst (hGen x))))
--   se b = let (l , p) = hGen b in riFold l ∙ p      

--   -- m' : IsGroupHom (snd H) (concatG G ∘ map g ∘ fst ∘ hGen) (snd G)
--   -- m' = {!!}
--  -- (concatG G ∘ map g ∘ fst ∘ hGen) ((snd H · x) y) ≡
--  --      concatG G (map g (fst (hGen x)) ++ map g (fst (hGen y)))

--   -- IsGroupHom.pres· m' x y = cong (concatG G)
--   --    (cong {x = fst (hGen (snd H ._·_ x y))} (map g)
--   --      {!!}
--   --  ∙  (map-++ g (fst (hGen x)) (fst (hGen y))))
--   --  ∙ sym (concatG· {G = G} ((map g ∘ fst ∘ hGen) x) ((map g ∘ fst ∘ hGen) y))
--   -- IsGroupHom.pres1 m' = {!!}
--   -- IsGroupHom.presinv m' = {!!}

--   -- h : (a : A) →
--   --     foldr (G .snd ._·_) (G .snd .1g) (map g (fst (hGen (fst m (g a ))))) ≡ g a
--   -- h = {!!}
--   -- H/ : Group (ℓ-max ℓ' ℓ'') 
--   -- H/ = _ , RGenL/ H (λ x → fst m (g x)) hSIF

--   -- homH/ : GroupHom H/ G
--   -- fst homH/ = rec/ ((snd G) .GroupStr.is-set)
--   --              (concatG G ∘ map g)
--   --                w
--   --    where
--   --      w : (a b : List A) →
--   --            RGenL H (λ x → fst m (g x)) a b →
--   --            concatG G (map g a) ≡ concatG G (map g b)
--   --      w a b p = {!p'!}
--   --        where
--   --          p' : _
--   --          p' = (sym (foldr-map (H .snd ._·_) (H .snd .1g) (fst m ∘ g) a))
--   --            ∙ p ∙
--   --              foldr-map (H .snd ._·_) (H .snd .1g) (fst m ∘ g) b  


--   -- IsGroupHom.pres· (snd homH/) =
--   --   elimProp2 {!!} {!!}
--   -- IsGroupHom.pres1 (snd homH/) = refl
--   -- IsGroupHom.presinv (snd homH/) =
--   --   elimProp/ {!!} {!!}

-- -- --   -- m' : GroupHom H G
-- -- --   -- m' = compGroupHom (GeneratedByConstr→L/ H _ hSIF hGen) homH/

-- -- --   m' : GroupHom H G
-- -- --   fst m' = concatG G ∘ map g ∘ fst ∘ hGen
-- -- --   IsGroupHom.pres· (snd m') = {!!}
-- -- --   IsGroupHom.pres1 (snd m') = {!!}
-- -- --   IsGroupHom.presinv (snd m') = {!!}


-- -- --   isoGH : Iso ⟨ G ⟩ ⟨ H ⟩ 
-- -- --   Iso.fun isoGH = fst m
-- -- --   Iso.inv isoGH = concatG G ∘ map g ∘ fst ∘ hGen 
-- -- --   Iso.rightInv isoGH = se
-- -- --   -- Iso.inv isoGH = concatG G ∘ map g ∘ {!!} 
-- -- --   -- Iso.rightInv isoGH = se


-- -- --   Iso.leftInv isoGH = {!!}

-- -- --   GIso : GroupIso G H
-- -- --   GIso = isoGH , snd m


-- -- --     -- GeneratedElim G gGen
-- -- --     --   (λ _ → G .snd .GroupStr.is-set _ _)
-- -- --     --   (ind (cong (λ z → concatG G (map g (fst (hGen z)))) M.pres1
-- -- --     --      ∙ {!(snd (hGen (1g (H .snd))))!})
-- -- --     --     λ {a} {l} p → {!? ∙ sym (snd m .IsGroupHom.pres· (g a) ?)!} )
-- -- --         -- ∙ cong₂ (G .snd ._·_) refl p)
      
-- -- -- --     -- rec₁ (G .snd .GroupStr.is-set _ _)
-- -- -- --     --   (λ (l' , p') →
-- -- -- --     --      let (l , p) = hGen (fst m a)
-- -- -- --     --          z : l ≡ l'
-- -- -- --     --          z = {!!}
-- -- -- --     --          ww = cong (concatG G ∘ (map g)) z  ∙ p'
-- -- -- --     --      in {!!})
-- -- -- --     --   (gGen a)
-- -- -- --     -- let (l , p) = hGen (fst m a)
        
-- -- -- --     -- in {!!}

-- -- -- --     -- map2₁
-- -- -- --     --   {!!}
-- -- -- --     --    {!hGen!} {!!}

-- -- -- -- -- m'))
-- -- -- -- --   module M' = IsGroupHom (snd (compGroupHom m' m))


-- -- -- -- --   sec-fold : ∀ l → fst m (fst m' (concatG H (map h l))) ≡ concatG H (map h l)
-- -- -- -- --   sec-fold = ind M'.pres1 λ p → M'.pres· _ _ ∙ cong₂ (snd H ._·_) (sec' _) p

-- -- -- -- --   ret-fold : ∀ l → fst m' (fst m (concatG G (map g l))) ≡ concatG G (map g l)
-- -- -- -- --   ret-fold = ind M.pres1 λ p → M.pres· _ _ ∙ cong₂ (snd G ._·_) (ret' _) p



-- -- -- -- --   sec : section (fst m) (fst m')
-- -- -- -- --   sec x =
-- -- -- -- --      rec₁ (H .snd .is-set _ _)
-- -- -- -- --       (λ (l , p) → cong (fst m ∘ fst m') (sym p) ∙∙ sec-fold l ∙∙ p)
-- -- -- -- --       (hGen x)

-- -- -- -- --   ret : retract (fst m) (fst m')
-- -- -- -- --   ret x =
-- -- -- -- --      rec₁ (G .snd .is-set _ _)
-- -- -- -- --       (λ (l , p) → cong (fst m' ∘ fst m) (sym p) ∙∙ ret-fold l ∙∙ p)
-- -- -- -- --       (gGen x)

-- -- -- -- --   GIso : GroupIso G H
-- -- -- -- --   Iso.fun (fst GIso) = fst m
-- -- -- -- --   Iso.inv (fst GIso) = fst m'
-- -- -- -- --   Iso.rightInv (fst GIso) = sec
-- -- -- -- --   Iso.leftInv (fst GIso) = ret
-- -- -- -- --   snd GIso = snd m



