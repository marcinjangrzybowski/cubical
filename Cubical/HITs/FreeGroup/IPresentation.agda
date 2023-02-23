{-

This file contains:

- An implementation of the free group of a type of generators as a HIT

-}
{-# OPTIONS --safe #-}

module Cubical.HITs.FreeGroup.IPresentation where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.FreeGroup.Base
open import Cubical.HITs.FreeGroup.Properties renaming (elimProp to elimPropFG ; rec to recFG)
open import Cubical.HITs.PropositionalTruncation renaming (map to map₁ ; map2 to map2₁ ; elim to elim₁)
open import Cubical.HITs.SetQuotients hiding (_/_)
  renaming (rec to rec/ ; [_] to [_]/ ; rec2 to rec2/ ; elimProp to elimProp/ ; elim to elim/)
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Function
open import Cubical.Foundations.CartesianKanOps
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Everything hiding (assoc)
open import Cubical.Data.List renaming (map to mapList)
open import Cubical.Data.FinData as FD
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Empty as ⊥

open import Cubical.Data.Sum as ⊎

open import Cubical.Data.List.FinData

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup

open import Cubical.Foundations.HLevels



open import Cubical.Algebra.Group.Generators

open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'
infixr 5 _η∷_ _η∷'_

pattern _η∷_ x xs = inl x ∷ xs
pattern _η∷'_ x xs = inr x ∷ xs


rlt' : B → (A → B) → (B → B) → (B → B → B) → List (A ⊎ A) → B
rlt' ε' η' inv' _·'_ = foldr (_·'_ ∘ ⊎.elim η' (λ b → inv' (η' b))) ε'

module Presentation (A : Type ℓ) (Ix : Type ℓ') (relator : Ix → List (A ⊎ A)) where

  data PresentedGroup : Type (ℓ-max ℓ ℓ')

  rlt : Ix → PresentedGroup

  data PresentedGroup where
    η     : A → PresentedGroup
    _·_   : PresentedGroup → PresentedGroup → PresentedGroup
    ε     : PresentedGroup
    inv   : PresentedGroup → PresentedGroup
    assoc : ∀ x y z → x · (y · z) ≡ (x · y) · z
    idr   : ∀ x → x ≡ x · ε
    idl   : ∀ x → x ≡ ε · x
    invr  : ∀ x → x · (inv x) ≡ ε
    invl  : ∀ x → (inv x) · x ≡ ε
    rel   : ∀ xs ix → xs ≡ rlt ix → xs ≡ ε 
    trunc : isSet (PresentedGroup)


  rlt = (rlt' ε η inv _·_) ∘ relator
   -- (foldr w ε) ∘ relator
   --  where
   --    w : A ⊎ A → PresentedGroup → PresentedGroup
   --    w (inl x) = η x ·_
   --    w (inr x) = inv (η x) ·_


  presentedGroupGroupStr : GroupStr PresentedGroup
  GroupStr.1g presentedGroupGroupStr = ε
  GroupStr._·_ presentedGroupGroupStr = _·_
  GroupStr.inv presentedGroupGroupStr = inv
  GroupStr.isGroup presentedGroupGroupStr =
   makeIsGroup trunc assoc (sym ∘ idr) (sym ∘ idl) invr invl 

  presentedGroupGroup : Group ((ℓ-max ℓ ℓ'))
  presentedGroupGroup = _ , presentedGroupGroupStr




  module elimProp   {B : PresentedGroup → Type ℓ''}
                    (bTrunc : ∀ x → isProp (B x))
                    (b : ∀ x → B (η x))
                    (b· : ∀ {x y} → B x → B y → B (x · y))
                    (bε : B ε) 
                    (bInv : ∀ {x} → B x → B (inv x))
                      where

    f : ∀ x → B x
    f (η x) = b x
    f (x · x₁) = b· (f x) (f x₁)
    f ε = bε
    f (inv x) = bInv (f x)
    f (assoc x x₁ x₂ i) =
      isProp→PathP
        (λ i → bTrunc (assoc x x₁ x₂ i))
        (b· (f x) (b· (f x₁) (f x₂)))
        (b· (b· (f  x) (f x₁)) (f x₂))
         i 
    f (idr x i) =
          isProp→PathP
        (λ i → bTrunc (idr x i))
        (f x)
        (b· (f x) bε)
         i 

    f (idl x i) =
        isProp→PathP
        (λ i → bTrunc (idl x i))
        (f x)
        (b· bε (f x))
         i 

    f (invr x i) =
        isProp→PathP
        (λ i → bTrunc (invr x i))
        (b· (f x) (bInv (f x)))
        bε
         i 

    f (invl x i) =
       isProp→PathP
        (λ i → bTrunc (invl x i))
        (b· (bInv (f x)) (f x))
        bε
         i 

    f (rel x ix x₁ i) =
       isProp→PathP
        (λ i → bTrunc (rel x ix x₁ i))
        (f x)
        bε
         i 
    f (trunc x y p q i i₁) =
      isOfHLevel→isOfHLevelDep 2 (λ x → isProp→isSet (bTrunc x))
        (f x) (f y) (cong f p) (cong f q) (trunc x y p q) i i₁


  module rec (B : Group ℓ'') (b : A → ⟨ B ⟩) where

    FtoB : GroupHom (freeGroupGroup A) B
    FtoB = recFG b

    module BG = GroupStr (snd B)
    module BGT = GroupTheory B


    module PGT = GroupTheory (_ , presentedGroupGroupStr)

    rltB = (rlt' BG.1g b BG.inv (BG._·_)) 


    -- module _ (Brel :  ∀ x → (ix : Ix) → x ≡ {!!} → x ≡ BG.1g )
    --                (Brel-η : (ix : Ix) → ∀ a → η a ≡ rlt ix → b a ≡ BG.1g )
    --                (Brel-· :  ∀ (ix : Ix) →
    --                  ∀ x y → x BG.· y ≡ rltB (relator ix) → (x) BG.· (y) ≡ BG.1g )
    --                (Brel-inv :
    --                  (ix : Ix) → ∀ x → BG.inv x ≡ rltB (relator ix) → BG.inv (x) ≡ BG.1g )
    --                     where



    --   f : PresentedGroup → ⟨ B ⟩
    --   f (η x) = b x
    --   f (x · x₁) = f x BG.· f x₁
    --   f ε = BG.1g
    --   f (inv x) = BG.inv (f x)
    --   f (assoc x x₁ x₂ i) = BG.·Assoc (f x) (f x₁) (f x₂) i
    --   f (idr x i) = BG.·IdR (f x) (~ i)
    --   f (idl x i) = BG.·IdL (f x) (~ i)
    --   f (invr x i) = BG.·InvR (f x) i
    --   f (invl x i) = BG.·InvL (f x) i


    --   f (rel x ix x₁ i) = Brel (f x) ix (λ i → {!f (x₁ )!}) i

    --   f (trunc x y p q i i₁) =
    --     BG.is-set (f x) (f y) (cong f p) (cong f q) i i₁

    --   gh : GroupHom presentedGroupGroup B
    --   gh = f , {!!}




  PresentedGeneratedBy' :
        (∀ a → Σ _ λ b → Path (PresentedGroup) (η b) (inv (η a)))
        → ⟨ GeneratedBy (presentedGroupGroup) (η) ⟩
  PresentedGeneratedBy' invGens =
    elimProp.f (λ _ → squash₁)
      (λ x → ∣ [ x ] , sym (idr (η x)) ∣₁)
           (map2₁ λ (x , p) (y , q) → x ++ y ,
       (cong (concatG (presentedGroupGroup)) (map-++ η x y)
         ∙∙ sym (concatG· {G = presentedGroupGroup} (mapList η x) (mapList η y))
         ∙∙ cong₂ _·_ p q ))
      ∣ [] , refl ∣₁
           (map₁ (uncurry
       (ind (λ p →  [] , sym inv1g ∙ cong inv p )
            λ {a} {l} z y →
               let (a' , p') = invGens a
                   (l' , p'') = concatGRev (presentedGroupGroup) η
                     invGens l
               in l' ++ [ a' ] ,
                      (cong (concatG (presentedGroupGroup)) ( map-++ η l' [ a' ]))  ∙
                    (sym (concatG· {G = (presentedGroupGroup)} (mapList η l') [ η a' ])) ∙
                   cong₂ {B = λ _ → PresentedGroup} 
                         {x = concatG (presentedGroupGroup) (mapList η l')}
                         {y = inv (concatG (presentedGroupGroup) (mapList η l))}
                         {C = λ _ _ → PresentedGroup}
                          _·_ (sym p'') (sym (idr _) ∙ p')
                    ∙ sym (invDistr _ _) ∙ cong inv y)))
       where

         open GroupTheory presentedGroupGroup


  -- concatGRevP : ∀ {ℓ ℓ'} (G : Group ℓ) → {A : Type ℓ'} → (f : A → ⟨ G ⟩) 
  --             → (∀ a → Σ _ λ b → (f b) ≡ (G .snd .GroupStr.inv (f a)))
  --             → ∀ l → Σ _ λ l' → G .snd .GroupStr.inv (concatG G (map f l))
  --                ≡ (concatG G (map f l'))  
  -- concatGRevP = ?
  
  -- PresentedGeneratedBy :
  --       ⟨ GeneratedBy (presentedGroupGroup) (η) ⟩
  -- PresentedGeneratedBy =
  --   elimProp.f (λ _ → squash₁)
  --     (λ x → ∣ [ x ] , sym (idr (η x)) ∣₁)
  --          (map2₁ λ (x , p) (y , q) → x ++ y ,
  --      (cong (concatG (presentedGroupGroup)) (map-++ η x y)
  --        ∙∙ sym (concatG· {G = presentedGroupGroup} (mapList η x) (mapList η y))
  --        ∙∙ cong₂ _·_ p q ))
  --     ∣ [] , refl ∣₁
        
  --          (map₁ (uncurry
  --      (ind (λ p →  [] , sym inv1g ∙ cong inv p )
  --           λ {a} {l} x y → 

  --             {!l!} , {!!})))
  --      where

  --        open GroupTheory presentedGroupGroup


data P' {A : Type ℓ} (P : ℙ (FreeGroup A)) (x : FreeGroup A)  : Type ℓ where 
  η : x ∈ P → P' P x
  id∈ : x ≡ ε → P' P x
  ·∈ : ∀ {x' y} → (x ≡ x' · y) → P' P x' → P' P y   → P' P x
  inv∈ : ∀ {x'} → x ≡ inv x' → P' P x' → P' P x
  norm∈ : ∀ g h →  P' P h → x ≡  (g · (h · inv g)) → P' P x 
  truncP' : isProp (P' P x)


Pclo : (A : Type ℓ) (P : ℙ (FreeGroup A)) → ℙ ((FreeGroup A))
Pclo A P x = P' P x , truncP' 

FromPres : (A : Type ℓ) (P : ℙ (FreeGroup A)) → Group ℓ
FromPres A P = freeGroupGroup A /
   ((Pclo A P , record { id-closed = id∈ refl ; op-closed = ·∈ refl ; inv-closed = inv∈ refl }) ,
    λ g h x → norm∈ g h x refl)


module Pres≡ (A : Type ℓ) (Ix : Type ℓ) (relator : Ix → List (A ⊎ A)) where



  open Presentation A Ix relator

  module FG = GroupStr (snd (freeGroupGroup A)) 
  module FGT = GroupTheory (freeGroupGroup A)

  module PG = GroupStr (snd presentedGroupGroup) 
  module PGT = GroupTheory (presentedGroupGroup) 

  P : ℙ (FreeGroup A)
  P x =  ∥ Σ Ix (λ ix → foldr (_·_ ∘ ⊎.elim η (λ b → inv (η b))) ε (relator ix) ≡ x) ∥₁ , squash₁

  fromPres : Group ℓ
  fromPres = FromPres A P

  ff : GroupHom (freeGroupGroup A) presentedGroupGroup
  ff = recFG η

  -- PresGeneratedBy' :
  --       (∀ a → Σ _ λ b → Path (PresentedGroup) (η b) (inv (η a)))
  --       → ⟨ GeneratedBy (FromPres A P) (η) ⟩
  -- PresGeneratedBy' = {!!}

  -- fromPresented : ⟨ presentedGroupGroup ⟩ → ⟨ fromPres ⟩ 
  -- fromPresented = {!!}

  -- toPresented : ⟨ fromPres ⟩ →  ⟨ presentedGroupGroup ⟩ 
  -- toPresented =
  --   rec/ trunc
  --        (fst ff)
  --        ww
  --     where
        

  --       ww : (a b : ⟨ freeGroupGroup A ⟩) →
  --             P' P (a FG.· FG.inv b)  → fst ff a ≡ fst ff b
  --       ww a b (η x) = elim₁ (λ _ → trunc _ _)
  --         (λ x₁ → let z = rel _ (fst x₁) (cong (fst ff) (sym (snd x₁)) ∙ {!!})
  --                 in PGT.invUniqueL z ∙ PGT.invInv _) x
  --       ww a b (id∈ x) = PGT.invUniqueL (cong (fst ff) x) ∙ PGT.invInv _
  --       ww a b (·∈ x r r₁) = {!!}
  --       ww a b (inv∈ {x₁} x r) =
  --         let z = ww _ _ {!r!}
  --         in {!!}
  --       ww a b (norm∈ g h r x) = {!!}
  --       ww a b (truncP' r r₁ i) = {!!}
        
  -- GIsoPres : GroupIso fromPres presentedGroupGroup
  -- GIsoPres = iso toPresented {!!} {!!} {!!} , {!!}




-- data P'' {A : Type ℓ} {Ix : Type ℓ} (relator : Ix → List (A ⊎ A)) : (x : FreeGroup A) → Type ℓ where 
--   η : ∀ ix → P'' relator ((rlt' ε η inv _·_ (relator (ix))))
--   id∈ : P'' relator ε
--   ·∈ : ∀ {x y} →  P'' relator x → P'' relator y   → P'' relator (x · y)
--   inv∈ : ∀ {x'} →  P'' relator x' → P'' relator (inv x')
--   norm∈ : ∀ g h →  P'' relator h → P'' relator (g · (h · inv g)) 
--   truncP'' : ∀ x → isProp (P'' relator x)

-- P''elim : {A : Type ℓ} {Ix : Type ℓ} (relator : Ix → List (A ⊎ A))
--             → {B : FreeGroup A → Type ℓ''} → (truncB : ∀ x → isProp (B x)) 
--             →    (ηB : ∀ ix → B ((rlt' ε η inv _·_ (relator (ix)))))
--                 -- id∈ : P'' relator ε
--                 -- ·∈ : ∀ {x y} →  P'' relator x → P'' relator y   → P'' relator (x · y)
--                 -- inv∈ : ∀ {x'} →  P'' relator x' → P'' relator (inv x')
--                 -- norm∈ : ∀ g h →  P'' relator h → P'' relator (g · (h · inv g)) 

--             → ∀ x → P'' relator x →  B x    
-- P''elim relator {B = B} tB ηB =
--   elimPropFG
--     (λ _ → isPropΠ λ _ → tB _)
--     w 
--     {!!}
--     {!!}
--     {!!}
--   where
--     w : ∀ a → P'' relator (η a) → B (η a)
--     w a x = {!x!}

-- FromPres' : {A : Type ℓ} {Ix : Type ℓ} (relator : Ix → List (A ⊎ A)) → Group ℓ
-- FromPres' {A = A} {Ix} relator = freeGroupGroup A /
--    ((((λ x → (P'' relator x , truncP'' x))) ,
--      record { id-closed = id∈ ; op-closed = ·∈ ; inv-closed = inv∈ })
--      , norm∈)

-- module _ {A : Type ℓ} {Ix : Type ℓ} (relator : Ix → List (A ⊎ A)) where

--   module PG = GroupStr (snd (FromPres' relator)) 
--   module PGT = GroupTheory (FromPres' relator) 
  

--   module FromPresElimProp' {B : ⟨ FromPres' relator ⟩  → Type ℓ''}
--                       (bTrunc : ∀ x → isProp (B x))
--                       (b : ∀ x → B ([ η x ]/))
--                       (b· : ∀ {x y} → B [ x ]/ → B [ y ]/ → B ([ x · y ]/ ))
--                       (bε : B [ ε ]/) 
--                       (bInv : ∀ {x} → B [ x ]/ → B (PG.inv [ x ]/))
--                         where
    
--     f : ∀ x → B x 
--     f = elimProp/ (λ _ → bTrunc _)
--       (elimPropFG (λ _ → bTrunc _)
--        b (λ _ _ → b·) bε λ _ → bInv )

--   module FromPresRec' {B : Group ℓ''}                      
--                       (b : A → ⟨ B ⟩)
--                       -- (b· : ∀ {x y} → B [ x ]/ → B [ y ]/ → B ([ x · y ]/ ))
--                       -- (bε : B [ ε ]/) 
--                       -- (bInv : ∀ {x} → B [ x ]/ → B (PG.inv [ x ]/))
--                         where

--     module BG = GroupStr (snd B) 
--     module BGT = GroupTheory B


--     f : ⟨ FromPres' relator ⟩ → ⟨ B ⟩ 
--     f = rec/ (BG.is-set)
--       (fst (recFG {Group = B} b))
--        {!!}


-- -- open Presentation



-- -- module elimProp {A : Type ℓ} {Ix : Type ℓ'} {R : Ix → ?}
-- --                   {B : ∀ {n} → ∀ {P} → PresentedGroup {A = A} {n = n} P → Type ℓ''}
-- --                   (bTrunc : ∀ {n} {P} → ∀ x → isProp (B {n} {P} x))
-- --                   (b : ∀ {n} {P} → ∀ x → B {n} {P} (η x))
-- --                   (b· : ∀ {n} {P} → ∀ {x y} → B {n} {P} x → B {n} {P} y → B (x · y))
-- --                   (bε : ∀ {n} {P} → B {n} {P} ε) 
-- --                   (bInv : ∀ {n} {P} → ∀ {x} → B {n} {P} x → B (inv x))
-- --                     where
-- --                   -- (onF : ∀ x → B (fromFree x))

-- --   f : ∀ {n} {P} → ∀ x → B x
-- --   f (η x) = b x
-- --   f (x · x₁) = b· (f x) (f x₁)
-- --   f ε = bε
-- --   f (inv x) = bInv (f x)
-- --   f (assoc x x₁ x₂ i) =
-- --     isProp→PathP
-- --       (λ i → bTrunc (assoc x x₁ x₂ i))
-- --       (b· (f x) (b· (f x₁) (f x₂)))
-- --       (b· (b· (f  x) (f x₁)) (f x₂))
-- --        i 
-- --   f (idr x i) =
-- --         isProp→PathP
-- --       (λ i → bTrunc (idr x i))
-- --       (f x)
-- --       (b· (f x) bε)
-- --        i 

-- --   f (idl x i) =
-- --       isProp→PathP
-- --       (λ i → bTrunc (idl x i))
-- --       (f x)
-- --       (b· bε (f x))
-- --        i 

-- --   f (invr x i) =
-- --       isProp→PathP
-- --       (λ i → bTrunc (invr x i))
-- --       (b· (f x) (bInv (f x)))
-- --       bε
-- --        i 

-- --   f (invl x i) =
-- --      isProp→PathP
-- --       (λ i → bTrunc (invl x i))
-- --       (b· (bInv (f x)) (f x))
-- --       bε
-- --        i 

-- --   f (rel x ix x₁ i) =
-- --      isProp→PathP
-- --       (λ i → bTrunc (rel x ix x₁ i))
-- --       (f x)
-- --       bε
-- --        i 
-- --   f (trunc x x₁ x₂ y i i₁) = {!!}

-- -- -- PresentedGeneratedBy : ∀ n → (R : Presentation A n)
-- -- --    → ⟨ GeneratedBy (presentedGroupGroup R) (η) ⟩
-- -- -- PresentedGeneratedBy n R x = {!x!}


-- -- -- -- fromList : ∀ {A : Type ℓ}  {Ix : Type ℓ'} {R : Ix → List A × List A}
-- -- -- --                   → List A → PresentedGroup A R 




-- -- -- -- fromList [] = ε
-- -- -- -- -- fromList (x ∷ []) = η x
-- -- -- -- fromList (x ∷ xs) = η x · fromList (xs)




-- -- -- -- -- module elimProp {A : Type ℓ}
-- -- -- -- --                   {Ix : Type ℓ'} {R : Ix → List A × List A}
-- -- -- -- --                   {B : PresentedGroup A R → Type ℓ''}
-- -- -- -- --                   (bTrunc : ∀ x → isProp (B x))
-- -- -- -- --                   (b : ∀ x → B (η x))
-- -- -- -- --                   (b· : ∀ {x y} → B x → B y → B (x · y))
-- -- -- -- --                   (bε : B ε) 
-- -- -- -- --                   (bInv : ∀ {x} → B x → B (inv x))
-- -- -- -- --                     where
-- -- -- -- --                   -- (onF : ∀ x → B (fromFree x))



-- -- -- -- --   f : ∀ n → Fin n ≃ Ix → ∀ x → B x


-- -- -- -- --   f' : ∀ n → (e : Fin n ≃ Ix) → ∀ ix  →
-- -- -- -- --          PathP (λ i → B (rel ix i))
-- -- -- -- --            (f n e (fromList (fst (R ix))))
-- -- -- -- --            (f n e (fromList (snd (R ix))))
-- -- -- -- --   -- f' = ?

-- -- -- -- --   f n e (η x) = b x
-- -- -- -- --   f n e (x · x₁) = b· (f n e x) (f n e  x₁)
-- -- -- -- --   f n e  ε = bε
-- -- -- -- --   f n e  (inv x) = bInv (f n e  x)
-- -- -- -- --   f n e (assoc x x₁ x₂ i) =
-- -- -- -- --     isProp→PathP
-- -- -- -- --       (λ i → bTrunc (assoc x x₁ x₂ i))
-- -- -- -- --       (b· (f n e x) (b· (f n e x₁) (f n e x₂)))
-- -- -- -- --       (b· (b· (f n e x) (f n e x₁)) (f n e x₂))
-- -- -- -- --        i 
-- -- -- -- --   f n e (idr x i) =
-- -- -- -- --         isProp→PathP
-- -- -- -- --       (λ i → bTrunc (idr x i))
-- -- -- -- --       (f n e x)
-- -- -- -- --       (b· (f n e x) bε)
-- -- -- -- --        i 

-- -- -- -- --   f n e (idl x i) =
-- -- -- -- --       isProp→PathP
-- -- -- -- --       (λ i → bTrunc (idl x i))
-- -- -- -- --       (f n e x)
-- -- -- -- --       (b· bε (f n e x))
-- -- -- -- --        i 

-- -- -- -- --   f n e (invr x i) =
-- -- -- -- --       isProp→PathP
-- -- -- -- --       (λ i → bTrunc (invr x i))
-- -- -- -- --       (b· (f n e x) (bInv (f n e x)))
-- -- -- -- --       bε
-- -- -- -- --        i 

-- -- -- -- --   f n e (invl x i) =
-- -- -- -- --      isProp→PathP
-- -- -- -- --       (λ i → bTrunc (invl x i))
-- -- -- -- --       (b· (bInv (f n e x)) (f n e x))
-- -- -- -- --       bε
-- -- -- -- --        i 
-- -- -- -- --   f n e (rel ix i) = {!!}
-- -- -- -- --   -- f (suc n) e (rel ix i) = {!!}

-- -- -- -- --   -- f' ix i
-- -- -- -- --       -- let z = isProp→PathP
-- -- -- -- --       --          (λ i → bTrunc (rel ix i))
-- -- -- -- --       --          (f (fromFree (fst (R ix))))
-- -- -- -- --       --          (f (fromFree (snd (R ix))))
-- -- -- -- --       --           i
-- -- -- -- --       -- in {!z!}
-- -- -- -- --   f n e (trunc x x₁ x₂ y i i₁) = {!!}

-- -- -- -- --   f' = {!!}



-- -- -- -- -- -- -- module elimProp {A : Type ℓ} {R : List A → List A → Type ℓ''}
-- -- -- -- -- -- --                   {B : PresentedGroup A  R → Type ℓ''}
-- -- -- -- -- -- --                   (bTrunc : ∀ x → isProp (B x))
-- -- -- -- -- -- --                   (b : ∀ x → B (η x))
-- -- -- -- -- -- --                   (b· : ∀ {x y} → B x → B y → B (x · y))
-- -- -- -- -- -- --                   (bε : B ε)
-- -- -- -- -- -- --                   (bInv : ∀ {x} → B x → B (inv x))
-- -- -- -- -- -- --                   -- (onF : ∀ x → B (fromFree x))
                  
-- -- -- -- -- -- --                     where


-- -- -- -- -- -- --   f : ∀ x → B x
  
-- -- -- -- -- -- --   f' : ∀ {a a'} → (r : R a a') →
-- -- -- -- -- -- --          PathP (λ i → B (rel r i))
-- -- -- -- -- -- --            (f (fromList a))
-- -- -- -- -- -- --            (f (fromList a'))
-- -- -- -- -- -- --   -- f' = {!!}

-- -- -- -- -- -- -- -- Goal: B (rel ix i)
-- -- -- -- -- -- -- -- ———— Boundary ——————————————————————————————————————————————
-- -- -- -- -- -- -- -- i = i0 ⊢ f (fromList a)
-- -- -- -- -- -- -- -- i = i1 ⊢ f (fromList a')

-- -- -- -- -- -- --   f (η x) = b x
-- -- -- -- -- -- --   f (x · x₁) = b· (f x) (f x₁)
-- -- -- -- -- -- --   f ε = bε
-- -- -- -- -- -- --   f (inv x) = bInv (f x)
-- -- -- -- -- -- --   f (assoc x x₁ x₂ i) =
-- -- -- -- -- -- --     isProp→PathP
-- -- -- -- -- -- --       (λ i → bTrunc (assoc x x₁ x₂ i))
-- -- -- -- -- -- --       (b· (f x) (b· (f x₁) (f x₂)))
-- -- -- -- -- -- --       (b· (b· (f x) (f x₁)) (f x₂))
-- -- -- -- -- -- --        i 
-- -- -- -- -- -- --   f (idr x i) =
-- -- -- -- -- -- --         isProp→PathP
-- -- -- -- -- -- --       (λ i → bTrunc (idr x i))
-- -- -- -- -- -- --       (f x)
-- -- -- -- -- -- --       (b· (f x) bε)
-- -- -- -- -- -- --        i 

-- -- -- -- -- -- --   f (idl x i) =
-- -- -- -- -- -- --       isProp→PathP
-- -- -- -- -- -- --       (λ i → bTrunc (idl x i))
-- -- -- -- -- -- --       (f x)
-- -- -- -- -- -- --       (b· bε (f x))
-- -- -- -- -- -- --        i 

-- -- -- -- -- -- --   f (invr x i) =
-- -- -- -- -- -- --       isProp→PathP
-- -- -- -- -- -- --       (λ i → bTrunc (invr x i))
-- -- -- -- -- -- --       (b· (f x) (bInv (f x)))
-- -- -- -- -- -- --       bε
-- -- -- -- -- -- --        i 

-- -- -- -- -- -- --   f (invl x i) =
-- -- -- -- -- -- --      isProp→PathP
-- -- -- -- -- -- --       (λ i → bTrunc (invl x i))
-- -- -- -- -- -- --       (b· (bInv (f x)) (f x))
-- -- -- -- -- -- --       bε
-- -- -- -- -- -- --        i 
-- -- -- -- -- -- --   f (rel {a} {a'} ix i) = f' ix i

-- -- -- -- -- -- --   -- f' ix i
-- -- -- -- -- -- --       -- let z = isProp→PathP
-- -- -- -- -- -- --       --          (λ i → bTrunc (rel ix i))
-- -- -- -- -- -- --       --          (f (fromFree (fst (R ix))))
-- -- -- -- -- -- --       --          (f (fromFree (snd (R ix))))
-- -- -- -- -- -- --       --           i
-- -- -- -- -- -- --       -- in {!z!}
-- -- -- -- -- -- --   f (trunc x x₁ x₂ y i i₁) = {!!}

-- -- -- -- -- -- --   f' {[]} {[]} r = {!!}
-- -- -- -- -- -- --   f' {[]} {x ∷ a'} r = {!!}
-- -- -- -- -- -- --   f' {x ∷ a} {[]} r = {!!}
-- -- -- -- -- -- --   f' {x ∷ a} {x₁ ∷ a'} r =
-- -- -- -- -- -- --     {!!}



-- -- -- -- -- -- Presented : {A : Type ℓ} (R : List A → List A → Type ℓ') → Group (ℓ-max ℓ ℓ')
-- -- -- -- -- -- Presented R = _ , (presentedGroupGroupStr {R = R})

-- -- -- -- -- -- Presented/ : (A : Type ℓ) {Ix : Type ℓ'} (R : Ix → FreeGroup A × FreeGroup A) →
-- -- -- -- -- --                Type (ℓ-max ℓ ℓ')
-- -- -- -- -- -- Presented/ A {Ix} R = FreeGroup A /
-- -- -- -- -- --                  λ x y → Σ Ix λ ix → (fst (R ix) ≡ x) × (snd (R ix) ≡ y)  



-- -- -- -- -- -- -- IsoPresentedQt : {A : Type ℓ} {Ix : Type ℓ'} (R : Ix → FreeGroup A × FreeGroup A)
-- -- -- -- -- -- --       → Iso ((PresentedGroup A {Ix} R)) (Presented/ A R)
-- -- -- -- -- -- -- IsoPresentedQt {A = A} {Ix} R = w
-- -- -- -- -- -- --   where


-- -- -- -- -- -- --     w : Iso (PresentedGroup A R) (Presented/ A R)
-- -- -- -- -- -- --     Iso.fun w (η x) = {!!}
-- -- -- -- -- -- --     Iso.fun w (x · x₁) = {!!}
-- -- -- -- -- -- --     Iso.fun w ε = {!!}
-- -- -- -- -- -- --     Iso.fun w (inv x) = {!!}
-- -- -- -- -- -- --     Iso.fun w (assoc x x₁ x₂ i) = {!!}
-- -- -- -- -- -- --     Iso.fun w (idr x i) = {!!}
-- -- -- -- -- -- --     Iso.fun w (idl x i) = {!!}
-- -- -- -- -- -- --     Iso.fun w (invr x i) = {!!}
-- -- -- -- -- -- --     Iso.fun w (invl x i) = {!!}
-- -- -- -- -- -- --     Iso.fun w (rel ix i) =
-- -- -- -- -- -- --       {!eq/ ? ? ? i!}
-- -- -- -- -- -- --     Iso.fun w (trunc x x₁ x₂ y i i₁) = {!!}
-- -- -- -- -- -- --     Iso.inv w =
-- -- -- -- -- -- --       rec/ trunc fromFree
-- -- -- -- -- -- --         λ a b r → sym (cong fromFree (fst (snd r))) ∙∙  rel (fst r) ∙∙ cong fromFree (snd (snd r)) 
-- -- -- -- -- -- --     Iso.rightInv w = {!!}
-- -- -- -- -- -- --     Iso.leftInv w = {!!}

-- -- -- -- -- -- -- PresentedGeneratedBy' : {A : Type ℓ} {Ix : Type ℓ'} (R : Ix → FreeGroup A × FreeGroup A) →
-- -- -- -- -- -- --                           (∀ a → Σ _ λ b → Path (PresentedGroup A {Ix} R) (η b) (inv (η a)))
-- -- -- -- -- -- --                            →  ⟨ GeneratedBy (Presented R) (η) ⟩
-- -- -- -- -- -- -- PresentedGeneratedBy' {A = A} {Ix} R invGens =
-- -- -- -- -- -- --    elimProp.f
-- -- -- -- -- -- --      (λ _ → squash₁)
-- -- -- -- -- -- --      (λ x → ∣ [ x ] , sym (idr (η x)) ∣₁)
-- -- -- -- -- -- --      (map2₁ λ (x , p) (y , q) → x ++ y ,
-- -- -- -- -- -- --        (cong (concatG (Presented R)) (map-++ η x y)
-- -- -- -- -- -- --          ∙∙ sym (concatG· {G = Presented R} (map η x) (map η y))
-- -- -- -- -- -- --          ∙∙ cong₂ _·_ p q ))
-- -- -- -- -- -- --      ∣ [] , refl ∣₁
-- -- -- -- -- -- --      (map₁ (uncurry
-- -- -- -- -- -- --        (ind (λ p →  [] , sym inv1g ∙ cong inv p )
-- -- -- -- -- -- --             λ {a} {l} z y →
-- -- -- -- -- -- --                let (a' , p') = invGens a
-- -- -- -- -- -- --                    (l' , p'') = concatGRev (Presented R) η
-- -- -- -- -- -- --                      invGens l
-- -- -- -- -- -- --                in l' ++ [ a' ] ,
-- -- -- -- -- -- --                       (cong (concatG (Presented R)) ( map-++ η l' [ a' ]))  ∙
-- -- -- -- -- -- --                     (sym (concatG· {G = (Presented R)} (map η l') [ η a' ])) ∙
-- -- -- -- -- -- --                    cong₂ {B = λ _ → PresentedGroup A R} 
-- -- -- -- -- -- --                          {x = concatG (Presented R) (map η l')}
-- -- -- -- -- -- --                          {y = inv (concatG (Presented R) (map η l))}
-- -- -- -- -- -- --                          {C = λ _ _ → PresentedGroup A R}
-- -- -- -- -- -- --                           _·_ (sym p'') (sym (idr _) ∙ p')
-- -- -- -- -- -- --                     ∙ sym (invDistr _ _) ∙ cong inv y)))
-- -- -- -- -- -- --   where

-- -- -- -- -- -- --     open GroupTheory (Presented R)







-- -- -- -- -- -- -- --(map₁ λ (x , p) → (rev x) , {!!} ∙ cong inv p )  
-- -- -- -- -- -- --   -- λ x → ∣ [ {!x!} ] , {!!} ∣₁ 
