{-

This file contains:

- An implementation of the free group of a type of generators as a HIT

-}
{-# OPTIONS --safe #-}

module Cubical.HITs.FreeGroup.IPresentation3 where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.FreeGroup.Base
open import Cubical.HITs.FreeGroup.Properties renaming (elimProp to elimPropFG ; rec to recFG)
open import Cubical.HITs.PropositionalTruncation renaming (map to map₁ ; map2 to map2₁ ; elim to elim₁)
open import Cubical.HITs.SetQuotients hiding (_/_) renaming (rec to rec/ ; [_] to [_]/ ; rec2 to rec2/)
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Function
open import Cubical.Foundations.CartesianKanOps
import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Everything hiding (assoc)
open import Cubical.Data.List renaming (map to mapList)
open import Cubical.Data.FinData as FD
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Nat.Order.Recursive
open import Cubical.Data.Empty as ⊥

open import Cubical.Data.Sum as ⊎

-- open import Cubical.Data.List.FinData

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup

open import Cubical.Foundations.HLevels

open import Cubical.Algebra.SymmetricGroup


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


-- rlt' : B → (A → B) → (B → B) → (B → B → B) → List (A ⊎ A) → B
-- rlt' ε' η' inv' _·'_ = foldr (_·'_ ∘ ⊎.elim η' (λ b → inv' (η' b))) ε'


LoopsOfG : ∀ {ℓ} {A : Type ℓ} → isGroupoid A →
     A → Group ℓ
LoopsOfG isG x =
 makeGroup {G = x ≡ x} refl
  _∙_ sym (isG x x) GL.assoc (sym ∘ GL.rUnit) (sym ∘ GL.lUnit) rCancel lCancel  

module Presentation (A : Type ℓ) (Ix : Type ℓ') (relator : Ix → (List (A ⊎ A) × A)) where

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
    rel   : ∀ ix → rlt ix ≡ ε 
    trunc : isSet (PresentedGroup)


  rlt ix = foldr ( _·_ ∘ ⊎.elim η (λ b → inv (η b))) (η (snd (relator ix))) (fst (relator ix))
     

  presentedGroupGroupStr : GroupStr PresentedGroup
  GroupStr.1g presentedGroupGroupStr = ε
  GroupStr._·_ presentedGroupGroupStr = _·_
  GroupStr.inv presentedGroupGroupStr = inv
  GroupStr.isGroup presentedGroupGroupStr =
   makeIsGroup trunc assoc (sym ∘ idr) (sym ∘ idl) invr invl 

  presentedGroupGroup : Group ((ℓ-max ℓ ℓ'))
  presentedGroupGroup = _ , presentedGroupGroupStr

  record Eliminators ℓ'' : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓ'')) where 
    field
      elimPropPG : {B : PresentedGroup → Type ℓ''}
                   (bTrunc : ∀ x → isProp (B x))
                   (b : ∀ x → B (η x))
                   (b· : ∀ {x y} → B x → B y → B (x · y))
                   (bε : B ε) 
                   (bInv : ∀ {x} → B x → B (inv x)) → ∀ x → B x
      recPG : (B : Group ℓ'')
              (b : A → ⟨ B ⟩)
              (Brel : ∀ ix →
                 foldr ( GroupStr._·_ (snd B) ∘ ⊎.elim b (λ y → GroupStr.inv (snd B) (b y)))
                                                  (b (snd (relator ix))) (fst (relator ix))
                   ≡ GroupStr.1g (snd B) )
              → (GroupHom presentedGroupGroup B)


  open Eliminators

  PresentedGeneratedBy' : (E : Eliminators (ℓ-max ℓ ℓ')) →
        (∀ a → Σ _ λ b → Path (PresentedGroup) (η b) (inv (η a)))
        → ⟨ GeneratedBy (presentedGroupGroup) (η) ⟩
  PresentedGeneratedBy' E invGens =
    E .elimPropPG (λ _ → squash₁)
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

  open import Cubical.HITs.EilenbergMacLane1 as EM

       
  toConst≃ : ∀ {ℓ'} (B : Type ℓ')  
       → (E : Eliminators ℓ')
       → (f : A → singl (idEquiv B))
       → (∀ ix → _)
       → GroupHom presentedGroupGroup (idEquivsG B)
  toConst≃ B E f ff = 
    E .Eliminators.recPG _
      f ff
      
  -- toPathsInG : ∀ {ℓ'} {B : Type ℓ'} → isGroupoid B
  --     → (E : Eliminators {!!})
  --      → (A → B ≡ B)
  --      → PresentedGroup → singl (B)
  -- toPathsInG {B = B} isG E f = 
  --   E .Eliminators.elimPropPG (λ _ → isPropSingl)
  --      (λ x → B , f x) (λ _ _ → B , refl) (B , refl) λ _ →  B , refl


     -- EM.elimSet _ {B = λ _ → singl B} (λ _ → isProp→isSet isPropSingl)
     --  {!!}
     --  λ g → {!!}

     -- EM.rec _ (isOfHLevel≃ 3 isG isG)
     --   (idEquiv _) {!!} {!!}
  
     -- EM.elimSet _ {B = λ _ → singl (idEquiv B)} (λ _ → isProp→isSet isPropSingl)
     --  ((idEquiv _) , refl)
     --  λ g → ΣPathP {!!}
  
  -- IdsOfG : ∀ {ℓ ℓ'} {A' : Type ℓ} {B : Type ℓ'} → (E : Eliminators (ℓ-max ℓ ℓ'))
  --              → (E' : Eliminators ℓ') → (E'' : Eliminators ℓ) →
  --           (isSetA : isSet A')
  --            (m' : A → A' ≃ A') (m'' : _)
  --            (f : A' → B) → isGroupoid B →
  --                (∀ a → (a' : A') → f a' ≡ f (fst (m' a) a')) → 
  --                (g : PresentedGroup) → (a' : A')
  --                   → f a' ≡
  --                    f (fst ( fst (Eliminators.recPG E'' (Symmetric-Group _ isSetA) m' m'')
  --                     g) a') 
  -- IdsOfG E E' E'' isSetA m' m'' f isGB p =
  --    ff

  --  where
  --   m : GroupHom presentedGroupGroup (Symmetric-Group _ isSetA)
  --   m = (Eliminators.recPG E'' (Symmetric-Group _ isSetA) m' m'')

  --   ff : ∀ (g : PresentedGroup) a' →
  --          f a' ≡
  --          f (fst (fst (recPG E'' (Symmetric-Group _ isSetA) m' m'') g) a')
  --   ff (η x) a' = {!p x a'!}
  --   ff (g · g₁) a' = {!!}
  --   ff ε a' = {!!}
  --   ff (inv g) a' = {!!}
  --   ff (assoc g g₁ g₂ i) a' = {!!}
  --   ff (idr g i) a' = {!!}
  --   ff (idl g i) a' = {!!}
  --   ff (invr g i) a' = {!!}
  --   ff (invl g i) a' = {!!}
  --   ff (rel ix i) a' = {!!}
  --   ff (trunc g g₁ x y i i₁) a' = {!!}

  --     snd ((zz'' a') g) ∙ {!!} 

  --   where
  --     zz : PresentedGroup → singl f
  --     zz = E .elimPropPG (λ _ → isPropSingl)
  --       (λ a → f ∘ fst ((fst m) (η a)) , funExt (p a)) (λ _ _ → (_ , refl)) (_ , refl) (idfun _)

  --     zz'' : ∀ a' → PresentedGroup → singl (f a')
  --     zz'' a' = E' .elimPropPG (λ _ → isPropSingl)
  --       (λ x → f (fst (fst m (η x)) a') , p x a')
  --        (λ x x₁ → _ , refl) (_ , refl) λ _ → _ , refl


  --     zz' : ∀ a' → GroupHom presentedGroupGroup (LoopsOfG isGB (f a'))
  --     zz' a' = E' .recPG _ (λ a → {!p a a'!}) {!!}


  -- bound : ℕ
  -- bound = 6

  -- module Eliminators (Bound : ∀ ix → length (fst (relator ix)) < bound ) where

  --  module elimProp   {B : PresentedGroup → Type ℓ''}
  --                    (bTrunc : ∀ x → isProp (B x))
  --                    (b : ∀ x → B (η x))
  --                    (b· : ∀ {x y} → B x → B y → B (x · y))
  --                    (bε : B ε) 
  --                    (bInv : ∀ {x} → B x → B (inv x))
  --                      where

  --    f : ∀ x → B x


  --    -- f'' : ∀ ix → B (rlt ix)
  --    -- f'' ix = foldrDep {B = B} {a = η (snd (relator ix))} {f = _·_ }
  --    --   (λ a {a'} → b· (f a))
  --    --     (b ((snd (relator ix)))) (mapList (⊎.elim η (λ b → inv (η b))) (fst (relator ix)))

  --    f (η x) = b x
  --    f (x · x₁) = b· (f x) (f x₁)
  --    f ε = bε
  --    f (inv x) = bInv (f x)
  --    f (assoc x x₁ x₂ i) =
  --      isProp→PathP
  --        (λ i → bTrunc (assoc x x₁ x₂ i))
  --        (b· (f x) (b· (f x₁) (f x₂)))
  --        (b· (b· (f  x) (f x₁)) (f x₂))
  --         i 
  --    f (idr x i) =
  --          isProp→PathP
  --        (λ i → bTrunc (idr x i))
  --        (f x)
  --        (b· (f x) bε)
  --         i 

  --    f (idl x i) =
  --        isProp→PathP
  --        (λ i → bTrunc (idl x i))
  --        (f x)
  --        (b· bε (f x))
  --         i 

  --    f (invr x i) =
  --        isProp→PathP
  --        (λ i → bTrunc (invr x i))
  --        (b· (f x) (bInv (f x)))
  --        bε
  --         i 

  --    f (invl x i) =
  --       isProp→PathP
  --        (λ i → bTrunc (invl x i))
  --        (b· (bInv (f x)) (f x))
  --        bε
  --         i 

  --    -- f (rel ix i) with f (rlt ix)
  --    -- ... | w = ?

  --    f (rel ix i) with  fst (relator ix) | Bound ix | (isProp→PathP (λ i → bTrunc (rel ix (~ i))) bε)
  --    ... | [] | bd | q = q (b (snd (relator ix))) (~ i) 
  --    ... | x ∷ xs | bd | q = {!x!}
  --    -- ... | [] | bd | q = {!!}
  --    -- ... | x ∷ [] | bd | q = {!!}
  --    -- ... | l@(x ∷ x₁ ∷ []) | bd | q = {!!}
  --    -- -- q {!!} (~ i)
  --    -- ... | x ∷ x₁ ∷ x₂ ∷ [] | bd | q = {!!}
  --    -- ... | x ∷ x₁ ∷ x₂ ∷ x₃ ∷ w | bd | q = {!!}
     


  --    -- with (relator ix) | Bound ix | isProp→PathP (λ i → bTrunc (rel ix i)) {!foldr ? (b (snd (relator ix))) (fst (relator ix))!} bε
  --    -- ... | [] , a | ww | q = {!  !}
  --    -- ... | x ∷ [] , a | ww | q = {!!}
  --    -- ... | x ∷ x₁ ∷ [] , a | ww | q = {!!}
  --    -- ... | x ∷ x₁ ∷ x₂ ∷ [] , a | ww | q = {!!}
  --    -- -- ... | x ∷ x₁ ∷ x₂ ∷ x₃ ∷ fst₁ , a | ()
  --    -- -- ... | [] , snd₁ = {!!}
  --    -- -- ... | x ∷ xs , snd₁ = {!!}

  --    f (trunc x y p q i i₁) =
  --      isOfHLevel→isOfHLevelDep 2 (λ x → isProp→isSet (bTrunc x))
  --        (f x) (f y) (cong f p) (cong f q) (trunc x y p q) i i₁
         
  --    -- f' ix with fst (relator ix) | Bound ix | (isProp→PathP (λ i → bTrunc (rel ix (~ i))) bε)
  --    -- ... | [] | bd | q = {!!}
  --    -- ... | x ∷ [] | bd | q = {!!}
  --    -- ... | x ∷ x₁ ∷ [] | bd | q = {!!}
  --    -- ... | x ∷ x₁ ∷ x₂ ∷ [] | bd | q = symP ({!!})
  --    -- ... | x ∷ x₁ ∷ x₂ ∷ x₃ ∷ w | bd | q = {!!}
  --    -- -- ... | x ∷ l | bd | q = {!!}



--   module rec (B : Group ℓ'') (b : A → ⟨ B ⟩) where

--     FtoB : GroupHom (freeGroupGroup A) B
--     FtoB = recFG b

--     module BG = GroupStr (snd B)
--     module BGT = GroupTheory B


--     module PGT = GroupTheory (_ , presentedGroupGroupStr)

--     rltB = (rlt' BG.1g b BG.inv (BG._·_)) 


--     module _ (Brel : (ix : Ix) → rltB (relator ix) ≡ BG.1g )
--                    -- (Brel-η : (ix : Ix) → ∀ a → η a ≡ rlt ix → b a ≡ BG.1g )
--                    -- (Brel-· :  ∀ (ix : Ix) →
--                    --   ∀ x y → x BG.· y ≡ rltB (relator ix) → (x) BG.· (y) ≡ BG.1g )
--                    -- (Brel-inv :
--                    --   (ix : Ix) → ∀ x → BG.inv x ≡ rltB (relator ix) → BG.inv (x) ≡ BG.1g )
--                         where



--       f : PresentedGroup → ⟨ B ⟩
--       f (η x) = b x
--       f (x · x₁) = f x BG.· f x₁
--       f ε = BG.1g
--       f (inv x) = BG.inv (f x)
--       f (assoc x x₁ x₂ i) = BG.·Assoc (f x) (f x₁) (f x₂) i
--       f (idr x i) = BG.·IdR (f x) (~ i)
--       f (idl x i) = BG.·IdL (f x) (~ i)
--       f (invr x i) = BG.·InvR (f x) i
--       f (invl x i) = BG.·InvL (f x) i


--       f (rel ix i) = {!Brel ix!}
--       -- Brel (f x) ix (λ i → {!f (x₁ )!}) i

--       f (trunc x y p q i i₁) =
--         BG.is-set (f x) (f y) (cong f p) (cong f q) i i₁

--       gh : GroupHom presentedGroupGroup B
--       gh = f , {!!}



-- data P' {A : Type ℓ} (P : ℙ (FreeGroup A)) (x : FreeGroup A)  : Type ℓ where 
--   η : x ∈ P → P' P x
--   id∈ : x ≡ ε → P' P x
--   ·∈ : ∀ {x' y} → (x ≡ x' · y) → P' P x' → P' P y   → P' P x
--   inv∈ : ∀ {x'} → x ≡ inv x' → P' P x' → P' P x
--   norm∈ : ∀ g h →  P' P h → x ≡  (g · (h · inv g)) → P' P x 
--   truncP' : isProp (P' P x)


-- Pclo : (A : Type ℓ) (P : ℙ (FreeGroup A)) → ℙ ((FreeGroup A))
-- Pclo A P x = P' P x , truncP' 

-- FromPres : (A : Type ℓ) (P : ℙ (FreeGroup A)) → Group ℓ
-- FromPres A P = freeGroupGroup A /
--    ((Pclo A P , record { id-closed = id∈ refl ; op-closed = ·∈ refl ; inv-closed = inv∈ refl }) ,
--     λ g h x → norm∈ g h x refl)

-- module _ (A : Type ℓ) (Ix : Type ℓ) (relator : Ix → List (A ⊎ A)) where
--   open Presentation A Ix relator

--   module FG = GroupStr (snd (freeGroupGroup A)) 
--   module FGT = GroupTheory (freeGroupGroup A)

--   module PG = GroupStr (snd presentedGroupGroup) 
--   module PGT = GroupTheory (presentedGroupGroup) 

--   P : ℙ (FreeGroup A)
--   P x =  ∥ Σ Ix (λ ix → foldr (_·_ ∘ ⊎.elim η (λ b → inv (η b))) ε (relator ix) ≡ x) ∥₁ , squash₁

--   fromPres : Group ℓ
--   fromPres = FromPres A P

--   ff : GroupHom (freeGroupGroup A) presentedGroupGroup
--   ff = recFG η

--   -- fromPresented : ⟨ presentedGroupGroup ⟩ → ⟨ fromPres ⟩ 
--   -- fromPresented = {!!}

--   -- toPresented : ⟨ fromPres ⟩ →  ⟨ presentedGroupGroup ⟩ 
--   -- toPresented =
--   --   rec/ trunc
--   --        (fst ff)
--   --        ww
--   --     where
        

--   --       ww : (a b : ⟨ freeGroupGroup A ⟩) →
--   --             P' P (a FG.· FG.inv b)  → fst ff a ≡ fst ff b
--   --       ww a b (η x) = elim₁ (λ _ → trunc _ _)
--   --         (λ x₁ → let z = rel _ (fst x₁) (cong (fst ff) (sym (snd x₁)) ∙ {!!})
--   --                 in PGT.invUniqueL z ∙ PGT.invInv _) x
--   --       ww a b (id∈ x) = PGT.invUniqueL (cong (fst ff) x) ∙ PGT.invInv _
--   --       ww a b (·∈ x r r₁) = {!!}
--   --       ww a b (inv∈ {x₁} x r) =
--   --         let z = ww _ _ {!r!}
--   --         in {!!}
--   --       ww a b (norm∈ g h r x) = {!!}
--   --       ww a b (truncP' r r₁ i) = {!!}
        
--   -- GIsoPres : GroupIso fromPres presentedGroupGroup
--   -- GIsoPres = iso toPresented {!!} {!!} {!!} , {!!}

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
